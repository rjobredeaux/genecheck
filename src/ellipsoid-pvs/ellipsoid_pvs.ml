(**
   This program is free software; you can redistribute it and/or
   modify it under the terms of the GNU General Public License as
   published by the Free Software Foundation\; either version 2 of the
   License, or (at your option) any later version.

   This program is distributed in the hope that it will be useful, but
   WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
   General Public License for more details.

   Written and (c) by Pierre-Loic Garoche ONERA, Xavier Thirioux ENSEEIHT
   and Romain Jobredeaux GEORGIA TECH
   Contact <ploc@garoche.net> for comment & bug reports
*)


open Cil_types
open Matrix.Float
open Num

let working_dir = "working_dir_pvs"

(*********************************************************************)
(*                 Plugin declaration                                *)
(*********************************************************************)
module Self = 
  Plugin.Register
    (struct
       let name = "ellipsoid-pvs" 
       let shortname = "ellipsoid-pvs"
       let help = "perform the complete proof process from annotated C code to ellipsoid specific proof strategies in PVS"
     end)

module Options =
struct
  module Enabled =
    Self.False(struct
		 let option_name = "-ellipsoid-pvs"
		 let descr = "Ellipsoid specific proofs in PVS" 
		 let help = "no help provided"
	       end)
end

(*********************************************************************)
(*                 Main functions                                    *)
(*********************************************************************)


let get_stmt_beh_ann code_ann =
  match code_ann.annot_content with
    | AStmtSpec _ -> true
    | _ -> false

let all_pis : (code_annotation * Property.identified_property list) list ref 
    = ref []

let all_glob_defs : (string * Cil_types.term) list ref = ref []

let prepost_re = Str.regexp ".*_\\(pre\\|post\\|assgfdsign\\).*"

class glob_visitor () = object
  inherit Visitor.frama_c_inplace
  method vglob_aux glob = 
    (match glob with
      |GAnnot(Dfun_or_pred(info,_),_) -> (match info.l_body with
	  |LBterm(t) -> all_glob_defs := (info.l_var_info.lv_name,t) :: !all_glob_defs
	  |_ -> ())
      |_ -> ()) ;
    Cil.DoChildren
	  
end

class property_visitor () = object
  inherit Visitor.frama_c_inplace

  method vstmt_aux stmt =
    let kf = Kernel_function.find_englobing_kf stmt in
    let annots = Annotations.code_annot stmt in
    List.iter (
      fun annot ->
	let props = Property.ip_of_code_annot kf stmt annot in
	let filtered_props = 
	  List.filter
	    (fun ip -> (* We keep only properties which names start with the name of the file *)
	      Str.string_match prepost_re (Property.Names.get_prop_name_id ip) 0
	    )
	    props
	in
	all_pis := (annot, filtered_props)::!all_pis
    ) annots;
    Cil.DoChildren
    
end

let emitter = Emitter.create "pvs-ellipsoid" [Emitter.Property_status] ~correctness:[] ~tuning:[] 


let extract_tactic annot pi = 
  Dynamic.get 
    ~plugin:"local-tactic" 
    "extract_tactic" 
    (Datatype.func2 Cil_datatype.Code_annotation.ty Property.ty (Datatype.option Datatype.string)) 
    annot
    pi


let pvs_ellipsoid_prove strategy pi =
  let select str = 
    Str.string_match 
      (Str.regexp (".*" ^ (Property.Names.get_prop_name_id pi) ^ "_WP.pvs")) str 0 
  in
  let pvs_file = 
    try
      let files = Array.to_list (Sys.readdir working_dir) in
      List.find select files
    with Not_found -> failwith "impossible to find pvs file"
  in
  Self.log ~verbose:2 "File is %s" pvs_file;
  (* We open the file and extract the theorem *)
  let theory_preamble, theory_defs, theory_thm = 
    let lexbuf = Lexing.from_channel (open_in (working_dir ^ "/" ^ pvs_file)) in
    try
      TrivialPVSParser.theory TrivialPVSLexer.token lexbuf
    with
	TrivialPVSLexer.UnexpectedToken -> (
	  Format.eprintf "Lexer problem, current string is '%s', char %i@.@?" (Lexing.lexeme lexbuf) ((Lexing.lexeme_start_p lexbuf).Lexing.pos_cnum);
	  exit 1)
  in
  Self.log ~verbose:2 "%a" TrivialPVS.pp_def theory_thm;
  (* Dealing with small bug of Why3: Abs1 -> Abs *)
  let pattern = Str.regexp "Abs1" in
  let theory_preamble = List.map (Str.global_replace pattern "Abs") theory_preamble in
  (* Create new file *)
  let new_file = working_dir ^ "/" ^ (Filename.chop_suffix pvs_file ".pvs") ^ "_automatic" in 
  let new_pvs_file = new_file ^ ".pvs" in
  let new_out = open_out new_pvs_file in
  let new_fmt = Format.formatter_of_out_channel new_out in
  TrivialPVS.print_ti new_fmt theory_preamble theory_defs theory_thm strategy;
  (* Call proveit: TODO get the result *)
  Self.log "Checking property %s..." (Property.Names.get_prop_name_id pi);
  let _ = Sys.command ("proveit -cq " ^ new_pvs_file) in
  (* Open the summary *)
  let summary_in = open_in (new_file ^ ".summary") in
  let found = ref false in
  try
    let line = ref "" in
    while not !found do
      let current_line = input_line summary_in in
      if  Str.string_match (Str.regexp (".*wp_thm\..*")) current_line 0 then (
	line := current_line; found := true
      )
    done;
    Self.log "retrieving results... ";
    if Str.string_match (Str.regexp (".*proved - incomplete.*")) !line 0 then
      let pvs_dep_pi = Property.ip_other "PVS unproved elements" None (Property.get_kinstr pi) in
      Property_status.emit emitter ~hyps:[pvs_dep_pi] pi Property_status.True
      (* marking the property as true, but incomplete *)
    else if  Str.string_match (Str.regexp (".*proved - complete.*")) !line 0 then
      Property_status.emit emitter ~hyps:[] pi Property_status.True
      (* Self.log "marking the property as true") *)
    else Property_status.emit emitter ~hyps:[] pi Property_status.Dont_know
      (* Self.log "marking the property as unknown") *)
  with _ -> ()


let propagate_proof_status pi =
  match Property_status.Feedback.get pi with
    | Property_status.Feedback.Unknown -> 
      Self.log ~verbose:2 "PI name is %s@.@?" (Property.Names.get_prop_name_id pi);
      Property_status.emit emitter ~hyps:[] pi Property_status.True
    | _ -> ()

let is_not_proved pi = 
  match Property_status.Feedback.get pi with
    | Property_status.Feedback.Unknown -> true
    | _ -> false
      

let list_to_matrix l m n =
  let content = Array.make_matrix m n  0. in
  let _ = List.fold_left
    (fun k e -> content.(k / n).(k mod n)<- e ;k+1) 0 l
  in matrix_of_array_array content

let get_def str = 
  let rec aux  = function
    |(s,t)::_ when s=str -> Some t
    | _:: q -> aux q
    | _ -> None
  in aux !all_glob_defs

let extract_int term = match term.term_node with
  |TConst(Integer(i,_)) -> Integer.to_int i
  |_ -> failwith "expected integer, found something else"
  
(*replace with the following functions for rational propagation*)

(* let string_to_num_ext s =  *)
(*   Str.string_match  *)
(*     (Str.regexp "\\([0-9]*\\\)\\(\\.?\\)\\([0-9]*\\\)\\(e\\|E?\\)\\(-?\\)\\([0-9]*\\\)") *)
(*     s 0; *)
(*   let tot_left_s = (Str.matched_group 1 s) ^ (Str.matched_group 3 s) in *)
(*   let tot_left =  *)
(*     if (String.length tot_left_s > 0) *)
(*     then (num_of_string tot_left_s) *)
(*     else (failwith "string_to_num failed, no digits") in *)
(*   let post_dot = String.length (Str.matched_group 3 s) in *)
(*   let left_side = match (String.length (Str.matched_group 2 s)) with *)
(*     |0 -> tot_left *)
(*     |_ -> tot_left // ((Int 10) **/ (Int post_dot)) in *)
(*   match (String.length (Str.matched_group 4 s)) with *)
(*     |0 -> left_side *)
(*     |_ -> let exponent = Str.matched_group 6 s in  *)
(* 	  (match String.length exponent with  *)
(* 	    |0 -> failwith "string_to_num failed, e but no exponent" *)
(* 	    |_ -> (match String.length (Str.matched_group 5 s) with *)
(* 		|0 -> left_side */ ((Int 10) **/ (num_of_string exponent)) *)
(* 		|_ -> left_side // ((Int 10) **/ (num_of_string exponent)))) *)


(* let rec extract_value term = match term.term_node with *)
(*   |TConst(LReal(r)) -> string_to_num_ext r.r_literal *)
(*   |TUnOp(op,t) -> (match op with  *)
(*       |Neg -> minus_num (extract_value t) *)
(*       |_ -> failwith "unexpected unary operator") *)
(*   |_ -> failwith (Format.sprintf "expected float, found something else") *)


let rec extract_value term : float  = match term.term_node with
  |TBinOp (op,t1,t2) -> (match op with
    |PlusA -> (extract_value t1) +. (extract_value t2)
    |MinusA -> (extract_value t1) -. (extract_value t2)
    |Mult -> (extract_value t1) *. (extract_value t2)
    |Div -> (extract_value t1) /. (extract_value t2)
    |_ -> failwith(Format.sprintf "unexpected binary operator"))
  |TConst(LReal(r)) ->  r.r_nearest
  |TConst(Integer(i,_)) -> Integer.to_float i
  |TUnOp(op,t) -> (match op with 
      |Neg -> -. (extract_value t)
      |_ -> failwith (Format.sprintf "unexpected unary operator"))
  |Tapp(info,_,terms) -> (match info.l_var_info.lv_name with
    |"dot_prod" -> (match (List.map extract_matrix terms) with
      |a::b::_ -> let m  =mult_matrix (transpose_matrix a) b in
		  get m 0 0
      |_ -> failwith (Format.sprintf "misuse of dot_prod"))
    |"\\sqrt" -> sqrt(extract_value (List.hd terms))
    |s -> failwith (Format.sprintf "unimplemented %s in extract_value" s))
  |TLval(term_val) -> (match (fst term_val) with
    | TVar(t) -> (match (get_def t.lv_name) with 
      |Some new_term -> extract_value new_term
      |_ -> failwith "lvalue not found in global declarations")
    | _ -> failwith "expected an lvalue of type TVar, didn't get it")
(*  |_ -> failwith (Format.sprintf "expected float, found something else")*)
  |	TSizeOf ( typ	)-> failwith (Format.sprintf "	size of a given C type.	")
  |	TSizeOfE ( term	)-> failwith (Format.sprintf "	size of the type of an expression.	")
  |	TSizeOfStr ( string	)-> failwith (Format.sprintf "	size of a string constant.	")
  |	TAlignOf ( typ	)-> failwith (Format.sprintf "	alignment of a type.	")
  |	TAlignOfE ( term	)-> failwith (Format.sprintf "	alignment of the type of an expression.	")
  |	TCastE ( typ , term	)-> failwith (Format.sprintf "	cast to a C type.	")
  |	TAddrOf ( term_lval	)-> failwith (Format.sprintf "	address of a term.	")
  |	TStartOf ( term_lval	)-> failwith (Format.sprintf "	beginning of an array.	")
  |	Tlambda ( quantifiers , term	)-> failwith (Format.sprintf "	lambda abstraction.	")
  |	TDataCons ( logic_ctor_info , terml	)-> failwith (Format.sprintf "	constructor of logic sum-type.	")
  |	Tif ( term1 , term2 , term3	)-> failwith (Format.sprintf "	conditional operator	")
  |	Tat ( term , logic_label	)-> failwith (Format.sprintf "	term refers to a particular program point.	")
  |	Tbase_addr ( logic_label , term	)-> failwith (Format.sprintf "	base address of a pointer.	")
  |	Toffset ( logic_label , term	)-> failwith (Format.sprintf "	offset from the base address of a pointer.	")
  |	Tblock_length ( logic_label , term	)-> failwith (Format.sprintf "	length of the block pointed to by the term.	")
  |	Tnull	-> failwith (Format.sprintf "	the null pointer.	")
  |	TLogic_coerce ( logic_type , term	)-> extract_value term
  |	TCoerce ( term , typ	)-> failwith (Format.sprintf "	coercion to a given C type.	")
  |	TCoerceE ( term , term2	)-> failwith (Format.sprintf "	coercion to the type of a given term.	")
  |	TUpdate ( term , term_offset , term2	)-> failwith (Format.sprintf "	functional update of a field.	")
  |	Ttypeof ( term	)-> failwith (Format.sprintf "	type tag for a term.	")
  |	Ttype ( typ	)-> failwith (Format.sprintf "	type tag for a C type.	")
  |	Tempty_set	-> failwith (Format.sprintf "	the empty set.	")
  |	Tunion ( termlist	)-> failwith (Format.sprintf "	union of terms.	")
  |	Tinter ( termlist	)-> failwith (Format.sprintf "	intersection of terms.	")
  |	Tcomprehension ( term , quantifier  , predicatenamedoption	)-> failwith (Format.sprintf "	set defined in comprehension ()	")
  |	Trange ( termoption , termoption2	)-> failwith (Format.sprintf "	range of integers.	")
  |	Tlet ( logic_info , term	)-> failwith (Format.sprintf "	local binding	")
      

    
and extract_matrix term = match term.term_node with
  |Tapp(info,_,terms) -> (match info.l_var_info.lv_name with
      |"inverse" -> inverse (extract_matrix (List.hd terms))
      |"block_m" -> (match (List.map extract_matrix terms) with
	  |(a::b::c::d::_) -> block_matrix a b c d
	  |_ -> failwith "misuse of block_m")
      |"zeros" -> (match (List.map extract_int terms) with
	  |(m::n::_) -> zeros_matrix m n
	  |_ -> failwith "improper use of zeros")
      |"mat_scalar_mult" -> (match terms with
	  |a::m::_ -> mult_scalar_matrix (extract_value a) (extract_matrix m)
	  |_ -> failwith "misuse of scalar mult")
      |"vect_scalar_mult" -> (match terms with
	|a::v::_ -> mult_scalar_matrix (extract_value a) (extract_matrix v)
	|_ -> failwith "misuse of vect scalar mult")
      |"V2Ml" -> transpose_matrix (extract_matrix (List.hd terms))
      |"block_v" -> (match terms with
	|v1::v2::_ -> block_v_matrix (extract_matrix v1) (extract_matrix v2)
	|_ -> failwith "misuse of block_v")
      |"mat_add" -> (match (List.map extract_matrix terms) with
	  |a::b::_ -> add_matrix a b
	  |_ -> failwith "misuse of add_mat")
      |"mat_mult" -> (match (List.map extract_matrix terms) with
	  |a::b::_ -> mult_matrix a b
	  |_ -> failwith "misuse of mat_mult")
      |"eye" -> ident_matrix (extract_int (List.hd terms))
      |"transpose" -> transpose_matrix (extract_matrix (List.hd terms))
      |"vect_mult" ->(match (List.map extract_matrix terms) with
	  |a::b::_ -> mult_matrix a b
	  |_ -> failwith "misuse of vect_mult")
      |s when Str.string_match (Str.regexp "mat_of_\\([0-9]+\\)x\\([0-9]+\\)_scalar") s 0 ->
	let m = int_of_string (Str.matched_group 1 s) in
	let n = int_of_string (Str.matched_group 2 s) in
	(* failwith (Format.sprintf "blah %s %i %i %i" s m n (List.length terms)) *)
	list_to_matrix (List.map extract_value terms) m n
      |s when Str.string_match (Str.regexp "vect_of_\\([0-9]+\\)_scalar") s 0 ->
	let m = int_of_string (Str.matched_group 1 s) in
	let n = 1 in
	(* failwith (Format.sprintf "blah %s %i %i %i" s m n (List.length terms)) *)
	list_to_matrix (List.map extract_value terms) m n
      |_ -> (match info.l_body with
	  |LBterm(t) -> extract_matrix t
	  |_ -> failwith "unidentified matrix identifer"))
  |TLval(term_val) -> (match (fst term_val) with
      | TVar(t) -> (match (get_def t.lv_name) with 
	  |Some new_term -> extract_matrix new_term
	  |_ -> failwith "lvalue not found in global declarations")
      | _ -> failwith "expected an lvalue of type TVar, didn't get it")
  |_ -> failwith "unidentified matrix"
    
let prove_pos_def pi = 
  match Property.get_behavior pi with
    | Some beh -> (match beh.b_requires, beh.b_post_cond with
	|r1 ::_, (_,p1):: _ -> (match r1.ip_content,p1.ip_content with 
	    | Papp(_,_,r :: _), Papp(_,_,p::_) ->
	      Self.log "Last Ellipsoid is:";
	      Self.log "%a" (fun fmt m-> Format.fprintf fmt "[%a]" (Utils.fprintf_list ~sep:"; " (Utils.fprintf_list ~sep:", " (Floating_point.pretty_normal ~use_hex:true))) (matrix_to_list_list m)) (extract_matrix r);
	      let q = sub_matrix (extract_matrix p) (extract_matrix r) in
	      let q_sym = mult_scalar_matrix 0.5 (add_matrix q (transpose q)) in
	      if (Posdef.check (matrix_to_array_array q_sym))
	      then (
		Property_status.emit emitter ~hyps:[] pi Property_status.True; 
		Self.log "Successfully checked that %a is positive definite" 
		  pp_matrix q_sym)
	      else (
		Self.log "Failed to check that %a is positive definite" 
		  pp_matrix (sub_matrix (extract_matrix p) (extract_matrix r));
		Self.log "Listing values of all computed variables : \n";
		List.iter 
		  (fun (s,t) -> Self.log "%s = %a\n" s 
		    (fun fmt t -> try (pp_matrix fmt (extract_matrix t)) with
		    |_ -> (Format.pp_print_float fmt (extract_value t))) t) !all_glob_defs
	      )
	    | _,_ -> Self.log "posdef check failed!")
	|_,_ -> Self.log "behavior %s is missing requirements of postconditions for posdef " beh.b_name;)
    | _ -> Self.log "blah"
      
let prove_pi annot pi =
  Dynamic.get ~plugin:"Wp" "wp_compute_ip" 
    (Datatype.func Property.ty Datatype.unit) pi;
  if is_not_proved pi then (
    let strategy = extract_tactic annot pi in
    match strategy with
      |Some "PosDef" -> prove_pos_def pi
      |_ -> pvs_ellipsoid_prove strategy pi;
 	(* propagate_proof_status pi *)
  )

	      
(*********************************************************************)
(*                  Plugin main function                             *)
(*********************************************************************)
   
    
let run () =
  if Options.Enabled.get () then (
    Dynamic.load_module "LocalTactics";
    Dynamic.load_module "Wp";
    if not (Dynamic.is_plugin_present "Wp") then (failwith "Need WP plugin" );
    if not (Dynamic.is_plugin_present "LocalTactics") then (failwith "Need local-tactic plugin" );
    
    (* Creating output directory for PVS files *)
    let _ = Sys.command ("mkdir -p " ^ working_dir) in
    
    (* Setting basic Wp plugin parameters *)
    Dynamic.Parameter.StringList.set "-wp-model" ["Typed+real"];
    Dynamic.Parameter.StringList.set "-wp-prover" ["why3:PVS"];
    Dynamic.Parameter.StringList.set "-wp-why-opt" ["-o"; working_dir];
    
    (* Only if .why files needed *)
    (* Dynamic.Parameter.String.set "-wp-out" working_dir; *)
    
    Ast.compute ();
    let prop_visitor = new property_visitor () in
    let glob_visitor = new glob_visitor () in

    (*Iterate to form a table of matrix definitions *)
    Visitor.visitFramacFileSameGlobals glob_visitor (Ast.get ());
    (* Iterate on program to accumulate properties *)
    Visitor.visitFramacFileSameGlobals prop_visitor (Ast.get ());
    let (proven,tot) = List.fold_left (fun (tot_proven,tot) (annot, pis) ->
      let ok =
      	List.fold_left (
      	  fun res pi ->
      	    prove_pi annot pi;
      	    match Property_status.Feedback.get pi with
      	      | Property_status.Feedback.Considered_valid 
      	      | Property_status.Feedback.Valid
      	      | Property_status.Feedback.Valid_under_hyp ->  res
      	      | Property_status.Feedback.Unknown -> false
      	      | _ ->  res
      	) true pis in
      if not ok then
      	(Self.log "Failed to prove Annotation: %a" Printer.pp_code_annotation annot;
	 (tot_proven,tot+1))
      else ( 
	Self.log "Successfully checked validity of annotation: %a" 
	  Printer.pp_code_annotation annot;
	(tot_proven+1, tot+1))
    ) (0,0) !all_pis in
    Self.log "Global Summary: Proved %i / %i properties." proven tot
  )    
    
  (** Extend the Frama-C entry point (the "main" of Frama-C). *)
  let () = Db.Main.extend run
    
