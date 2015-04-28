
type theory = string list * string list * string
    
let pp_def = Format.pp_print_string
  
let rec fprintf_list ~sep:sep f fmt = function
  | []   -> ()
  | [e]  -> f fmt e
  | x::r -> Format.fprintf fmt "%a%(%)%a" f x sep (fprintf_list ~sep f) r

let rename_thm thm =
  let pattern_thm =  Str.regexp "THEOREM " in
  Str.global_replace pattern_thm "bool = " thm
        
let filter_defs defs = 
  List.filter (fun s -> 
    not (List.exists (fun pat ->
      try 
	let _ = Str.search_forward (Str.regexp pat) s 0 in
	true
      with Not_found -> false
    ) ["eqmem"; "havoc"; "eqb"])
  ) defs
    
let intro wp_suffix = 
  "IMPORTING linalg@matrices, linalg@matrix_operator, linalg@ellipsoid, WP" ^ wp_suffix ^ "\n" ^ 
"\n" ^ 
"  Vector_no_param: TYPE = [# length: posnat, vect: vectors[length].Vector #]\n" ^ 
"\n" ^ 
"  Zero_ext(i,j:int) : Matrix\n" ^ 
"  Matrix_select_ext(M: Matrix, i, j: int): real\n" ^ 
"  Vector_select_ext(V: Vector_no_param, i: int): real\n" ^ 
"  Eye_ext(i:int) :Matrix\n" ^ 
"\n" ^ 
"  Zero_mat_ti(i: int, j:int): Matrix =\n" ^ 
"  if i>0 & j>0\n" ^ 
"  then Zero_mat(i,j)\n" ^ 
"  else Zero_ext(i,j)\n" ^ 
"  endif\n" ^ 
"\n" ^ 
"  Matrix_select(M: Matrix, i, j: int): real =\n" ^ 
"   if 0 <= i & i < M`rows and 0 <= j & j < M`cols\n" ^ 
"   then M`matrix(i,j)\n" ^ 
"   else Matrix_select_ext(M, i, j)\n" ^ 
"   endif\n" ^ 
"\n" ^ 
"  Vector_select(V: Vector_no_param, i:int):real =\n" ^ 
"   if 0<= i AND i< V`length\n" ^ 
"   then V`vect(i)\n" ^ 
"   else Vector_select_ext(V,i)\n" ^ 
"   endif\n" ^ 
"\n" ^ 
"  Matrix_mult_ext(M1, M2: Matrix): Matrix\n" ^ 
"\n" ^ 
"  Matrix_mult(M1, M2: Matrix): Matrix =\n" ^ 
"    if M1`cols = M2`rows then M1 * M2 else Matrix_mult_ext(M1, M2) endif\n" ^ 
"\n" ^ 
"  Matrix_add_ext(M1, M2: Matrix): Matrix\n" ^ 
"\n" ^ 
"Matrix_add(M1, M2: Matrix): Matrix =\n" ^ 
"    if M1`cols = M2`cols and M1`rows = M2`rows then M1+M2 else Matrix_add_ext(M1,M2) endif\n" ^ 
"\n" ^ 
"  Block_ext(M1,M2,M3,M4:Matrix) : Matrix\n" ^ 
"\n" ^ 
"  Block_ti(M1,M2,M3,M4:Matrix) : Matrix =\n" ^ 
"  if M1`rows=M2`rows & M1`cols=M3`cols & M4`cols=M2`cols & M4`rows = M3`rows\n" ^ 
"  then Block2M(M2Block(M1`rows,M4`rows,M1`cols,M4`cols)(M1,M3,M2,M4))\n" ^ 
"  else (Block_ext(M1,M2,M3,M4))\n" ^ 
"  endif	\n" ^ 
"\n" ^ 
"Vector_mult_ext (M:Matrix, V:Vector_no_param) : Vector_no_param\n" ^ 
"Vector_mult (M:Matrix, V:Vector_no_param): Vector_no_param = \n" ^ 
"   if M`cols = V`length then (# length := M`rows, vect:=M*V`vect #) else Vector_mult_ext(M,V) endif\n" ^ 
"\n" ^ 
"Dot_prod_ext (V1, V2:Vector_no_param) : real\n" ^ 
"*(V1, V2:Vector_no_param) : real = if V1`length = V2`length then V1`vect*V2`vect else Dot_prod_ext(V1,V2) endif\n" ^ 
"\n" ^ 
"semidefpos_ext(M: Matrix): boolean \n" ^ 
"semidefpos?( M: Matrix): boolean = if square?(M) then semidef_pos?(M) else semidefpos_ext(M) endif\n" ^ 
"\n" ^ 
"in_ellipsoid_ext?(Q: Matrix,x: Vector_no_param) : bool\n" ^ 
"in_ellipsoidQ?(Q: Matrix, x: Vector_no_param):\n" ^ 
"		  MACRO bool =\n" ^ 
"		  	IF x`length = Q`cols AND Q`cols=Q`rows	\n" ^ 
"			THEN in_ellipsoid_Q?(x`length, Q,x`vect)\n" ^ 
"			ELSE in_ellipsoid_ext?(Q,x)\n" ^ 
"			ENDIF\n" ^ 
""

let ti = "{{ a_matrix := Matrix,\n" ^ 
"  	   		  a_vector := Vector_no_param,\n" ^ 
"			  l_vect_select := Vector_select,\n" ^ 
" 			  l_vect_length := LAMBDA (v:Vector_no_param): v`length,\n" ^ 
"  	    		  l_mat_row := LAMBDA (M:Matrix): M`rows,\n" ^ 
" 			  l_mat_col := LAMBDA (M:Matrix): M`cols,\n" ^ 
"	    		  l_mat_select := Matrix_select,\n" ^ 
"			  l_mat_mult := Matrix_mult,\n" ^ 
"			  p_in_ellipsoidq := in_ellipsoidQ?,\n" ^ 
"	 		  l_transpose:= transpose,\n" ^ 
"			  l_zeros := Zero_mat_ti,\n" ^ 
"			  l_mat_scalar_mult := *,\n" ^ 
"			  l_block_m :=Block_ti ,\n" ^ 
"			  l_eye := LAMBDA (i:int) :if i>0 then I(i) else Eye_ext(i) endif, \n" ^ 
"			  l_vect_mult := Vector_mult,\n" ^ 
"			  l_dot_prod := *,\n" ^ 
"			  p_symmetric := symmetric?,\n" ^ 
"			  p_semidefpos := semidefpos?,\n" ^ 
"			  l_v2ml := LAMBDA (V:Vector_no_param): V2Ml(V`length,V`vect),\n" ^ 
"			  p_in_ellipsoidq_ext := in_ellipsoid_ext?,\n" ^ 
"			  p_semidefpos_ext := semidefpos_ext,\n" ^ 
"			  l_dot_prod_ext := Dot_prod_ext,\n" ^ 
"			  l_eye_ext := Eye_ext,\n" ^ 
"			  l_vect_mult_ext := Vector_mult_ext,\n" ^ 
"			  l_mat_mult_ext := Matrix_mult_ext,\n" ^ 
"			  l_mat_add_ext := Matrix_add_ext,\n" ^ 
"			  l_zeros_ext := Zero_ext,\n" ^ 
"			  l_block_m_ext := Block_ext }}\n" ^ 
""

let pp_strategy fmt s =
  match s with
    | Some s -> 
      Format.fprintf fmt "%%|- wp_thm: PROOF (%s) QED" s
    | None -> Format.fprintf fmt "%% no identified strategy"

let cpt = ref 0
let get_new_suffix () =
  incr cpt;
  string_of_int !cpt

let print_ti fmt preamble defs thm strategy =
  let wp_suffix = get_new_suffix () in
  Format.fprintf fmt "@[<v 1>WP%s: THEORY@,@[<v 1>BEGIN@,%a@,@,%a@,@,%a@]@,@]@.END WP%s@.@.@."
    wp_suffix
    (fprintf_list ~sep:"@," (fun fmt s -> Format.fprintf fmt "IMPORTING %s" s)) preamble
    (fprintf_list ~sep:"@,@," Format.pp_print_string) (filter_defs defs)
    Format.pp_print_string (rename_thm thm)
    wp_suffix;
  Format.fprintf fmt 
    "@[<v 1>TIWP%s: THEORY@,@[<v 1>BEGIN@,%s@,@,@[<v 5>IMPORTING WP%s %s@]@,@,%s@,%a@]@,@]@.END TIWP%s@."
    wp_suffix
    (intro wp_suffix)
    wp_suffix
    ti
    "wp_thm: THEOREM wp"
    pp_strategy strategy
    wp_suffix

     
