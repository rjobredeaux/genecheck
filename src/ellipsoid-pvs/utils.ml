(*
 * SMT-AI: an abstract interpreter to be used by a k-induction model checker
 * Copyright (C) 2010  P.L. Garoche and P. Roux
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 *)

let rec fprintf_list ~sep f fmt = function
  | []   -> ()
  | [e]  -> f fmt e
  | x::r -> Format.fprintf fmt "%a%(%)%a" f x sep (fprintf_list ~sep f) r

let string_of_float f =
  let f = ceil (f *. 100.) /. 100. in
  let s = string_of_float f in
  try
    let dotpos = String.index s '.' in
    String.sub s 0 (dotpos + 3)
  with Not_found | Invalid_argument _ -> s

let string_of_num s = 
  let s = Num.float_of_num s in
  string_of_float s

let num_of_strings neg left right exp =
  let neg_num neg = 
    if neg then
      Num.minus_num
    else
      fun x -> x
  in
  let base = 
    match right with
    | None -> 
      neg_num neg (Num.num_of_int (int_of_string left))
    | Some right -> (
      let nb_dec = String.length right in
      let n_s = left ^ right in
      let d_s = "1" ^ String.make nb_dec '0' in
      try
	let n = Num.num_of_string n_s in
	let d = Num.num_of_string d_s in
	neg_num neg (Num.div_num n d)
      with Failure s -> raise (Failure (s ^ ": n = " ^ n_s ^", d = " ^ d_s))
    )
  in
  match exp with 
    Some (posneg_exp, exp) -> 
      let e = int_of_string exp in
      Num.mult_num base (Num.power_num (Num.num_of_int 10) (neg_num posneg_exp (Num.num_of_int e)))
  | _ -> base
