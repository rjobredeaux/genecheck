(*
 * SMT-AI: an abstract interpreter to be used by a k-induction model checker
 * Copyright (C) 2010-2012  P.L. Garoche and P. Roux
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

(** This module is an interface towards a C code proving positive definiteness
    of matrices *)

(** Takes as input a square matrix of Num of size nxn and returns 1 if it
    manages to prove that the matrix is symmetric positive definite and 0
    otherwise (i.e. the matrix is either not symmetric positive definite
    or its smallest eigenvalue is too small for the proof to succeed). *)
val check : float array array -> bool

(* Local Variables: *)
(* compile-command:"make -C .." *)
(* End: *)
