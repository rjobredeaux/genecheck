/*@ logic matrix eye(integer i);
  @ logic matrix zeros(integer row, integer col);
  @ logic matrix block_m (matrix a11, matrix a12, 
  @                       matrix a21, matrix a22);
  @ logic vector block_v (vector v1, vector v2);
  @ logic matrix mat_of_2x2_scalar(real x0000, 
  @         real x0001, real x0100, real x0101);*/

/*@ predicate symmetric (matrix P);
  @ predicate semidefpos (matrix P);
  @ predicate in_ellipsoidQ(matrix Q, vector x);*/


/*@ logic vector vect_scalar_mult (real a, vector v);
  @ logic matrix mat_scalar_mult (real a, matrix A);
  @ logic matrix mat_add(matrix A, matrix B);
  @ logic vector vect_mult(matrix A, vector x);
  @ logic matrix mat_mult(matrix A, matrix B);*/

/*@ requires in_ellipsoidQ(Q,vect_of_n_scalar(_state_->s_1,
                                            _state_->s_2,
                                            ...));
  @ ensures in_ellipsoidQ(Q,vect_of_n_scalar(_state_->s_1,
                                           _state_->s_2,
                                           ...));*/
void example_compute(t_example_io *_io_, t_example_state *_state_){
...
  /*@ requires pre_i
    @ ensures post_i
    @ PROOF_TACTIC (use_strategy ( strategy_i ) )*/
  {
  // instruction i;
  }
  ...
}

/*@  logic matrix mat_add(matrix A, matrix B);
  @  logic matrix mat_add_ext(matrix A, matrix B);
  @  axiom mat_add_ext:
  @    \forall matrix A, matrix B;
  @    mat_row(A) != mat_row(B) ||
  @    mat_col(A) != mat_col(B) ==>
  @    mat_add(A,B) == mat_add_ext(A,B);
  @  axiom mat_add_select:
  @    \forall matrix A, B;
  @    mat_row(A) == mat_row(B) ==>
  @    mat_col(A) == mat_col(B) ==>
  @    \forall integer i, j;
  @    0 <= i < mat_row(mat_add(A, B)) ==>
  @    0 <= j < mat_col(mat_add(A, B)) ==>
  @    mat_select(mat_add(A, B), i, j) ==
  @      mat_select(A, i, j) + mat_select(B, i, j);
  @  axiom mat_add_row:
  @    \forall matrix A, B;
  @    mat_row(A) == mat_row(B) ==>
  @    mat_col(A) == mat_col(B) ==>
  @    mat_row(mat_add(A, B)) == mat_row(A);
  @  axiom mat_add_col:
  @    \forall matrix A, B;
  @    mat_row(A) == mat_row(B) ==>
  @    mat_col(A) == mat_col(B) ==>
  @    mat_col(mat_add(A, B)) == mat_col(A);*/

/*@  axiom in_ellipsoidQ:
  @    \forall matrix Q, vector x;
  @    vect_length(x)==mat_col(Q) &&
  @    mat_col(Q)==mat_row(Q) ==>
  @    ((symmetric(Q) && semidefpos(Q) && 
  @    semidefpos(block_m(eye(1),V2Ml(x),transpose(V2Ml(x)),Q))) <==>
  @    in_ellipsoidQ(Q, x));*/

/*@ requires in_ellipsoidQ(Q_prop,vect_of_n_scalar(x1,x2,...,xn);
  @ requires x_tilde1 = x1 + epsilon_1 && abs(epsilon_1) <= b1;
  @ requires x_tilde2 = x2 + epsilon_2 && abs(epsilon_2) <= b2;
  @ ...
  @ requires x_tilden = xn + epsilon_n && abs(epsilon_n) <= bn;
  @ ensures in_ellipsoidQ(Q_inv,
  @ vect_of_n_scalar(x_tilde1,x_tilde2,...,x_tilden));
  @ PROOF_TACTIC(use_strategy(PosDef) */

