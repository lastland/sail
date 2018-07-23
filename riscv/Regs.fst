module Regs

open Types

let n_reg_t : pos = 3

let rPC : reg_t = 0
let rnextPC : reg_t = 1
let rXs : reg_t = 2

let n_regtype (n : reg_t) : pos =
  match n with
  | 0 -> 1 (* PC *)
  | 1 -> 1 (* nextPC *)
  | 2 -> 32 (* Xs *)

let regval (n : reg_t) : Type0 =
  match n with
  | 0 -> bv_t 64 (* PC *)
  | 1 -> bv_t 64 (* nextPC *)
  | 2 -> bv_t 64 (* Xs *)
