module Regs

open Types

let n_reg_t : pos = 3

let rPC : reg_t = 0
let rnextPC : reg_t = 1
let rXs : reg_t = 2

let n_regtype (n : reg_t) : pos =
  match n with
  | rPC -> 1
  | rnextPC -> 1
  | rXs -> 32

let regval (n : reg_t) : Type0 =
  match n with
  | rPC -> bits 64
  | rnextPC -> bits 64
  | rXs -> bits 64
