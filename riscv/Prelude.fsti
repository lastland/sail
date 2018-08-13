module Prelude

open Types
open State

val sign_extend : #n:int -> #m:int -> bv_t n -> int_exact m ->
                Pure (bv_t m)
                     (requires m >= n)
                     (ensures fun _ -> True)

val zero_extend : #n:int -> #m:int -> bv_t n -> int_exact m ->
                  Pure (bv_t m)
                       (requires m >= n)
                       (ensures fun _ -> True)

val slice : #n:int -> #m:int -> bv_t m -> int -> int_exact n ->
            Pure (bv_t n)
                 (requires m >= 0 && n >= 0)
                 (ensures fun _ -> True)

val get_slice_int : w:int -> int -> int -> bv_t w

val replicate_bits : #n:int -> bv_t n -> m:int -> bv_t (op_Multiply n m)

val write_ram : m:int -> n:int -> bv_t m -> bv_t m ->
                bv_t (op_Multiply 8 n) -> st bool

val read_ram : m:int -> n:int -> bv_t m -> bv_t m ->
               st (bv_t (op_Multiply 8 n))

val shift_bits_right : #n:int -> #m:int -> bv_t n -> bv_t m -> bv_t n
val shift_bits_left : #n:int -> #m:int -> bv_t n -> bv_t m -> bv_t n

let coerce_int (n:int) : int_exact n = n
