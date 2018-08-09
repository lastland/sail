module Types

open FStar.Seq
open FStar.List.Tot
module B = FStar.BV

let bitzero = false

let bitone = true

let int_to_nat (n:int) : nat = if n > 0 then n else 0

let bv_t (n:int) = B.bv_t (int_to_nat n)

let pow2 (n:int) = FStar.Math.Lib.powx 2 (int_to_nat n)

let int_exact (m:int) : Type = n:int{n = m}

let int_between (a:int) (b:int) : Type = n:int{a <= n && n <= b}

val signed : #n:int -> bv_t n -> int_between (-pow2 (n - 1)) (pow2 (n - 1) - 1)
val unsigned : #n:int -> bv_t n -> int_between 0 (pow2 (n - 1))

val bv_subrange : #n:int -> bv_t n -> m:int -> o:int ->
    Pure (bv_t (m - (o - 1)))
         (requires o <= m && m <= n)
         (ensures fun _ -> True)

val bv_index : #n:int -> bv_t n -> m:int ->
    Pure bool
    (requires 0 <= m && m < n)
    (ensures fun _ -> True)

let update_list (#a:Type)(l:list a)(n:nat{n < length l})(e:a) : list a =
  let s = seq_of_list l in
  seq_to_list (upd s n e)

let bvand (#n:int) (a:bv_t n) (b:bv_t n) : Tot (bv_t n) =
  if n <= 0 then a
  else B.bvand a b

let bvxor (#n:int) (a:bv_t n) (b:bv_t n) : Tot (bv_t n) =
  if n <= 0 then a
  else B.bvxor a b

let bvor (#n:int) (a:bv_t n) (b:bv_t n) : Tot (bv_t n) =
  if n <= 0 then a
  else B.bvor a b

let bvnot (#n:int) (a:bv_t n) : Tot (bv_t n) =
  if n <= 0 then a
  else B.bvnot a

let bvshl (#n:int) (a:bv_t n) (s:nat) : Tot (bv_t n) =
  if n <= 0 then a
  else B.bvshl a s

let bvshr (#n:int) (a:bv_t n) (s:nat) : Tot (bv_t n) =
  if n <= 0 then a
  else B.bvshr a s

assume type real
