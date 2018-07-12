module Types

open FStar.Seq
open FStar.List.Tot

let int_to_nat (n:int) : nat = if n > 0 then n else 0

let bv_t (n:int) : Type = FStar.BitVector.bv_t (int_to_nat n)

let int_exact (m:int) : Type = n:int{n = m}

let int_between (a:int) (b:int) : Type = n:int{a <= n && n <= b}

let rec splitAt_length_l : #a:Type -> n:nat -> l:list a -> m:nat -> Lemma
  (length l = n ==> m <= n ==>
   (let (l1, _) = splitAt m l in
    length l1 = m)) = fun #a n l m ->
    if m = 0 then ()
    else match l with
      | [] -> ()
      | x :: xs ->
        if n = 0 then ()
        else splitAt_length_l (n-1) xs (m-1)

let rec splitAt_length_r : #a:Type -> n:nat -> l:list a -> m:nat -> Lemma
  (length l = n ==> m <= n ==>
   (let (_, l2) = splitAt m l in
    length l2 = n - m)) = fun #a n l m ->
    if m = 0 then ()
    else match l with
      | [] -> ()
      | x :: xs ->
        if n = 0 then ()
        else splitAt_length_r (n-1) xs (m-1)

let sub_bv (#n:int) (s:bv_t n)(m:int)(o:int) : bv_t (m - (o - 1)) =
  let l = seq_to_list s in
  let _, (l1:list bool{length l1 = n - o}) = splitAt (int_to_nat o) l in
  let (l2:list bool{length l2 = m - o + 1}), _ = splitAt (int_to_nat (m - o + 1)) l1 in
  seq_of_list l2

let access_bv (#n:int)(s:bv_t n)(m:int{0 <= m && m < n}) : bool =
  FStar.Seq.index s m

let upd_bv (#n:int)(s:bv_t n)(m:int{0 <= m && m < n})(b:bool) : bv_t n =
  FStar.Seq.upd s m b
