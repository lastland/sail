module State

open FStar.List.Tot

open Util
open Regs

noeq type state = {
  ok : bool;
  regs : regmap
}

let state_eq (s0:state)(s1:state):Type0 =
  s0.ok == s1.ok /\
  equal s0.regs s1.regs
 (* Define a stateful monad to simplify defining the instruction semantics *)
let st (a:Type) = state -> option a * state

unfold
let return (#a:Type) (x:a) :st a =
  fun s -> Some x, s

unfold
let bind (#a:Type) (#b:Type) (m:st a) (f:a -> st b) :st b =
  fun s0 ->
    let x, s1 = m s0 in
    match x with
    | Some x' ->
      let y, s2 = f x' s1 in
      y, {s2 with ok=s0.ok && s1.ok && s2.ok}
    | None -> None, {s1 with ok=false}

unfold
let get : st state =
  fun s -> Some s, s

unfold
let set (s:state) : st unit =
  fun _ -> None, s

unfold
let fail (#a:Type) : st a =
  fun s -> None, {s with ok=false}

unfold
let check_imm (valid:bool) : st unit =
  if valid then
    return ()
  else
    fail

unfold
let check (valid: state -> bool) : st unit =
  s <-- get;
  if valid s then
    return ()
  else
    fail

unfold
let run (f:st unit) (s:state) : state = snd (f s)

unfold
let read_reg (r:reg_t):
  st (l:list (regval r){length l = n_regtype r}) =
  s <-- get;
  let l:(l:list (regtyp r){length l = n_regtype r}) =
    (lemma_range_length (n_regtype r);
     reglist r) in
  let l':(l:list (regval r){length l = n_regtype r}) =
    map (fun x -> s.regs r x) l in
  return l'

unfold
let update_reg' (r:reg_t) (n:regtyp r) (v:regval r) : st unit =
  s <-- get;
  set ({s with regs = update_regmap r n v s.regs})

unfold
let update_reg (r:reg_t)
  (l:list (regval r){length l = n_regtype r}) : st unit =
  s <-- get;
  set ({s with regs = fun r' -> if r = r' then
          let f : regtyp r -> regval r =
            fun n -> List.Tot.index l n in f
        else s.regs r'})
