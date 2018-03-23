default Order dec

$include <arith.sail>

val add_vec_int : forall ('n : Int) ('ord : Order).
  (vector('n, 'ord, bit), int) -> vector('n, 'ord, bit)

overload operator + = {add_vec_int}

val bool_not = {ocaml: "not", lem: "not"}: bool -> bool

val cast cast_0_vec_dec : forall ('l : Int).
  atom(0) -> vector('l, dec, bit)

register COUNT : vector(64, dec, bit)

register INT : bool

function test () -> unit = {
  COUNT = 0;
  while bool_not(INT) do COUNT = COUNT + 1
}
