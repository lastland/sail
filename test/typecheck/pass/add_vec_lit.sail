default Order inc

val add_vec = {ocaml: "add_vec", lem: "add_vec"}: forall ('n : Int).
  (vector('n, inc, bit), vector('n, inc, bit)) -> vector('n, inc, bit)

val add_atom = {ocaml: "add_int", lem: "add_int"}: forall 'n 'm.
  (atom('n), atom('m)) -> atom('n + 'm)

val cast unsigned : forall ('n : Int).
  vector('n, inc, bit) -> {'m, 0 <= 'm <= 2 ^ 'n - 1. atom('n)}

overload operator + = {add_vec, add_atom}

let x : int = 3

let x : {'m, 0 <= 'm <= 30. atom('m)} = 0xF + 0x2
