$ifndef _FLOW
$define _FLOW

val not_bool = "not" : bool -> bool
val and_bool = "and_bool" : (bool, bool) -> bool
val or_bool = "or_bool" : (bool, bool) -> bool

val eq_atom = {ocaml: "eq_int", lem: "eq", c: "eq_int"} : forall 'n 'm. (atom('n), atom('m)) -> bool

val neq_atom = {lem: "neq"} : forall 'n 'm. (atom('n), atom('m)) -> bool

function neq_atom (x, y) = not_bool(eq_atom(x, y))

val lteq_atom = "lteq" : forall 'n 'm. (atom('n), atom('m)) -> bool
val gteq_atom = "gteq" : forall 'n 'm. (atom('n), atom('m)) -> bool
val lt_atom = "lt"     : forall 'n 'm. (atom('n), atom('m)) -> bool
val gt_atom = "gt"     : forall 'n 'm. (atom('n), atom('m)) -> bool

val eq_int = {ocaml: "eq_int", lem: "eq", c: "eq_int"} : (int, int) -> bool

val lteq_int = "lteq" : (int, int) -> bool
val gteq_int = "gteq" : (int, int) -> bool
val lt_int = "lt" : (int, int) -> bool
val gt_int = "lt" : (int, int) -> bool

overload operator == = {eq_atom, eq_int}

$ifdef TEST

val __flow_test : forall 'n 'm. (atom('n), atom('m)) -> unit

function __flow_test (x, y) = {
  if lteq_atom(x, y) then {
    _prove(constraint('n <= 'm))
  } else {
    _prove(constraint('n > 'm))
  }
}

$endif

$endif
