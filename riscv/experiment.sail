val lt : forall 'n 'm. (atom('n), atom('m)) -> bool
function lt (n, m) = true

val operator + = {fstar: "op_Addition"}: forall 'n 'm. (atom('n), atom('m)) -> atom('n + 'm)
val operator - = {fstar: "op_Subtraction"}: forall 'n 'm. (atom('n), atom('m)) -> atom('n - 'm)

val f : forall 'n 'm 'p, 'n <= 'p & 'p <= 'm. (range('n, 'm), atom('p)) -> atom('p + 1)
function f (t, x) = x + 1

val g : forall 'n 'm, 'n <= 'm. range('n, 'm) -> {'p, 'n <= 'p & 'p <= 'm. atom('p)}
function g x = x

val h : forall 'n 'm. (atom('n), atom('n + 'm)) -> atom('m)
function h (x, y) = y - x

val p : atom(32) -> atom(32)
function p x = x

val q : (atom(32), atom(64)) -> atom(32)
function q (x, y) = p (h (x, y))

val r : forall 'n. range('n, 32) -> {'p, 'n <= 'p & 'p <= 32. atom('p)}
function r x = x
