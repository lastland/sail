infix 4 ==
infixl 6 /

$include <flow.sail>
$include <arith.sail>

val quotient : (int, int) -> int

overload operator / = {quotient}

union T = {C1 : int, C2 : int}

function test (x : int, y : T) -> int = match y {
  C1(z) if z == 0 => 0,
  C1(z) if z != 0 => x / z,
  C2(z) => z
}
