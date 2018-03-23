default Order dec

$include <flow.sail>
$include <arith.sail>

infix 4 ...

type operator ... ('n : Int) ('m : Int) = {'o, 'n <= 'o <= 'm. atom('o)}

val branch : forall 'n, 0 <= 'n <= 63. atom('n) -> 0 ... 63

function branch x = {
  let y = x;
  if y < 32 then {
    let z = 31;
    z + 32
  } else y - 32
}
