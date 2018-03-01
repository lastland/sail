default Order inc

$include <arith.sail>

val branch : forall 'n, 0 <= 'n <= 63. atom('n) -> {'m, 0 <= 'm <= 63. atom('m)}

function branch x = if x < 32 then x + 2 else x - 2
