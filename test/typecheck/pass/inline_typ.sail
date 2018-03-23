$include <arith.sail>

function test (x : atom('n), y : atom('m)) -> forall 'n 'm. atom('m + 'n) = x + y 