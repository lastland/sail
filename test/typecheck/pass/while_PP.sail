default Order dec

$include <arith.sail>

function test n : int -> int = {
  i : int = 1;
  j : int = 1;
  while i < n do {
    j = i * j;
    i = i + 1
  };
  j
}
