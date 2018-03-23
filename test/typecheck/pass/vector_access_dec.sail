default Order dec

$include <vector_dec.sail>

val test : vector(4, dec, bit) -> unit

function test v = {
  z = vector_access(v, 3);
  z = v[3]
}
