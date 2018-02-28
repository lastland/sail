
val bitvector_access_dec : forall 'n 'm, 'n >= 0 & 0 <= 'm <= 'n - 1.
  (vector('n, dec, bit), atom('m)) -> bit

val bitvector_access_inc : forall 'n 'm, 'n >= 0 & 0 <= 'm <= 'n - 1.
  (vector('n, inc, bit), atom('m)) -> bit

overload vector_access = {bitvector_access_inc, bitvector_access_dec}

val bv : vector(64, inc, bit) -> bit

function bv x = x[32]
