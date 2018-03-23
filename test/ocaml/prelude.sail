default Order dec

infix 4 ==

$include <flow.sail>
$include <arith.sail>
$include <vector_dec.sail>

val eq_vec = "eq_list" : forall 'n. (bits('n), bits('n)) -> bool

val eq_string = "eq_string" : (string, string) -> bool

val eq_real = "eq_real" : (real, real) -> bool

val eq_anything = {
    ocaml: "(fun (x, y) -> x = y)",
    interpreter: "eq_anything"
  } : forall ('a : Type). ('a, 'a) -> bool

overload operator == = {eq_vec, eq_string, eq_real, eq_anything}

val vcons : forall ('n : Int) ('a : Type).
  ('a, vector('n, dec, 'a)) -> vector('n + 1, dec, 'a)

val append = "append" : forall ('n : Int) ('m : Int) ('a : Type).
  (vector('n, dec, 'a), vector('m, dec, 'a)) -> vector('n + 'm, dec, 'a)

val not_vec = "not_vec" : forall 'n. bits('n) -> bits('n)

overload ~ = {not_bool, not_vec}

val neq_vec : forall 'n. (bits('n), bits('n)) -> bool

function neq_vec (x, y) = not_bool(eq_vec(x, y))

val neq_anything : forall ('a : Type). ('a, 'a) -> bool

function neq_anything (x, y) = not_bool(x == y)

overload operator != = {neq_vec, neq_anything}

val builtin_and_vec = "and_vec" : forall 'n. (bits('n), bits('n)) -> bits('n)

val and_vec : forall 'n. (bits('n), bits('n)) -> bits('n)

function and_vec (xs, ys) = builtin_and_vec(xs, ys)

overload operator & = {and_bool, and_vec}

val builtin_or_vec = "or_vec" : forall 'n. (bits('n), bits('n)) -> bits('n)

val or_vec : forall 'n. (bits('n), bits('n)) -> bits('n)

function or_vec (xs, ys) = builtin_or_vec(xs, ys)

overload operator | = {or_bool, or_vec}

val hex_slice = "hex_slice" : forall 'n 'm. (string, atom('n), atom('m)) -> bits('n - 'm)

val __SetSlice_bits = "set_slice" : forall 'n 'm.
  (atom('n), atom('m), bits('n), int, bits('m)) -> bits('n)

val __SetSlice_int = "set_slice_int" : forall 'w. (atom('w), int, int, bits('w)) -> int

val __raw_SetSlice_int : forall 'w. (atom('w), int, int, bits('w)) -> int

val __raw_GetSlice_int = "get_slice_int" : forall 'w. (atom('w), int, int) -> bits('w)

val __GetSlice_int : forall 'n. (atom('n), int, int) -> bits('n)

function __GetSlice_int (n, m, o) = __raw_GetSlice_int(n, m, o)

val __raw_SetSlice_bits : forall 'n 'w.
  (atom('n), atom('w), bits('n), int, bits('w)) -> bits('n)

val __raw_GetSlice_bits : forall 'n 'w.
  (atom('n), atom('w), bits('n), int) -> bits('w)

val __ShiftLeft : forall 'm. (bits('m), int) -> bits('m)

val __SignExtendSlice : forall 'm. (bits('m), int, int) -> bits('m)

val __ZeroExtendSlice : forall 'm. (bits('m), int, int) -> bits('m)

val cast cast_unit_vec : bit -> bits(1)

function cast_unit_vec bitone = 0b1
and cast_unit_vec bitzero = 0b0

val print = "print_endline" : string -> unit

val putchar = "putchar" : forall ('a : Type). 'a -> unit

val concat_str = "concat_str" : (string, string) -> string

val DecStr : int -> string

val HexStr : int -> string

val BitStr = "string_of_bits" : forall 'n. bits('n) -> string

val xor_vec = "xor_vec" : forall 'n. (bits('n), bits('n)) -> bits('n)

val int_power : (int, int) -> int

val real_power = "real_power" : (real, int) -> real

overload operator ^ = {xor_vec, int_power, real_power}

val add_vec = "add_vec" : forall 'n. (bits('n), bits('n)) -> bits('n)

val add_vec_int = "add_vec_int" : forall 'n. (bits('n), int) -> bits('n)

val add_real = "add_real" : (real, real) -> real

overload operator + = {add_vec, add_vec_int, add_real}

val sub_vec : forall 'n. (bits('n), bits('n)) -> bits('n)

val sub_vec_int = "sub_vec_int" : forall 'n. (bits('n), int) -> bits('n)

val sub_real = "sub_real" : (real, real) -> real

val negate_real = "negate_real" : real -> real

overload operator - = {sub_vec, sub_vec_int, sub_real}

overload negate = {negate_range, negate_int, negate_real}

val mult_real = "mult_real" : (real, real) -> real

overload operator * = {mult_range, mult_int, mult_real}

val Sqrt = "sqrt_real" : real -> real

val gteq_real = "gteq_real" : (real, real) -> bool

overload operator >= = {gteq_atom, gteq_int, gteq_real}

val lteq_real = "lteq_real" : (real, real) -> bool

overload operator <= = {lteq_atom, lteq_int, lteq_real}

val gt_real = "gt_real" : (real, real) -> bool

overload operator > = {gt_atom, gt_int, gt_real}

val lt_real = "lt_real" : (real, real) -> bool

overload operator < = {lt_atom, lt_int, lt_real}

val RoundDown = "round_down" : real -> int

val RoundUp = "round_up" : real -> int

val abs = "abs_num" : real -> real

val quotient_real = "quotient_real" : (real, real) -> real

val quotient = "quotient" : (int, int) -> int

infixl 7 /

overload operator / = {quotient_nat, quotient, quotient_real}

val modulus = "modulus" : (int, int) -> int

infixl 7 %

overload operator % = {modulus}

val Real = "to_real" : int -> real

val shl_int = "shl_int" : (int, int) -> int

val shr_int = "shr_int" : (int, int) -> int

val min_int = "min_int" : (int, int) -> int

val max_int = "max_int" : (int, int) -> int

overload min = {min_nat, min_int}

overload max = {max_nat, max_int}

val cast ex_int : int -> {'n, true. atom('n)}

function ex_int 'n = n

val slice = "slice" : forall ('n : Int) ('m : Int), 'm >= 0 & 'n >= 0.
  (bits('m), int, atom('n)) -> bits('n)

val pow2 = "pow2" : forall 'n. atom('n) -> atom(2 ^ 'n)

