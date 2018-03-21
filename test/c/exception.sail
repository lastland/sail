$include <flow.sail>

val print = "print_endline" : string -> unit
val print_int = "print_int" : (string, int) -> unit

union exception = {
  Epair : (atom(42), atom(24)),
  Eunknown : unit,
  Estring : string
}

val f : unit -> unit effect {escape}

function f () = throw(Estring("test"))

val g : unit -> string effect {escape}

function g () = {
  print("in g()");
  return("g return");
  throw(Estring("never thrown from g"));
}

val main : unit -> unit effect {escape}

function main () = {
  try {
    print(g());
    f(); // will throw Estring
    throw(Epair(42, 24));
    throw(Eunknown());
  } catch {
    Eunknown()   => print("Caught Eunknown"),
    Epair(x, y)  => print("Caught Epair"),
    Estring(str) => {
      print("Caught Estring");
      print(str)
    }
  };
  try () catch {
    _ => print("Unreachable!")
  };
  try throw(Epair(42, 24)) catch {
    Epair(x, _)  => {
      print("2nd try Caught Epair");
      print_int("x = ", x);
    },
    _            => ()
  };
  f();
  ()
}