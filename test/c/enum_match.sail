$include <flow.sail>

val print = "print_endline" : string -> unit

enum test = A | B

function main (() : unit) -> unit = {
  let x = A;
  match x {
    B => print("B"),
    A => print("A")
  }
}