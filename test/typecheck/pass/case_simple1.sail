val case_test : forall ('b : Type). (atom(10), 'b) -> 'b

function case_test (x, y) = match (x, y) {_ => y}
