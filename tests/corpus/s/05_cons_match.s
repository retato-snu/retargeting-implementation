# Build a two-element list Cons(1, Cons(2, Nil())) and match its head exhaustively.
# The Cons branch returns the head h = 1; the Nil branch (unreached) returns 0.
# expect: 1
main =
  let one = 1 in
  let two = 2 in
  let n = Nil() in
  let c = Cons(two, n) in
  let cc = Cons(one, c) in
  match cc with
  | Cons(h, t) -> return h
  | Nil() -> return 0
  end
