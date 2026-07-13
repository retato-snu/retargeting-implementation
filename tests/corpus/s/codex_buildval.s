# build Cons(1, Cons(2, Nil())) directly.
# expect: Cons(1, Cons(2, Nil()))
main =
  let n = Nil() in
  let two = 2 in
  let c2 = Cons(two, n) in
  let one = 1 in
  let c1 = Cons(one, c2) in
  return c1
