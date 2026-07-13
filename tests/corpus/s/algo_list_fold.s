# Fold a Cons/Nil list to its sum (a left-to-right structural fold). Addition
# a + b is written a - (0 - b) (no add primitive). Over the list
# Cons(4, Cons(7, Cons(2, Cons(5, Nil())))) the sum is 4+7+2+5 = 18.
# expect: 18
def sum(lst) =
  match lst with
  | Nil() -> return 0
  | Cons(h, t) ->
      let r = sum(t) in
      let neg = 0 - r in
      let total = h - neg in
      return total
  end;
main =
  let n = Nil() in
  let l1 = Cons(5, n) in
  let l2 = Cons(2, l1) in
  let l3 = Cons(7, l2) in
  let l4 = Cons(4, l3) in
  let r = sum(l4) in
  return r
