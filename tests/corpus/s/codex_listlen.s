# expect: 4
def len(lst) =
  match lst with
  | Nil() -> return 0
  | Cons(h, t) ->
      let r = len(t) in
      let one = 1 in
      let negone = 0 - one in
      let total = r - negone in
      return total
  end;
main =
  let n = Nil() in
  let l1 = Cons(8, n) in
  let l2 = Cons(7, l1) in
  let l3 = Cons(6, l2) in
  let l4 = Cons(5, l3) in
  let r = len(l4) in
  return r
