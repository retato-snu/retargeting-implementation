# expect: 9
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
  let l1 = Cons(4, n) in
  let l2 = Cons(3, l1) in
  let l3 = Cons(2, l2) in
  let r = sum(l3) in
  return r
