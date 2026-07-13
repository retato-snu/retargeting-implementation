# Reverse a Cons/Nil list with an accumulator: rev(lst, acc) conses each head of
# lst onto acc. Reversing Cons(1, Cons(2, Cons(3, Nil()))) yields
# Cons(3, Cons(2, Cons(1, Nil()))). The expected value is the whole reversed list.
# expect: Cons(3, Cons(2, Cons(1, Nil())))
def rev(lst, acc) =
  match lst with
  | Nil() -> return acc
  | Cons(h, t) ->
      let acc2 = Cons(h, acc) in
      let r = rev(t, acc2) in
      return r
  end;
main =
  let n = Nil() in
  let l1 = Cons(3, n) in
  let l2 = Cons(2, l1) in
  let l3 = Cons(1, l2) in
  let empty = Nil() in
  let r = rev(l3, empty) in
  return r
