# A recursive def traversing an encoded list with nested matches (no add, no mul):
# return the last element of Cons(1, Cons(2, Cons(3, Nil()))) = 3.
# Recursion descends the tail; the inner match distinguishes the singleton case.
# expect: 3
def last(lst) =
  match lst with
  | Cons(h, t) ->
      match t with
      | Nil() -> return h
      | Cons(h2, t2) ->
          let r = last(t) in
          return r
      end
  | Nil() -> return 0
  end;
main =
  let n = Nil() in
  let l1 = Cons(3, n) in
  let l2 = Cons(2, l1) in
  let l3 = Cons(1, l2) in
  let r = last(l3) in
  return r
