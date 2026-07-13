# Insertion sort over a Cons/Nil list of nonnegative integers. insert(x, sorted)
# places x into the already-sorted list using a recursive leq (iszero/sub only);
# sort folds insert over the list. Sorting Cons(3, Cons(1, Cons(2, Nil())))
# yields the ordered list Cons(1, Cons(2, Cons(3, Nil()))).
# expect: Cons(1, Cons(2, Cons(3, Nil())))
def leq(a, b) =
  let za = iszero(a) in
  match za with
  | True() -> return za
  | False() ->
      let zb = iszero(b) in
      match zb with
      | True() ->
          let f = False() in
          return f
      | False() ->
          let a1 = a - 1 in
          let b1 = b - 1 in
          let r = leq(a1, b1) in
          return r
      end
  end;
def insert(x, sorted) =
  match sorted with
  | Nil() ->
      let e = Nil() in
      let c = Cons(x, e) in
      return c
  | Cons(h, t) ->
      let ok = leq(x, h) in
      match ok with
      | True() ->
          let c = Cons(x, sorted) in
          return c
      | False() ->
          let rest = insert(x, t) in
          let c = Cons(h, rest) in
          return c
      end
  end;
def sort(lst) =
  match lst with
  | Nil() ->
      let e = Nil() in
      return e
  | Cons(h, t) ->
      let s = sort(t) in
      let r = insert(h, s) in
      return r
  end;
main =
  let n = Nil() in
  let l1 = Cons(2, n) in
  let l2 = Cons(1, l1) in
  let l3 = Cons(3, l2) in
  let r = sort(l3) in
  return r
