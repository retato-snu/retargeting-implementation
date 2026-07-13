# maximum of Cons(2, Cons(5, Cons(3, Nil()))) using recursive equality/zero tests = 5.
# expect: 5
def leq(a, b) =
  let za = iszero(a) in
  match za with
  | True() ->
      let t = True() in
      return t
  | False() ->
      let zb = iszero(b) in
      match zb with
      | True() ->
          let f = False() in
          return f
      | False() ->
          let one = 1 in
          let a1 = a - one in
          let b1 = b - one in
          let r = leq(a1, b1) in
          return r
      end
  end;
def max2(a, b) =
  let ok = leq(a, b) in
  match ok with
  | True() -> return b
  | False() -> return a
  end;
def listmax(xs) =
  match xs with
  | Nil() -> return 0
  | Cons(h, t) ->
      match t with
      | Nil() -> return h
      | Cons(th, tt) ->
          let m = listmax(t) in
          let r = max2(h, m) in
          return r
      end
  end;
main =
  let n = Nil() in
  let three = 3 in
  let five = 5 in
  let two = 2 in
  let c3 = Cons(three, n) in
  let c2 = Cons(five, c3) in
  let c1 = Cons(two, c2) in
  let r = listmax(c1) in
  return r
