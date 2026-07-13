# expect: True()
def member(x, lst) =
  match lst with
  | Nil() ->
      let out = False() in
      return out
  | Cons(h, t) ->
      let diff = h - x in
      let eq = iszero(diff) in
      match eq with
      | True() ->
          let out = True() in
          return out
      | False() ->
          let r = member(x, t) in
          return r
      end
  end;
main =
  let n = Nil() in
  let l1 = Cons(9, n) in
  let l2 = Cons(7, l1) in
  let l3 = Cons(4, l2) in
  let target = 7 in
  let r = member(target, l3) in
  return r
