# Cons(9, Cons(8, Nil())) has at least two elements.
# expect: True()
def atleast2(xs) =
  match xs with
  | Nil() ->
      let f = False() in
      return f
  | Cons(h, t) ->
      match t with
      | Nil() ->
          let f = False() in
          return f
      | Cons(h2, t2) ->
          let tval = True() in
          return tval
      end
  end;
main =
  let n = Nil() in
  let eight = 8 in
  let nine = 9 in
  let c2 = Cons(eight, n) in
  let c1 = Cons(nine, c2) in
  let r = atleast2(c1) in
  return r
