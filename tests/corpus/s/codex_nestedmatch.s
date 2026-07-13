# expect: False()
def both(pair) =
  match pair with
  | Pair(a, b) ->
      match a with
      | True() ->
          match b with
          | True() ->
              let out = True() in
              return out
          | False() ->
              let out = False() in
              return out
          end
      | False() ->
          let out = False() in
          return out
      end
  end;
main =
  let t = True() in
  let f = False() in
  let p = Pair(t, f) in
  let r = both(p) in
  return r
