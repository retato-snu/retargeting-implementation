# expect: 30
def choose(x, y) =
  let z = iszero(x) in
  match z with
  | True() ->
      let p = y * y in
      return p
  | False() ->
      let p = x * y in
      let r = p - 3 in
      return r
  end;
main =
  let a = 0 in
  let b = 5 in
  let r1 = choose(a, b) in
  let c = 2 in
  let d = 4 in
  let r2 = choose(c, d) in
  let neg = 0 - r2 in
  let total = r1 - neg in
  return total
