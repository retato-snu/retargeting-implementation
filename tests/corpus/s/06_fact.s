# A recursive def over an integer: factorial via iszero base case, sub to recurse,
# and mul to combine. fact(4) = 4*3*2*1 = 24. Uses only sub/mul/iszero (no add).
# expect: 24
def fact(n) =
  let b = iszero(n) in
  match b with
  | True() -> return 1
  | False() ->
      let m = n - 1 in
      let r = fact(m) in
      let p = n * r in
      return p
  end;
main =
  let s = 4 in
  let r = fact(s) in
  return r
