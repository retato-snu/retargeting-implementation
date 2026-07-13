# A recursive def counting an integer down to its base case and returning 0.
# countdown(5) recurses 5 -> 4 -> ... -> 0 and returns 0 at the iszero base.
# expect: 0
def countdown(n) =
  let b = iszero(n) in
  match b with
  | True() -> return 0
  | False() ->
      let m = n - 1 in
      let r = countdown(m) in
      return r
  end;
main =
  let s = 5 in
  let r = countdown(s) in
  return r
