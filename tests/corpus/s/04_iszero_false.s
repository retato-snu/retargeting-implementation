# iszero(5) yields False(); the match takes the False branch.
# expect: 0
main =
  let z = 5 in
  let b = iszero(z) in
  match b with
  | True() -> return 1
  | False() -> return 0
  end
