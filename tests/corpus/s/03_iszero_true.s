# iszero(0) yields the Boolean constructor True(); the match takes the True branch.
# expect: 1
main =
  let z = 0 in
  let b = iszero(z) in
  match b with
  | True() -> return 1
  | False() -> return 0
  end
