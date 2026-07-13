# expect: 27
def power(base, exp) =
  let done = iszero(exp) in
  match done with
  | True() -> return 1
  | False() ->
      let next = exp - 1 in
      let rest = power(base, next) in
      let prod = base * rest in
      return prod
  end;
main =
  let b = 3 in
  let e = 3 in
  let r = power(b, e) in
  return r
