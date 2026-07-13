# pow(2, 5) by recursive multiplication = 32.
# expect: 32
def pow(base, exp) =
  let z = iszero(exp) in
  match z with
  | True() -> return 1
  | False() ->
      let one = 1 in
      let next = exp - one in
      let rest = pow(base, next) in
      let r = base * rest in
      return r
  end;
main =
  let two = 2 in
  let five = 5 in
  let r = pow(two, five) in
  return r
