# Computing a negative value without a negative literal: 0 - 5 = -5.
# expect: -5
main =
  let n = 5 in
  let r = 0 - n in
  return r
