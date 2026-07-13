# A let-chain reusing an earlier binding twice.
# x = 7; y = x * x = 49; z = y - x = 42.
# expect: 42
main =
  let x = 7 in
  let y = x * x in
  let z = y - x in
  return z
