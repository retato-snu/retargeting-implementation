# Returning a constructor value (not an integer): Pair(7, 7).
# expect: Pair(7, 7)
main =
  let a = 7 in
  let p = Pair(a, a) in
  return p
