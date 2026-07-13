# Pure arithmetic over the two binary primitives (sub then mul).
# (10 - 4) * 3 = 6 * 3 = 18.
# expect: 18
main =
  let a = 10 in
  let b = 4 in
  let d = a - b in
  let r = d * 3 in
  return r
