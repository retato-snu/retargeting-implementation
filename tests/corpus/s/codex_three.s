# tri(3, 4, 5) computes 3 * 4 - 5 = 7.
# expect: 7
def tri(a, b, c) =
  let p = a * b in
  let r = p - c in
  return r;
main =
  let a = 3 in
  let b = 4 in
  let c = 5 in
  let r = tri(a, b, c) in
  return r
