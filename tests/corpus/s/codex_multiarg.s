# expect: 20
def mix(a, b, c) =
  let ab = a * b in
  let cc = c * c in
  let negcc = 0 - cc in
  let sum = ab - negcc in
  let out = sum - b in
  return out;
main =
  let x = 3 in
  let y = 2 in
  let z = 4 in
  let r = mix(x, y, z) in
  return r
