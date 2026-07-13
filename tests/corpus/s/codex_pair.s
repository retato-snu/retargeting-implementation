# expect: Pair(16, 8)
def makepair(n) =
  let square = n * n in
  let neg = 0 - n in
  let double = n - neg in
  let p = Pair(square, double) in
  return p;
main =
  let x = 4 in
  let r = makepair(x) in
  return r
