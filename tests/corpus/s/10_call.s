# A non-recursive function call (LetCall) with S-Return: dbl(21) = 42.
# expect: 42
def dbl(x) =
  let r = x * 2 in
  return r;
main =
  let a = 21 in
  let r = dbl(a) in
  return r
