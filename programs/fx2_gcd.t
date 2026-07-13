# Euclid's gcd, a classical kernel: g(a,b) = ifz b then a else g(b, a % b), a
# 2-argument function using the primitive remainder (%). main takes one
# argument, so the second operand is pinned to 3: the program computes gcd(x,3).
# case: arg=0 => 3
# case: arg=1 => 1
# case: arg=2 => 1
# case: arg=3 => 3
# case: arg=6 => 3
# case: arg=7 => 1
# case: arg=8 => 1
# case: arg=9 => 3
g(a, b) = ifz b then a else g(b, a % b); g(x, 3)
