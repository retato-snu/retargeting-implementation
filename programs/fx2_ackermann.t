# Ackermann's function A(m,n), as a 2-argument recursion. main takes one
# argument, so m is pinned to 2: the program computes A(2, x).
# case: arg=0 => 3
# case: arg=1 => 5
# case: arg=2 => 7
# case: arg=3 => 9
a(m, n) = ifz m then n + 1 else ifz n then a(m - 1, 1) else a(m - 1, a(m, n - 1)); a(2, x)
