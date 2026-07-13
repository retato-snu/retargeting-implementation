# Recursive-call result is let-bound and reused twice, doubling each level.
# case: arg=0 => 1
# case: arg=3 => 8
# case: arg=5 => 32
reuse(n) = ifz n then 1 else let r = reuse(n - 1) in r - (0 - r); reuse(x)
