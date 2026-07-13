# Powers of two by recursion, a classical kernel: powtwo(n) = 2^n for
# nonnegative n.
# powtwo(0)=1, powtwo(1)=2, powtwo(3)=8, powtwo(5)=32.
# case: arg=0 => 1
# case: arg=1 => 2
# case: arg=3 => 8
# case: arg=5 => 32
powtwo(n) = ifz n then 1 else 2 * powtwo(n - 1); powtwo(x)
