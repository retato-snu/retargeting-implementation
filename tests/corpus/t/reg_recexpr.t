# Recursive call uses a computed argument: (n - 1) * 1. rec(n)=0-n for nonnegative n.
# case: arg=0 => 0
# case: arg=2 => -2
# case: arg=4 => -4
rec(n) = ifz n then 0 else rec((n - 1) * 1) - 1; rec(x)
