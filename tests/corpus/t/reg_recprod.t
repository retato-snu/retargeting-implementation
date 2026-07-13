# Recursive product with nested let binding. prod(n)=n! for small nonnegative n.
# case: arg=0 => 1
# case: arg=3 => 6
# case: arg=5 => 120
prod(n) = ifz n then 1 else let p = prod(n - 1) in n * p; prod(x)
