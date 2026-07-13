# Main calls the recursive function on an expression of x: count(x * 2).
# case: arg=0 => 0
# case: arg=2 => 4
# case: arg=3 => 6
count(n) = ifz n then 0 else 1 - (0 - count(n - 1)); count(x * 2)
