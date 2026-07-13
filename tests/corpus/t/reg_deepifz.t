# Recursive function with five nested ifz tests before the recursive fallback.
# case: arg=0 => 7
# case: arg=4 => 19
# case: arg=5 => 6
# case: arg=9 => 18
deep(n) = ifz n then 7 else ifz (n - 1) then 11 else ifz (n - 2) then 13 else ifz (n - 3) then 17 else ifz (n - 4) then 19 else deep(n - 5) - 1; deep(x)
