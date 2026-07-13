# Five function definitions; main composes combo, square, and dec calls.
# case: arg=0 => 0
# case: arg=2 => 6
# case: arg=3 => 12
dec(n) = ifz n then 0 else n - 1; dbl(n) = n - (0 - n); square(n) = n * n; sum(n) = ifz n then 0 else n - (0 - sum(n - 1)); combo(n) = dbl(sum(n)) - square(dec(n)); combo(x) - (0 - square(dec(x)))
