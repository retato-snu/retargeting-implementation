# ifz scrutinee is the non-trivial arithmetic expression (x * (x - 2)) - (3 * (x - 2)).
# It is zero at x=2 and x=3, and nonzero for the other listed cases.
# case: arg=0 => 9
# case: arg=2 => 7
# case: arg=3 => 7
# case: arg=4 => 9
ifz (x * (x - 2)) - (3 * (x - 2)) then 7 else 9
