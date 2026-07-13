# ifz takes the then-branch when its scrutinee is zero: (3 - 3) = 0 -> 1.
# expect: 1
ifz (3 - 3) then 1 else 2
