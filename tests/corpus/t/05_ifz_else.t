# ifz takes the else-branch when its scrutinee is non-zero: (3 - 1) = 2 -> 2.
# expect: 2
ifz (3 - 1) then 1 else 2
