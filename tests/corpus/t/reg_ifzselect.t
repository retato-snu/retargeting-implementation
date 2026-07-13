# ifz selects between two different arithmetic expressions of x.
# x=4 chooses the first expression: (4*3)-6 = 6. Others use the second expression.
# case: arg=4 => 6
# case: arg=0 => 6
# case: arg=5 => -4
# case: arg=2 => -4
ifz x - 4 then (x * (x - 1)) - 6 else ((x - 2) * (x - 3)) - (x * 2)
