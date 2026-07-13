# Deeply nested arithmetic with parentheses and no input dependence.
# Left side: (8 - (3 * (2 - 1))) * ((9 - 6) - 1) = (8 - 3) * 2 = 10.
# Right side: (5 - 2) * (4 - (3 - 2)) = 3 * 3 = 9. Result 10 - 9 = 1.
# expect: 1
(((8 - (3 * (2 - 1))) * ((9 - 6) - 1)) - ((5 - 2) * (4 - (3 - 2))))
