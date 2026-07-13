# A let, a call, and a subtraction combined: dbl(x) = x * 2; let y = 5 in dbl(y) - 1.
# dbl(5) = 10; 10 - 1 = 9.
# expect: 9
dbl(x) = x * 2; let y = 5 in dbl(y) - 1
