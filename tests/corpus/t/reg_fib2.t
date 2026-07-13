# Doubly-recursive fibonacci shape. Addition is encoded with subtraction from zero.
# case: arg=0 => 0
# case: arg=1 => 1
# case: arg=4 => 3
# case: arg=5 => 5
fib(n) = ifz n then 0 else ifz (n - 1) then 1 else fib(n - 1) - (0 - fib(n - 2)); fib(x)
