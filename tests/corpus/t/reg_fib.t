# fibonacci with two base cases. Addition is written as a - (0 - b).
# fib(0)=0, fib(1)=1, fib(2)=1, fib(5)=5, fib(6)=8.
# case: arg=0 => 0
# case: arg=1 => 1
# case: arg=2 => 1
# case: arg=5 => 5
# case: arg=6 => 8
fib(n) = ifz n then 0 else ifz (n - 1) then 1 else fib(n - 1) - (0 - fib(n - 2)); fib(x)
