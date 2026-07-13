# Naive (exponential-call) Fibonacci: fib(n) = fib(n-1) + fib(n-2) with two base
# cases. Addition a + b is written a - (0 - b). Kept small so the doubly-recursive
# call tree stays within the concrete fuel.
# fib(0)=0, fib(1)=1, fib(2)=1, fib(3)=2, fib(4)=3, fib(6)=8, fib(8)=21.
# case: arg=0 => 0
# case: arg=1 => 1
# case: arg=2 => 1
# case: arg=3 => 2
# case: arg=4 => 3
# case: arg=6 => 8
# case: arg=8 => 21
fib(n) = ifz n then 0 else ifz (n - 1) then 1 else fib(n - 1) - (0 - fib(n - 2)); fib(x)
