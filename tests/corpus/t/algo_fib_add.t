# Naive (exponential-call) Fibonacci written with T's addition: the recursive case
# is fib(n-1) + fib(n-2). Same shape as algo_fib_naive.t, which spells the same
# sum as a - (0 - b); running both pins the Add rule against the Sub encoding of it.
# fib(0)=0, fib(1)=1, fib(2)=1, fib(3)=2, fib(4)=3, fib(6)=8, fib(8)=21.
# case: arg=0 => 0
# case: arg=1 => 1
# case: arg=2 => 1
# case: arg=3 => 2
# case: arg=4 => 3
# case: arg=6 => 8
# case: arg=8 => 21
fib(n) = ifz n then 0 else ifz (n - 1) then 1 else fib(n - 1) + fib(n - 2); fib(x)
