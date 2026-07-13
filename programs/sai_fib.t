# The doubly-recursive Fibonacci, from the "fib" benchmark of Wei, Chen, Rompf,
# "Staged Abstract Interpreters", OOPSLA 2019, Fig. 9 (their suite is collected
# from Ashley-Dybvig'98 / Johnson et al.'13 / Vardoulakis-Shivers'11):
#   (fib n) = if (< n 2) n (+ (fib (- n 1)) (fib (- n 2))).
# The (< n 2) base case is two ifz tests, each returning n itself (0 and 1); the
# program computes fib(x).
# case: arg=0 => 0
# case: arg=1 => 1
# case: arg=2 => 1
# case: arg=5 => 5
# case: arg=8 => 21
# case: arg=10 => 55
fib(n) = ifz n then n else ifz (n - 1) then n else fib(n - 1) + fib(n - 2); fib(x)
