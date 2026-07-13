# Collatz step counting, a classical kernel: collatz(n) counts the steps of
# n -> n/2 (n even) / 3n+1 (n odd) until n reaches 1. floor(n/2) is the
# primitive n / 2 and evenness is n % 2. collatz takes a single argument, so
# the program computes collatz(x) directly.
# collatz(1)=0; collatz(2)=1; collatz(3): 3->10->5->16->8->4->2->1 = 7;
# collatz(4)=2; collatz(5): 5->16->8->4->2->1 = 5; collatz(6)=8; collatz(8)=3.
# case: arg=1 => 0
# case: arg=2 => 1
# case: arg=3 => 7
# case: arg=4 => 2
# case: arg=5 => 5
# case: arg=6 => 8
# case: arg=8 => 3
collatz(n) = ifz (n - 1) then 0 else ifz (n % 2) then collatz(n / 2) + 1 else collatz(n * 3 + 1) + 1; collatz(x)
