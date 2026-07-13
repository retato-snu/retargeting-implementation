# Faithful re-port of algo_collatz.t using the arithmetic primitives div/mod.
# Collatz steps-to-1: the number of steps to reach 1 under n -> n/2 (n even),
# n -> 3n+1 (n odd). The old encoding computed floor(n/2) with a half(n)
# subtract-by-2 chain and tested evenness as n - 2*half(n); here floor(n/2) is
# the primitive n / 2 and evenness is n % 2 directly (no half chain). '+1' is
# still - (0 - 1) since T has no addition. Same function, same cases as
# algo_collatz.t (the correctness oracle).
# collatz(1)=0; collatz(2)=1; collatz(3): 3->10->5->16->8->4->2->1 = 7;
# collatz(4)=2; collatz(5): 5->16->8->4->2->1 = 5; collatz(6)=8; collatz(8)=3.
# case: arg=1 => 0
# case: arg=2 => 1
# case: arg=3 => 7
# case: arg=4 => 2
# case: arg=5 => 5
# case: arg=6 => 8
# case: arg=8 => 3
collatz(n) = ifz (n - 1) then 0 else ifz (n % 2) then collatz(n / 2) - (0 - 1) else collatz(n * 3 - (0 - 1)) - (0 - 1); collatz(x)
