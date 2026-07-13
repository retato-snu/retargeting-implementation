# Collatz steps-to-1: the number of steps to reach 1 under n -> n/2 (n even),
# n -> 3n+1 (n odd). T has no division, so floor(n/2) is computed by a helper
# half(n) that subtracts 2 repeatedly: half(n) = 0,0,1,1,2,2,... Evenness is then
# n - 2*half(n) = 0. 3n+1 is n*3 - (0 - 1); +1 is - (0 - 1).
# collatz(1)=0; collatz(2)=1; collatz(3): 3->10->5->16->8->4->2->1 = 7;
# collatz(4)=2; collatz(5): 5->16->8->4->2->1 = 5; collatz(6)=8; collatz(8)=3.
# case: arg=1 => 0
# case: arg=2 => 1
# case: arg=3 => 7
# case: arg=4 => 2
# case: arg=5 => 5
# case: arg=6 => 8
# case: arg=8 => 3
half(n) = ifz n then 0 else ifz (n - 1) then 0 else half(n - 2) - (0 - 1); collatz(n) = ifz (n - 1) then 0 else ifz (n - 2 * half(n)) then collatz(half(n)) - (0 - 1) else collatz(n * 3 - (0 - 1)) - (0 - 1); collatz(x)
