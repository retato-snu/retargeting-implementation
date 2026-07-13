# McCarthy's 91 function (Manna & McCarthy 1970), the classic nested-recursion
# benchmark of the program-analysis / verification literature:
#   mc(n) = n - 10          if n > 100
#   mc(n) = mc(mc(n + 11))  otherwise      (= 91 for every 0 <= n <= 100)
# T has no order comparison, so the n > 100 test is gt100(n): count n down and
# report whether it hits 101 (n >= 101) before 0 (n <= 100) — exact for every
# n >= 0, O(n) per test. Addition is a - (0 - b).
# Cases stay at moderate call counts: mc(50) makes 103 mc-calls, each with an
# O(100) gt100 scan (~500k S-steps); mc(0)'s 203 calls would brush the 1M
# concrete I_S^T fuel, so the smallest case is 50. The abstract analyses run
# at the unknown argument and are unaffected.
# case: arg=50 => 91
# case: arg=87 => 91
# case: arg=99 => 91
# case: arg=100 => 91
# case: arg=101 => 91
# case: arg=102 => 92
# case: arg=111 => 101
gt100(n) = ifz (n - 101) then 1 else ifz n then 0 else gt100(n - 1);
mc(n) = ifz gt100(n) then mc(mc(n - (0 - 11))) else n - 10;
mc(x)
