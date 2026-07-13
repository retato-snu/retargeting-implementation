# McCarthy's 91 function:
#   mc(n) = n - 10          if n > 100
#   mc(n) = mc(mc(n + 11))  otherwise      (= 91 for every 0 <= n <= 100)
# The test "n > 100" is the primitive comparison 100 < n (= 1 iff n >= 101), and
# mc takes a single argument, so the program computes mc(x) directly. The
# "# case:" lines record the concrete input/output pairs the program is checked
# against (scripts/check-programs.sh runs them).
# case: arg=50 => 91
# case: arg=87 => 91
# case: arg=99 => 91
# case: arg=100 => 91
# case: arg=101 => 91
# case: arg=102 => 92
# case: arg=111 => 101
mc(n) = ifz (100 < n) then mc(mc(n + 11)) else n - 10;
mc(x)
