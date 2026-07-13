# ifz over the external input, exercising both branches across arguments.
# arg = 0 takes the then-branch (1); arg = 3 takes the else-branch (3 * 10 = 30).
# case: arg=0 => 1
# case: arg=3 => 30
ifz x then 1 else x * 10
