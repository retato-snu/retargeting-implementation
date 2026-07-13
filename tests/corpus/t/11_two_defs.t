# Two function definitions; the main expression calls the first.
# inc(x) = x - 1; dec is defined but unused; let a = 10 in inc(a) = 9.
# expect: 9
inc(x) = x - 1; dec(x) = x * 1; let a = 10 in inc(a)
