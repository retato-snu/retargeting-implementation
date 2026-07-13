# A recursive function run at several arguments. f(x) counts x down to its base
# case via ifz and returns 100 for every non-negative argument (the recursion
# depth depends on the argument). The main expression applies f to the implicit
# external input x, so the result depends on the supplied arg.
# Negative args are intentionally omitted: f never reaches the base case for them.
# case: arg=0 => 100
# case: arg=1 => 100
# case: arg=2 => 100
# case: arg=5 => 100
f(x) = ifz x then 100 else f(x - 1); f(x)
