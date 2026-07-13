# Three-way mutual recursion a -> b -> c -> a, decreasing the argument each step.
# case: arg=0 => 10
# case: arg=1 => 20
# case: arg=2 => 30
# case: arg=5 => 30
a(n) = ifz n then 10 else b(n - 1); b(n) = ifz n then 20 else c(n - 1); c(n) = ifz n then 30 else a(n - 1); a(x)
