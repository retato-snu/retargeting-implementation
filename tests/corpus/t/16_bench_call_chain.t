# Benchmark shape: a call chain of length 3 of unary functions, each fi(x) = x - 1,
# applied to the leaf 100: f0(f1(f2(100))) = 100 - 1 - 1 - 1 = 97.
# expect: 97
f0(x) = x - 1; f1(x) = x - 1; f2(x) = x - 1; f0(f1(f2(100)))
