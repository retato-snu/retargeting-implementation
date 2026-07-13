# Benchmark shape: a let-chain of length 4. x1 = 1; each xi = x(i-1) - 1; the body
# is x4 - 1. Values: x1=1, x2=0, x3=-1, x4=-2; result = x4 - 1 = -3.
# expect: -3
let x1 = 1 in
let x2 = x1 - 1 in
let x3 = x2 - 1 in
let x4 = x3 - 1 in
x4 - 1
