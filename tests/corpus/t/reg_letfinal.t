# Let-chain feeding into a final nested arithmetic expression.
# a=2; b=8; c=6; d=6; e=4; f=0; final ((0-4)*(2-1))-((6-6)*(8-4)) = -4.
# expect: -4
let a = 2 in let b = a * 4 in let c = b - a in let d = c * (a - 1) in let e = d - (b - c) in let f = e * (c - d) in ((f - e) * (a - 1)) - ((d - c) * (b - e))
