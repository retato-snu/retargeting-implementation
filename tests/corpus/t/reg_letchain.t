# Long let-chain where later bindings reuse earlier ones.
# a=3; b=6; c=3; d=6; e=0; f=0; result f-d = 0-6 = -6.
# expect: -6
let a = 3 in let b = a * 2 in let c = b - a in let d = c * (a - 1) in let e = d - b in let f = e * c in f - d
