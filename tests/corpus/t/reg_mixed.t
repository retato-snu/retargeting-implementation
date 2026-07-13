# Mixes let, ifz, multiplication, subtraction, and nested arithmetic.
# x=2: base=0, scale=-1, first branch gives (-1*3)-(2*2) = -7.
# x=1: base=-1, scale=0, second branch gives 1-4 = -3.
# x=4: base=2, scale=3, final branch gives ((2-3)*(4-1))-2 = -5.
# case: arg=2 => -7
# case: arg=1 => -3
# case: arg=4 => -5
let base = x - 2 in let scale = (base * base) - 1 in ifz base then (scale * 3) - (x * 2) else ifz scale then (x * x) - 4 else ((base - scale) * (x - 1)) - 2
