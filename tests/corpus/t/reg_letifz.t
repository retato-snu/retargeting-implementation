# Uses a let to bind an ifz result and then computes with it.
# x=0: k=1, m=-1, result -1. x=3: k=4, m=8, result 29. x=5: k=2, m=8, result 11.
# case: arg=0 => -1
# case: arg=3 => 29
# case: arg=5 => 11
let k = ifz x - 3 then 4 else ifz x then 1 else 2 in let m = k * (x - 1) in (m * k) - x
