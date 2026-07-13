# Deep factorial: fact(n) = n * fact(n-1), base fact(0)=1. The recursion nests n
# deep, exercising a long call/return spine. Kept small (<= 8) so the product
# stays a small integer and the run stays within the concrete fuel.
# fact(0)=1, fact(1)=1, fact(3)=6, fact(5)=120, fact(6)=720, fact(7)=5040,
# fact(8)=40320.
# case: arg=0 => 1
# case: arg=1 => 1
# case: arg=3 => 6
# case: arg=5 => 120
# case: arg=6 => 720
# case: arg=7 => 5040
# case: arg=8 => 40320
fact(n) = ifz n then 1 else n * fact(n - 1); fact(x)
