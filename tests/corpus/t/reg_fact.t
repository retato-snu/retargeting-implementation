# factorial by recursion. fact(n) = 1 when n is zero, otherwise n * fact(n-1).
# fact(0)=1, fact(1)=1, fact(4)=24, fact(6)=720.
# case: arg=0 => 1
# case: arg=1 => 1
# case: arg=4 => 24
# case: arg=6 => 720
fact(n) = ifz n then 1 else n * fact(n - 1); fact(x)
