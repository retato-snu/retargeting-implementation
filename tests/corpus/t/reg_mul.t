# multiply by 4 using repeated addition, with addition written as a - (0 - b).
# mulfour(0)=0, mulfour(1)=4, mulfour(3)=12, mulfour(5)=20.
# case: arg=0 => 0
# case: arg=1 => 4
# case: arg=3 => 12
# case: arg=5 => 20
mulfour(n) = ifz n then 0 else 4 - (0 - mulfour(n - 1)); mulfour(x)
