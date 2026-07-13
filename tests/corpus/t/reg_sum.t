# sum(n) = 1 + 2 + ... + n, using subtraction to emulate addition.
# sum(0)=0, sum(1)=1, sum(4)=10, sum(6)=21.
# case: arg=0 => 0
# case: arg=1 => 1
# case: arg=4 => 10
# case: arg=6 => 21
sum(n) = ifz n then 0 else n - (0 - sum(n - 1)); sum(x)
