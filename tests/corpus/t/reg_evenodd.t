# mutually recursive parity functions. even returns 1 for even inputs and 0 for odd inputs.
# even(0)=1, even(1)=0, even(2)=1, even(5)=0, even(6)=1.
# case: arg=0 => 1
# case: arg=1 => 0
# case: arg=2 => 1
# case: arg=5 => 0
# case: arg=6 => 1
even(n) = ifz n then 1 else odd(n - 1); odd(n) = ifz n then 0 else even(n - 1); even(x)
