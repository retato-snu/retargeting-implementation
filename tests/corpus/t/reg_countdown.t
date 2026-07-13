# countdown reaches zero and returns the same constant for every terminating input.
# down(0)=7, down(2)=7, down(5)=7.
# case: arg=0 => 7
# case: arg=2 => 7
# case: arg=5 => 7
down(n) = ifz n then 7 else down(n - 1); down(x)
