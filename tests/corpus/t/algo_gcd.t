# Euclid's algorithm by repeated subtraction, with the second operand fixed at 3
# (T functions take one argument). Each recursive step is the Euclid identity
# gcd(a, 3) = gcd(a - 3, 3) for a >= 3; the base cases a in {0,1,2} give
# gcd(0,3)=3, gcd(1,3)=1, gcd(2,3)=1. So gcd3(a) = gcd(a, 3).
# gcd(3,3)=3, gcd(6,3)=3, gcd(9,3)=3 (multiples of 3); gcd(7,3)=1; gcd(8,3)=1.
# case: arg=0 => 3
# case: arg=1 => 1
# case: arg=2 => 1
# case: arg=3 => 3
# case: arg=6 => 3
# case: arg=7 => 1
# case: arg=8 => 1
# case: arg=9 => 3
gcd3(a) = ifz a then 3 else ifz (a - 1) then 1 else ifz (a - 2) then 1 else gcd3(a - 3); gcd3(x)
