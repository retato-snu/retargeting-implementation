# gcd(n, 6) with the second operand fixed. Repeatedly subtract 6, then handle remainders.
# gcd(0,6)=6, gcd(4,6)=2, gcd(9,6)=3, gcd(12,6)=6, gcd(25,6)=1.
# case: arg=0 => 6
# case: arg=4 => 2
# case: arg=9 => 3
# case: arg=12 => 6
# case: arg=25 => 1
gcdsix(n) = ifz n then 6 else ifz (n - 1) then 1 else ifz (n - 2) then 2 else ifz (n - 3) then 3 else ifz (n - 4) then 2 else ifz (n - 5) then 1 else gcdsix(n - 6); gcdsix(x)
