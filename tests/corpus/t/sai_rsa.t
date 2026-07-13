# SAI benchmark port (OOPSLA'19 Fig. 9 row "rsa"; artifact benchmarks/rsa.scm).
# RSA encrypt/decrypt roundtrip: fast modular exponentiation with the odd/even
# exponent split, the public-exponent legality check 1 < e < phi(n) with
# gcd(e, phi) = 1, private-exponent computation, the m > n encryption error
# check, and the final decrypt(encrypt(x)) == x comparison with an error value.
# Scaled instance: p=3, q=11, n=33, phi=20, e=7, d=3 (the original's n=1927
# needs modulo by 1927: T has no division, and a subtraction-loop modulus is
# affordable only as an enumerated ifz chain, here 33 arms). The instance is
# chosen so that e != d (in the original e=7, d=263): phi=20 is the smallest
# scaled phi whose unit group is not all self-inverse, so encryption (e=7) and
# decryption (d=3) are genuinely different computations, as in the original.
# gcd(e,20)=1 is decided as odd(e) and 5-not-dividing-e, equivalent for
# phi = 20 = 2^2*5. Two-argument modpow packs exp*64+base (small field high).
# Deviation (forced): modulo-inverse via extended-gcd returns a pair and its
# Bezout coefficients go negative - pairs and negatives cannot be packed
# affordably (half diverges on negatives) - so the equivalent first-order
# search findd finds d with e*d = 1 mod phi; d is unique, the value agrees.
# 33 is squarefree and e*d = 21 = 1 mod lambda(33)=10, so the roundtrip is the
# identity on all of 0..32 and main returns the decrypted plaintext.
# case: arg=0 => 0
# case: arg=2 => 2
# case: arg=13 => 13
# case: arg=32 => 32
half(n) = ifz n then 0 else ifz (n - 1) then 0 else half(n - 2) - (0 - 1);
oddp(n) = n - 2 * half(n);
mod5(a) = ifz a then 0 else ifz (a - 1) then 1 else ifz (a - 2) then 2 else ifz (a - 3) then 3 else ifz (a - 4) then 4 else mod5(a - 5);
mod20(a) = ifz a then 0 else ifz (a - 1) then 1 else ifz (a - 2) then 2 else ifz (a - 3) then 3 else ifz (a - 4) then 4 else ifz (a - 5) then 5 else ifz (a - 6) then 6 else ifz (a - 7) then 7 else ifz (a - 8) then 8 else ifz (a - 9) then 9 else ifz (a - 10) then 10 else ifz (a - 11) then 11 else ifz (a - 12) then 12 else ifz (a - 13) then 13 else ifz (a - 14) then 14 else ifz (a - 15) then 15 else ifz (a - 16) then 16 else ifz (a - 17) then 17 else ifz (a - 18) then 18 else ifz (a - 19) then 19 else mod20(a - 20);
mod33(a) = ifz a then 0 else ifz (a - 1) then 1 else ifz (a - 2) then 2 else ifz (a - 3) then 3 else ifz (a - 4) then 4 else ifz (a - 5) then 5 else ifz (a - 6) then 6 else ifz (a - 7) then 7 else ifz (a - 8) then 8 else ifz (a - 9) then 9 else ifz (a - 10) then 10 else ifz (a - 11) then 11 else ifz (a - 12) then 12 else ifz (a - 13) then 13 else ifz (a - 14) then 14 else ifz (a - 15) then 15 else ifz (a - 16) then 16 else ifz (a - 17) then 17 else ifz (a - 18) then 18 else ifz (a - 19) then 19 else ifz (a - 20) then 20 else ifz (a - 21) then 21 else ifz (a - 22) then 22 else ifz (a - 23) then 23 else ifz (a - 24) then 24 else ifz (a - 25) then 25 else ifz (a - 26) then 26 else ifz (a - 27) then 27 else ifz (a - 28) then 28 else ifz (a - 29) then 29 else ifz (a - 30) then 30 else ifz (a - 31) then 31 else ifz (a - 32) then 32 else mod33(a - 33);
sq(a) = a * a;
mpow(p) = let e = half(half(half(half(half(half(p)))))) in let b = p - 64 * e in ifz e then 1 else ifz oddp(e) then mod33(sq(mpow(half(e) * 64 - (0 - b)))) else mod33(b * mpow((e - 1) * 64 - (0 - b)));
lt20(e) = ifz half(half(half(half(e)))) then 1 else ifz (e - 16) then 1 else ifz (e - 17) then 1 else ifz (e - 18) then 1 else ifz (e - 19) then 1 else 0;
islegal(e) = ifz e then 0 else ifz (e - 1) then 0 else ifz lt20(e) then 0 else ifz oddp(e) then 0 else ifz mod5(e) then 0 else 1;
findd(b) = ifz (mod20(7 * b) - 1) then b else findd(b - (0 - 1));
privd(u) = ifz islegal(7) then 0 - 1 else findd(1);
lt34(m) = ifz half(half(half(half(half(m))))) then 1 else ifz (m - 32) then 1 else ifz (m - 33) then 1 else 0;
encrypt(m) = ifz lt34(m) then 0 - 1 else mpow(7 * 64 - (0 - m));
decrypt(c) = mpow(privd(0) * 64 - (0 - c));
let c = encrypt(x) in let m = decrypt(c) in ifz (m - x) then m else 0 - 1
