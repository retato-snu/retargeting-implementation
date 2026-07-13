# The RSA encrypt/decrypt roundtrip, from the "rsa" benchmark of Wei, Chen,
# Rompf, "Staged Abstract Interpreters", OOPSLA 2019, Fig. 9, at the scaled
# instance p=3, q=11, n=33, phi=20, e=7, d=3, chosen so that e != d. Modular
# power is the 2-argument mpow(base,exp) with the odd/even exponent split, and
# the remainders are primitives: mod5/mod20/mod33 are %5/%20/%33, oddness is %2,
# and the legality/encryption range tests are the primitive comparisons e < 20 /
# m < 34. The public-exponent legality check 1 < e < phi with gcd(e,phi)=1
# (islegal), the modular-inverse search findd (e*d = 1 mod phi, d unique), the
# m>=n encryption error, and the decrypt(encrypt(x))==x comparison are all here.
# 33 is squarefree and e*d = 21 = 1 mod lambda(33)=10, so the roundtrip is the
# identity on 0..32. The "# case:" lines record the concrete input/output pairs
# the program is checked against (scripts/check-programs.sh runs them).
# case: arg=0 => 0
# case: arg=2 => 2
# case: arg=13 => 13
# case: arg=32 => 32
mod5(a) = a % 5;
mod20(a) = a % 20;
mod33(a) = a % 33;
sq(a) = a * a;
mpow(b, e) = ifz e then 1 else ifz (e % 2) then mod33(sq(mpow(b, e / 2))) else mod33(b * mpow(b, e - 1));
islegal(e) = ifz e then 0 else ifz (e - 1) then 0 else ifz (e < 20) then 0 else ifz (e % 2) then 0 else ifz mod5(e) then 0 else 1;
findd(b) = ifz (mod20(7 * b) - 1) then b else findd(b + 1);
privd(u) = ifz islegal(7) then 0 - 1 else findd(1);
encrypt(m) = ifz (m < 34) then 0 - 1 else mpow(m, 7);
decrypt(c) = mpow(c, privd(0));
let c = encrypt(x) in let m = decrypt(c) in ifz (m - x) then m else 0 - 1
