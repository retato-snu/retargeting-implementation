# SAI benchmark port (OOPSLA'19 Fig. 9 row "solovay-strassen"; artifact
# benchmarks/solovay-strassen.scm, Matt Might's probabilistic primality tester).
# The full pipeline is kept: modulo-power, the recursive Jacobi symbol (with its
# genuinely two-variable a/n recursion: the a>n reduction, the even-a and even-n
# halving arms, and the quadratic-reciprocity flip with the (-1)^((a-1)(n-1)/4)
# sign), the Fermat stage (trivial-divisor or-chain + is-fermat-prime? loop,
# as in sai_fermat.t), the Euler check jacobi(a,n) = a^((n-1)/2) mod n with the
# even-n early-composite arm, and the generate-solovay-strassen-prime outer
# loop that Fermat-generates a candidate and Solovay-certifies it.
# Scaling, as in sai_fermat.t: the tested number is pinned to n = 15 and the
# random draws become the deterministic seed orbit s -> s+3 mod 16, so the
# search returns a certified witness seed instead of a prime; the Euler base is
# the original's a = 1 + (seed mod (n-1)); ss iterations = 1 (the only Euler
# liars for 15 are a in {1,14}, and the +3 orbit has no consecutive pair of
# them); the artifact's FIXME'd a=2 arm (which returns -1 for every n) is
# ported with its intended value (+1 when n mod 8 is 1 or 7). Jacobi's -1 goes
# through T's native negatives; jmod15 folds mod 15 on {-1,0,1} explicitly.
# Packing: two-variable pairs as a*16+b (operands stay <= 15 except the packed
# a<=196 fed to modv's subtraction loop), (seed,iters) as seed*4+iters.
# The orbit from seed 14 Fermat-certifies 14 itself (14 and 14+3=1 are both
# Fermat liars) and 14 is an Euler liar, so gssp returns 14.
# case: arg=14 => 14
half(n) = ifz n then 0 else ifz (n - 1) then 0 else half(n - 2) - (0 - 1);
d16(p) = half(half(half(half(p))));
m16(p) = p - 16 * d16(p);
modtwo(n) = n - 2 * half(n);
mod7(a) = ifz a then 0 else ifz (a - 1) then 1 else ifz (a - 2) then 2 else ifz (a - 3) then 3 else ifz (a - 4) then 4 else ifz (a - 5) then 5 else ifz (a - 6) then 6 else mod7(a - 7);
mod15(a) = ifz (a - 15) then 0 else ifz half(half(half(half(a)))) then a else mod15(a - 15);
sq(a) = a * a;
mpow(p) = let b = d16(p) in let e = p - 16 * b in ifz e then 1 else ifz modtwo(e) then mod15(sq(mpow(b * 16 - (0 - half(e))))) else mod15(b * mpow(b * 16 - (0 - (e - 1))));
lcg(s) = m16(s - (0 - 3));
trivial(n) = ifz modtwo(n) then 1 else ifz mod7(n) then 1 else 0;
d4(p) = half(half(p));
m4(p) = p - 4 * d4(p);
isfp(p) = let i = m4(p) in ifz i then 1 else (let a = d4(p) in ifz (mpow(a * 16 - (0 - 14)) - 1) then isfp(lcg(a) * 4 - (0 - (i - 1))) else 0);
genfp(s) = ifz trivial(15) then (ifz isfp(s * 4 - (0 - 2)) then genfp(lcg(s)) else s) else genfp(lcg(s));
ltv(p) = let a = d16(p) in let b = p - 16 * a in ifz a then (ifz b then 0 else 1) else ifz b then 0 else ltv((a - 1) * 16 - (0 - (b - 1)));
modv(p) = let a = d16(p) in let n = p - 16 * a in ifz ltv(a * 16 - (0 - n)) then modv((a - n) * 16 - (0 - n)) else a;
gcds(p) = let a = d16(p) in let b = p - 16 * a in ifz a then b else ifz b then a else ifz ltv(a * 16 - (0 - b)) then gcds((a - b) * 16 - (0 - b)) else gcds(a * 16 - (0 - (b - a)));
jacobi(p) = let a = d16(p) in let n = p - 16 * a in ifz (n - 1) then 1 else ifz (a - 1) then 1 else ifz (gcds(a * 16 - (0 - n)) - 1) then (ifz (a - 2) then (let n8 = n - 8 * half(half(half(n))) in ifz (n8 - 1) then 1 else ifz (n8 - 7) then 1 else 0 - 1) else ifz ltv(n * 16 - (0 - a)) then (ifz modtwo(a) then jacobi(half(a) * 16 - (0 - n)) * jacobi(2 * 16 - (0 - n)) else ifz modtwo(n) then jacobi(a * 16 - (0 - half(n))) * jacobi(a * 16 - (0 - 2)) else jacobi(n * 16 - (0 - a)) * (ifz modtwo(half(half((a - 1) * (n - 1)))) then 1 else 0 - 1)) else jacobi(modv(a * 16 - (0 - n)) * 16 - (0 - n))) else 0;
jmod15(j) = ifz (j - (0 - 1)) then 14 else ifz j then 0 else 1;
issbody(p) = let s = d4(p) in let a = modv(s * 16 - (0 - 14)) - (0 - 1) in let j = jacobi(a * 16 - (0 - 15)) in let e = mpow(a * 16 - (0 - 7)) in ifz j then 0 else ifz (jmod15(j) - e) then iss(lcg(s) * 4 - (0 - (m4(p) - 1))) else 0;
iss(p) = let i = m4(p) in ifz i then 1 else ifz modtwo(15) then (ifz (15 - 2) then issbody(p) else 0) else issbody(p);
gssp(s) = let w = genfp(s) in ifz iss(w * 4 - (0 - 1)) then gssp(lcg(w)) else w;
gssp(m16(x))
