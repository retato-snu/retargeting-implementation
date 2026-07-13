# The Solovay-Strassen probabilistic primality tester (Matt Might's), from the
# "solovay-strassen" benchmark of Wei, Chen, Rompf, "Staged Abstract
# Interpreters", OOPSLA 2019, Fig. 9. The full pipeline is here: modular power,
# the genuinely two-variable Jacobi symbol recursion (a>n reduction, even-a /
# even-n halving arms, the quadratic-reciprocity flip with the
# (-1)^((a-1)(n-1)/4) sign), the Fermat stage (trivial-divisor check +
# is-fermat-prime? loop), the Euler check jacobi(a,n) = a^((n-1)/2) mod n, and
# the outer generate-solovay-strassen-prime loop. mpow, jacobi, modv, gcds, isfp,
# iss and issbody are 2-argument functions; the mods are primitives (mod7 = %7,
# mod15 = %15, oddness = %2) and the order tests are the primitive comparison
# a < b (modv and gcds keep their subtractive-loop structure). Jacobi's -1 rides
# T's native negatives; jmod15 folds mod 15 on {-1,0,1}. Scaling: the tested
# number is pinned to n = 15, the random draws are the deterministic orbit
# s -> (s+3) mod 16, and gssp returns the certified witness seed. The orbit from
# seed 14 Fermat-certifies 14 (14 and 14+3=1 are both Fermat liars) and 14 is an
# Euler liar, so gssp returns 14 — the single "# case:" line below, which
# scripts/check-programs.sh runs.
# case: arg=14 => 14
mod7(a) = a % 7;
mod15(a) = a % 15;
sq(a) = a * a;
mpow(b, e) = ifz e then 1 else ifz (e % 2) then mod15(sq(mpow(b, e / 2))) else mod15(b * mpow(b, e - 1));
lcg(s) = (s + 3) % 16;
trivial(n) = ifz (n % 2) then 1 else ifz mod7(n) then 1 else 0;
isfp(a, i) = ifz i then 1 else ifz (mpow(a, 14) - 1) then isfp(lcg(a), i - 1) else 0;
genfp(s) = ifz trivial(15) then (ifz isfp(s, 2) then genfp(lcg(s)) else s) else genfp(lcg(s));
modv(a, n) = ifz (a < n) then modv(a - n, n) else a;
gcds(a, b) = ifz a then b else ifz b then a else ifz (a < b) then gcds(a - b, b) else gcds(a, b - a);
jacobi(a, n) = ifz (n - 1) then 1 else ifz (a - 1) then 1 else ifz (gcds(a, n) - 1) then (ifz (a - 2) then (let n8 = n % 8 in ifz (n8 - 1) then 1 else ifz (n8 - 7) then 1 else 0 - 1) else ifz (n < a) then (ifz (a % 2) then jacobi(a / 2, n) * jacobi(2, n) else ifz (n % 2) then jacobi(a, n / 2) * jacobi(a, 2) else jacobi(n, a) * (ifz (((a - 1) * (n - 1) / 4) % 2) then 1 else 0 - 1)) else jacobi(modv(a, n), n)) else 0;
jmod15(j) = ifz (j + 1) then 14 else ifz j then 0 else 1;
issbody(s, i) = let a = modv(s, 14) + 1 in let j = jacobi(a, 15) in let e = mpow(a, 7) in ifz j then 0 else ifz (jmod15(j) - e) then iss(lcg(s), i - 1) else 0;
iss(s, i) = ifz i then 1 else ifz (15 % 2) then (ifz (15 - 2) then issbody(s, i) else 0) else issbody(s, i);
gssp(s) = let w = genfp(s) in ifz iss(w, 1) then gssp(lcg(w)) else w;
gssp(x % 16)
