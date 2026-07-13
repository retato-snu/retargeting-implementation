# SAI benchmark port (OOPSLA'19 Fig. 9 row "fermat"; artifact benchmarks/fermat.scm,
# Matt Might's Fermat primality test). Pipeline kept whole: modulo-power with the
# odd/even split, the is-trivial-composite? divisibility or-chain, the
# is-fermat-prime? iteration loop (a^(n-1) = 1 mod n for several bases a), and
# the generate-fermat-prime search loop. Scaled instance: the tested candidate
# is pinned to n = 15 (T cannot do modulo by a runtime-variable modulus at an
# affordable cost, see sai_rsa.t), so the random search for a prime CANDIDATE
# becomes a deterministic search for a certified WITNESS SEED: the original's
# (random byte-size) draws become the lcg orbit s -> s+3 mod 16, and genfp
# returns the first seed whose next two orbit bases are both Fermat liars for
# 15 (a^14 = 1 mod 15, i.e. a in {1,4,11,14}; iterations = 2). The divisor
# or-chain is truncated to {2,7} - the full chain contains 3 and 5 and would
# constant-fold the scaled candidate to trivially-composite before the Fermat
# phase runs. Packing: base^exp as base*16+exp, (seed,iters) as seed*4+iters.
# case: arg=1 => 1
# case: arg=8 => 11
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
genfp(m16(x))
