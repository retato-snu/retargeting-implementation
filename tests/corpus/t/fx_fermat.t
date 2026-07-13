# Faithful re-port of sai_fermat.t using div/mod for every quotient/remainder.
# SAI benchmark port (OOPSLA'19 Fig. 9 row "fermat"; Matt Might's Fermat test).
# Pipeline kept whole: modulo-power with the odd/even split, is-trivial-composite
# divisibility, the is-fermat-prime iteration loop, and the generate loop. The
# tested candidate is pinned to n = 15; the random search becomes the lcg orbit
# s -> (s+3) mod 16, and genfp returns the first seed whose next two orbit bases
# are both Fermat liars for 15. The pair packing REMAINS (base*16+exp,
# seed*4+iters); only the ARITHMETIC encoding changes. The old port built every
# quotient from a half chain (d16/d4/half), evenness/remainder by subtract-back
# (modtwo, m16/m4), and the moduli mod7/mod15 as subtract-by-k recursions; here
# each is the primitive: p / 16, p % 16, p / 4, p % 4, n % 2, a % 7, a % 15, and
# e / 2 for the exponent halving in mpow. Same functions, same cases as
# sai_fermat.t (the correctness oracle).
# case: arg=1 => 1
# case: arg=8 => 11
# case: arg=14 => 14
d16(p) = p / 16;
m16(p) = p % 16;
modtwo(n) = n % 2;
mod7(a) = a % 7;
mod15(a) = a % 15;
sq(a) = a * a;
mpow(p) = let b = d16(p) in let e = p - 16 * b in ifz e then 1 else ifz modtwo(e) then mod15(sq(mpow(b * 16 - (0 - e / 2)))) else mod15(b * mpow(b * 16 - (0 - (e - 1))));
lcg(s) = m16(s - (0 - 3));
trivial(n) = ifz modtwo(n) then 1 else ifz mod7(n) then 1 else 0;
d4(p) = p / 4;
m4(p) = p % 4;
isfp(p) = let i = m4(p) in ifz i then 1 else (let a = d4(p) in ifz (mpow(a * 16 - (0 - 14)) - 1) then isfp(lcg(a) * 4 - (0 - (i - 1))) else 0);
genfp(s) = ifz trivial(15) then (ifz isfp(s * 4 - (0 - 2)) then genfp(lcg(s)) else s) else genfp(lcg(s));
genfp(m16(x))
