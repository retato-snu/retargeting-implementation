# The Fermat primality test (Matt Might's), from the "fermat" benchmark of Wei,
# Chen, Rompf, "Staged Abstract Interpreters", OOPSLA 2019, Fig. 9. mpow (modular
# power, odd/even split) and isfp (the Fermat-liar iteration loop) are 2-argument
# functions, and div/mod are the primitives (/ %). The tested candidate is pinned
# to n = 15, the random search is the lcg orbit s -> (s+3) mod 16, and genfp
# returns the first seed whose next two orbit bases are both Fermat liars for 15.
# The "# case:" lines record the concrete input/output pairs the program is
# checked against (scripts/check-programs.sh runs them).
# case: arg=1 => 1
# case: arg=8 => 11
# case: arg=14 => 14
mod7(a) = a % 7;
mod15(a) = a % 15;
sq(a) = a * a;
mpow(b, e) = ifz e then 1 else ifz (e % 2) then mod15(sq(mpow(b, e / 2))) else mod15(b * mpow(b, e - 1));
lcg(s) = (s + 3) % 16;
trivial(n) = ifz (n % 2) then 1 else ifz mod7(n) then 1 else 0;
isfp(a, i) = ifz i then 1 else ifz (mpow(a, 14) - 1) then isfp(lcg(a), i - 1) else 0;
genfp(s) = ifz trivial(15) then (ifz isfp(s, 2) then genfp(lcg(s)) else s) else genfp(lcg(s));
genfp(x % 16)
