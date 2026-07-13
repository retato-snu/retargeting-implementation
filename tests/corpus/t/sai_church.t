# SAI benchmark port (OOPSLA'19 Fig. 9 row "church"; artifact benchmarks/church.sch).
# Church-numeral arithmetic: plus, mult, the classic pred, sub = iterated pred,
# church0?, and the mutually-decrementing equality church=?; the original's main
# is ((church=? church3) church3). T is first-order, so numerals are
# defunctionalized to their iteration counts: pred becomes the arithmetic
# predecessor clamped at 0 (Church pred of zero is zero), and sub = (s2 pred) s1
# becomes the b-fold predecessor recursion its iterator unfolds to. plus and
# mult COMPOSE iterators (plus chains p1's applications after p2's, mult feeds
# m1 as m2's step), so their defunctionalized images are count addition and
# count multiplication directly - not recursions, which would add structure
# the lambda-towers do not have. Binary functions take a packed pair a*16+b
# (operands stay < 16; decode = half chains). plusc and multc are defined but
# unused, exactly as plus/mult are dead code in the original file. Main is the
# original equality check with the program argument substituted for the first
# church3: cheq(pack(x, 3)) - 1 iff x = 3.
# case: arg=0 => 0
# case: arg=1 => 0
# case: arg=3 => 1
# case: arg=5 => 0
# case: arg=9 => 0
half(n) = ifz n then 0 else ifz (n - 1) then 0 else half(n - 2) - (0 - 1);
d16(p) = half(half(half(half(p))));
m16(p) = p - 16 * d16(p);
predc(n) = ifz n then 0 else n - 1;
plusc(p) = d16(p) - (0 - m16(p));
multc(p) = d16(p) * m16(p);
subc(p) = let b = m16(p) in ifz b then d16(p) else subc(predc(d16(p)) * 16 - (0 - (b - 1)));
iszero(n) = ifz n then 1 else 0;
cheq(p) = let a = d16(p) in let b = m16(p) in ifz a then iszero(b) else ifz b then 0 else cheq(subc(a * 16 - (0 - 1)) * 16 - (0 - subc(b * 16 - (0 - 1))));
cheq(x * 16 - (0 - 3))
