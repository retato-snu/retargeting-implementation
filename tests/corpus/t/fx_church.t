# Faithful re-port of sai_church.t using div/mod for the pair unpack.
# SAI benchmark port (OOPSLA'19 Fig. 9 row "church"). Church-numeral arithmetic
# defunctionalized to iteration counts: predc is the arithmetic predecessor
# clamped at 0, subc = the b-fold predecessor recursion, and cheq is the
# mutually-decrementing Church equality. Binary functions still take a packed
# pair a*16 + b (the pack REMAINS; multi-arg is a later milestone); only the
# DECODE changes. The old port decoded with half chains (d16 = p / 16 via four
# halves, m16 = p - 16*d16); here the digits are the primitives p / 16 and
# p % 16 directly. plusc/multc stay defined-but-unused, exactly as plus/mult
# are dead code in the original. Main is the equality check with the program
# argument substituted for the first church3: cheq(pack(x, 3)) - 1 iff x = 3.
# Same function, same cases as sai_church.t (the correctness oracle).
# case: arg=0 => 0
# case: arg=1 => 0
# case: arg=3 => 1
# case: arg=5 => 0
# case: arg=9 => 0
predc(n) = ifz n then 0 else n - 1;
plusc(p) = p / 16 - (0 - (p % 16));
multc(p) = (p / 16) * (p % 16);
subc(p) = let b = p % 16 in ifz b then p / 16 else subc(predc(p / 16) * 16 - (0 - (b - 1)));
iszero(n) = ifz n then 1 else 0;
cheq(p) = let a = p / 16 in let b = p % 16 in ifz a then iszero(b) else ifz b then 0 else cheq(subc(a * 16 - (0 - 1)) * 16 - (0 - subc(b * 16 - (0 - 1))));
cheq(x * 16 - (0 - 3))
