# Church numerals, from the "church" benchmark of Wei, Chen, Rompf, "Staged
# Abstract Interpreters", OOPSLA 2019, Fig. 9. Church-numeral equality is
# defunctionalized to iteration counts, so subc, plusc, multc and cheq are
# 2-argument functions on the counts: predc is the arithmetic predecessor clamped
# at 0, subc is the b-fold predecessor, and cheq is the mutually-decrementing
# Church equality. plusc/multc are defined but unused, exactly as plus/mult are
# dead code in the original. Main is the equality check with the program argument
# in place of the first numeral: cheq(x, 3) = 1 iff x = 3. The "# case:" lines
# record the concrete input/output pairs the program is checked against
# (scripts/check-programs.sh runs them).
# case: arg=0 => 0
# case: arg=1 => 0
# case: arg=3 => 1
# case: arg=5 => 0
# case: arg=9 => 0
predc(n) = ifz n then 0 else n - 1;
plusc(a, b) = a + b;
multc(a, b) = a * b;
subc(a, b) = ifz b then a else subc(predc(a), b - 1);
iszero(n) = ifz n then 1 else 0;
cheq(a, b) = ifz a then iszero(b) else ifz b then 0 else cheq(subc(a, 1), subc(b, 1));
cheq(x, 3)
