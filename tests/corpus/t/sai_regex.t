# SAI benchmark port (OOPSLA'19 Fig. 9 row "regex"; artifact
# benchmarks/regex-derivative.scm, Matt Might's Brzozowski-derivative matcher).
# Unlike the precomputed-automaton port this replaces, this version performs
# the derivative COMPUTATION at runtime on encoded regex trees: d/dc's case
# analysis over the node kinds, the simplifying smart constructors seq/alt/rep
# (null/blank absorption, inlined at their use sites), the nullability test
# regex-empty, and the regex-match loop that repeatedly derives by the next
# input character and tests nullability at the end. Encoding: a regex tree is
# tag + 8*c1 + 64*c2 with tags 0 = unmatchable (#f), 1 = blank (#t), 2/3 =
# atoms a/b, 4/5/6 = seq/alt/rep; the c1 slot holds 3 bits, so the smaller
# child sits low (enough for the exercised pattern; decode cost forces this).
# The pattern is ab* = (seq a (rep b)) = 1940; its derivative closure is
# {ab*, b* = 30, null} and every runtime-built node stays small. d/dc is
# specialized per alphabet symbol (dda/ddb) - T's unary functions cannot
# afford packing the character with an arbitrary tree. regex-empty follows the
# intended semantics of the artifact's FIXME'd seq/alt arms (and/or of the
# children); on this pattern and inputs the two are indistinguishable. The
# input string is the argument's binary digits, low bit first (a=0, b=1) up to
# a leading 1 sentinel: x = 2 is "a", 6 is "ab", 14 is "abb", 3 is "b", 4 is
# "aa", 1 is "". The match loop packs string*64 + regex (derivatives fit 6
# bits; the 1940-node start pattern is derived once, outside the pack).
# case: arg=1 => 0
# case: arg=2 => 1
# case: arg=3 => 0
# case: arg=4 => 0
# case: arg=6 => 1
# case: arg=14 => 1
half(n) = ifz n then 0 else ifz (n - 1) then 0 else half(n - 2) - (0 - 1);
d8(p) = half(half(half(p)));
repc(q) = ifz q then 1 else ifz (q - 1) then 1 else 6 - (0 - 8 * q);
empt(re) = ifz re then 0 else ifz (re - 1) then 1 else ifz (re - 2) then 0 else ifz (re - 3) then 0 else (let d = d8(re) in let t = re - 8 * d in let dd = d8(d) in let c1 = d - 8 * dd in ifz (t - 4) then (ifz empt(c1) then 0 else empt(dd)) else ifz (t - 5) then (ifz empt(c1) then empt(dd) else 1) else 1);
dda(re) = ifz (re - 2) then 1 else ifz re then 0 else ifz (re - 1) then 0 else ifz (re - 3) then 0 else (let d = d8(re) in let t = re - 8 * d in let dd = d8(d) in let c1 = d - 8 * dd in ifz (t - 4) then (let l = (let g = dda(c1) in ifz g then 0 else ifz (g - 1) then dd else 4 - (0 - (8 * g - (0 - 64 * dd)))) in let r = (ifz empt(c1) then 0 else dda(dd)) in (ifz l then r else ifz r then l else 5 - (0 - (8 * l - (0 - 64 * r))))) else ifz (t - 5) then (let l = dda(c1) in let r = dda(dd) in (ifz l then r else ifz r then l else 5 - (0 - (8 * l - (0 - 64 * r))))) else (let g = dda(d) in ifz g then 0 else ifz (g - 1) then repc(d) else 4 - (0 - (8 * g - (0 - 64 * repc(d))))));
ddb(re) = ifz (re - 3) then 1 else ifz re then 0 else ifz (re - 1) then 0 else ifz (re - 2) then 0 else (let d = d8(re) in let t = re - 8 * d in let dd = d8(d) in let c1 = d - 8 * dd in ifz (t - 4) then (let l = (let g = ddb(c1) in ifz g then 0 else ifz (g - 1) then dd else 4 - (0 - (8 * g - (0 - 64 * dd)))) in let r = (ifz empt(c1) then 0 else ddb(dd)) in (ifz l then r else ifz r then l else 5 - (0 - (8 * l - (0 - 64 * r))))) else ifz (t - 5) then (let l = ddb(c1) in let r = ddb(dd) in (ifz l then r else ifz r then l else 5 - (0 - (8 * l - (0 - 64 * r))))) else (let g = ddb(d) in ifz g then 0 else ifz (g - 1) then repc(d) else 4 - (0 - (8 * g - (0 - 64 * repc(d))))));
rm(p) = let w = half(half(half(half(half(half(p)))))) in let re = p - 64 * w in ifz (w - 1) then empt(re) else rm(half(w) * 64 - (0 - (ifz (w - 2 * half(w)) then dda(re) else ddb(re))));
ifz (x - 1) then empt(1940) else rm(half(x) * 64 - (0 - (ifz (x - 2 * half(x)) then dda(1940) else ddb(1940))))
