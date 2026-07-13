# SAI benchmark port (OOPSLA'19 Fig. 9 row "lattice"; artifact
# benchmarks/toplas98/lattice.scm). The original counts the monotone maps
# between two lattices: maps-rest enumerates images element by element, maps-1
# filters the target elements consistent with the picks so far via the target's
# comparator, and the to-collect continuation sums the leaf counts; the entry
# point is (count-maps l3 l3) on the two-point chain l3 = {low, high}, printing 3.
# Port: source lattice = a chain of length x (the program argument), target
# pinned to the two-point chain. maps(i,v) counts monotone extensions when i
# elements remain and the previous image is v: candidate images w in {0,1} are
# admitted exactly when cmp2(v,w) is not 'more' (the maps-1 filter), and counts
# add up (the to-collect sum). The comparator returns 0/1/2 for less/equal/more
# ('uncomparable' never arises on a chain). Pairs pack in base 2: (i,v) as
# i*2+v, comparator input as a*2+b. count-maps(chain_2, chain_2) = maps(2*2) = 3
# reproduces the original's printed count. The original also defines lexico
# (lex-first/lex-fixed), which lifts the base comparator to sequences with the
# four-valued algebra less/equal/more/UNCOMPARABLE - and never runs it:
# count-maps calls maps-rest directly, so lexico is dead code in the benchmark.
# The port mirrors that: lexfirst/lexfx below compare packed 2-symbol
# sequences (bits a1 a2 b1 b2 of p), returning 0/1/2/3 with 3 = uncomparable
# (a direction change), and are dead like the original.
# case: arg=1 => 2
# case: arg=2 => 3
# case: arg=4 => 5
# case: arg=6 => 7
half(n) = ifz n then 0 else ifz (n - 1) then 0 else half(n - 2) - (0 - 1);
m2(p) = p - 2 * half(p);
cmp2(p) = let a = half(p) in let b = m2(p) in ifz (a - b) then 1 else ifz a then 0 else 2;
lexfx(q) = let pr = half(half(q)) in let c = cmp2(q - 4 * half(half(q))) in ifz (c - 1) then pr else ifz (c - pr) then pr else 3;
lexfirst(p) = let h1 = half(p) in let h2 = half(h1) in let h3 = half(h2) in let pr = cmp2(h3 * 2 - (0 - (h1 - 2 * h2))) in ifz (pr - 1) then cmp2((h2 - 2 * h3) * 2 - (0 - (p - 2 * h1))) else lexfx(pr * 4 - (0 - ((h2 - 2 * h3) * 2 - (0 - (p - 2 * h1)))));
maps(p) = let i = half(p) in ifz i then 1 else (let v = m2(p) in (ifz (cmp2(v * 2) - 2) then 0 else maps((i - 1) * 2)) - (0 - (ifz (cmp2(v * 2 - (0 - 1)) - 2) then 0 else maps((i - 1) * 2 - (0 - 1)))));
maps(x * 2)
