# The "lattice" benchmark of Wei, Chen, Rompf, "Staged Abstract Interpreters",
# OOPSLA 2019, Fig. 9. Counts the monotone maps from a chain of length x into the
# pinned two-point target chain. maps(i,v) counts monotone extensions when i
# source elements remain and the previous image is v: candidate images w in {0,1}
# are admitted exactly when cmp2(v,w) is not 'more' (the maps-1 filter), and the
# counts add up (the to-collect sum). cmp2(a,b) returns 0/1/2 for less/equal/more
# on {0,1}^2; maps and cmp2 are 2-argument functions. count-maps(chain_x,
# chain_2) = maps(x,0) = x+1 reproduces the original's printed count (3 at x=2).
# The original's lexicographic comparator (lex-first/lex-fixed) lifts cmp2 to
# 2-symbol sequences, i.e. a 4-tuple (a1,a2,b1,b2); an application in T takes at
# most 3 arguments, and the comparator is dead in the original (count-maps calls
# maps directly), so it is omitted here.
# case: arg=1 => 2
# case: arg=2 => 3
# case: arg=4 => 5
# case: arg=6 => 7
cmp2(a, b) = ifz (a - b) then 1 else ifz a then 0 else 2;
maps(i, v) = ifz i then 1 else (ifz (cmp2(v, 0) - 2) then 0 else maps(i - 1, 0)) + (ifz (cmp2(v, 1) - 2) then 0 else maps(i - 1, 1));
maps(x, 0)
