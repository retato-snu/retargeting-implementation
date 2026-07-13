# SAI benchmark port (OOPSLA'19 Fig. 9 row "matrix"; artifact
# benchmarks/toplas98/matrix.scm). The original tests {+1,-1} matrices for
# maximality under row reordering, column reordering, and row/column negation,
# and its algorithmic core is INCREMENTAL row-by-row construction with pruning:
# "if (append mat1 mat2) is maximal, then so is mat1", so the search only ever
# extends maximal prefixes and never enumerates the full matrix space;
# go-folder counts the maximal matrices found per size. Port: the same
# pruned incremental search over width-2 rows encoded as 2-bit integers
# ({0,2,3} = the rows with nonincreasing bits; bit 1/0 stands for +1/-1, so
# rowok is the original's column-ordering constraint that rejects row 01, and
# extending only with rows r <= previous row is the lexicographic row-ordering
# constraint, realized by scan's descending candidate walk - candidates below
# the prefix are never constructed, which is the original's pruning). cnt(x
# rows) plays go-folder's per-size count: the argument is the matrix height,
# as in (really-go 7 7)'s size parameter. Pairs pack small: (rows,prev) as
# rows*4+prev, scan state as rows*16+r. Not portable (no lists in T): the
# column-partition refinement machinery (zulu's -split-), matrices wider than
# the 2-bit row encoding, and the 3000-matrix result-list accumulation.
# Counts: nonincreasing length-x sequences over {0,2,3} = C(x+2,2).
# case: arg=0 => 1
# case: arg=1 => 3
# case: arg=2 => 6
# case: arg=3 => 10
# case: arg=5 => 21
half(n) = ifz n then 0 else ifz (n - 1) then 0 else half(n - 2) - (0 - 1);
d4(p) = half(half(p));
m4(p) = p - 4 * d4(p);
d16(q) = half(half(half(half(q))));
rowok(r) = ifz (r - 1) then 0 else 1;
cnt(p) = let rows = d4(p) in ifz rows then 1 else scan(rows * 16 - (0 - m4(p)));
scan(q) = let rows = d16(q) in let r = q - 16 * rows in (ifz rowok(r) then 0 else cnt((rows - 1) * 4 - (0 - r))) - (0 - (ifz r then 0 else scan(q - 1)));
cnt(x * 4 - (0 - 3))
