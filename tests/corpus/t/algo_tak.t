# Takeuchi's tak function, the call-heavy triple recursion of the Gabriel Lisp
# benchmark suite (Gabriel 1985, "Tak"; McCarthy's z-returning variant):
#   tak(x,y,z) = z if not (y < x), else
#                tak(tak(x-1,y,z), tak(y-1,z,x), tak(z-1,x,y)).
# T functions take one argument, so the triple is packed base-8 with every
# component shifted by +2: p = (x+2)*64 + (y+2)*8 + (z+2). The shift keeps
# every packed digit nonnegative (arguments reach -1 via z-1 when z = 0, and a
# first argument reaches -2 transiently via x-1 when x = -1; such calls return
# without recursing), so digits stay in 0..7 whenever the instance maximum is
# <= 5. tak works entirely in shifted space — x-1 and the y < x test are
# shift-invariant — and main unshifts the result. Unpacking is the half-chain
# idiom (q8 = div 8, as in the sai_* ports); y < x on digits is the 7-arm
# positivity chain pos7(x - y).
# The Gabriel instance tak(18,12,6) overflows the packing budget (digit <= 7
# means component <= 5); the scaled instances below keep the recursion shape.
# tak(4,2,0)'s 53 calls x O(pack) unpacking exceeds the concrete I_S^T fuel;
# the abstract analyses run at the unknown argument and are unaffected.
# pack(x,y,z) = (x+2)*64 + (y+2)*8 + (z+2), so the cases are
# 282 = tak(2,1,0) = 1;  355 = tak(3,2,1) = 2;  419 = tak(4,2,1) = 2.
# case: arg=282 => 1
# case: arg=355 => 2
# case: arg=419 => 2
half(n) = ifz n then 0 else ifz (n - 1) then 0 else half(n - 2) - (0 - 1);
q8(p) = half(half(half(p)));
pos7(d) = ifz (d - 1) then 1 else ifz (d - 2) then 1 else ifz (d - 3) then 1 else ifz (d - 4) then 1 else ifz (d - 5) then 1 else ifz (d - 6) then 1 else ifz (d - 7) then 1 else 0;
tak(p) = let a = q8(q8(p)) in let r = p - 64 * a in let b = q8(r) in let c = r - 8 * b in ifz pos7(a - b) then c else tak(tak((a - 1) * 64 - (0 - (b * 8 - (0 - c)))) * 64 - (0 - (tak((b - 1) * 64 - (0 - (c * 8 - (0 - a)))) * 8 - (0 - tak((c - 1) * 64 - (0 - (a * 8 - (0 - b))))))));
tak(x) - 2
