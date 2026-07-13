# Faithful re-port of algo_tak.t using div/mod (unpack) and lt (comparison).
# Takeuchi's tak function (Gabriel 1985), McCarthy's z-returning variant:
#   tak(x,y,z) = z if not (y < x), else
#                tak(tak(x-1,y,z), tak(y-1,z,x), tak(z-1,x,y)).
# The single T argument still packs the triple base-8 with every component
# shifted by +2: p = (x+2)*64 + (y+2)*8 + (z+2). The multi-arg packing REMAINS
# (multi-arg is a later milestone); only the ENCODING of the unpack and the
# comparison change. The old port unpacked with a q8 (=div 8) half chain and
# tested y < x with the 7-arm positivity chain pos7(x - y); here the top digit
# is p / 64, the packed remainder is p - 64*a, the middle digit r / 8, and
# y < x is the primitive (b < a) on the shifted digits (shift-invariant).
# For the scaled instances every shifted digit stays in 0..7, so (b < a) and
# pos7(a - b) agree exactly. main unshifts the result (- 2). Cases from
# algo_tak.t: pack(x,y,z) = (x+2)*64 + (y+2)*8 + (z+2), so
# 282 = tak(2,1,0) = 1;  355 = tak(3,2,1) = 2;  419 = tak(4,2,1) = 2.
# case: arg=282 => 1
# case: arg=355 => 2
# case: arg=419 => 2
tak(p) = let a = p / 64 in let r = p - 64 * a in let b = r / 8 in let c = r - 8 * b in ifz (b < a) then c else tak(tak((a - 1) * 64 - (0 - (b * 8 - (0 - c)))) * 64 - (0 - (tak((b - 1) * 64 - (0 - (c * 8 - (0 - a)))) * 8 - (0 - tak((c - 1) * 64 - (0 - (a * 8 - (0 - b))))))));
tak(x) - 2
