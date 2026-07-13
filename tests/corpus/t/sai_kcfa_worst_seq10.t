# SAI kcfa-worst family, faithful-semantics witness (not a Fig. 9 row; see
# sai_kcfa_worst_16/32/64.t for the Fig. 9 rows). This variant keeps the
# original's SEQUENTIAL double call: level i really evaluates (f_i #t) then
# (f_i #f) as 'let t = f(1) in f(0)', so the concrete run makes ~2^11 calls
# and the {0,1} merge at every x_i arises from the two calls themselves (not
# from an unknown argument), exactly as in the original. n = 10 is the largest
# depth whose concrete run fits the corpus' I_S^T fuel (n = 11 already
# exhausts the S-CEK step budget; 16/32/64 would need 2^17..2^65 calls). x_1
# is threaded as the pack high bit (pack stays in 0..3, extractor x1of is a
# finite ifz dispatch) and the final kz projects y_1 = x_1, like the original
# z. The program is closed (main takes no argument), like the original; its
# value is the last call chain's x_1 = 0 = the original's #f.
# expect: 0
x1of(p) = ifz p then 0 else ifz (p - 1) then 0 else 1;
k1(v) = let t = k2(v * 2 - (0 - 1)) in k2(v * 2);
k2(p) = let a = x1of(p) in let t = k3(a * 2 - (0 - 1)) in k3(a * 2);
k3(p) = let a = x1of(p) in let t = k4(a * 2 - (0 - 1)) in k4(a * 2);
k4(p) = let a = x1of(p) in let t = k5(a * 2 - (0 - 1)) in k5(a * 2);
k5(p) = let a = x1of(p) in let t = k6(a * 2 - (0 - 1)) in k6(a * 2);
k6(p) = let a = x1of(p) in let t = k7(a * 2 - (0 - 1)) in k7(a * 2);
k7(p) = let a = x1of(p) in let t = k8(a * 2 - (0 - 1)) in k8(a * 2);
k8(p) = let a = x1of(p) in let t = k9(a * 2 - (0 - 1)) in k9(a * 2);
k9(p) = let a = x1of(p) in let t = k10(a * 2 - (0 - 1)) in k10(a * 2);
k10(p) = let a = x1of(p) in let t = kz(a * 2 - (0 - 1)) in kz(a * 2);
kz(p) = x1of(p);
let t = k1(1) in k1(0)
