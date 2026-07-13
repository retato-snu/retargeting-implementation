# SAI benchmark port (OOPSLA'19 Fig. 9 row "kcfa-worst-64"; artifact
# benchmarks/kcfa-worst-case-64.scm). The k-CFA worst-case family (Van Horn &
# Mairson): a chain of 64 functions where level i evaluates (f_i #t) (f_i #f) -
# every f_i is called with both booleans, so a monovariant analysis merges both
# values into x_i at every level - and the innermost 64-ary application
# (z x_1 .. x_64) projects the FIRST bound variable y_1 = x_1 out of the
# nested closure environments. Port: booleans are 1/0; each level keeps both
# call sites but selects by the flowing bit (ifz x_i) - the original's
# evaluate-both-calls shape would make the concrete run take 2^64 calls and
# the corpus executes every program concretely under the I_S^T fuel (see
# sai_kcfa_worst_seq12.t for a faithful sequential-double-call witness at the
# largest n that fits). The analysis, whose unknown argument reaches both
# branches, still merges both constants into every x_i. The y_1 = x_1
# projection is preserved by threading x_1 (the first level's argument,
# normalized to a bit) alongside the flowing bit as the pack x_1*2 + x_i; the
# pack stays in 0..3, so the field extractors x1of/xiof are finite ifz
# dispatches, and the final kz returns x_1 exactly as the original z does. At
# arg 0 the value 0 coincides with the original program's value #f.
# case: arg=0 => 0
# case: arg=1 => 1
# case: arg=7 => 1
x1of(p) = ifz p then 0 else ifz (p - 1) then 0 else 1;
xiof(p) = ifz p then 0 else ifz (p - 1) then 1 else ifz (p - 2) then 0 else 1;
k1(v) = ifz v then k2(1) else k2(2);
k2(p) = let a = x1of(p) in ifz xiof(p) then k3(a * 2 - (0 - 1)) else k3(a * 2);
k3(p) = let a = x1of(p) in ifz xiof(p) then k4(a * 2 - (0 - 1)) else k4(a * 2);
k4(p) = let a = x1of(p) in ifz xiof(p) then k5(a * 2 - (0 - 1)) else k5(a * 2);
k5(p) = let a = x1of(p) in ifz xiof(p) then k6(a * 2 - (0 - 1)) else k6(a * 2);
k6(p) = let a = x1of(p) in ifz xiof(p) then k7(a * 2 - (0 - 1)) else k7(a * 2);
k7(p) = let a = x1of(p) in ifz xiof(p) then k8(a * 2 - (0 - 1)) else k8(a * 2);
k8(p) = let a = x1of(p) in ifz xiof(p) then k9(a * 2 - (0 - 1)) else k9(a * 2);
k9(p) = let a = x1of(p) in ifz xiof(p) then k10(a * 2 - (0 - 1)) else k10(a * 2);
k10(p) = let a = x1of(p) in ifz xiof(p) then k11(a * 2 - (0 - 1)) else k11(a * 2);
k11(p) = let a = x1of(p) in ifz xiof(p) then k12(a * 2 - (0 - 1)) else k12(a * 2);
k12(p) = let a = x1of(p) in ifz xiof(p) then k13(a * 2 - (0 - 1)) else k13(a * 2);
k13(p) = let a = x1of(p) in ifz xiof(p) then k14(a * 2 - (0 - 1)) else k14(a * 2);
k14(p) = let a = x1of(p) in ifz xiof(p) then k15(a * 2 - (0 - 1)) else k15(a * 2);
k15(p) = let a = x1of(p) in ifz xiof(p) then k16(a * 2 - (0 - 1)) else k16(a * 2);
k16(p) = let a = x1of(p) in ifz xiof(p) then k17(a * 2 - (0 - 1)) else k17(a * 2);
k17(p) = let a = x1of(p) in ifz xiof(p) then k18(a * 2 - (0 - 1)) else k18(a * 2);
k18(p) = let a = x1of(p) in ifz xiof(p) then k19(a * 2 - (0 - 1)) else k19(a * 2);
k19(p) = let a = x1of(p) in ifz xiof(p) then k20(a * 2 - (0 - 1)) else k20(a * 2);
k20(p) = let a = x1of(p) in ifz xiof(p) then k21(a * 2 - (0 - 1)) else k21(a * 2);
k21(p) = let a = x1of(p) in ifz xiof(p) then k22(a * 2 - (0 - 1)) else k22(a * 2);
k22(p) = let a = x1of(p) in ifz xiof(p) then k23(a * 2 - (0 - 1)) else k23(a * 2);
k23(p) = let a = x1of(p) in ifz xiof(p) then k24(a * 2 - (0 - 1)) else k24(a * 2);
k24(p) = let a = x1of(p) in ifz xiof(p) then k25(a * 2 - (0 - 1)) else k25(a * 2);
k25(p) = let a = x1of(p) in ifz xiof(p) then k26(a * 2 - (0 - 1)) else k26(a * 2);
k26(p) = let a = x1of(p) in ifz xiof(p) then k27(a * 2 - (0 - 1)) else k27(a * 2);
k27(p) = let a = x1of(p) in ifz xiof(p) then k28(a * 2 - (0 - 1)) else k28(a * 2);
k28(p) = let a = x1of(p) in ifz xiof(p) then k29(a * 2 - (0 - 1)) else k29(a * 2);
k29(p) = let a = x1of(p) in ifz xiof(p) then k30(a * 2 - (0 - 1)) else k30(a * 2);
k30(p) = let a = x1of(p) in ifz xiof(p) then k31(a * 2 - (0 - 1)) else k31(a * 2);
k31(p) = let a = x1of(p) in ifz xiof(p) then k32(a * 2 - (0 - 1)) else k32(a * 2);
k32(p) = let a = x1of(p) in ifz xiof(p) then k33(a * 2 - (0 - 1)) else k33(a * 2);
k33(p) = let a = x1of(p) in ifz xiof(p) then k34(a * 2 - (0 - 1)) else k34(a * 2);
k34(p) = let a = x1of(p) in ifz xiof(p) then k35(a * 2 - (0 - 1)) else k35(a * 2);
k35(p) = let a = x1of(p) in ifz xiof(p) then k36(a * 2 - (0 - 1)) else k36(a * 2);
k36(p) = let a = x1of(p) in ifz xiof(p) then k37(a * 2 - (0 - 1)) else k37(a * 2);
k37(p) = let a = x1of(p) in ifz xiof(p) then k38(a * 2 - (0 - 1)) else k38(a * 2);
k38(p) = let a = x1of(p) in ifz xiof(p) then k39(a * 2 - (0 - 1)) else k39(a * 2);
k39(p) = let a = x1of(p) in ifz xiof(p) then k40(a * 2 - (0 - 1)) else k40(a * 2);
k40(p) = let a = x1of(p) in ifz xiof(p) then k41(a * 2 - (0 - 1)) else k41(a * 2);
k41(p) = let a = x1of(p) in ifz xiof(p) then k42(a * 2 - (0 - 1)) else k42(a * 2);
k42(p) = let a = x1of(p) in ifz xiof(p) then k43(a * 2 - (0 - 1)) else k43(a * 2);
k43(p) = let a = x1of(p) in ifz xiof(p) then k44(a * 2 - (0 - 1)) else k44(a * 2);
k44(p) = let a = x1of(p) in ifz xiof(p) then k45(a * 2 - (0 - 1)) else k45(a * 2);
k45(p) = let a = x1of(p) in ifz xiof(p) then k46(a * 2 - (0 - 1)) else k46(a * 2);
k46(p) = let a = x1of(p) in ifz xiof(p) then k47(a * 2 - (0 - 1)) else k47(a * 2);
k47(p) = let a = x1of(p) in ifz xiof(p) then k48(a * 2 - (0 - 1)) else k48(a * 2);
k48(p) = let a = x1of(p) in ifz xiof(p) then k49(a * 2 - (0 - 1)) else k49(a * 2);
k49(p) = let a = x1of(p) in ifz xiof(p) then k50(a * 2 - (0 - 1)) else k50(a * 2);
k50(p) = let a = x1of(p) in ifz xiof(p) then k51(a * 2 - (0 - 1)) else k51(a * 2);
k51(p) = let a = x1of(p) in ifz xiof(p) then k52(a * 2 - (0 - 1)) else k52(a * 2);
k52(p) = let a = x1of(p) in ifz xiof(p) then k53(a * 2 - (0 - 1)) else k53(a * 2);
k53(p) = let a = x1of(p) in ifz xiof(p) then k54(a * 2 - (0 - 1)) else k54(a * 2);
k54(p) = let a = x1of(p) in ifz xiof(p) then k55(a * 2 - (0 - 1)) else k55(a * 2);
k55(p) = let a = x1of(p) in ifz xiof(p) then k56(a * 2 - (0 - 1)) else k56(a * 2);
k56(p) = let a = x1of(p) in ifz xiof(p) then k57(a * 2 - (0 - 1)) else k57(a * 2);
k57(p) = let a = x1of(p) in ifz xiof(p) then k58(a * 2 - (0 - 1)) else k58(a * 2);
k58(p) = let a = x1of(p) in ifz xiof(p) then k59(a * 2 - (0 - 1)) else k59(a * 2);
k59(p) = let a = x1of(p) in ifz xiof(p) then k60(a * 2 - (0 - 1)) else k60(a * 2);
k60(p) = let a = x1of(p) in ifz xiof(p) then k61(a * 2 - (0 - 1)) else k61(a * 2);
k61(p) = let a = x1of(p) in ifz xiof(p) then k62(a * 2 - (0 - 1)) else k62(a * 2);
k62(p) = let a = x1of(p) in ifz xiof(p) then k63(a * 2 - (0 - 1)) else k63(a * 2);
k63(p) = let a = x1of(p) in ifz xiof(p) then k64(a * 2 - (0 - 1)) else k64(a * 2);
k64(p) = let a = x1of(p) in ifz xiof(p) then kz(a * 2 - (0 - 1)) else kz(a * 2);
kz(p) = x1of(p);
k1(x)
