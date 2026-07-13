# SAI benchmark port (OOPSLA'19 Fig. 9 row "mbrotZ"; artifact benchmarks/mbrotZ.sch).
# Mandelbrot escape-time counting: per grid point, iterate z -> z^2 + c from the
# point itself (the original's loop1 also starts at the offset point), counting
# iterations until |z| exceeds the escape radius 2 OR the max-count cap is hit;
# an outer loop sweeps the grid from n-1 down to 0 and the counts land in a
# matrix. Port: T has integers only, so the complex float arithmetic becomes
# fixed-point arithmetic at scale 4 (z_fp = 4z; z^2 truncates as
# half(half(z*z))) on the nonnegative real axis c_fp = 0..n-1 - the original's
# negative-quadrant region and the imaginary axis are unreachable because half
# (repeated subtraction by 2) diverges on negatives, and zr^2 - zi^2 + cr goes
# negative. Escape |z| >= 2 is z_fp >= 8, i.e. esc(z) = half^3(z) nonzero. The
# original's max-count loop guard IS ported (unlike the escaping-segment-only
# variant it replaces): max-count = 8 (scaled from 64), unrolled into the step
# chain s0..s8 because packing the counter into the loop state would blow the
# decode budget; interior points (c_fp 0 and 1, which never escape) correctly
# return the cap 8. The (z,c) state packs as c*32+z (both < 32). The grid loop
# returns the SUM of counts (the original returns one matrix entry, but T has
# no arrays to read back from).
# case: arg=1 => 8
# case: arg=2 => 16
# case: arg=3 => 20
# case: arg=4 => 22
# case: arg=6 => 24
half(n) = ifz n then 0 else ifz (n - 1) then 0 else half(n - 2) - (0 - 1);
d32(p) = half(half(half(half(half(p)))));
m32(p) = p - 32 * d32(p);
esc(z) = half(half(half(z)));
nxt(p) = let c = d32(p) in let z = m32(p) in c * 32 - (0 - (half(half(z * z)) - (0 - c)));
s0(p) = ifz esc(m32(p)) then s1(nxt(p)) else 0;
s1(p) = ifz esc(m32(p)) then s2(nxt(p)) else 1;
s2(p) = ifz esc(m32(p)) then s3(nxt(p)) else 2;
s3(p) = ifz esc(m32(p)) then s4(nxt(p)) else 3;
s4(p) = ifz esc(m32(p)) then s5(nxt(p)) else 4;
s5(p) = ifz esc(m32(p)) then s6(nxt(p)) else 5;
s6(p) = ifz esc(m32(p)) then s7(nxt(p)) else 6;
s7(p) = ifz esc(m32(p)) then s8(nxt(p)) else 7;
s8(p) = 8;
grid(n) = ifz n then 0 else grid(n - 1) - (0 - s0((n - 1) * 32 - (0 - (n - 1))));
grid(x)
