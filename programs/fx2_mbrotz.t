# Mandelbrot escape-time counting, from the "mbrotZ" benchmark of Wei, Chen,
# Rompf, "Staged Abstract Interpreters", OOPSLA 2019, Fig. 9, on the nonnegative
# real axis at scale 4: per grid point c_fp = 0..n-1, iterate z -> z^2/4 + c from
# z = c, counting steps until |z| escapes (z_fp >= 8) or the max-count cap 8 is
# hit; the grid loop sums the counts. Each unrolled step s0..s8 is a 2-argument
# function of the state (c,z), and nxt(c,z) returns the next z = z^2/4 + c
# directly: z^2/4 is the primitive (z*z)/4 and the escape test |z|>=2 is z/8
# nonzero. The "# case:" lines record the concrete input/output pairs the program
# is checked against (scripts/check-programs.sh runs them).
# case: arg=1 => 8
# case: arg=2 => 16
# case: arg=3 => 20
# case: arg=4 => 22
# case: arg=6 => 24
esc(z) = z / 8;
nxt(c, z) = z * z / 4 + c;
s0(c, z) = ifz esc(z) then s1(c, nxt(c, z)) else 0;
s1(c, z) = ifz esc(z) then s2(c, nxt(c, z)) else 1;
s2(c, z) = ifz esc(z) then s3(c, nxt(c, z)) else 2;
s3(c, z) = ifz esc(z) then s4(c, nxt(c, z)) else 3;
s4(c, z) = ifz esc(z) then s5(c, nxt(c, z)) else 4;
s5(c, z) = ifz esc(z) then s6(c, nxt(c, z)) else 5;
s6(c, z) = ifz esc(z) then s7(c, nxt(c, z)) else 6;
s7(c, z) = ifz esc(z) then s8(c, nxt(c, z)) else 7;
s8(c, z) = 8;
grid(n) = ifz n then 0 else grid(n - 1) + s0(n - 1, n - 1);
grid(x)
