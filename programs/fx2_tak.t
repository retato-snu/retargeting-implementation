# Takeuchi's tak, from the Gabriel Lisp benchmark suite, as a 3-argument
# recursion. main takes one argument, so y and z are fixed at 2 and 0: the
# program computes tak(x, 2, 0).
# case: arg=0 => 0
# case: arg=1 => 0
# case: arg=2 => 0
# case: arg=3 => 2
# case: arg=4 => 1
# case: arg=5 => 2
# case: arg=6 => 1
tak(x, y, z) = ifz (y < x) then z else tak(tak(x - 1, y, z), tak(y - 1, z, x), tak(z - 1, x, y)); tak(x, 2, 0)
