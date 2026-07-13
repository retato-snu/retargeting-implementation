# Ackermann's function, the classic nested double recursion A(m,n) =
#   n+1                     if m = 0
#   A(m-1, 1)               if n = 0
#   A(m-1, A(m, n-1))       otherwise
# T functions take one argument, so each m-level is its own single-arg function
# a0/a1/a2 (= A(0,.)/A(1,.)/A(2,.)); the nested call A(m-1, A(m, n-1)) is kept
# literally as a1(a2(n - 1)) etc. With "+1" written as n - (0 - 1).
# A(2,n) = 2n+3: A(2,0)=3, A(2,1)=5, A(2,2)=7, A(2,3)=9.
# case: arg=0 => 3
# case: arg=1 => 5
# case: arg=2 => 7
# case: arg=3 => 9
a0(n) = n - (0 - 1); a1(n) = ifz n then a0(1) else a0(a1(n - 1)); a2(n) = ifz n then a1(1) else a1(a2(n - 1)); a2(x)
