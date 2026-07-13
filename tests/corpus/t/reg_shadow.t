# Heavy variable shadowing across nested lets.
# outer a=2; b=6; shadow a=5; shadow b=25; shadow a=15; result 15-25 = -10.
# expect: -10
let a = 2 in let b = a * 3 in let a = b - 1 in let b = a * a in let a = b - (a * 2) in a - b
