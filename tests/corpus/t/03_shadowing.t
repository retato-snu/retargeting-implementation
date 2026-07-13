# Shadowing: the inner let x rebinds x; the body uses the inner binding.
# let x = 5 in (let x = x - 2 in x * 2) = let x = 3 in 3 * 2 = 6.
# expect: 6
let x = 5 in let x = x - 2 in x * 2
