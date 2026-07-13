# ifz chain nested four deep, classifying the implicit input x.
# x=0 -> 100; x=1 -> 10; x=2 -> 20; x=3 -> 30; otherwise -> 40.
# case: arg=0 => 100
# case: arg=1 => 10
# case: arg=2 => 20
# case: arg=3 => 30
# case: arg=5 => 40
ifz x then 100 else ifz x - 1 then 10 else ifz x - 2 then 20 else ifz x - 3 then 30 else 40
