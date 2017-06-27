a :: p -> q -> p
a x1 _ = x1

b :: (p -> q -> r) -> (p -> q) -> p -> r
b x1 x2 x3 = x1 x3 (x2 x3)

d :: (((a -> r) -> r) -> r) -> a -> r
d x1 x2 = x1 (\ c8 -> c8 x2)

e :: (((p -> q) -> c) -> c) -> p -> (q -> c) -> c
e x1 x2 x3 = x1 (\ c9 -> x3 (c9 x2))

f :: ((c -> c) -> c) -> c
f x1 = x1 (\ c6 -> c6)

lift0 :: a -> ((a -> r) -> r)
lift0 x1 x2 = x2 x1

lift1 :: (a -> b) -> ((a -> c) -> c) -> (b -> c) -> c
lift1 x1 x2 x3 = x2 (\ c8 -> x3 (x1 c8))

lift2 :: (a -> b -> c) -> ((a -> r) -> r) ->
    ((b -> r) -> r) -> (c -> r) -> r
lift2 x1 x2 x3 x4 = x3 (\ c17 -> x2 (\ c19 -> x4 (x1 c19 c17)))

type K = Integer

main = print (start id)

start = (((lift2 (+) :: (((Integer -> K) -> K) -> (((Integer -> K) -> K) -> ((Integer -> K) -> K)))) (lift0 1 :: ((Integer -> K) -> K))) (lift0 2 :: ((Integer -> K) -> K)))
