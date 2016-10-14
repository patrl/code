type E = Int
type D r a = r -> (a, r)

unit :: a -> D r a
unit x i = (x, i)

bind :: D r a -> (a -> D r b) -> D r b
bind m k i = uncurry k $ m i

he :: E -> E
he = id

heD :: D E E
heD = he >>= unit -- == get

put :: E -> D E E
put x i = (x, x)

uncurryD :: D r (D s a) -> D (r, s) a
uncurryD m (i, j) = (x, (k, l))
  where (n, k) = m i
        (x, l) = n j

s :: D E (D E (D E E))
s = put 5 `bind` \x ->
      unit $ heD `bind` \y ->
        unit $ heD `bind` \z ->
          unit $ x + y + z

main :: IO ()
main = print $ uncurryD (uncurryD s) ((1, 2), 3)
-- (10, ((5, 2), 3)) [destructive update!]
