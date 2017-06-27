type E = Int
type D s a = s -> Maybe (a, s)

unit :: a -> D s a
unit x i = Just (x, i)

bind :: D s a -> (a -> D s b) -> D s b
bind m k i = m i >>= uncurry k

heD :: D E E
heD = \x -> Just (x, x)

project :: Eq a => a -> D a a
project n i
  | n == i = Just (n, n)
  | otherwise = Nothing

to :: D r (D s a) -> D (r, s) a
to m (i, j) = do (n, _) <- m i
                 (x, _) <- n j
                 return $ (x, (i, j))

fro :: D (r, s) a -> D r (D s a)
fro m i = Just $ (\j -> do (x, _) <- m (i, j)
                           return (x, j),     i)

s :: D E (D E (D E E))
s = project 1 `bind` \x ->
      unit $ heD `bind` \y ->
        unit $ heD `bind` \z ->
          unit $ x + y + z

main :: IO ()
main = print $ (to.to.fro.fro.to.to $ s) ((1, 2), 3)
