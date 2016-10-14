data PM a = PM [(a, Float)]
  deriving (Show, Eq)

instance Functor PM where
  fmap f (PM a) = PM [(f x, n) | (x, n) <- a]

instance Applicative PM where
  pure = return
  PM a <*> PM b = PM [(f x, m*n) | (f, m) <- a, (x, n) <- b]

instance Monad PM where
  PM a >>= f = PM [(y, m*n) | (x, m) <- a, (y, n) <- unPM $ f x]
  return x = PM [(x, 1)]

unPM :: PM t -> [(t, Float)]
unPM (PM x) = x

certainly, impossible :: a -> PM a
certainly = return
impossible x = PM [(x, 0)]
