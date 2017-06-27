import Control.Monad

hm :: (a, a -> (b, b -> c)) -> ((a, b), (a, b) -> c)
hm (a, f) = ((a, fst (f a)), \(x,y) -> snd (f x) y)

gm :: ((a, b), (a, b) -> c) -> (a, a -> (b, b -> c))
gm ((a,b), f) = (a, \x -> (b, \y -> f (x, y)))

instance Show (a -> b) where
  show f = "<fun>"

data F a = P a [a] | Rec (F a) [F a]

p1 (P x xs) = x
p2 (P x xs) = xs

instance Monad F where
  return x = P x [x]
  P x ys >>= f = P (p1 $ f x) $ concat [p2 $ f y | y <- ys]

instance Applicative F where
  pure = return
  (<*>) = ap

instance Functor F where
  fmap f m = pure f <*> m

data FF e a = A e | B (e, FF e (e -> a))
