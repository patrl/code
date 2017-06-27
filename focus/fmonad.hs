import Control.Monad

data F a = F { getF :: (a, [a]) }

instance Show a => Show (F a) where
  show (F m) = show m

instance Monad F where
  return x = F (x, [x])
  F (x, xs) >>= f = F (fst (getF (f x)), xs >>= snd . getF . f)

instance Applicative F where
  pure = return
  (<*>) = ap

instance Functor F where
  fmap = (<*>) . pure

type E = Int

domain :: [E]
domain = [1..3]

fmark :: E -> F E
fmark x = F (x, domain)

who :: [E]
who = domain

whoF = do x <- who
          return (fmark x)

disj x y = [x,y]
