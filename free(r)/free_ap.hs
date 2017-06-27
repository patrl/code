{-# LANGUAGE GADTs, RankNTypes #-}

data Ap f a where
  Pure :: a -> Ap f a
  Ap   :: f a -> Ap f (a -> b) -> Ap f b

instance Functor (Ap f) where
  fmap f (Pure a)   = Pure (f a)
  fmap f (Ap x y)   = Ap x ((f .) <$> y)

instance Applicative (Ap f) where
  pure = Pure
  Pure f <*> y = fmap f y
  Ap x y <*> z = Ap x (flip <$> y <*> z)

liftAp :: f a -> Ap f a
liftAp x = Ap x (Pure id)


data Free f a = Ret a | Free (f (Free f a))

data AdderF k = Add Int (Bool -> k) | Clear k | Total (Int -> k)

instance Functor AdderF where
  fmap f (Add x k) = Add x (f . k)
  fmap f (Clear k) = Clear (f k)
  fmap f (Total k) = Total (f . k)

newtype C m a = C { unC :: forall r. (a -> m r) -> m r }

x :: C [] Int
x = C ([] >>=)

y :: forall r. (Int -> r) -> [r]
y f = undefined
