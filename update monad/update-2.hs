{-# LANGUAGE DeriveFunctor #-}

data Form = P | Q | R | Conj Form Form | Neg Form deriving (Show, Eq)

type W = Form -> Bool
type C = [W]

newtype ST a = ST { unST :: C -> (a, C) } deriving Functor

instance Monad ST where
  return x = ST $ \c -> (x, c)
  ST m >>= f = ST $ \c -> let (x, c') = m c in unST (f x) c'

instance Applicative ST where
  pure = return
  mf <*> mx = do {f <- mf; x <- mx; return (f x)}

eval :: Form -> ST Form
eval P = ST $ \c -> (P, [w | w <- c, w P])
eval Q = ST $ \c -> (Q, [w | w <- c, w Q])
eval R = ST $ \c -> (R, [w | w <- c, w R])
eval (Conj p q) = do {p' <- eval p; q' <- eval q; return (Conj p' q')}
eval (Neg p) = ST $ \c -> (p, [w | w <- c, null $ (unST . eval) p [w]])
