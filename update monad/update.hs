import Control.Applicative
import Control.Monad

newtype Upd m s a = Upd { runUpd :: m s -> m (a,s) }

instance Monad m => Monad (Upd m s) where
  return x = Upd $ \ss -> do s <- ss
                             return (x,s)
  Upd m >>= k = Upd $ \ss -> do (a,s) <- m ss
                                runUpd (k a) (return s)

{--
 -
 - Only monadic if we restrict the type-space to distributive updates
 -
 - (Upd m) is distributive iff ∀ss: m ss == do {s <- ss; m $ return s}
   - For Set, ∀ss: m ss == U{m {s} | s <- ss}
   - For Reader, ∀ss: \i -> m (\j -> ss j) i == \i -> m (\j -> ss i) i
   - For Cont, ∀ss: \k -> m (\c -> ss c) k == \k -> ss (\s -> m (\c -> c s) k)
 -
 - Without this restriction, `return x >>= k == k x` fails for certain k
 -
--}

newtype Updd s a = Updd {runUpdd :: [s] -> [[(a, s)]]}

instance Monad (Updd s) where
  return x = Updd $ \ss -> [[(x,s)] | s <- ss]
  Updd m >>= k = Updd $ \ss -> do
    vs <- m ss
    (x,s) <- vs
    runUpdd (k x) [s]

-- boilerplate
instance Monad m => Functor (Upd m s) where
  fmap = liftM

instance Monad m => Applicative (Upd m s) where
  pure = return
  (<*>) = ap

instance Functor (Updd s) where
  fmap = liftM

instance Applicative (Updd s) where
  pure = return
  (<*>) = ap

instance MonadPlus m => MonadPlus (Upd m s) where
  mzero = Upd (\s -> mzero)
  mplus (Upd m) (Upd n) = Upd (\ss -> m ss `mplus` n ss)

instance MonadPlus m => Alternative (Upd m s) where
  (<|>) = mplus
  empty = mzero
