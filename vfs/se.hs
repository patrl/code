type R r a = r -> a

uncurryR :: R r (R s a) -> R (r, s) a -- an isomorphism
uncurryR m (r,s) = m r s

curryR :: R (r, s) a -> R r (R s a)   -- another isomorphism
curryR m r s = m (r,s)

type S r a = r -> (a,r)

uncurryS :: S r (S s a) -> S (r, s) a -- not an isomorphism!
uncurryS m (r,s) = (v,(t,u))
  where (n,t) = m r
        (v,u) = n s

type NR r a = r -> [a]

uncurryNR :: NR r (NR s a) -> NR (r, s) a -- not an isomorphism!
uncurryNR m (r,s) = [v | n <- m r, v <- n s]

type NS r a = r -> [(a, r)]

uncurryNS :: NS r (NS s a) -> NS (r, s) a -- not an isomorphism!
uncurryNS m (r,s) = [(v, (t,u)) | (n,t) <- m r, (v,u) <- n s]

data Seq a b = Nil | Push (Seq a b) (Either a b) deriving (Show, Eq)

curryRSeq :: R (Seq a b) c -> Either a b -> Seq a b -> c
curryRSeq m r s = m $ Push s r

uncurryRSeq :: R (Either a b) (R (Seq a b) c) -> R (Seq a b) c
uncurryRSeq m (Push s r) = m r s

get :: Int -> Seq a b -> Either a b
get 0 (Push s v) = v
get n (Push s v) = get (n-1) s

concatSeq :: Seq a b -> Seq a b -> Seq a b
concatSeq Nil s = s
concatSeq (Push s1 v) s2 = Push (concatSeq s1 s2) v
