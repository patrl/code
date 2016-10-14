type R r a = r -> a

uncurryR :: R r (R s a) -> R (r, s) a -- an isomorphism
uncurryR m (r, s) = m r s

curryR :: R (r, s) a -> R r (R s a)   -- another isomorphism
curryR m r s = m (r, s)

type S r a = r -> (a, r)

uncurryS :: S r (S s a) -> S (r, s) a -- not an isomorphism!
uncurryS m (r, s) = (v, (t, u))
  where (n, t) = m r
        (v, u) = n s
