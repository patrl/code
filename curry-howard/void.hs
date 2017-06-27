data Void
type Not a = a -> Void

test :: Not (Not (Either a (Not a)))
test k = k (Right (\x -> k (Left x)))
