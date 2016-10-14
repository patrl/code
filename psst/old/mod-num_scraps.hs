some :: [E] -> Var -> Tower Var -- indefinite determiner
some np i k ss = [s' | s <- ss,
                       x <- np,
                       s' <- k i [put x i s]]

sigma :: Var -> U -> U -- selective maximization
sigma i u ss = [s | s <- u ss,
                    all (lt i s) $ u ss]

num :: Int -> Var -> U -> U -- selective cardinality test
num n i u ss = [s | s <- u ss,
                    length (s i) == n]

exactly :: Int -> [E] -> Var -> Tower Var
exactly n np i = num n i . sigma i . some np i

justSigma :: [E] -> Var -> Tower Var -- for debugging/sanity checks
justSigma np i = sigma i . some np i

lift :: E -> Var -> Tower Var
lift e i k ss =
  [s' | s <- ss,
        s' <- k i [put e i s]]
