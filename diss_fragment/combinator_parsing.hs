module Main (main) where
import Data.List.Split (splitOn) 

-- types for trees
type Terminal  = [Char]
type Label     = [Char]
type Input     = [[Char]]
data ParseTree = Leaf Terminal | Branch (Label,(ParseTree,ParseTree)) 
--    deriving (Show, Eq)

-- monadic bits: Parser monad == State.List monad!
type Parser = Input -> [(ParseTree,Input)]

ret :: ParseTree -> Parser
ret a = \s -> [(a,s)]

bind :: Parser -> (ParseTree -> Parser) -> Parser
m `bind` f = \s -> concatMap (\(a,s') -> f a s') $ m s

-- zero and plus
zero :: Parser
zero = \s -> []

plus :: Parser -> Parser -> Parser
m `plus` n = \s -> concat [m s, n s]

-- leaf, branch parsers
leaf :: Terminal -> Parser
leaf t []                 = []
leaf t (x:xs) | t == x    = [(Leaf x,xs)]
              | otherwise = []

branch :: Label -> Parser -> Parser -> Parser
branch lab m n = m `bind` \x -> n `bind` \y -> ret $ Branch (lab,(x,y))

-- and that's it! let's get cookin..
det,verb,ditr,prep,n,np,dp,pp,vp,s :: Parser
det   = leaf "the"           `plus` 
        leaf "a"              `plus` 
        leaf "every"
verb  = leaf "owns"          `plus` 
        leaf "beats"         `plus` 
        leaf "sees"
ditr  = leaf "gives"         `plus` 
        leaf "shows"         `plus` 
        leaf "owes"
prep  = leaf "with"          `plus` 
        leaf "in"            `plus` 
        leaf "near"
n     = leaf "farmer"        `plus`
        leaf "donkey"        `plus`
        leaf "camera"        `plus`
        leaf "house"
np    = n                    `plus`
        branch "NP" n pp
dp    = leaf "Simon"         `plus`
        branch "DP" det np
pp    = leaf "inside"        `plus`
        branch "PP" prep dp
vp    = leaf "left"          `plus`
        branch "VP" verb dp  `plus`
        branch "VP" vp pp    `plus`
        branch "VP" (branch "VP" ditr dp) dp
s     = branch "S" dp vp

-- parsers
tokenize :: [Char] -> Input
tokenize str = filter 
                   (\str -> not $ str == "") $
                   splitOn " " str
        
getParseTrees :: (ParseTree,Input) -> [ParseTree]
getParseTrees (a,s) | length s == 0 = [a]
                    | otherwise     = [ ]

parseDebug :: [Char] -> [(ParseTree,Input)]
parseDebug = s . tokenize
        
parse :: [Char] -> [ParseTree]
parse = concatMap getParseTrees . parseDebug

-- some test cases
s1 = parse "Simon left"
s2 = parse "a donkey left"
s3 = parse "Simon owns a donkey"
s4 = parse "Simon beats every donkey in the house"
s5 = parse "Simon beats every donkey in the house near the farmer"

-- because the grammar's recursive, can get into loops
-- if you ask for more derivations than it knows about
-- e.g. take 3 s4 ==> \bot
-- also some left-recursive loops? need to look at..

-- pretty printing
texify :: ParseTree -> [Char]
texify (Leaf s) = s
texify (Branch (lab, (left, right))) =
      "[." ++ lab ++ " " ++ texify left ++ " " ++ texify right ++ " ]"

output :: [ParseTree] -> [Char]
output []     = ""
output (x:xs) = "\\Tree " ++ texify x ++ "\n" ++ output xs

main = putStrLn $ output $ take 4 s5