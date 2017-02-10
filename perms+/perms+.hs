import Data.List

data Things = B | M | X | Y | Z | BT | MT | XT | YT | ZT
    deriving (Show, Eq, Enum, Ord)

uni :: [Things]
uni = [B ..]

depth :: Int
depth = 3

hos :: [Things]
hos = take depth uni

los :: [Things]
los = take depth $ drop 5 uni

newUni :: [Things]
newUni = hos ++ los

prec :: (Things, Things) -> [Things] -> Bool
prec (t1, t2) ts = elemIndices t1 ts <= elemIndices t2 ts

uniPerms :: [[Things]]
uniPerms = sort [ ts | ts <- permutations newUni,
                       all (\n -> prec (hos!!n, los!!n) ts) [0 .. depth-1] ]

uniPermsFiltered = sort [ ts | ts <- uniPerms,
                               all (`elem` hos) $ take depth ts ]

main = print [ length uniPerms,
               length uniPermsFiltered ]
