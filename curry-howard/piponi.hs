import System.Process

infixr 5 :->
data Proposition = Proposition :-> Proposition
                 | Symbol String
                 | Bot deriving Eq

not p = p :-> Bot

instance Show Proposition where
  show (a :-> b) = "(" ++ show a ++ " -> " ++ show b ++ ")"
  show (Symbol s) = s
  show Bot = "⊥"

data Proof = MP Proof Proof
           | Axiom String Proposition deriving Eq

instance Show Proof where
  show (Axiom n t) = "(" ++ n ++ " :: " ++ show t ++ ")"
  show (MP f x) = "(" ++ show f ++ " " ++ show x ++ ")"

source :: Proposition -> Proposition
source (a :-> b) = a

target :: Proposition -> Proposition
target (a :-> b) = b

consequence :: Proof -> Proposition
consequence (Axiom _ p) = p
consequence (MP f _) = target $ consequence f

infixl 5 @@
(@@) :: Proof -> Proof -> Proof
f @@ g | source (consequence f) == consequence g = MP f g
       | otherwise = error $ "@@ error "++show f ++"   "++show g

a :: Proposition -> Proof
a m@(p :-> (q :-> p'))
 | p==p' = Axiom "a" m

b :: Proposition -> Proof
b m@((p :-> (q :-> r)) :-> ((p' :-> q') :-> (p'' :-> r')))
 | p==p' && p==p'' && q==q' && r==r' = Axiom "b" m

c :: Proposition -> Proof
c m@(((p :-> Bot) :-> Bot) :-> p')
 | p==p' = Axiom "c" m

identity :: Proposition -> Proof
identity p = b1 @@ a1 @@ a2 where
  b1 = b ((p :-> (p :-> p) :-> p)
             :-> (p :-> p :-> p)
             :-> (p :-> p))
  a1 = a (p :-> (p :-> p) :-> p)
  a2 = a (p :-> p :-> p)

class Translatable a where
  (#) :: a -> Proposition -> a

instance Translatable Proposition where
  Bot#k = k
  (p :-> q)#k = (p#k) :-> (q#k)
  p#k = (p :-> k) :-> k

compile start = do
  readFile "preamble.hs" >>= writeFile "out.hs"
  appendFile "out.hs" "\nstart = "
  appendFile "out.hs" (show $ start#(Symbol "K"))
  appendFile "out.hs" "\n"
  system "ghci out.hs"

integer = Symbol "Integer"
int n = Axiom ("lift0 " ++ show n) integer
plus = Axiom "lift2 (+)" (integer :-> integer :-> integer)

ex1 = plus @@ int 1 @@ int 2




pushdown q proof = g (
            consequence proof
            :-> (q :-> source (consequence proof))
            :-> (q :-> target (consequence proof))
            ) @@ proof

g' p q r = g $ ((q :-> r) :-> (p :-> q) :-> (p :-> r))
g2 a b | source (consequence a) == target (consequence b) =
    ((g' (source (consequence b))
        (target (consequence b)) (target (consequence a))) @@ a) @@ b

not' k p = p :-> k

not'2 k = not' k . not' k
not'4 k = not'2 k . not'2 k

instance Translatable Proof where
  m@(Axiom "a" _)#k = a ((consequence m)#k)
  m@(Axiom "b" _)#k = b ((consequence m)#k)
  m@(MP f g)#k = (f#k) @@ (g#k)
  m@(Axiom "c" (((p :-> Bot) :-> Bot) :-> p'))#k =
          foldl1 g2 (reverse $ steps p) where
          steps Bot = [f (((k :-> k) :-> k) :-> k)]
          steps p@(Symbol _) = [d (not'4 k p :-> not'2 k p)]
          steps (p :-> q) =
              let pushed = map (pushdown (p#k)) (steps q)
              in e (not'2 k ((p#k) :-> (q#k)) :->
                source (consequence (head pushed))) : pushed
  m@(Axiom a p)#k = Axiom a (p#k)
  x#k = error ("Can't gg_proof k " ++ show x)

d m@((((p :-> k) :-> k1) :-> k2) :-> (p' :-> k3))
    | (p,k,k,k)==(p',k1,k2,k3) = Axiom "d" m

e m@((((p :-> q) :-> end1) :-> end2) :->
     (p' :-> ((q' :-> end3) :-> end4))) |
     (p,q,end1,end1,(end1,end1))==(p',q',end1,end2,(end3,end4)) =
 Axiom "e" m

f m@(((result :-> end1) :-> end2) :-> end3) |
    (result,result,result)==(end1,end2,end3) = Axiom "f" m

g m@((q :-> r) :-> (p :-> q') :-> (p' :-> r'))
    = if (p,q,r)==(p',q',r') then Axiom "(.)" m else error "g"
