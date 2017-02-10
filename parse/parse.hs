import Control.Applicative
import Data.Char

newtype Parser a = Parser { parse :: String -> [(a,String)] }

instance Monad Parser where
  return x = Parser $ \inp -> [(x,inp)]
  p >>= f  = Parser $ \inp -> case parse p inp of
                              []    -> []
                              [(v,out)] -> parse (f v) out

instance Applicative Parser where
  pure    = return
  m <*> n = do
    f <- m
    x <- n
    return $ f x

instance Functor Parser where
  fmap f m = do
    x <- m
    return $ f x

instance Monoid (Parser a) where
  mempty        = Parser $ \inp -> []
  m `mappend` n = Parser $ \inp -> parse m inp ++ parse n inp

instance Alternative Parser where
  empty   = mempty
  p <|> q = Parser $ \inp -> case parse p inp of
                             [] -> parse q inp
                             xs -> xs

item :: Parser Char
item = Parser $ \inp -> case inp of
                        []     -> []
                        (x:xs) -> [(x,xs)]

satisfy :: (Char -> Bool) -> Parser Char
satisfy p = do x <- item
               if p x then return x else mempty

digit :: Parser Char
digit = satisfy isDigit

char :: Char -> Parser Char
char c = satisfy (c ==)

string :: String -> Parser String
string []     = return []
string (c:cs) = do
  char c
  string cs
  return $ c:cs

number :: Parser Int
number = do
  s <- string "-" <|> return ""
  cs <- some digit
  return $ read (s ++ cs)
