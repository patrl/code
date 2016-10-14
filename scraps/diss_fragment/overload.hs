{-# OPTIONS -XTypeFamilies #-}

module Main (main) where

class Fun a where
     type Dom a :: *
     type Cod a :: *
     (#)        :: a -> Dom a -> Cod a

main = putStrLn "hi"