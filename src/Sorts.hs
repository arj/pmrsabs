module Sorts (
  Sort(..), SortedSymbol(..),
  createSort,
  o, (~>)
  ) where

data Sort = Base
          | DataDomain
          | Arrow Sort Sort
          deriving (Eq,Ord)

instance Show Sort where
  show Base               = "o"
  show DataDomain         = "d"
  show (Arrow s1@Base s2) = show s1 ++ " -> " ++ show s2
  show (Arrow s1 s2)      = "(" ++ show s1 ++ ") -> " ++ show s2

createSort :: Int -> Sort
createSort 0 = Base
createSort n = Arrow Base $ createSort (n-1)

data SortedSymbol = SortedSymbol String Sort
  deriving (Eq,Ord)

instance Show SortedSymbol where
  show (SortedSymbol s _) = s

o :: Sort
o = Base

(~>) :: Sort -> Sort -> Sort
(~>) s1 s2 = Arrow s1 s2