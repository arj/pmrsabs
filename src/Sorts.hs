module Sorts (
	Sort(..), SortedSymbol(..),
	createSort,
	o, (~>)
	) where

data Sort a = Base a
            | Arrow (Sort a) (Sort a)
            deriving (Eq,Ord)

instance Show a => Show (Sort a) where
	show (Base b) = show b
	show (Arrow s1@(Base _) s2) = show s1 ++ " -> " ++ show s2
	show (Arrow s1 s2) = "(" ++ show s1 ++ ") -> " ++ show s2

createSort :: Int -> a -> Sort a
createSort 0 b = Base b
createSort n b = Arrow (Base b) $ createSort (n-1) b

data SortedSymbol a = SortedSymbol String (Sort a)
  deriving (Eq,Ord)

instance Show a => Show (SortedSymbol a) where
  show (SortedSymbol s _) = s

o :: Sort ()
o = Base ()

(~>) :: Sort a -> Sort a -> Sort a
(~>) s1 s2 = Arrow s1 s2