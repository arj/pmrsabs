module Sorts (
  Sort(..), SortedSymbol(..), RankedAlphabet,
  createSort,
  o, (~>),
  ar,
  sortToList, sortFromList,
  mkRankedAlphabet, rankedAlphabetToSet
  ) where

import Data.Set (Set)
import qualified Data.Set as S

import Data.Map (Map)
import qualified Data.Map as M

data Sort = Base
          | DataDomain
          | Arrow Sort Sort
          deriving (Eq,Ord)

instance Show Sort where
  show Base               = "o"
  show DataDomain         = "d"
  show (Arrow s1@Base s2) = show s1 ++ " -> " ++ show s2
  show (Arrow s1 s2)      = "(" ++ show s1 ++ ") -> " ++ show s2

type RankedAlphabet = Map String Sort

mkRankedAlphabet :: [SortedSymbol] -> RankedAlphabet
mkRankedAlphabet = foldl f M.empty
  where
    f ack (SortedSymbol f srt) = M.insert f srt ack

rankedAlphabetToSet :: RankedAlphabet -> Set SortedSymbol
rankedAlphabetToSet = S.fromList . map (uncurry SortedSymbol) . M.toList

createSort :: Int -> Sort
createSort 0 = Base
createSort n = Arrow Base $ createSort (n-1)

data SortedSymbol = SortedSymbol String Sort
  deriving (Eq,Ord)

instance Show SortedSymbol where
  show (SortedSymbol s srt) = s ++ ":" ++ show srt

o :: Sort
o = Base

infixr 5 ~>

(~>) :: Sort -> Sort -> Sort
(~>) s1 s2 = Arrow s1 s2

ar :: Sort -> Int
ar Base = 0
ar (Arrow _ s) = 1 + ar s

sortToList :: Sort -> [Sort]
sortToList Base = [Base]
sortToList (Arrow s s2) = s : sortToList s2

sortFromList :: [Sort] -> Sort
sortFromList = foldl Arrow Base