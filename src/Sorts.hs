module Sorts (
  Sort(..), SortedSymbol(..), RankedAlphabet, Symbol,
  createSort,
  o, (~>),
  ar,
  sortToList, sortFromList,
  mkRankedAlphabet, rankedAlphabetToSet,
  replaceLastArg,
  ) where

import Data.Set (Set)
import qualified Data.Set as S

import Data.Map (Map)
import qualified Data.Map as M

import Debug.Trace (trace)

type Symbol = String

data Sort = Base
          | Data
          | Arrow Sort Sort
          deriving (Eq,Ord)

instance Show Sort where
  show Base                     = "o"
  show Data               = "d"
  show (Arrow s1@Base s2)       = show s1 ++ " -> " ++ show s2
  show (Arrow s1@Data s2) = show s1 ++ " -> " ++ show s2
  show (Arrow s1 s2)            = "(" ++ show s1 ++ ") -> " ++ show s2

type RankedAlphabet = Map Symbol Sort

mkRankedAlphabet :: [SortedSymbol] -> RankedAlphabet
mkRankedAlphabet = foldl f M.empty
  where
    f ack (SortedSymbol s srt) = M.insert s srt ack

rankedAlphabetToSet :: RankedAlphabet -> Set SortedSymbol
rankedAlphabetToSet = S.fromList . map (uncurry SortedSymbol) . M.toList

createSort :: Int -> Sort
createSort 0 = Base
createSort n = Arrow Base $ createSort (n-1)

data SortedSymbol = SortedSymbol { ssF :: Symbol
  , ssSort :: Sort
}
  deriving (Eq,Ord)

instance Show SortedSymbol where
  show (SortedSymbol s srt) = s-- ++ ":" ++ show srt

o :: Sort
o = Base

infixr 5 ~>

(~>) :: Sort -> Sort -> Sort
(~>) s1 s2 = Arrow s1 s2

ar :: Sort -> Int
ar Base = 0
ar Data = 0
ar (Arrow _ s) = 1 + ar s

sortToList :: Sort -> [Sort]
sortToList Base = [Base]
sortToList Data = [Data]
sortToList (Arrow s s2) = s : sortToList s2

sortFromList :: [Sort] -> Sort
sortFromList = foldr1 Arrow

replaceLastArg :: Sort -> Sort -> Sort
replaceLastArg _ Data           = Data
replaceLastArg _ Base           = Base
replaceLastArg s (Arrow _ Base) = Arrow s Base
replaceLastArg s (Arrow _ Data) = Arrow s Data
replaceLastArg s (Arrow s1 s2 ) = Arrow s1 (replaceLastArg s s2)