module Sorts (
  Sort(..), SortedSymbol(..), RankedAlphabet, Symbol,

  createSort,
  removeSigma0,
  sigmaN,
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

type Symbol = String

data Sort = Base
          | Data
          | Arrow Sort Sort
          deriving (Eq,Ord)

instance Show Sort where
  show Base = "o"
  show Data = "d"
  show (Arrow s1@Base s2) = show s1 ++ " -> " ++ show s2
  show (Arrow s1@Data s2) = show s1 ++ " -> " ++ show s2
  show (Arrow s1 s2)      = "(" ++ show s1 ++ ") -> " ++ show s2

-- | Creates a basic sort of arity n.
createSort :: Int -> Sort
createSort 0 = Base
createSort n = Arrow Base $ createSort (n-1)

-- | An abbreviation for the basic sort.
o :: Sort
o = Base

-- | Syntactic sugar for creation of arrow sorts.
(~>) :: Sort -> Sort -> Sort
(~>) s1 s2 = Arrow s1 s2
infixr 5 ~>

-- | Returns the arity of the given sort.
ar :: Sort -> Int
ar Base = 0
ar Data = 0
ar (Arrow _ s) = 1 + ar s

-- | Transforms a sort to a list of sorts by
-- traversing the sort tree to the right and returning
-- the left elements as list items.
-- The last list item is always base or data.
sortToList :: Sort -> [Sort]
sortToList Base = [Base]
sortToList Data = [Data]
sortToList (Arrow s s2) = s : sortToList s2

-- | Creates a sort from a list of sorts.
-- Reverse operation of sortToList.
sortFromList :: [Sort] -> Sort
sortFromList = foldr1 Arrow

-- | Replaces the last argument, i.e. the rightmost left child of the sort
-- tree with a new sort.
replaceLastArg :: Sort -> Sort -> Sort
replaceLastArg _ Data           = Data
replaceLastArg _ Base           = Base
replaceLastArg s (Arrow _ Base) = Arrow s Base
replaceLastArg s (Arrow _ Data) = Arrow s Data
replaceLastArg s (Arrow s1 s2 ) = Arrow s1 (replaceLastArg s s2)

data SortedSymbol = SortedSymbol
                  { ssF    :: Symbol
                  , ssSort :: Sort
                  }
                  deriving (Eq,Ord)

instance Show SortedSymbol where
  show (SortedSymbol s _srt) = s-- ++ ":" ++ show srt

-- ** Definition of a ranked alphabet

type RankedAlphabet = Map Symbol Sort

-- | Creates a ranked alphabet from a list of sorted symbols.
mkRankedAlphabet :: [SortedSymbol] -> RankedAlphabet
mkRankedAlphabet = foldl f M.empty
  where
    f ack (SortedSymbol s srt) = M.insert s srt ack

-- | Creates a set of sorted symbols from a ranked alphabet.
rankedAlphabetToSet :: RankedAlphabet -> Set SortedSymbol
rankedAlphabetToSet = S.fromList . map (uncurry SortedSymbol) . M.toList

-- | Removes all symbols of arity 0 from the ranked alphabet.
removeSigma0 :: RankedAlphabet -> RankedAlphabet
removeSigma0 = M.filter (\srt -> ar srt > 0)

-- | Returns the subset of the ranked alphabet that only contains
-- symbols of arity n.
sigmaN :: Int -> RankedAlphabet -> RankedAlphabet
sigmaN n = M.filter ((n ==) . ar)
