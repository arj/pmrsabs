module Sorts (
  Sort(..), SortedSymbol(..), RankedAlphabet, Symbol,

  createSort,
  removeSigma0,
  sigmaN,
  o, (~>),
  ar,
  sortToList, sortFromList,
  mkRankedAlphabet, rankedAlphabetToSet,
  closeRankedAlphabet,
  replaceLastArg,
  unify, unify', unboundToBase,
  substTB
  ) where

import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M
import Control.Arrow (second)

type Symbol = String

data Sort = Base
          | Data
          | Arrow Sort Sort
          | SVar Symbol
          deriving (Eq,Ord)

instance Show Sort where
  show Base = "o"
  show Data = "d"
  show (SVar x) = x
  show (Arrow s1@Base s2) = show s1 ++ " -> " ++ show s2
  show (Arrow s1@Data s2) = show s1 ++ " -> " ++ show s2
  show (Arrow s1@(SVar _) s2) = show s1 ++ " -> " ++ show s2
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
sortToList x@(SVar _) = [x]
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
replaceLastArg _ x@(SVar _)     = x
replaceLastArg s (Arrow _ Base) = Arrow s Base
replaceLastArg s (Arrow _ Data) = Arrow s Data
replaceLastArg s (Arrow _ x@(SVar _)) = Arrow s x
replaceLastArg s (Arrow s1 s2 ) = Arrow s1 (replaceLastArg s s2)

data SortedSymbol = SortedSymbol
                  { ssF    :: Symbol
                  , ssSort :: Sort
                  }
                  deriving (Eq,Ord)

instance Show SortedSymbol where
  show (SortedSymbol s _srt) = s ++ ":" ++ show _srt

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

closeRankedAlphabet :: RankedAlphabet -> RankedAlphabet
closeRankedAlphabet = M.map f
  where
    f (Base) = Base
    f (Data) = Data
    f (Arrow s1 s2) = Arrow (f s1) (f s2)
    f (SVar _) = Base

-- | Removes all symbols of arity 0 from the ranked alphabet.
removeSigma0 :: RankedAlphabet -> RankedAlphabet
removeSigma0 = M.filter (\srt -> ar srt > 0)

-- | Returns the subset of the ranked alphabet that only contains
-- symbols of arity n.
sigmaN :: Int -> RankedAlphabet -> RankedAlphabet
sigmaN n = M.filter ((n ==) . ar)

type SortConstraints = [(Sort, Sort)]

type Substitution = [(Symbol,Sort)]

fv :: Sort -> Set Symbol
fv Base = S.empty
fv Data = S.empty
fv (SVar x) = S.singleton x
fv (Arrow s1 s2) = fv s1 `S.union` fv s2

subst :: Symbol -> Sort -> Sort -> Sort
subst _ _ Base = Base
subst _ _ Data = Data
subst x s srt@(SVar y) = if x == y then s else srt
subst x s (Arrow s1 s2) = Arrow (subst x s s1) (subst x s s2)

substSC :: Symbol -> Sort -> SortConstraints -> SortConstraints
substSC x s sc = map f sc
  where
    f (s1,s2) = (subst x s s1, subst x s s2)

substS :: Symbol -> Sort -> Substitution -> Substitution
substS x s sc = map f sc
  where
    f (s1,s2) = (s1, subst x s s2)

substTB :: Substitution -> Substitution -> Substitution
substTB sub tb = map (second f) tb
  where
    f :: Sort -> Sort
    f srt = foldl (\ack (x,s) -> subst x s ack) srt sub

unify :: SortConstraints -> Either String Substitution
unify tc = do
  res <- unify' tc
  return $ foldl (\ack (x,s) -> substS x s ack) res res

unboundToBase :: Substitution -> Substitution
unboundToBase s = map (second f) s
  where
    f (SVar _) = Base
    f t = t

unify' :: SortConstraints -> Either String Substitution
unify' [] = return []
unify' ((s1,s2):rest) =
  if s1 == s2
    then unify' rest
    else
      case (s1,s2) of
        (Arrow t1 t2, Arrow t1' t2') -> unify' $ [(t1,t1'),(t2,t2')] ++ rest
        (SVar x     , t            ) -> if x `S.member` fv t
                                        then Left $ "Not unifiable: " ++ show s1 ++ " = " ++ show s2 ++ "\n" ++ show rest
                                        else do
                                          res <- unify' $ substSC x t rest
                                          return $ (x,t) : res
        (t          , SVar x       ) -> if x `S.member` fv t
                                        then Left $ "Not unifiable: " ++ show s1 ++ " = " ++ show s2 ++ "\n" ++ show rest
                                        else do
                                          res <- unify' $ substSC x t rest
                                          return $ (x,t) : res
        (_          , _            ) -> Left $ "Not unifiable: " ++ show s1 ++ " = " ++ show s2 ++ "\n" ++ show rest
