module Abstraction (
  wPMRS, sPMRS,
  Binding,
  substHead,
  rmatch
  ) where

import Prelude hiding (pi)

import PMRS
import Term

import Data.MultiMap (MultiMap)
import qualified Data.MultiMap as MM

import Data.Set (Set)
import qualified Data.Set as S

import Debug.Trace

traceRet :: Show a => String -> a -> a
traceRet str a = let b = a in trace (str ++ " return " ++ show b) b

-- | Head substitute function.
hs :: Ord a => Binding a -> Head a -> Set String -> Set (Term a)
hs _ k@(Nt _) _ = S.singleton $ headToTerm k
hs _ k@(T _) _  = S.singleton $ headToTerm k
hs s (Var x) xs =
  if S.member x xs then
    S.empty
  else
    S.unions $ map f xitm
  where
    xitm = MM.lookup x s
    f (App xi tm) =
        let deltas = hs s xi (S.insert x xs) in
        S.map (\d -> app d tm) deltas


type Binding a = MultiMap String (Term a)

-- |Given a term and a set of bindings S, substHead replaces the
--  head of the term - if it is a variable - with all possible
--  substitutions from S, recursively.
substHead :: Ord a => Binding a -> Term a -> Set (Term a)
substHead s (App xi@(Var _) ts) = S.map (\d -> app d ts) deltas
  where
    deltas = hs s xi $ S.empty
substHead _ t                   = S.singleton t

toBinding :: Set (Term a, Term a) -> Binding a
toBinding s = MM.fromList $ S.foldr f [] s
  where
    f ((App (Var x) []),p) ack = (x,p) : ack -- TODO with [] or _ ?
    f _ ack = ack

rmatch :: (Show a, Ord a) => Rules a -> Term a -> Term a -> Set (Term a, Term a) -> Binding a
rmatch r u1 p1 bnd
  | S.member (u1,p1) bnd  = trace (show (u1,p1) ++ " is a member of " ++ show bnd) $ MM.empty
  | otherwise = traceRet ("Calling rmatch' " ++ show u1 ++ " " ++ show p1) $ rmatch' u1 p1
  where
    rmatch' u (App (Var x) _) = MM.fromList [(x,u)]
    rmatch' u@(App (T a2) ts) p@(App (T a1) ps) =
      if a1 == a2 then
        let bnd' = S.insert (u,p) bnd in
        MM.unions $ map (\(ti,pi) -> rmatch r ti pi bnd') $ zip ts ps
      else
        MM.empty
    rmatch' u@(App (Var _) _) p = MM.unions $ map (\t -> rmatch r t p bnd') ts
      where
        vbnd = toBinding bnd
        ts = S.toList $ substHead vbnd u
        bnd' = S.insert (u,p) bnd
    rmatch' u@(App (Nt f) ts) p =
      let nonemptyRules = filter nonempty rulesForf in
      MM.unions $ map (\(Rule _ _ _ t) -> rmatch r t p bnd) $ nonemptyRules
      where
        rulesForf = MM.lookup f r
        bnd' = S.insert (u,p) bnd
        v = last ts
        --
        nonempty (Rule _ _ (Just q) _) = not $ MM.null $ rmatch r v q bnd'
        nonempty (Rule _ xs Nothing  _)
          | null xs   = True
          | otherwise =
            let q = var $ last xs in
            not $ MM.null $ rmatch r v q bnd'

wPMRS :: PMRS a -> PMRS a
wPMRS = undefined

sPMRS :: PMRS a -> PMRS a
sPMRS = undefined