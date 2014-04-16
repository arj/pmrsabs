module Abstraction (
	wPMRS, sPMRS,
	Binding,
	substHead
	) where

import PMRS
import Term

import Data.MultiMap (MultiMap)
import qualified Data.MultiMap as MM

import Data.Set (Set)
import qualified Data.Set as S

-- | Head substitute function.
hs :: Ord a => Binding a -> Head a -> Set String -> Set (Term a)
hs _ k@(Nt _) _ = S.singleton $ headToTerm k
hs _ k@(T _) _  = S.singleton $ headToTerm k
hs s (Var x) xs =
	if S.member x xs then
		S.empty
	else
		let xitm = MM.lookup x s in
		let f (App xi tm) =
			let deltas = hs s xi (S.insert x xs) in
			S.map (\d -> app d tm) deltas
		in
		S.unions $ map f xitm

type Binding a = MultiMap String (Term a)

-- |Given a term and a set of bindings S, substHead replaces the
--  head of the term - if it is a variable - with all possible
--  substitutions from S, recursively.
substHead :: Ord a => Binding a -> Term a -> Set (Term a)
substHead s (App xi@(Var _) ts) = S.map (\d -> app d ts) deltas
	where
		deltas = hs s xi $ S.empty
substHead _ t                   = S.singleton t

wPMRS :: PMRS a -> PMRS a
wPMRS = undefined

sPMRS :: PMRS a -> PMRS a
sPMRS = undefined