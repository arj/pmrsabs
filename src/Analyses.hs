module Analyses where

import PMRS
import Term
import Sorts

import Data.Set (Set)
import qualified Data.Set as S

import Text.Printf

data Constraint = CTrue
data Reachable = R Symbol Constraint Symbol

instance Show Constraint where
	show CTrue = "true"

instance Show Reachable where
	show (R f c s) = printf "(%s,%s,%s)"  f (show c) s

-- | Calculates the set of symbols
-- That are reachable as head symbols for the
-- PMRS beginning with the start term.
reachability :: PMRS -> Term -> Set Symbol
reachability prms start = undefined

reachRule :: PMRSRule -> Set Reachable
reachRule (PMRSRule f xs Nothing (App (T s ) ts)) = S.singleton $ R f CTrue s
reachRule (PMRSRule f xs Nothing (App (Nt s) ts)) = S.singleton $ R f CTrue s
reachRule (PMRSRule f xs Nothing (App (Nt s) ts)) = S.singleton $ R f CTrue s

--reachTerm ()