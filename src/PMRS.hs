{-# LANGUAGE TypeSynonymInstances,FlexibleInstances #-}
module PMRS (
  PMRSRule(..), PMRS(..),
  PMRSRules,

  listToRules, matchingRules,
  prettyPrintPMRS,
  cleanup
  ) where

import Aux
import Term
import Sorts
import Data.List

import Data.MultiMap (MultiMap)
import qualified Data.MultiMap as MM

import Data.Set (Set)
import qualified Data.Set as S

import Control.Monad.Writer

data PMRSRule = PMRSRule { pmrsRuleF :: SortedSymbol
  , pmrsRuleVars :: [String]
  , pmrsRulePattern :: Maybe Term
  , pmrsRuleBody ::  Term
} deriving (Eq,Ord)

matchingRules :: PMRSRules -> Term -> [PMRSRule]
matchingRules rs (App (Nt f) _) = MM.lookup f rs
matchingRules _  (App _ _) = []

type PMRSRules = MultiMap SortedSymbol PMRSRule

instance Show PMRSRule where
  show (PMRSRule f xs p body) = unwords $ filter (not . null) [show f, unwords xs, showMaybe p,"=>",show body]

listToRules :: [PMRSRule] -> PMRSRules
listToRules lst = MM.fromList $ map fPairUp lst
  where
    fPairUp r@(PMRSRule f _ _ _) = (f,r)

data PMRS = PMRS { pmrsTerminals :: Set SortedSymbol
  , pmrsNonterminals :: Set SortedSymbol
  , pmrsRules :: PMRSRules
  , pmrsStart :: SortedSymbol
}

cleanup :: PMRS -> PMRS
-- | Removes rules if they are not used anywhere.
-- Could be improved by doing a reachability analysis.
-- At the moment two unused nonterminals an keep each
-- other alive by referencing themselves.
cleanup (PMRS sigma n r s) = PMRS sigma n r' s
  where
    nts = S.insert s $ S.unions $ map (getN . pmrsRuleBody) $ concat $ MM.elems r
    r'  = MM.filter (\(PMRSRule f _ _ _) -> S.member f nts) r

instance Show PMRS where
  show (PMRS t nt r s) = "<" ++ (intercalate ",\n" [showSet t,showSet nt,show $ concat $ MM.elems r,show s]) ++ ">"

prettyPrintPMRS :: PMRS -> Writer String ()
prettyPrintPMRS (PMRS _ _ r s) = do
  tell "%BEGING"
  tell "\n"
  prettyPrintRules s r
  tell "%ENDG"
  tell "\n"

prettyPrintRule :: PMRSRule => Writer String ()
prettyPrintRule (PMRSRule f xs p body) = tell $ unwords $ filter (not . null) [show f, unwords xs, showMaybe p,"=",show body]

prettyPrintRules :: SortedSymbol -> PMRSRules -> Writer String ()
prettyPrintRules s r = do
  -- Ensure that rules with the start symbol are at the beginning of the list.
  let (startRules,otherRules) = partition (\rule -> s == pmrsRuleF rule) $ concat $ MM.elems r
  let ruleList = startRules ++ otherRules
  forM_ ruleList $ \currentRule -> do
    prettyPrintRule currentRule
    tell ".\n"
  return ()

instance PrettyPrint PMRS where
  prettyPrint pmrs = execWriter $ prettyPrintPMRS pmrs