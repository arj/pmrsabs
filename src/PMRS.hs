{-# LANGUAGE TypeSynonymInstances,FlexibleInstances #-}
module PMRS (
  PMRSRule(..), PMRS,
  PMRSRules,

  mkPMRS, getTerminals, getNonterminals, getRules, getStartSymbol,

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

import Data.Map (Map)
import qualified Data.Map as M

import Data.Maybe
import Control.Monad
import Control.Monad.Writer

data PMRSRule = PMRSRule { pmrsRuleF :: SortedSymbol
  , pmrsRuleVars :: [String]
  , pmrsRulePattern :: Maybe Term
  , pmrsRuleBody ::  Term
} deriving (Eq,Ord)

matchingRules :: PMRSRules -> Term -> [PMRSRule]
matchingRules rs (App (Nt f) _) = MM.lookup f rs
matchingRules _  (App _ _) = []

variableTypes :: PMRSRule -> TypeBinding
variableTypes (PMRSRule (SortedSymbol f srt) xs p _) = M.fromList alltypes
  where
    alltypes  = xstypes ++ ptypes
    ptypes    = maybe [] typesP p
    typesP p' = zip (S.toList $ fv p') $ repeat o
    types     = init $ sortToList srt
    xstypes   = zip xs types


type PMRSRules = MultiMap SortedSymbol PMRSRule

instance Show PMRSRule where
  show (PMRSRule f xs p body) = unwords $ filter (not . null) [show f, unwords xs, showMaybe p,"=>",show body]

listToRules :: [PMRSRule] -> PMRSRules
listToRules lst = MM.fromList $ map fPairUp lst
  where
    fPairUp r@(PMRSRule f _ _ _) = (f,r)

data PMRS = PMRS RankedAlphabet RankedAlphabet PMRSRules SortedSymbol

getTerminals :: PMRS -> RankedAlphabet
getTerminals (PMRS f _ _ _) = f

getNonterminals :: PMRS -> RankedAlphabet
getNonterminals (PMRS _ f _ _) = f

getRules :: PMRS -> PMRSRules
getRules (PMRS _ _ f _) = f

getStartSymbol :: PMRS -> SortedSymbol
getStartSymbol (PMRS _ _ _ f) = f

mkPMRS :: Monad m => RankedAlphabet -> RankedAlphabet -> PMRSRules -> SortedSymbol -> m PMRS
mkPMRS t nt r s = do
  let rules = concat $ MM.elems r
  forM_ rules $ \r -> do
    let bnd = variableTypes r
    srt <- typeCheck bnd $ pmrsRuleBody r
    if srt == o
      then return ()
      else fail ("The body of the rule " ++ show r ++ " is not of sort o but of sort " ++ show srt)
  return $ PMRS t nt r s

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
  show (PMRS t nt r s) =
    let t'  = rankedAlphabetToSet t
        nt' = rankedAlphabetToSet nt
    in "<" ++ (intercalate ",\n" [showSet t',showSet nt',show $ concat $ MM.elems r,show s]) ++ ">"

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