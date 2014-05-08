{-# LANGUAGE TypeSynonymInstances,FlexibleInstances #-}
module PMRS (
  PMRSRule(..), PMRS,
  PMRSRules,

  mkPMRS, getTerminals, getNonterminals, getRules, getStartSymbol,
  unmakePMRS,

  listToRules, matchingRules, filterRealPMRule,
  prettyPrintPMRS,
  cleanup,

  getPMVariables,

  step
  ) where

import Aux
import Term
import Sorts
import Data.List
import CommonRS

import Data.MultiMap (MultiMap)
import qualified Data.MultiMap as MM

import Data.Set (Set)
import qualified Data.Set as S

import Data.Map (Map)
import qualified Data.Map as M

import Data.Maybe
import Control.Monad
import Control.Monad.Writer

data PMRSRule = PMRSRule { pmrsRuleF :: Symbol
  , pmrsRuleVars :: [String]
  , pmrsRulePattern :: Maybe Term
  , pmrsRuleBody ::  Term
} deriving (Eq,Ord)

typeOfVariables :: PMRSRule -> RankedAlphabet -> TypeBinding
typeOfVariables (PMRSRule f xs p _) ra = M.fromList alltypes
  where
    srt       = ra M.! f
    alltypes  = xstypes ++ ptypes
    ptypes    = maybe [] typesP p
    typesP p' = zip (S.toList $ fv p') $ repeat o
    types     = init $ sortToList srt
    xstypes   = zip xs types

getPMVariables :: PMRS -> Set String
-- ^ Returns all variables used in pattern matching.
getPMVariables pmrs = S.unions $ map extractPMVars rules
  where
    extractPMVars (PMRSRule _ _ p _) = maybe S.empty fv p
    rules = concat $ MM.elems $ getRules pmrs

type PMRSRules = Rules PMRSRule

instance Show PMRSRule where
  show (PMRSRule f xs p body) = unwords $ filter (not . null) [show f, unwords xs, showMaybe p,"=>",show body]

listToRules :: [PMRSRule] -> PMRSRules
listToRules lst = MM.fromList $ map fPairUp lst
  where
    fPairUp r@(PMRSRule f _ _ _) = (f,r)

-- | Filters the rules that are really pattern matching.
-- A rule with Just x is not really pattern matching.
filterRealPMRule :: PMRSRules -> PMRSRules
filterRealPMRule rules = MM.filter pRealPMRule rules
  where
    pRealPMRule (PMRSRule _ _ (Just (App (Var _) _)) _) = False
    pRealPMRule (PMRSRule _ _  Nothing               _) = False
    pRealPMRule _                                       = True

data PMRS = PMRS RankedAlphabet RankedAlphabet PMRSRules Symbol

getTerminals :: PMRS -> RankedAlphabet
getTerminals (PMRS f _ _ _) = f

getNonterminals :: PMRS -> RankedAlphabet
getNonterminals (PMRS _ f _ _) = f

getRules :: PMRS -> PMRSRules
getRules (PMRS _ _ f _) = f

getStartSymbol :: PMRS -> Symbol
getStartSymbol (PMRS _ _ _ f) = f

unmakePMRS :: PMRS -> (RankedAlphabet, RankedAlphabet, PMRSRules, Symbol)
-- ^ Destructs a PMRS into terminals, nonterminals, rules and start symbol
unmakePMRS (PMRS sigma n r s) = (sigma, n, r, s)

mkPMRS :: Monad m => RankedAlphabet -> RankedAlphabet -> PMRSRules -> Symbol -> m PMRS
mkPMRS t nt r s = do
  let rules = concat $ MM.elems r
  forM_ rules $ \r' -> do
    let bnd = M.unions [t, nt, typeOfVariables r' nt]
    srt <- typeCheck bnd $ pmrsRuleBody r'
    if srt == o
      then return ()
      else fail ("The body of the rule " ++ show r ++ " is not of sort o but of sort " ++ show srt)
  return $ PMRS t nt r s

cleanup :: PMRS -> PMRS
-- | Removes rules if they are not used anywhere.
-- Could be improved by doing a reachability analysis.
-- At the moment two unused nonterminals can keep each
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

prettyPrintRules :: Symbol -> PMRSRules -> Writer String ()
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

-- | One reduction step of a given term using the rules from a PMRS.
-- A step means a substitution is applied on every nonterminal present in t.
step :: PMRS -> Term -> Term
step pmrs t = replaceNt (stepSingle pmrs) t

-- | Given a nonterminal with arguments reduces one step.
-- If the symbol requires pattern matching to be reduced
-- and it is not yet clear which case is applicable, nothing
-- happens.
stepSingle :: PMRS -> Symbol -> [Term] -> Term
stepSingle pmrs nt args = undefined
  where
    rules = matchingRules (getRules pmrs) $ App (Nt nt) args
