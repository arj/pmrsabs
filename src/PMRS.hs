{-# LANGUAGE TypeSynonymInstances,FlexibleInstances #-}
module PMRS (
  Rule(..), PMRS(..),

  Rules,

  listToRules, matchingRules,
  prettyPrintPMRS, prettyPrintRule, prettyPrintRules,
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

data Rule a = Rule { ruleF :: SortedSymbol a
  , ruleVars :: [String]
  , rulePattern :: Maybe (Term a)
  , ruleBody ::  Term a
} deriving (Eq,Ord)

matchingRules :: Ord a => Rules a -> Term a -> [Rule a]
matchingRules rs (App (Nt f) _) = MM.lookup f rs
matchingRules _  (App _ _) = []

showMaybe :: Show a => Maybe a -> String
showMaybe Nothing = ""
showMaybe (Just p) = show p

type Rules a = MultiMap (SortedSymbol a) (Rule a)

instance Show a => Show (Rule a) where
  show (Rule f xs p body) = unwords $ filter (not . null) [show f, unwords xs, showMaybe p,"=>",show body]

listToRules :: Ord a => [Rule a] -> Rules a
listToRules lst = MM.fromList $ map fPairUp lst
  where
    fPairUp r@(Rule f _ _ _) = (f,r)

data PMRS a = PMRS { terminals :: Set (SortedSymbol a)
  , nonterminals :: Set (SortedSymbol a)
  , rules :: Rules a
  , start :: SortedSymbol a
}

instance Show a => Show (PMRS a) where
  show (PMRS t nt r s) = "<" ++ (intercalate ",\n" [showSet t,showSet nt,show $ concat $ MM.elems r,show s]) ++ ">"

prettyPrintPMRS :: (Show a, Ord a) => PMRS a -> Writer String ()
prettyPrintPMRS (PMRS _ _ r s) = do
  tell "%BEGING"
  tell "\n"
  prettyPrintRules s r
  tell "%ENDG"
  tell "\n"

prettyPrintRule :: Show a => Rule a => Writer String ()
prettyPrintRule (Rule f xs p body) = tell $ unwords $ filter (not . null) [show f, unwords xs, showMaybe p,"=",show body]

prettyPrintRules :: (Show a, Ord a) => SortedSymbol a -> Rules a -> Writer String ()
prettyPrintRules s r = do
  -- Ensure that rules with the start symbol are at the beginning of the list.
  let (startRules,otherRules) = partition (\rule -> s == ruleF rule) $ concat $ MM.elems r
  let ruleList = startRules ++ otherRules
  forM_ ruleList $ \currentRule -> do
    prettyPrintRule currentRule
    tell ".\n"
  return ()

cleanup :: Ord a => PMRS a -> PMRS a
-- | Removes rules if they are not used anywhere.
-- Could be improved by doing a reachability analysis.
-- At the moment two unused nonterminals an keep each
-- other alive by referencing themselves.
cleanup (PMRS sigma n r s) = PMRS sigma n r' s
  where
    nts = S.insert s $ S.unions $ map (getN . ruleBody) $ concat $ MM.elems r
    r'  = MM.filter (\(Rule f _ _ _) -> S.member f nts) r

instance (Show a, Ord a) => PrettyPrint (PMRS a) where
  prettyPrint pmrs = execWriter $ prettyPrintPMRS pmrs