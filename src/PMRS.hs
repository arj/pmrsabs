{-# LANGUAGE TypeSynonymInstances,FlexibleInstances #-}
module PMRS (
  Rule(..), PMRS(..),

  Rules,

  listToRules
  ) where

import Term
import Sorts
import Data.List

import Data.MultiMap (MultiMap)
import qualified Data.MultiMap as MM

import Data.Set (Set)
import qualified Data.Set as S

data Rule a = Rule { ruleF :: SortedSymbol a
  , ruleVars :: [String]
  , rulePattern :: Maybe (Term a)
  , ruleBody ::  Term a
} deriving (Eq,Ord)

showMaybe :: Show a => Maybe a -> String
showMaybe Nothing = ""
showMaybe (Just p) = show p

type Rules a = MultiMap (SortedSymbol a) (Rule a)

instance Show a => Show (Rule a) where
  show (Rule f xs p body) = unwords $ filter (not . null) [show f, unwords xs, showMaybe p,"=>",show body]

listToRules :: Ord a => [Rule a] -> Rules a
listToRules lst = MM.fromList $ map f lst
  where
    f r@(Rule f _ _ _) = (f,r)

data PMRS a = PMRS { terminals :: Set (SortedSymbol a)
  , nonterminals :: Set (SortedSymbol a)
  , rules :: Rules a
  , start :: SortedSymbol a
}

showSet :: Show a => Set a -> [Char]
showSet s = if S.null s then "[]" else show s

instance Show a => Show (PMRS a) where
  show (PMRS t nt r s) = "<" ++ (intercalate "," [showSet t,showSet nt,show $ concat $ MM.elems r,show s]) ++ ">"