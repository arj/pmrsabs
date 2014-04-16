{-# LANGUAGE TypeSynonymInstances,FlexibleInstances #-}
module PMRS (
  Rule(..), PMRS(..)
  ) where

import Term
import Sorts
import Data.List
import qualified Data.Set as S

data Rule a = Rule { ruleF :: SortedSymbol a
  , ruleVars :: [String]
  , rulePattern :: Maybe (Term a)
  , ruleBody ::  Term a
}

showMaybe :: Show a => Maybe a -> String
showMaybe Nothing = ""
showMaybe (Just p) = show p

instance Show a => Show (Rule a) where
  show (Rule f xs p body) = unwords $ filter (not . null) [show f, unwords xs, showMaybe p,"=>",show body]

data PMRS a = PMRS { rankedAlphabet :: S.Set (String, Int)
  , nonterminals :: S.Set (SortedSymbol a)
  , terminals :: S.Set (SortedSymbol a)
  , rules :: S.Set (Rule a)
  , start :: SortedSymbol a
}

showSet :: Show a => S.Set a -> [Char]
showSet s = if S.null s then "[]" else show s

instance Show a => Show (PMRS a) where
  show (PMRS ra nt t r s) = "<" ++ (intercalate "," [showSet ra,showSet nt,showSet t,showSet r,show s]) ++ ">"