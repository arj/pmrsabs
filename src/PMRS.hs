{-# LANGUAGE TypeSynonymInstances,FlexibleInstances #-}
module PMRS where

import Data.List
import qualified Data.Set as S

data Sort a = Base a
            | Arrow (Sort a) (Sort a)

instance Show a => Show (Sort a) where
	show (Base b) = show b
	show (Arrow s1@(Base _) s2) = show s1 ++ " -> " ++ show s2
	show (Arrow s1 s2) = "(" ++ show s1 ++ ") -> " ++ show s2

createSort :: Int -> a -> Sort a
createSort 0 b = Base b
createSort n b = Arrow (Base b) $ createSort (n-1) b

data SortedSymbol a = SS String (Sort a)

instance Show a => Show (SortedSymbol a) where
  show (SS s _) = s

data Head a = Var String
          | Nt (SortedSymbol a)
          | T (SortedSymbol a)

instance Show a => Show (Head a) where
	show (Var x) = x
	show (Nt (SS s _)) = s -- ++ ":" ++ show sort
	show (T  (SS s _))  = s -- ++ ":" ++ show sort

data Term a = App (Head a) [Term a]

instance Show a => Show (Term a) where
	show (App h []) = show h
	show (App h lst) = show h ++ " " ++ unwords (map show lst)

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