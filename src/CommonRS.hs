module CommonRS where

import Sorts
import Term

import Data.MultiMap (MultiMap)
import qualified Data.MultiMap as MM

type Rules a = MultiMap Symbol a

matchingRules :: Rules a -> Symbol -> [a]
matchingRules = flip MM.lookup

matchingRulesByTerm :: Rules a -> Term -> [a]
matchingRulesByTerm rs (App (Nt f) _) = MM.lookup f rs
matchingRulesByTerm _  (App _ _) = []

