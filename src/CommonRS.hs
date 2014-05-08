module CommonRS where

import Sorts
import Term

import Data.MultiMap (MultiMap)
import qualified Data.MultiMap as MM

type Rules a = MultiMap Symbol a

matchingRules :: Rules a -> Term -> [a]
matchingRules rs (App (Nt f) _) = MM.lookup f rs
matchingRules _  (App _ _) = []