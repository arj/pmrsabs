module Aux
where

import Data.Set (Set)
import qualified Data.Set as S

showSet :: Show a => Set a -> [Char]
showSet s = if S.null s then "[]" else show s

showMaybe :: Show a => Maybe a -> String
showMaybe Nothing = ""
showMaybe (Just p) = show p

class PrettyPrint a where
	prettyPrint :: a -> String