module Aux
where

import Data.Set (Set)
import qualified Data.Set as S
import Debug.Trace (traceShow)

traceIt :: Show a => a -> a
traceIt a = traceShow (show a) a

showSet :: Show a => Set a -> [Char]
showSet s = if S.null s then "[]" else show s

showMaybe :: Show a => Maybe a -> String
showMaybe Nothing = ""
showMaybe (Just p) = show p

showMaybePrefix :: Show a => String -> Maybe a -> String
showMaybePrefix _ Nothing = ""
showMaybePrefix s (Just p) = s ++ show p

class PrettyPrint a where
	prettyPrint :: a -> String

mapi :: (Int -> b -> c) -> [b] -> [c]
mapi f = zipWith f [0..]

allTheSame :: (Eq a) => [a] -> Bool
-- ^ Checks if the members of a list are all the same. /allTheSame [] == True/.
allTheSame [] = True
allTheSame xs = and $ map (== head xs) (tail xs)

filterMap :: (a -> Maybe b) -> [a] -> [b]
filterMap _ []     = []
filterMap f (x:xs) = case f x of
	  Just x' -> x' : filterMap f xs
	  Nothing -> filterMap f xs

-- | Given a list returns a unique list
uniqueList :: (Ord a) => [a] -> [a]
uniqueList = S.toList . S.fromList

-- | Creates a fresh variable name that is not
-- in xs and has a prefix f.
freshVar :: [String] -> String -> String
freshVar xs f
  | f `elem` xs = freshVar xs (f ++ "_")
  | otherwise   = f

lookupList :: [a] -> Int -> Maybe a
lookupList _  n | n<0 = Nothing
lookupList [] _ = Nothing
lookupList (x:_) 0 = return x
lookupList (_:xs) n = lookupList xs (n-1)