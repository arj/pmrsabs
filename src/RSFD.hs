module RSFD
where

import Aux
import Sorts
import Term
import PMRS

import Data.List

import Data.Map (Map)
import qualified Data.Map as M

import Data.Set (Set)
import qualified Data.Set as S

import Data.MultiMap (MultiMap)
import qualified Data.MultiMap as MM

import Control.Monad.Writer

data RSFDRule a = RSFDRule { rsfdRuleHead :: SortedSymbol a
  , rsfdRuleVars :: [String]
  , rsfdBody     :: Term a
} deriving (Eq, Ord)

instance Show a => Show (RSFDRule a) where
  show (RSFDRule f xs body) = unwords $ filter (not . null) [show f, unwords xs, "=>",show body]

type RSFDRules a = MultiMap (SortedSymbol a) (RSFDRule a)

type DataDomain = Map String Int

type RankedAlphabet a = Set (SortedSymbol a)

data RSFD a = RSFD { rsfdTerminals :: RankedAlphabet a
  , rsfdNonterminals :: RankedAlphabet a
  , rsfdData :: DataDomain
  , rsfdRules :: RSFDRules a
  , rsfdStart :: SortedSymbol a
}

instance Show a => Show (RSFD a) where
	show (RSFD t nt d r s) = "<" ++ (intercalate ",\n" [showSet t,showSet nt,show d,show $ concat $ MM.elems r,show s]) ++ ">"

prettyPrintRSFD :: (Show a, Ord a) => RSFD a -> Writer String ()
prettyPrintRSFD (RSFD _ _ _ r s) = do
  tell "%BEGING"
  tell "\n"
  prettyPrintRules s r
  tell "%ENDG"
  tell "\n"

prettyPrintRule :: Show a => RSFDRule a => Writer String ()
prettyPrintRule (RSFDRule f xs body) = tell $ unwords $ filter (not . null) [show f, unwords xs, "=",show body]

prettyPrintRules :: (Show a, Ord a) => SortedSymbol a -> RSFDRules a -> Writer String ()
prettyPrintRules s r = do
  -- Ensure that rules with the start symbol are at the beginning of the list.
  let (startRules,otherRules) = partition (\rule -> s == rsfdRuleHead rule) $ concat $ MM.elems r
  let ruleList = startRules ++ otherRules
  forM_ ruleList $ \currentRule -> do
    prettyPrintRule currentRule
    tell ".\n"
  return ()

instance (Show a, Ord a) => PrettyPrint (RSFD a) where
  prettyPrint rsfd = execWriter $ prettyPrintRSFD rsfd

-- Steps:
-- (0. Flatten pattern matching?)
--  1. Create finite data domain D from Sigma
--     We only need the terminal symbols that are actually
--     used in the pattern matching part of the symbols.
--  2. Transform all pattern matching rules to normal
--     rules with case statement. And combine
--     several rules into one, e.g.
--     Filter p nil -> t1 and Filter p (cons _ _) -> t2
--     must be combined to Filter p d -> case(d,t1,t2)
--  3. d must be of type d, thus we have to ensure that
--     the calls to filter only use elements of d.
--     Enforce this by an analysis and transformation.
--     We probably only need depth 1 as case cannot look deeper.
--  4. CPS transformation if necessary? We cannot return values
--     of type d!

extractDataDomain :: Ord a => PMRS a -> DataDomain
extractDataDomain (PMRS sigma _ _ _) = M.fromList $ zip (S.toList $ S.map f sigma) [0..]
  where
	f (SortedSymbol s _) = s

transformRules :: Rules a -> DataDomain -> RSFDRules a
transformRules rules dd = undefined

fromWPMRS :: PMRS () -> RSFD ()
fromWPMRS = undefined