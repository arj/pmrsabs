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

data RSFDRule = RSFDRule { rsfdRuleHead :: SortedSymbol
  , rsfdRuleVars :: [String]
  , rsfdBody     :: Term
} deriving (Eq, Ord)

instance Show RSFDRule where
  show (RSFDRule f xs body) = unwords $ filter (not . null) [show f, unwords xs, "=>",show body]

type RSFDRules = MultiMap SortedSymbol RSFDRule

type DataDomain = Map String Int

data RSFD = RSFD { rsfdTerminals :: RankedAlphabet
  , rsfdNonterminals :: RankedAlphabet
  , rsfdData :: DataDomain
  , rsfdRules :: RSFDRules
  , rsfdStart :: SortedSymbol
}

instance Show RSFD where
  show (RSFD t nt d r s) =
    let t'  = rankedAlphabetToSet t
        nt' = rankedAlphabetToSet nt
    in "<" ++ (intercalate ",\n" [showSet t',showSet nt',show d,show $ concat $ MM.elems r,show s]) ++ ">"

prettyPrintRSFD :: RSFD -> Writer String ()
prettyPrintRSFD (RSFD _ _ _ r s) = do
  tell "%BEGING"
  tell "\n"
  prettyPrintRules s r
  tell "%ENDG"
  tell "\n"

prettyPrintRule :: RSFDRule => Writer String ()
prettyPrintRule (RSFDRule f xs body) = tell $ unwords $ filter (not . null) [show f, unwords xs, "=",show body]

prettyPrintRules :: SortedSymbol -> RSFDRules -> Writer String ()
prettyPrintRules s r = do
  -- Ensure that rules with the start symbol are at the beginning of the list.
  let (startRules,otherRules) = partition ((s ==) . rsfdRuleHead) $ concat $ MM.elems r
  let ruleList = startRules ++ otherRules
  forM_ ruleList $ \currentRule -> do
    prettyPrintRule currentRule
    tell ".\n"
  return ()

instance PrettyPrint RSFD where
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

extractDataDomain :: PMRS -> DataDomain
extractDataDomain pmrs = M.fromList $ zip lst [0..]
  where
    fn (SortedSymbol s _) = s
    sigma = S.empty
    lst   = S.toList $ S.map fn sigma

transformRules :: PMRSRules -> DataDomain -> RSFDRules
transformRules rules dd = undefined
  where
    keys = MM.keys rules


fromWPMRS :: PMRS -> RSFD
fromWPMRS = undefined