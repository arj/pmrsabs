module RSFD
where

import Data.List
import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.MultiMap as MM
import Control.Monad (forM_, when)
import Control.Monad.Writer (Writer, tell, execWriter)

import Aux
import Sorts
import Term
import CommonRS

data RSFDRule = RSFDRule { rsfdRuleHead :: Symbol
  , rsfdRuleVars :: [String]
  , rsfdBody     :: Term
} deriving (Eq, Ord)

instance Show RSFDRule where
  show (RSFDRule f xs body) = unwords $ filter (not . null) [f, unwords xs, "=>",show body]

type RSFDRules = Rules RSFDRule

type Data = Map Term Int

data RSFD = RSFD { rsfdTerminals :: RankedAlphabet
  , rsfdNonterminals :: RankedAlphabet
  , rsfdData         :: Data
  , rsfdRules        :: RSFDRules
  , rsfdStart        :: Symbol
}

mkRSFDRules :: [RSFDRule] -> RSFDRules
mkRSFDRules lst = MM.fromList $ map fPairUp lst
  where
    fPairUp r = (rsfdRuleHead r,r)

-- | Extract types of the variables for a rule.
-- Be careful with eta abstraction!
typeOfVariables :: RSFDRule -> RankedAlphabet -> TypeBinding
typeOfVariables (RSFDRule _ [] _) _  = M.empty
typeOfVariables (RSFDRule f xs _) ra = 
  if length types == length xs + 1
    then M.fromList $ zip xs types -- omitting return type!
    else M.fromList $ (lastx,lasttp) : inittp
  where
    srt    = ra M.! f
    types  = sortToList srt
    --
    initxs = init xs
    lastx  = last xs
    inittp = zip initxs types
    resttp = drop (length initxs) types
    lasttp = if null resttp
             then Base
             else foldr1 (~>) resttp


mkRSFD :: Monad m => RankedAlphabet -> RankedAlphabet -> Data -> RSFDRules -> Symbol -> m RSFD
mkRSFD sigma n d r s = do
  let rules = concat $ MM.elems r
  forM_ rules $ \r' -> do
    let bnd = M.unions [sigma, n, typeOfVariables r' n]
    srt <- typeCheck bnd $ rsfdBody r'
    if srt == o
      then return ()
      else fail ("The body of the rule " ++ show r' ++ " is not of sort o but of sort " ++ show srt)
  when (not $ MM.member r s) $ fail ("No rule for the start symbol: " ++ show s)
  return $ RSFD sigma n d r s

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
prettyPrintRule (RSFDRule f xs body) = tell $ unwords $ filter (not . null) [f, unwords xs, "=",show body]

prettyPrintRules :: Symbol -> RSFDRules -> Writer String ()
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
