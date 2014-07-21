module RSFD
where

import Aux
import Sorts
import Term
import PMRS (PMRS, getRules, PMRSRule(..), PMRSRules, unmakePMRS, filterRealPMRule, pIsPMRule, pIsPseudo)
import qualified PMRS as P
import CommonRS

import Data.List

import Data.Map (Map)
import qualified Data.Map as M

import Data.Set (Set)
import qualified Data.Set as S

import Data.MultiMap (MultiMap)
import qualified Data.MultiMap as MM

import Control.Monad.Writer

import Data.Maybe

import Debug.Trace

data RSFDRule = RSFDRule { rsfdRuleHead :: Symbol
  , rsfdRuleVars :: [String]
  , rsfdBody     :: Term
} deriving (Eq, Ord)

instance Show RSFDRule where
  show (RSFDRule f xs body) = unwords $ filter (not . null) [show f, unwords xs, "=>",show body]

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
typeOfVariables r@(RSFDRule f xs _) ra = 
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
             then trace (show r) Base
             else foldr1 (~>) resttp


mkRSFD :: Monad m => RankedAlphabet -> RankedAlphabet -> Data -> RSFDRules -> Symbol -> m RSFD
mkRSFD sigma n d r s = do
  let rules = concat $ MM.elems r
  forM_ rules $ \r' -> do
    let bnd = M.unions [sigma, n, typeOfVariables r' n]
    srt <- typeCheck bnd $ rsfdBody r'
    if srt == o
      then return ()
      else fail ("The body of the rule " ++ show r ++ " is not of sort o but of sort " ++ show srt)
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
prettyPrintRule (RSFDRule f xs body) = tell $ unwords $ filter (not . null) [show f, unwords xs, "=",show body]

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

extractData :: PMRS -> Data
extractData pmrs = M.fromList $ zip lst [0..]
  where
    rules   = concat $ MM.elems $ getRules pmrs
    lst     = S.toList $ foldl extract S.empty rules
    --
    extract ack (PMRSRule _ _ p _) = maybe ack (checkAndInsert ack) p
    --
    -- We don't accept plain variable patterns as domains, as we do not
    -- pattern match on anything here.
    checkAndInsert ack (App (Var _) []) = ack
    checkAndInsert ack p'               = flip S.insert ack $ replaceVarsBy "_" p'

errStr :: String
errStr = "err"

errSymbol :: Term
errSymbol = terminal errStr

-- | Transforms a given PMRS rule into an RSFD rule if it is a non-pm
-- rule or a pseudo pm rule, i.e. the pattern is a variable, see pIsPMRule.
pmrsRuleToRSDFRule :: PMRSRule -> RSFDRule
pmrsRuleToRSDFRule (PMRSRule f xs Nothing t)                 = RSFDRule f xs t
pmrsRuleToRSDFRule (PMRSRule f xs (Just (App (Var px) _)) t) = RSFDRule f (xs ++ [px]) t
pmrsRuleToRSDFRule _ = error "Pattern matching rules cannot be converted directly."

extractPT :: Data -> PMRSRule -> (Int, Term)
extractPT dd (PMRSRule _ _ (Just p) t) = (dataLookup p dd,t)

-- TODO t -> t' by replacing all
transformRules :: PMRSRules -> Data -> RSFDRules
transformRules rules dd = MM.unions [rsfdNormalRules, rsfdPmRules, rsfdPseudoPmRules]
  where
    -- Extract all groups of pattern matching rules
    -- Now for all pattern matching rules
    keys                     = MM.keys pmRules
    (allPmRules,normalRules) = MM.partition pIsPMRule rules
    (pseudoPmRules,pmRules)  = MM.partition pIsPseudo allPmRules
    --
    rsfdNormalRules          = MM.map pmrsRuleToRSDFRule normalRules
    rsfdPseudoPmRules        = MM.map pmrsRuleToRSDFRule pseudoPmRules
    rsfdPmRules              = mkRSFDRules $ map combineRulesPerKey keys
    --
    -- | For each nonterminal symbol (key) the corresponding pattern
    -- matching rule is extracted and a RSFD rule is created that has
    -- a case expression with the corresponding terms at the corresponding
    -- positions, and err if the pattern is not checked for in this rule
    combineRulesPerKey :: Symbol -> RSFDRule
    combineRulesPerKey key = RSFDRule f (xs ++ ["_p"]) body
      where
        body = Case "_p" ts'
        --
        ts' = map placeTi [0..(M.size dd)-1]
        --
        placeTi :: Int -> Term
        -- ^ Looks up the correct term for the pattern or returns err symbol.
        placeTi idx = fromMaybe errSymbol $ lookup idx pIndexTs -- TODO Type conversion from /o/ to /d/ is still necessary!
        --
        headRule = head $ MM.lookup key pmRules
        f        = pmrsRuleF headRule
        xs       = pmrsRuleVars headRule
        --
        pIndexTs          = map (extractPT dd) $ MM.lookup key pmRules

dataLookup :: Term -> Data -> Int
dataLookup p dd = fromJust $ M.lookup p' dd
  where
    p' = replaceVarsBy "_" p

-- TODO Missing: Change type of pattern-matching
-- nonterminals from F: s -> ... -> o -> o to F: s -> ... -> d -> o!
fromWPMRS :: Monad m => PMRS -> m RSFD
fromWPMRS pmrs = mkRSFD sg' nt' dd rs' st
  where
    (sg,nt,rs,st) = unmakePMRS pmrs
    --
    sg' = M.insert errStr o sg
    nt' = M.mapWithKey adjustSorts $ nt
    dd  = extractData pmrs
    rs' = transformRules rs dd
    pmF = MM.keys $ filterRealPMRule rs
    --
    adjustSorts f srt =
      if f `elem` pmF
        then replaceLastArg Data srt
        else srt -- No changes