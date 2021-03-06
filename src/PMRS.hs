{-# LANGUAGE TypeSynonymInstances,FlexibleInstances #-}
--module PMRS
  
--  (PMRSRule(..), PMRS,
--  PMRSRules,

--  mkPMRS, getTerminals, getNonterminals, getRules, getStartSymbol,
--  unmakePMRS,

--  listToRules, filterRealPMRule,
--  prettyPrintPMRS,
--  cleanup,

--  getPMVariables,
--  pIsPseudo,
--  pIsPMRule,

--  step, nSteps, stepSingle,
--  reduce)
module PMRS
where

import qualified Data.MultiMap as MM
import Data.Set (Set)
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Maybe (isJust)
import Control.Arrow (first)
import Control.Monad (when, forM_)
import Control.Monad.Writer (Writer, tell, execWriter)
import Control.Exception (assert)

import HORS (HORS(..), HORSRule(..))
import Aux
import Term
import Sorts
import Data.List
import CommonRS

data PMRSRule = PMRSRule { pmrsRuleF :: Symbol
  , pmrsRuleVars :: [String]
  , pmrsRulePattern :: Maybe Term
  , pmrsRuleBody ::  Term
} deriving (Eq,Ord)

typeOfVariables :: PMRSRule -> RankedAlphabet -> TypeBinding
typeOfVariables (PMRSRule f xs p _) ra = M.fromList alltypes
  where
    srt       = ra M.! f
    alltypes  = xstypes ++ ptypes
    ptypes    = maybe [] typesP p
    typesP p' = zip (S.toList $ fv p') $ repeat o
    types     = init $ sortToList srt
    xstypes   = zip xs types

-- | Returns all variables used in pattern matching.
getPMVariables :: PMRS -> Set String
getPMVariables pmrs = S.unions $ map extractPMVars rules
  where
    extractPMVars (PMRSRule _ _ p _) = maybe S.empty fv p
    rules = concat $ MM.elems $ getRules pmrs

type PMRSRules = Rules PMRSRule

instance Show PMRSRule where
  show (PMRSRule f xs p body) = unwords $ filter (not . null) [show f, unwords xs, showMaybePrefix "|" p,"=>",show body]

listToRules :: [PMRSRule] -> PMRSRules
listToRules lst = MM.fromList $ map fPairUp lst
  where
    fPairUp r@(PMRSRule f _ _ _) = (f,r)

argCount :: PMRSRule -> Int
argCount (PMRSRule _ xs Nothing _)  = length xs
argCount (PMRSRule _ xs (Just _) _) = 1 + length xs

-- | Filters the rules that are really pattern matching.
-- A rule with Just x is not really pattern matching.
filterRealPMRule :: PMRSRules -> PMRSRules
filterRealPMRule rules = MM.filter pRealPMRule rules
  where
    pRealPMRule (PMRSRule _ _ (Just (App (Var _) _)) _) = False
    pRealPMRule (PMRSRule _ _  Nothing               _) = False
    pRealPMRule _                                       = True

-- | Checks if the nonterminal is a pattern
-- matching nonterminal in its last argument.
pIsPMSymbol :: PMRS -> Symbol -> Bool
pIsPMSymbol pmrs f = pIsPMRule rule
  where
    rule = head $ (getRules pmrs) MM.! f


-- | Checks if the PMRS rule is a pm rule, including pseudo pm.
pIsPMRule :: PMRSRule -> Bool
pIsPMRule (PMRSRule _ _ p _) = isJust p

-- | Checks if the PMRS rule is a pseudo rule, i.e. the pattern is a variable.
pIsPseudo :: PMRSRule -> Bool
pIsPseudo (PMRSRule _ _ (Just (App (Var _) _)) _) = True
pIsPseudo (PMRSRule _ _ (Just _              ) _) = False
pIsPseudo (PMRSRule _ _ Nothing                _) = False

-- | Checks whether the rule is a valid wPMRS rule.
pIsWPMRSRule :: PMRSRule -> Bool
pIsWPMRSRule (PMRSRule _ _ (Just p) t) = S.null $ S.intersection (fv p) (fv t)
pIsWPMRSRule (PMRSRule _ _ Nothing  _) = True

data PMRS = PMRS RankedAlphabet RankedAlphabet PMRSRules Symbol

getTerminals :: PMRS -> RankedAlphabet
getTerminals (PMRS f _ _ _) = f

getNonterminals :: PMRS -> RankedAlphabet
getNonterminals (PMRS _ f _ _) = f

getRules :: PMRS -> PMRSRules
getRules (PMRS _ _ f _) = f

getStartSymbol :: PMRS -> Symbol
getStartSymbol (PMRS _ _ _ f) = f

unmakePMRS :: PMRS -> (RankedAlphabet, RankedAlphabet, PMRSRules, Symbol)
-- ^ Destructs a PMRS into terminals, nonterminals, rules and start symbol
unmakePMRS (PMRS sigma n r s) = (sigma, n, r, s)

mkWPMRS :: Monad m => RankedAlphabet -> RankedAlphabet -> PMRSRules -> Symbol -> m PMRS
mkWPMRS t nt r s = do
  let s_srt = nt M.! s
  when (s_srt /= o) $ fail ("Start symbol " ++ show s ++ " has sort " ++ show s_srt ++ " but should have o")
  mkPMRS t nt r s

-- | Checks whether the given PMRS is a wPMRS, i.e.,
-- it does not use the variables defined in the patterns
-- on the RHSs.
isWPMRS :: PMRS -> Bool
isWPMRS (PMRS _ _ r s) = sortOk && (all pIsWPMRSRule $ concat $ MM.elems r)
  where
    sortOk = length xs == 0
    PMRSRule _ xs _ _ = head $ matchingRules r s

mkPMRS :: Monad m => RankedAlphabet -> RankedAlphabet -> PMRSRules -> Symbol -> m PMRS
mkPMRS t nt r s = do -- TODO Check if rule for start symbol have arity 0
  let rules = concat $ MM.elems r
  forM_ rules $ \r' -> do
    let bnd = M.unions [t, nt, typeOfVariables r' nt]
    srt <- typeCheck bnd $ pmrsRuleBody r'
    when (pIsPseudo r') $ fail ("Pseudo rules are not allowed " ++ show r')
    if srt == o
      then return ()
      else fail ("The body of the rule " ++ show r ++ " is not of sort o but of sort " ++ show srt)
  return $ PMRS t nt r s

addHORS :: Monad m => PMRS -> HORS -> m PMRS
addHORS (PMRS pt pnt prs ps) (HORS ht hnt hrs _) = mkPMRS t nt rs' ps
  where
    t = M.union pt ht
    nt = M.union pnt hnt
    rs' = MM.union prs $ MM.map horsToPMRSrule hrs
    horsToPMRSrule (HORSRule f xs term) = PMRSRule f xs Nothing term

mkPMRSErr :: RankedAlphabet -> RankedAlphabet -> PMRSRules -> Symbol -> PMRS
mkPMRSErr t nt rs s = runRM $ mkPMRS t nt rs s

mkUntypedPMRS :: PMRSRules -> Symbol -> PMRS
mkUntypedPMRS rs s = PMRS M.empty M.empty rs s

addUntypedHORS :: PMRS -> HORS -> PMRS
addUntypedHORS (PMRS _ _ prs ps) (HORS _ _ hrs _) = mkUntypedPMRS rs' ps
  where
    rs' = MM.union prs $ MM.map horsToPMRSrule hrs
    horsToPMRSrule (HORSRule f xs t) = PMRSRule f xs Nothing t

-- |Extract terminal and nonterminal symbols in the form of a ranked alphabet.
-- The sort is defined as haskell's undefined, so don't access it!
-- (I know that is bad style...)
extractUntypedSymbols :: PMRSRules -> (RankedAlphabet, RankedAlphabet)
extractUntypedSymbols rules = (M.unions terminals, M.unions nonterminals)
  where
    (terminals, nonterminals) = unzip $ map f $ rulesToRuleList rules
    f (PMRSRule _ _ _ t) =
      let ts  = S.toList $ getT t in
      let nts = S.toList $ getN t in
      let tssort = zipWith SortedSymbol ts $ repeat (assert False undefined) in
      let ntsort = zipWith SortedSymbol nts $ repeat (assert False undefined) in
      (mkRankedAlphabet tssort, mkRankedAlphabet ntsort)

-- | Removes rules if they are not used anywhere.
-- Could be improved by doing a reachability analysis.
-- At the moment two unused nonterminals can keep each
-- other alive by referencing themselves.
cleanup :: PMRS -> PMRS
cleanup (PMRS sigma n r s) = PMRS sigma n r' s
  where
    nts = S.insert s $ S.unions $ map (getN . pmrsRuleBody) $ concat $ MM.elems r
    r'  = MM.filter (\(PMRSRule f _ _ _) -> S.member f nts) r

instance Show PMRS where
  show (PMRS t nt r s) =
    let t'  = rankedAlphabetToSet t
        nt' = rankedAlphabetToSet nt
    in "<" ++ (intercalate ",\n" [showSet t',showSet nt',show $ concat $ MM.elems r,show s]) ++ ">"

prettyPrintPMRS :: PMRS -> Writer String ()
prettyPrintPMRS (PMRS _ _ r s) = do
  tell "%BEGINPMRS"
  tell "\n"
  prettyPrintRules s r
  tell "%ENDPMRS"
  tell "\n"

prettyPrintRule :: PMRSRule -> Writer String ()
prettyPrintRule (PMRSRule f xs p body) = tell $ unwords $ filter (not . null) [f, unwords xs, showMaybePrefix "|" p,"=",show body]

prettyPrintRules :: Symbol -> PMRSRules -> Writer String ()
prettyPrintRules s r = do
  -- Ensure that rules with the start symbol are at the beginning of the list.
  let (startRules,otherRules) = partition (\rule -> s == pmrsRuleF rule) $ concat $ MM.elems r
  let ruleList = startRules ++ otherRules
  forM_ ruleList $ \currentRule -> do
    prettyPrintRule currentRule
    tell ".\n"
  return ()

instance PrettyPrint PMRS where
  prettyPrint pmrs = execWriter $ prettyPrintPMRS pmrs

-- | Extracts all the patterns and subpatterns, and replaces
-- all variables with an underscore.
patternDomain :: PMRS -> Set Term
patternDomain pmrs = S.fromList lst
  where
    varsmb      = "_"
    rules       = concat $ MM.elems $ getRules pmrs
    patterns    = S.toList $ foldl extract S.empty rules
    subpatterns = S.unions $ map subterms patterns
    terminals   = S.fromList $ map createTerm $ M.toList $ getTerminals pmrs
    terminalpt  = S.filter isTerminalHead subpatterns
    lst         = S.toList $ S.union terminals terminalpt
    --
    createTerm (s,srt) = app (terminal s) $ replicate (ar srt) $ var varsmb
    --
    extract ack (PMRSRule _ _ p _) = maybe ack (checkAndInsert ack) p
    --
    -- We don't accept plain variable patterns as domains, as we do not
    -- pattern match on anything here.
    checkAndInsert ack (App (Var _) []) = ack
    checkAndInsert ack p'               = flip S.insert ack $ replaceVarsBy varsmb p'

--------------------------

type Application = (Symbol,[Term])

stepRem :: PMRS -> Term -> Set Term -> (Set Term, Set Term)
stepRem pmrs t known =
  if t `S.member` known
    then (S.singleton t, known)
    else (step pmrs t, S.insert t known)

stepsRem' :: Int -> PMRS -> Term -> Set Term -> (Set Term, Set Term)
stepsRem' 0 _    t known = (S.singleton t, known)
stepsRem' n pmrs t known = (S.unions ts, S.unions knowns)
  where
    (res,known') = first S.toList $ stepRem pmrs t known
    (ts,knowns ) = unzip $ map (\term -> stepsRem' (n-1) pmrs term known') res

-- | Version of step that remembers terms that
-- have already been looked at (toplevel only!)
-- and does not reduce them again.
steps' :: Int -> PMRS -> Term -> Set Term
steps' n pmrs t = fst $ stepsRem' n pmrs t S.empty

steps :: Int -> PMRS -> Term -> Set Term
steps 0 _    t = S.singleton t
steps n pmrs t = S.unions $ map (steps (n-1) pmrs) res
  where
    res = S.toList $ step pmrs t

step :: PMRS -> Term -> Set Term
step pmrs (App (Nt f) ts) =
  if not $ S.null reductions
    then reductions
    else if pIsPMSymbol pmrs f && not (null ts)
      then S.map reduceLast $ step pmrs (last ts)
      else S.fromList $ map (App (Nt f)) ts'
  where
    reduceLast t = App (Nt f) $ init ts ++ [t]
    reductions   = reduce pmrs (f,ts)
    reductionsTs = map (S.toList . step pmrs) ts
    ts'          = sequence reductionsTs
step pmrs (App h ts) = S.fromList $ map (App h) ts'
  where
    reductionsTs = map (S.toList . step pmrs) ts
    ts'          = sequence reductionsTs

filterTerminalTrees :: Set Term -> Set Term
filterTerminalTrees ts = S.map ntCut ts

-- | Given a set of rules and a term of the form (F t1 ... tn)
-- the function returns the set of terms that it can be reduced to.
-- The set might be empty!
reduce :: PMRS -> Application -> Set Term
reduce pmrs (f,ts) = S.fromList result
  where
    result    = filterMap (applyRule ts) rules
    -- Fetch all the matching rules for f
    rules     = filter pArgNum $ (getRules pmrs) MM.! f
    -- Check if #arguments match #requiredArgs
    pArgNum r = length ts == argCount r

applyRule :: [Term] -> PMRSRule -> Maybe Term
applyRule ts (PMRSRule _ xs Nothing  t) =
  assert (length ts == length xs) $
  return $ substAll (zip xs ts) t
applyRule ts (PMRSRule _ xs (Just p) t) =
  assert (length ts == 1 + length xs) $
  case isMatching p tsLast of
    Nothing -> Nothing -- Not matching
    Just s  -> return $ substAll (s ++ (zip xs tsInit)) t
  where
    -- Crashes on empty list!
    tsInit = init ts
    tsLast = last ts

-- | Unfolds a single group of PMRS pattern matching rules to depth n.
unfolding :: PMRS -> Symbol -> Int -> PMRS
unfolding (PMRS sigma n r s) nt depth = assert True undefined
  where
    r' = MM.foldlWithKey (\m f r -> if f == nt then unfold' m r else MM.insert f r m) MM.empty r
    ts = trees sigma depth
    --
    unfold' m r@(PMRSRule f xs  Nothing t) = MM.insert f r m
    unfold' m r@(PMRSRule f xs (Just p) t) = MM.insert f r m
      