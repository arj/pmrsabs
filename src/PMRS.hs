{-# LANGUAGE TypeSynonymInstances,FlexibleInstances #-}
module PMRS
--(
--  PMRSRule(..), PMRS,
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
--  reduce
--  )
where

import Aux
import Term
import Sorts
import Data.List
import CommonRS

import Data.MultiMap (MultiMap)
import qualified Data.MultiMap as MM

import Data.Set (Set)
import qualified Data.Set as S

import Data.Map (Map)
import qualified Data.Map as M

import Data.Maybe
import Control.Arrow
import Control.Monad
import Control.Monad.Writer

import Control.Exception (assert)

import Debug.Trace (trace)

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

getPMVariables :: PMRS -> Set String
-- ^ Returns all variables used in pattern matching.
getPMVariables pmrs = S.unions $ map extractPMVars rules
  where
    extractPMVars (PMRSRule _ _ p _) = maybe S.empty fv p
    rules = concat $ MM.elems $ getRules pmrs

type PMRSRules = Rules PMRSRule

instance Show PMRSRule where
  show (PMRSRule f xs p body) = unwords $ filter (not . null) [show f, unwords xs, showMaybe p,"=>",show body]

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
  tell "%BEGING"
  tell "\n"
  prettyPrintRules s r
  tell "%ENDG"
  tell "\n"

prettyPrintRule :: PMRSRule => Writer String ()
prettyPrintRule (PMRSRule f xs p body) = tell $ unwords $ filter (not . null) [show f, unwords xs, showMaybe p,"=",show body]

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