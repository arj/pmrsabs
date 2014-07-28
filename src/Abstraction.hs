module Abstraction
(
  wPMRS, sPMRS,
  Binding,
  substHead,
  rmatch,
  simpleTerms,
  bindingAnalysis
  )
where

import           Prelude hiding (pi)
import           Control.Arrow (first)
import           Data.SetMap (SetMap)
import qualified Data.SetMap as SM
import qualified Data.MultiMap as MM
import qualified Data.Map as M
import           Data.Set (Set)
import qualified Data.Set as S
import           Data.Char (toUpper)

import Aux
import PMRS hiding (step)
import Term
import Sorts
import CommonRS

-- | A binding is a map from a string to a set of terms.
type Binding = SetMap String Term

-- | Head substitute function.
hs :: Binding -> Head -> Set String -> Set Term
hs _ k@(Nt _) _ = S.singleton $ headToTerm k
hs _ k@(T _) _  = S.singleton $ headToTerm k
hs s (Var x) xs =
  if S.member x xs then
    S.empty
  else
    S.unions $ map f xitm
  where
    xitm = S.toList $ SM.lookup x s
    f (App xi tm) =
        let deltas = hs s xi (S.insert x xs) in
        S.map (\d -> app d tm) deltas

-- |Given a term and a set of bindings S, substHead replaces the
--  head of the term - if it is a variable - with all possible
--  substitutions from S, recursively.
substHead :: Binding -> Term -> Set Term
substHead s (App xi@(Var _) ts) = S.map (\d -> app d ts) deltas
  where
    deltas = hs s xi $ S.empty
substHead _ t                   = S.singleton t

-- | Converts a set of pairs of terms to a binding.
-- Only pairs whose fst element is a simple variable are
-- converted.
toBinding :: Set (Term, Term) -> Binding
toBinding s = S.foldr f SM.empty s
  where
    f ((App (Var x) []),p) ack = SM.insert x p ack
    f _ ack = ack

-- | Convert a binding into a set of terms pairs.
fromBinding :: Binding -> Set (Term, Term)
fromBinding = S.fromList . map (first var) . SM.toList

-- | @rmatch rs u p bnd@ calculates a minimal reduction from a term @u@ to a term @p@
-- using rules @rs@ and bindings @bnd@. If a minimal reduction exists, new acquired bindings
-- for variables used during the reduction are returned.
rmatch :: PMRSRules-> Term -> Term -> Set (Term, Term) -> Binding
rmatch r u1 p1 bnd
  | S.member (u1,p1) bnd  = SM.empty
  | otherwise = rmatch' u1 p1
  where
    rmatch' u (App (Var x) _) = SM.singleton x u
    rmatch' u@(App (T a2) ts) p@(App (T a1) ps)
      | a1 == a2 =
        let bnd' = S.insert (u,p) bnd in
        SM.unions $ map (\(ti,pi) -> rmatch r ti pi bnd') $ zip ts ps
      | otherwise = SM.empty
    rmatch' u@(App (Var _) _) p = SM.unions $ map (\t -> rmatch r t p bnd') ts
      where
        vbnd = toBinding bnd
        ts = S.toList $ substHead vbnd u
        bnd' = S.insert (u,p) bnd
    rmatch' u@(App (Nt f) ts) p =
      let nonemptyRules = filter nonempty rulesForf in
      SM.unions $ map (\(PMRSRule _ _ _ t) -> rmatch r t p bnd) $ nonemptyRules
      where
        rulesForf = MM.lookup f r
        bnd' = S.insert (u,p) bnd
        v = last ts
        --
        nonempty (PMRSRule _ _ (Just q) _) = not $ SM.null $ rmatch r v q bnd'
        nonempty (PMRSRule _ xs Nothing  _)
          | null xs   = True
          | otherwise =
            let q = var $ last xs in
            not $ SM.null $ rmatch r v q bnd'

-- | Extracts all simple terms begining with a variable or nonterminal from
-- a given PMRS with a starting symbol of the included 0-order HORS.
simpleTerms :: Symbol -> PMRS -> Set Term
simpleTerms gS pmrs = S.insert mainS $ allSubT
  where
    r       = getRules pmrs
    mainSmb = getStartSymbol pmrs
    rhs     = map pmrsRuleBody $ concat $ MM.elems r
    allSubT = S.unions $ map subterms' rhs
    mainS   = app main [s]
    main    = sToSymbol mainSmb
    s       = sToSymbol gS

-- | One step of the binding analysis.
-- @step rs bnd u@ returns all bindings that can be derived
-- from the simple term @u@ (and all its head derivatives) using the rules @rs@ and
-- the already existing binding @bnd@.
step :: PMRSRules -> Binding -> Term -> Binding
step rs bnd u = SM.union bnd $ SM.unions $ concat $ map bndPerTerms $ S.toList rulesPerTerm
  where
    terms        = substHead bnd u
    -- Set (Term a1, [Rule a1])
    rulesPerTerm = S.map (\t -> (t,matchingRulesByTerm rs t)) terms
    bndPerTerms (term,trules) = map (bndFromRule term) trules
    --
    minRed s p   = rmatch rs s p (fromBinding bnd)
    --
    bndFromRule (App _ ts) (PMRSRule _ xs (Just p) _)
      | length ts < 1 + length xs = SM.empty -- No partial application
      | otherwise                 = SM.union (SM.fromList $ zip xs (init ts)) (minRed (last ts) p)
    bndFromRule (App _ ts) (PMRSRule _ xs Nothing  _) = SM.fromList $ zip xs ts

bindingAnalysisOneRound :: Symbol -> PMRS -> Binding -> Binding
bindingAnalysisOneRound gs pmrs bnd = foldl (step rs) bnd terms
  where
    rs    = getRules pmrs
    terms = S.toList $ simpleTerms gs pmrs

bindingAnalysis :: Symbol -> PMRS -> Binding -> Binding
bindingAnalysis gs pmrs bnd
  | bnd == bnd' = bnd'
  | otherwise   = bindingAnalysis gs pmrs bnd'
  where
    bnd' = bindingAnalysisOneRound gs pmrs bnd

-- | Transforms normal rules into weak rules that do not use
-- their pattern matching variable in the body but instead
-- use new nonterminals corresponding to the variables.
weakPMrules :: PMRSRules -> PMRSRules
weakPMrules rs = MM.map f rs
  where
    f r@(PMRSRule _ _  Nothing  _) = r
    f   (PMRSRule g xs (Just p) b) =
      -- TODO Wrong sort!
      let pmxs = map (\x -> (x,nonterminal (headToUpper x))) $ S.toList $ fv p
          b'   = substAll pmxs b in
      PMRSRule g xs (Just p) b'

-- | From the binding analysis, new rules are created that map
-- nonterminals that correspond to the variables to the terms found
-- in the binding analysis.
instantiationRules :: Binding -> (Set SortedSymbol , PMRSRules)
instantiationRules bnd = (S.fromList symbols, listToRules rs)
  where
    (symbols, rs) = unzip $ map (uncurry bndToRule) $ SM.toList bnd
    -- TODO Correct sort missing!
    bndToRule x t =
      let f   = headToUpper x
          smb = SortedSymbol f o
      in (smb, PMRSRule f [] Nothing t)

-- | Transforms the first letter in a string to upper case.
headToUpper :: String -> String
headToUpper []     = []
headToUpper (x:xs) = toUpper x : xs

-- | Generates a weak PMRS from a start symbol (0-order HORS included into the PMRS),
-- and a PMRS.
wPMRS :: Monad m => Symbol -> PMRS -> m PMRS
wPMRS gs pmrs = mkWPMRS sig nt' rs' s'
  where
    sig    = getTerminals pmrs
    nt     = getNonterminals pmrs
    rs     = getRules pmrs
    s      = getStartSymbol pmrs
    nt'    = M.unions [nt_s',nt,mkRankedAlphabet $ S.toList instnt]
    rs'    = MM.insert s' start $ (weakPMrules rs) `MM.union` instrs
    bnd    = bindingAnalysis gs pmrs SM.empty
    --
    s'     = freshVar (M.keys nt) "S"
    nt_s'  = M.singleton s' o
    start  = PMRSRule s' [] Nothing $ app (nonterminal s) [nonterminal gs]
    --
    pmvars = getPMVariables pmrs
    --
    bndpm  = SM.filterWithKey (\(k,_) -> S.member k pmvars) bnd
    --
    (instnt,instrs) = instantiationRules bndpm

sPMRS :: PMRS -> PMRS
sPMRS = undefined