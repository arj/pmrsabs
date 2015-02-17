{-# LANGUAGE ScopedTypeVariables, BangPatterns #-}

module WPMRSTransformer
where

import GHC.Base (assert)
import qualified Data.Map as M
import qualified Data.MultiMap as MM
import Text.Printf (printf)
import qualified Data.Set as S

import CommonRS (rulesToRuleList)
import Aux (traceIt)
import Term (var, app, nonterminal, terminal, substTerminals, Term, Head(Nt), appendArgs,isomorphic)
import Sorts (ar,o,(~>),createSort,RankedAlphabet,Symbol,Sort(Base))
import PMRS (PMRS(..), PMRSRules(..), PMRSRule(..), isWPMRS, patternDomain)
import HORS (HORS(..), HORSRule(..), mkHorsRules, mkHORS, mkUntypedHORS)

fromPMRS :: Monad m => PMRS -> m HORS
fromPMRS pmrs@(PMRS sigma n r s) =
  if (not $ isWPMRS pmrs)
    then error "Cannot transform: PMRS is not a weak PMRS."
    else
      let patterns = patternDomain pmrs in
      let param = Param 1 (S.size patterns) "" (terminal "bot") in -- TODO set prefix
      let pm = searchTerm patterns in
      let (_nAux, rAux) = auxRules param in
      let (_nTerminals, rTerminals) = rulesForTerminals param sigma pm in
      let (_nRules, rRules) = rulesForRules param pm r in
      let (s', _nStart, rStart) = mkStart param s in
      let rules = rAux ++ rTerminals ++ rRules ++ rStart in
      let rs = mkHorsRules rules in
      -- mkHORS sigma nTerminals rs "S"
      return $ mkUntypedHORS rs s'
  where
    searchTerm patterns t =
        let mapping = zip (S.toList patterns) [1..] in
        searchTerm' t mapping
    --
    searchTerm' :: Term -> [(Term, Int)] -> Int
    searchTerm' _ [] = assert True undefined
    searchTerm' t ((ti,i):rs)
      | isomorphic t ti = i
      | otherwise       = searchTerm' t rs
        

---

data Param = Param { paramDepth :: Int
                   , paramCntPM :: Int
                   , paramSuffix :: String
                   , paramBot :: Term
                   }

simpleParam = Param 1 4 "" (terminal "bot")

idPair :: Symbol
idPair = "Pair"

mkStart :: Param -> Symbol -> (Symbol, RankedAlphabet, [HORSRule])
mkStart param s = (s', ra, [rule])
  where
    s'   = "S_HORS" ++ paramSuffix param
    ra   = assert False undefined
    npi1   = nonterminal $ "Pi1" ++ paramSuffix param
    rule = HORSRule s' [] $ app npi1 $ [terminal s]

rulesForRules :: Param -> (Term -> Int) -> PMRSRules -> (RankedAlphabet, [HORSRule])
rulesForRules param pm rules = (ra, rs)
  where
    (ras, rss) = unzip $ M.elems $ M.map (mkRuleForRule param pm) $ MM.toMap rules
    ra = M.unions ras
    rs = concat rss

mkRuleForRule :: Param -> (Term -> Int) -> [PMRSRule] -> (RankedAlphabet, [HORSRule])
mkRuleForRule param pm rs@(PMRSRule f xs (Just _) _:_) = (ra, [r1,r2])
  where
    ra = assert False undefined
    --
    suffix = paramSuffix param
    f_case = f ++ "_case" ++ suffix
    f_caseTerm = nonterminal f_case
    parg = "parg" ++ suffix
    selector = "f" ++ suffix
    m k = Nt $ "T_" ++ k ++ suffix
    --
    args = var selector : csTerm
    --
    cs     = genXs "c" $ paramCntPM param
    csTerm = genXsTerm "c" $ paramCntPM param
    xs' = xs ++ [parg,selector] ++ cs
    xsTerm = map var xs
    pi2  = nonterminal $ "Pi2" ++ suffix
    pi2Arg p = app pi2 [var p]
    --
    r1 = HORSRule f xs' $ app f_caseTerm (xsTerm ++ [pi2Arg parg,var selector] ++ csTerm)
    --
    patternsLookupMap = map (\(PMRSRule _ _ (Just p) t) -> (pm p, t)) rs
    --

    --
    createCases i =
        case lookup i patternsLookupMap of
            Just t -> appendArgs (substTerminals m t) args
            Nothing -> paramBot param
    --
    r2 = HORSRule f_case xs' $ app (var parg) $ map createCases [1..(paramCntPM param)]

mkRuleForRule param pm rs@(PMRSRule _ _  Nothing  _:_) = (undefined, map horsMap rs)
  where
    suffix = paramSuffix param
    m k = Nt $ "T_" ++ k ++ suffix
    selector = "f" ++ suffix
    --
    cs     = genXs "c" $ paramCntPM param
    csTerm = genXsTerm "c" $ paramCntPM param
    args = var selector : csTerm
    --
    horsMap (PMRSRule f xs Nothing t) = HORSRule f (xs ++ [selector] ++ cs) $ appendArgs (substTerminals m t) args

-- | Given a ranked alphabet of terminal symbols this function
-- returns a rankedalphabet of nonterminals and a list of rules representing
-- wrappers for the terminals.
rulesForTerminals :: Param -> RankedAlphabet -> (Term -> Int) -> (RankedAlphabet, [HORSRule])
rulesForTerminals param ra pm = foldl f (ra0, rs0) $ M.toList ra
  where
    ra0 = M.empty
    rs0 = []
    --
    f (raAck, rsAck) (k,srt) =
      let (ra', rs') = terminalRules param k srt pm in
      ((M.union raAck ra'), rsAck ++ rs')

-- |Wrapper rule for a terminal that creates a pair of
-- a normal tree created from terminals and a pattern-matchable tree.
-- Formally we have: @T_k f c1 ... cn = Pair k Just_k f c1 ... cn@ if @ar(k)=0@
-- and @T_k x1 ... xl f c1 ... cn = Pair (Mk_k (Pi1 x1) ... (Pi1 xl)) (Case_k x1 ... xl) f c1 ... cn@
--  if @ar(k)>0@.
terminalRules :: Param -> Symbol -> Sort -> (Term -> Int) -> (RankedAlphabet, [HORSRule])
terminalRules param k Base pm = (ra, rs)
  where
    ra = M.fromList [justkT, tkT]
    rs = [justkR, tkR]
    --
    suffix = paramSuffix param
    justk  = "Just_" ++ k ++ suffix
    tk     = "T_" ++ k ++ suffix
    pair   = idPair ++ suffix
    selector = "f" ++ suffix
    --
    pT       = createSort $ paramCntPM param
    churchPairT = (pT ~> pT ~> pT) ~> pT
    --
    justkT   = (justk, pT)
    tkT      = (tk, churchPairT)
    --
    justkR   = HORSRule justk cs $ var $ printf "c%i" $ pm (terminal k)
    tkR      = HORSRule tk (selector : cs) $ app (nonterminal pair) $ [terminal k, nonterminal justk, var "f"] ++ csTerm
    --
    cs     = genXs "c" $ paramCntPM param
    csTerm = genXsTerm "c" $ paramCntPM param
    --
terminalRules param k ksrt pm = (ra, [mk_k, case_k, r])
  where
    ra     = M.unions [ra_mk_k, ra_case_k, assert False undefined]
    --
    suffix = paramSuffix param
    nmkk   = nonterminal $ "Mk_" ++ k ++ suffix
    ncasek = nonterminal $ "Case_" ++ k ++ suffix
    npair  = nonterminal $ idPair ++ suffix
    npi1   = nonterminal $ "Pi1" ++ suffix
    npi2   = nonterminal $ "Pi2" ++ suffix
    tk     = "T_" ++ k ++ suffix
    --
    r      = HORSRule tk (xs ++ ["f"] ++ cs) t
    t      = app npair $ [mkcall, ccall, var "f"] ++ csTerm
    mkcall = app nmkk $ map (\xi -> app npi1 [xi]) xsTerm
    ccall  = app ncasek $ map (\xi -> app npi2 [xi]) xsTerm -- TODO Adjust type!
    l      = ar ksrt
    n      = paramCntPM param
    xs     = genXs "x" l
    xsTerm = genXsTerm "x" l
    cs     = genXs "c" n
    csTerm = genXsTerm "c" n
    --
    (ra_mk_k,mk_k) = mkMkRule param k xs xsTerm
    (ra_case_k, case_k) = mkCasekRule param k xs cs pm

-- |Creates the making rule that creates a single terminal tree from its arguments.
-- We have: @Mk_k x1 ... xl = k x1 .. xl@
mkMkRule :: Param -> Symbol -> [String] -> [Term] -> (RankedAlphabet, HORSRule)
mkMkRule param k xs xsTerm = (ra, HORSRule f xs t)
  where
    ra  = M.singleton f $ assert False undefined
    f   = "Mk_" ++ k ++ paramSuffix param
    t   = app (terminal k) $ xsTerm

-- |Creates the case rule that establishes new pattern matching for
-- given subterms and a terminal.
-- We have @Case_k x1 ... xl cnt c1 ... cn = [(complicated pm-term)]@
mkCasekRule :: Param -> Symbol -> [String] -> [String] -> (Term -> Int) -> (RankedAlphabet, HORSRule)
mkCasekRule param k xs cs _pm = (ra, HORSRule f (xs ++ cs) t)
  where
    ra = M.singleton f $ assert False undefined
    f  = "Case_" ++ k ++ paramSuffix param
    t  = var "undefined" -- assert False undefined

-- |Creates the auxilliary rules that are needed
-- for church encoding pairs, pattern matching and natural numbers
-- up to cntDepth.
auxRules :: Param -> (RankedAlphabet, [HORSRule])
auxRules param = (ra, rs)
  where
    ra = M.fromList $ [pairT, k1T, k2T, pi1T, pi2T]
    rs = [pairR,k1R,k2R,pi1R,pi2R]
    --
    suffix = paramSuffix param
    pair = idPair ++ suffix
    k1   = "K1" ++ suffix
    k2   = "K2" ++ suffix
    pi1  = "Pi1" ++ suffix
    pi2  = "Pi2" ++ suffix
    --
    pT       = createSort $ paramCntPM param
    churchPairT = (pT ~> pT ~> pT) ~> pT
    kT          = o ~> pT ~> pT
    --
    pairT = (pair, pT ~> pT ~> churchPairT)
    k1T   = (k1, kT)
    k2T   = (k2, kT)
    pi1T  = (pi1, churchPairT ~> pT)
    pi2T  = (pi2, churchPairT ~> pT)
    --
    pairR = HORSRule pair (["x","y","f"] ++ cs) $ app (var "f") ([var "x", var "y"] ++ csTerm)
    k1R   = HORSRule k1 (["x","y"] ++ cs) $ var "x"
    k2R   = HORSRule k2 (["x","y"] ++ cs) $ app (var "y") csTerm
    pi1R  = HORSRule pi1 ["p"] $ app (var "p") $ nonterminal k1 : map (const $ terminal "bot") csTerm
    pi2R  = HORSRule pi2 ("p" : cs) $ app (var "p") $ [nonterminal k2] ++ csTerm
    --
    ns     = genXs "n" $ paramDepth param
    cs     = genXs "c" $ paramCntPM param
    csTerm = genXsTerm "c" $ paramCntPM param

genXs :: String -> Int -> [String]
genXs x n = map (\i -> x ++ show i) [1..n]

genXsTerm :: String -> Int -> [Term]
genXsTerm x n = map var $ genXs x n