{-# LANGUAGE ScopedTypeVariables, BangPatterns #-}

module WPMRSTransformer
where

import qualified Data.Map as M
import qualified Data.MultiMap as MM
import Text.Printf (printf)
import qualified Data.Set as S
import Data.Tuple

import Aux (uncurry4)
import Term (var, app, nonterminal, terminal, substTerminals, Term, Head(Nt), appendArgs,isomorphic, heightCut, height)
import Sorts (ar,o,(~>),createSort,RankedAlphabet,Symbol,Sort(Base), sortFromList,sortToList,lift)
import PMRS (PMRS(..), PMRSRules, PMRSRule(..), isWPMRS, patternDomain)
import HORS (HORS(..), HORSRule(..), HORSRules, mkHorsRules, mkHORS, mkUntypedHORS)

data TransformerResult = TR { trMapping :: [(Int, Term)]
                            , trHors :: (RankedAlphabet, RankedAlphabet, HORSRules, Symbol)
                            }

fromPMRSInner :: PMRS -> String -> TransformerResult
fromPMRSInner pmrs@(PMRS sigma nonterminals r s) suffix =
  if (not $ isWPMRS pmrs)
    then error "Cannot transform: PMRS is not a weak PMRS."
    else
      let patterns = patternDomain pmrs in
      let max_height = maximum $ map height $ S.toList patterns in
      let bots = "bot" ++ suffix in
      let bot = terminal bots in
      let m = mapping patterns in
      let param = Param max_height (S.size patterns) suffix bot (searchTerm m) (searchTermInv m) nonterminals in
      let (nCnt, rCnt) = mkCounters param in
      let (nAux, rAux) = auxRules param in
      let (nTerminals, rTerminals) = rulesForTerminals param sigma in
      let (nRules, rRules) = rulesForRules param r in
      let (s', _nStart, rStart) = mkStart param s in
      let rules = rCnt ++ rAux ++ rTerminals ++ rRules ++ rStart in
      let rs = mkHorsRules rules in
      let nts = M.unions [nCnt, nAux, nTerminals, nRules] in
      let sigma' = M.insert bots o sigma in
      TR (map swap m) (sigma',nts,rs,s')
  where
    mapping p = zip (S.toList p) [1..]
    --

searchTerm :: [(Term, Int)] -> Term -> Int
searchTerm m term = searchTerm' term m
  where
    searchTerm' :: Term -> [(Term, Int)] -> Int
    searchTerm' t [] = error $ "In WPMRSTransformer I couldn't find a mapping for " ++ (show t) ++ " in " ++ (show m)
    searchTerm' t ((ti,i):rs)
      | isomorphic t ti = i
      | otherwise       = searchTerm' t rs

searchTermInv :: [(Term, Int)] -> Int -> Term
searchTermInv m i = fst $ m !! i

fromPMRS :: Monad m => PMRS -> m HORS
fromPMRS pmrs = uncurry4 mkHORS $ trHors $ fromPMRSInner pmrs "" -- TODO set suffix

fromUntypedPMRS :: PMRS -> ([(Int, Term)], HORS)
fromUntypedPMRS pmrs = (m, mkUntypedHORS rs s)
  where
    TR m (_, _, rs, s) = fromPMRSInner pmrs "" -- TODO set suffix

---

data Param = Param { paramDepth :: Int
                   , paramCntPM :: Int
                   , paramSuffix :: String
                   , paramBot :: Term
                   , paramMap :: Term -> Int
                   , paramMapInv :: Int -> Term
                   , paramNonterminals :: RankedAlphabet
                   }

simpleParam :: Param
simpleParam = Param 1 4 "" (terminal "bot") (searchTerm m) (searchTermInv m) (M.empty)
  where
    m = [(terminal "z",1)
        ,(terminal "nil",2)
        ,(app (terminal "succ") [var "_"],3)
        ,(app (terminal "cons") [var "_", var "_"],4)
        ]

idPair :: Symbol
idPair = "Pair"

mkStart :: Param -> Symbol -> (Symbol, RankedAlphabet, [HORSRule])
mkStart param s = (s', ra, [rule])
  where
    s'   = "S_HORS" ++ paramSuffix param
    ra   = M.singleton s' o
    npi1 = nonterminal $ "Pi1" ++ paramSuffix param
    rule = HORSRule s' [] $ app npi1 $ [nonterminal s]

rulesForRules :: Param -> PMRSRules -> (RankedAlphabet, [HORSRule])
rulesForRules param rules = (ra, rs)
  where
    (ras, rss) = unzip $ M.elems $ M.map (mkRuleForRule param) $ MM.toMap rules
    ra = M.unions ras
    rs = concat rss

mkRuleForRule :: Param -> [PMRSRule] -> (RankedAlphabet, [HORSRule])
mkRuleForRule param rs@(PMRSRule f xs (Just _) _:_) = (ra, [r1,r2])
  where
    pT       = createSort $ paramCntPM param
    churchPairT = (o ~> pT ~> pT) ~> pT
    --
    f_sort =
        case M.lookup f $ paramNonterminals param of
            Just srt -> srt
            Nothing -> error $ "Couldn't lookup " ++ f ++ " in nonterminals."
    --
    -- Takes all the arguments but the last 'two', i.e. all non-pattern-matching arguments
    -- and lifts them to church pairs.
    argsSortLifted = map (lift churchPairT) $ init $ init $ sortToList f_sort
    liftedNonPMArgSort = sortFromList $ argsSortLifted ++ [pT, churchPairT]
    --
    r1T = (f,lift churchPairT f_sort)
    r2T = (f_case, liftedNonPMArgSort)
    ra = M.fromList [r1T, r2T]
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
    pm = paramMap param
    patternsLookupMap = map (\(PMRSRule _ _ (Just p) t) -> (pm p, t)) rs
    --

    --
    createCases i =
        case lookup i patternsLookupMap of
            Just t -> appendArgs (substTerminals m t) args
            Nothing -> paramBot param
    --
    r2 = HORSRule f_case xs' $ app (var parg) $ map createCases [1..(paramCntPM param)]

mkRuleForRule param rs@(PMRSRule f xs  Nothing  _:_) = (ra, map horsMap rs)
  where
    pT       = createSort $ paramCntPM param
    churchPairT = (o ~> pT ~> pT) ~> pT
    ra = M.singleton f $ sortFromList $ replicate (1 + length xs) churchPairT
    --
    suffix = paramSuffix param
    m k = Nt $ "T_" ++ k ++ suffix
    selector = "f" ++ suffix
    --
    cs     = genXs "c" $ paramCntPM param
    csTerm = genXsTerm "c" $ paramCntPM param
    args = var selector : csTerm
    --
    horsMap (PMRSRule f' xs' Nothing t) = HORSRule f' (xs' ++ [selector] ++ cs) $ appendArgs (substTerminals m t) args

-- | Given a ranked alphabet of terminal symbols this function
-- returns a rankedalphabet of nonterminals and a list of rules representing
-- wrappers for the terminals.
rulesForTerminals :: Param -> RankedAlphabet -> (RankedAlphabet, [HORSRule])
rulesForTerminals param ra = foldl f (ra0, rs0) $ M.toList ra
  where
    ra0 = M.empty
    rs0 = []
    --
    f (raAck, rsAck) (k,srt) =
      let (ra', rs') = terminalRules param k srt in
      ((M.union raAck ra'), rsAck ++ rs')

mkJustRule :: Param -> Symbol -> Sort -> (RankedAlphabet, HORSRule)
mkJustRule param k srt = (ra, justkR)
  where
    ra = M.singleton justk pT
    --
    suffix = paramSuffix param
    justk  = "Just_" ++ k ++ suffix
    pT     = createSort $ paramCntPM param
    --
    pm = paramMap param
    --
    cs     = genXs "c" $ paramCntPM param
    justkR   = HORSRule justk cs $ var $ printf "c%i" $ pm $ app (terminal k) $ replicate (ar srt) $ var "_"


-- |Wrapper rule for a terminal that creates a pair of
-- a normal tree created from terminals and a pattern-matchable tree.
-- Formally we have: @T_k f c1 ... cn = Pair k Just_k f c1 ... cn@ if @ar(k)=0@
-- and @T_k x1 ... xl f c1 ... cn = Pair (Mk_k (Pi1 x1) ... (Pi1 xl)) (Case_k x1 ... xl) f c1 ... cn@
--  if @ar(k)>0@.
terminalRules :: Param -> Symbol -> Sort -> (RankedAlphabet, [HORSRule])
terminalRules param k Base = (ra, [tkR,rs_just])
  where
    ra = M.union ra_just $ M.fromList [tkT]
    --
    (ra_just,rs_just) = mkJustRule param k Base
    --
    suffix = paramSuffix param
    justk  = "Just_" ++ k ++ suffix
    tk     = "T_" ++ k ++ suffix
    pair   = idPair ++ suffix
    selector = "f" ++ suffix
    --
    pT       = createSort $ paramCntPM param
    churchPairT = (o ~> pT ~> pT) ~> pT
    --
    tkT      = (tk, churchPairT)
    --
    tkR      = HORSRule tk (selector : cs) $ app (nonterminal pair) $ [terminal k, nonterminal justk, var "f"] ++ csTerm
    --
    cs     = genXs "c" $ paramCntPM param
    csTerm = genXsTerm "c" $ paramCntPM param
    --
terminalRules param k ksrt = (ra, [just_k, case_k, r])
  where
    ra     = M.unions [ra_just_k, ra_case_k, M.singleton tk tkT, M.singleton "br_br" (o ~> o ~> o)]
    --
    suffix = paramSuffix param
    ncasek = nonterminal $ "Case_" ++ k ++ suffix
    npair  = nonterminal $ idPair ++ suffix
    npi1   = nonterminal $ "Pi1" ++ suffix
    npi2   = nonterminal $ "Pi2" ++ suffix
    tk     = "T_" ++ k ++ suffix
    --
    pT          = createSort $ paramCntPM param
    churchPairT = (o ~> pT ~> pT) ~> pT
    tkT         = sortFromList $ replicate (1 + ar ksrt) churchPairT
    --
    r      = HORSRule tk (xs ++ ["f"] ++ cs) $ body ccall
    mkcall = app (terminal k) $ map (\xi -> app npi1 [xi]) xsTerm
    ccall  = app ncasek $ map (\xi -> app npi2 [xi]) xsTerm
    l      = ar ksrt
    n      = paramCntPM param
    xs     = genXs "x" l
    xsTerm = genXsTerm "x" l
    cs     = genXs "c" n
    csTerm = genXsTerm "c" n
    --
    body pmpart = app npair $ [mkcall, pmpart, var "f"] ++ csTerm
    --
    (ra_case_k, case_k) = mkCasekRule param k ksrt xs cs
    (ra_just_k, just_k) = mkJustRule param k ksrt

createCaseCases :: Param -> Symbol -> Sort -> [String] -> [String] -> Term
createCaseCases param k _srt xs cs = inner xs []
  where
    inner :: [String] -> [Int] -> Term
    inner [xn] is = app (var xn) $ zipWith (\i _ -> createTerm $ reverse $ i:is) [1..] cs
    inner (xi:rest) is = app (var xi) $ zipWith (\i _ -> inner rest (i:is)) [1..] cs
    cut = heightCut $ paramDepth param
    --
    createTerm pos =
        let i = paramMap param $ cut $ app (terminal k) $ map (paramMapInv param) pos in
        var $ cs !! (i-1)

-- |Creates the case rule that establishes new pattern matching for
-- given subterms and a terminal.
-- We have @Case_k x1 ... xl cnt c1 ... cn = [(complicated pm-term)]@
mkCasekRule :: Param -> Symbol -> Sort -> [String] -> [String] -> (RankedAlphabet, HORSRule)
mkCasekRule param k srt xs cs = (ra, HORSRule f (xs ++ cs) body)
  where        
    pT   = createSort $ paramCntPM param
    ra   = M.singleton f $ sortFromList $ replicate (1 + length xs) $ pT
    f    = "Case_" ++ k ++ paramSuffix param
    body = createCaseCases param k srt xs cs

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
    churchPairT = (o ~> pT ~> pT) ~> pT
    kT          = o ~> pT ~> pT
    --
    pairT = (pair, o ~> pT ~> churchPairT)
    k1T   = (k1, kT)
    k2T   = (k2, kT)
    pi1T  = (pi1, churchPairT ~> o)
    pi2T  = (pi2, churchPairT ~> pT)
    --
    pairR = HORSRule pair (["x","y","f"] ++ cs) $ app (var "f") ([var "x", var "y"] ++ csTerm)
    k1R   = HORSRule k1 (["x","y"] ++ cs) $ var "x"
    k2R   = HORSRule k2 (["x","y"] ++ cs) $ app (var "y") csTerm
    pi1R  = HORSRule pi1 ["p"] $ app (var "p") $ nonterminal k1 : map (const $ terminal "bot") csTerm
    pi2R  = HORSRule pi2 ("p" : cs) $ app (var "p") $ [nonterminal k2] ++ csTerm
    --
    -- ns     = genXs "n" $ paramDepth param
    cs     = genXs "c" $ paramCntPM param
    csTerm = genXsTerm "c" $ paramCntPM param

genXs :: String -> Int -> [String]
genXs x n = map (\i -> x ++ show i) [1..n]

genXsTerm :: String -> Int -> [Term]
genXsTerm x n = map var $ genXs x n

mkCounters :: Param -> (RankedAlphabet, [HORSRule])
mkCounters param = (ra, rs)
  where
    depth = paramDepth param
    suffix = paramSuffix param
    cnt n = "Cnt" ++ (show n) ++ suffix
    --
    cntArgs = map (\i -> "cnt" ++ (show i)) [1..depth]
    --
    cntT = sortFromList $ replicate (depth+1) o
    --
    rCnt n = HORSRule (cnt n) cntArgs $ var $ "cnt" ++ (show n)
    raCnt n = M.singleton (cnt n) cntT
    --
    ra = M.unions $ map raCnt [1..depth]
    rs = map rCnt [1..depth]