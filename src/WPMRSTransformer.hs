module WPMRSTransformer
where

import GHC.Base (assert)
import qualified Data.Map as M
import Text.Printf (printf)

import Term (var, app, nonterminal, terminal, substTerminals, Term, Head(Nt))
import Sorts (ar,(~>),createSort,RankedAlphabet,Symbol,Sort(Base))
import PMRS (PMRS(..), PMRSRule(..))
import HORS (HORS(..), HORSRule(..))

fromPMRS :: PMRS -> HORS
fromPMRS (PMRS _t _n _rs _s) = assert False undefined

---

data Param = Param { paramDepth :: Int
                   , paramCntPM :: Int
                   , paramPrefix :: String
                   }

idPair :: Symbol
idPair = "Pair"

rulesForHORSRules :: Param -> [PMRSRule] -> (RankedAlphabet, [HORSRule])
rulesForHORSRules param rules = (ra, map g rules)
  where
    ra = assert False undefined
    prefix = paramPrefix param
    m k = Nt $ prefix ++ "T_" ++ k
    --
    g (PMRSRule f xs Nothing t) = HORSRule f xs $ substTerminals m t
    g _ = error "rulesForHORSRules may only be called for PMRSRules with no pm"

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
    prefix = paramPrefix param
    justk  = prefix ++ "Just_" ++ k
    tk     = prefix ++ "T_" ++ k
    pair   = prefix ++ idPair
    --
    counterT = createSort $ paramDepth param
    pT       = createSort $ paramCntPM param
    churchPairT = (pT ~> (counterT ~> pT) ~> pT) ~> pT
    --
    justkT   = (justk, counterT ~> pT)
    tkT      = (tk, churchPairT)
    --
    justkR   = HORSRule justk ("n" : cs) $ var $ printf "c%i" $ pm (terminal k)
    tkR      = HORSRule tk ("f" : cs) $ app (nonterminal pair) $ [terminal k, nonterminal justk, var "f"] ++ csTerm
    --
    cs     = genXs "c" $ paramCntPM param
    csTerm = genXsTerm "c" $ paramCntPM param
    --
terminalRules param k ksrt pm = (ra, [mk_k, case_k, r])
  where
    ra     = M.unions [ra_mk_k, ra_case_k, assert False undefined]
    --
    prefix = paramPrefix param
    nmkk   = nonterminal $ prefix ++ "Mk_" ++ k
    ncasek = nonterminal $ prefix ++ "Case_" ++ k
    npair  = nonterminal $ prefix ++ idPair
    npi1   = nonterminal $ prefix ++ "Pi1"
    tk     = prefix ++ "T_" ++ k
    --
    r      = HORSRule tk (xs ++ ["f"] ++ cs) t
    t      = app npair $ [mkcall, ccall, var "f"] ++ csTerm
    mkcall = app nmkk $ map (\xi -> app npi1 [xi]) xsTerm
    ccall  = app ncasek xsTerm
    l      = ar ksrt
    n      = paramCntPM param
    xs     = genXs "x" l
    xsTerm = genXsTerm "x" l
    cs     = genXs "c" n
    csTerm = genXsTerm "c" n
    --
    (ra_mk_k,mk_k) = mkMkRule param k xs xsTerm cs csTerm
    (ra_case_k, case_k) = mkCasekRule param k xs cs pm

-- |Creates the making rule that creates a single terminal tree from its arguments.
-- We have: @Mk_k x1 ... xl c1 ... cn = k (x1 c1 ... cn) (xl c1 ... cn)@
mkMkRule :: Param -> Symbol -> [String] -> [Term] -> [String] -> [Term] -> (RankedAlphabet, HORSRule)
mkMkRule param k xs xsTerm cs csTerm = (ra, HORSRule f (xs ++ cs) t)
  where
    ra  = M.singleton f $ assert False undefined
    f   = paramPrefix param ++ "Mk_" ++ k
    t   = app (terminal k) $ xis
    xis = map (\xi -> app xi csTerm) xsTerm

-- |Creates the case rule that establishes new pattern matching for
-- given subterms and a terminal.
-- We have @Case_k x1 ... xl cnt c1 ... cn = [(complicated pm-term)]@
mkCasekRule :: Param -> Symbol -> [String] -> [String] -> (Term -> Int) -> (RankedAlphabet, HORSRule)
mkCasekRule param k xs cs _pm = (ra, HORSRule f (xs ++ ["cnt"] ++ cs) t)
  where
    ra = M.singleton f $ assert False undefined
    f  = paramPrefix param ++ "Case_" ++ k
    t  = var "undefined" -- assert False undefined

-- |Creates the auxilliary rules that are needed
-- for church encoding pairs, pattern matching and natural numbers
-- up to cntDepth.
auxRules :: Param -> (RankedAlphabet, [HORSRule])
auxRules param = (ra, rs)
  where
    ra = M.fromList $ cntTs ++ [pairT, k1T, k2T, pi1T, pi2T]
    rs = cntRs ++ [pairR,k1R,k2R,pi1R,pi2R]
    --
    prefix = paramPrefix param
    cnt :: Int -> String
    cnt i = prefix ++ "Cnt" ++ show i
    pair = prefix ++ idPair
    k1   = prefix ++ "K1"
    k2   = prefix ++ "K2"
    pi1  = prefix ++ "Pi1"
    pi2  = prefix ++ "Pi2"
    --
    counterT = createSort $ paramDepth param
    pT       = createSort $ paramCntPM param
    churchPairT = (pT ~> (counterT ~> pT) ~> pT) ~> pT
    kT          = counterT ~> pT ~> (counterT ~> pT) ~> pT
    --
    cntTs = map (\i -> (cnt i, counterT)) [1..paramDepth param]
    pairT = (pair, pT ~> (counterT ~> pT) ~> churchPairT)
    k1T   = (k1, kT)
    k2T   = (k2, kT)
    pi1T  = (pi1, churchPairT ~> pT)
    pi2T  = (pi2, counterT ~> churchPairT ~> pT)
    --
    cntiR = \i -> HORSRule (cnt i) ns $ var $ printf "n%i" i
    cntRs = map cntiR [1..paramDepth param]
    pairR = HORSRule pair (["x","y","f"] ++ cs) $ app (var "f") ([var "x", var "y"] ++ csTerm)
    k1R   = HORSRule k1 (["n","x","y"] ++ cs) $ app (var "x") csTerm
    k2R   = HORSRule k2 (["n","x","y"] ++ cs) $ app (var "y") $ var "n" : csTerm
    pi1R  = HORSRule pi1 ("p" : cs) $ app (var "p") $ [app (nonterminal k1) [nonterminal $ cnt 0]] ++ csTerm
    pi2R  = HORSRule pi2 ("n" : "p" : cs) $ app (var "p") $ [app (nonterminal k2) [var "n"]] ++ csTerm
    --
    ns     = genXs "n" $ paramDepth param
    cs     = genXs "c" $ paramCntPM param
    csTerm = genXsTerm "c" $ paramCntPM param

genXs :: String -> Int -> [String]
genXs x n = map (\i -> x ++ show i) [1..n]

genXsTerm :: String -> Int -> [Term]
genXsTerm x n = map var $ genXs x n