module WPMRSTransformer
where

import GHC.Base (assert)
import Data.Map (Map)
import qualified Data.Map as M
import Text.Printf (printf)

import Term (var, app, nonterminal, terminal, Term)
import Sorts ((~>),createSort,RankedAlphabet,Symbol,Sort(Base))
import PMRS (PMRS)
import HORS (HORS(..), HORSRule(..))

fromHORS :: HORS -> PMRS
fromHORS (HORS t n rs s) = assert False undefined

---

data Param = Param { paramDepth :: Int
                   , paramCntPM :: Int
                   , paramPrefix :: String
                   }

idPair :: Symbol
idPair = "Pair"

allRulesForTerminals :: Param -> RankedAlphabet -> (Term -> Int) -> (RankedAlphabet, [HORSRule])
allRulesForTerminals param ra pm = foldl f (ra0, rs0) $ M.toList ra
  where
    (ra0, rs0) = auxRules param
    --
    f (raAck, rsAck) (k,srt) =
      let (ra', rs') = terminalRules param k srt pm in
      ((M.union raAck ra'), rsAck ++ rs')

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
    cs     = map (printf "c%i") [1..paramCntPM param]
    csTerm = map var cs
    --
terminalRules param k ksrt pm = assert False undefined

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
    ns     = map (printf "n%i") [1..paramDepth param]
    cs     = map (printf "c%i") [1..paramCntPM param]
    csTerm = map var cs