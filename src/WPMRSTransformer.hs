module WPMRSTransformer
where

import GHC.Base (assert)
--import Data.Map (Map)
import qualified Data.Map as M
import Text.Printf (printf)

import Term (var, app, nonterminal)
import Sorts ((~>),createSort,RankedAlphabet)
import PMRS (PMRS)
import HORS (HORS(..), HORSRule(..))

fromHORS :: HORS -> PMRS
fromHORS (HORS t n rs s) = assert False undefined

---

-- |Creates the auxilliary rules that are needed
-- for church encoding pairs, pattern matching and natural numbers
-- up to cntDepth.
auxRules :: String -> Int -> Int -> (RankedAlphabet, [HORSRule])
auxRules prefix cntDepth cntPM = (ra, rs)
  where
  	ra = M.fromList $ cntTs ++ [pairT, k1T, k2T, pi1T, pi2T]
  	rs = cntRs ++ [pairR,k1R,k2R,pi1R,pi2R]
  	--
  	cnt :: Int -> String
  	cnt i = prefix ++ "Cnt" ++ show i
  	pair = prefix ++ "Pair"
  	k1   = prefix ++ "K1"
  	k2   = prefix ++ "K2"
  	pi1  = prefix ++ "Pi1"
  	pi2  = prefix ++ "Pi2"
  	--
  	counterT    = createSort cntDepth -- church encoded nat up to n
  	pT          = createSort cntPM
  	churchPairT = (pT ~> (counterT ~> pT) ~> pT) ~> pT
  	kT          = counterT ~> pT ~> (counterT ~> pT) ~> pT
  	--
  	cntTs = map (\i -> (cnt i, counterT)) [1..cntDepth]
  	pairT = (pair, pT ~> (counterT ~> pT) ~> churchPairT)
  	k1T   = (k1, kT)
  	k2T   = (k2, kT)
  	pi1T  = (pi1, churchPairT ~> pT)
  	pi2T  = (pi2, counterT ~> churchPairT ~> pT)
  	--
  	cntiR = \i -> HORSRule (cnt i) ns $ var $ printf "n%i" i
  	cntRs = map cntiR [1..cntDepth]
  	pairR = HORSRule pair (["x","y","f"] ++ cs) $ app (var "f") ([var "x", var "y"] ++ csTerm)
  	k1R   = HORSRule k1 (["n","x","y"] ++ cs) $ app (var "x") csTerm
  	k2R   = HORSRule k2 (["n","x","y"] ++ cs) $ app (var "y") $ var "n" : csTerm
  	pi1R  = HORSRule pi1 ("p" : cs) $ app (var "p") $ [app (nonterminal k1) [nonterminal $ cnt 0]] ++ csTerm
  	pi2R  = HORSRule pi2 ("n" : "p" : cs) $ app (var "p") $ [app (nonterminal k2) [var "n"]] ++ csTerm
  	--
  	ns     = map (printf "n%i") [1..cntDepth]
  	cs     = map (printf "c%i") [1..cntPM]
  	csTerm = map var cs