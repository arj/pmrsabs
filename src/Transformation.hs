module Transformation where

import RSFD
import PMRS
import Term
import Sorts 

import Data.Map (Map)
import qualified Data.Map as M

import Data.Set (Set)
import qualified Data.Set as S

import Data.MultiMap (MultiMap)
import qualified Data.MultiMap as MM

type Patterns = Set Term

patternDomain :: PMRS -> Patterns
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

maxHeight :: Patterns -> Int
maxHeight = maximum . map height . S.toList

wPMRStoRSFD :: Monad m => PMRS -> m RSFD
wPMRStoRSFD _ = mkRSFD t nt M.empty rules "$S"
    where
      pair = RSFDRule "$Pair" ["x","y","f"] (app (var "f") [var "x", var "y"])
      k1   = RSFDRule "$K1" ["n","c","x1","x2"] (var "x1")
      k2   = RSFDRule "$K2" ["n","c","x1","x2"] (app (var "x2") [var "n", var "c"])
      pi1  = RSFDRule "$Pi1" ["p"] (app (var "p") [app (nonterminal "$K1") [derr, nonterminal "$Cerr"]])
      pi2  = RSFDRule "$Pi2" ["p", "n", "c"] (app (var "p") [app (nonterminal "$K2") [var "n", var "c"]])
      pi2i = RSFDRule "$Pi2i" ["p", "c"] (app (var "p") [app (nonterminal "$K2") [D 5, var "c"]]) -- Replace 5 with real value
      cerr = RSFDRule "$Cerr" ["d"] (terminal "$err")
      lift = RSFDRule "$Lift" ["c", "f", "d"] (app (var "c") [var "d", var "f"])
      d    = RSFDRule "$D" ["d", "n", "c"] (app (var "c") [var "d"])
      terr = RSFDRule "$Terr" ["f"] (app (nonterminal "$Pair") [terminal "$err", (app (nonterminal "$D") [derr]), var "f"])
      --
      derr = D 10


      --
      t  = M.fromList [("$err", o)]
      nt = M.fromList [("$Pair", o ~> tsetter ~> tpair)
                      ,("$K1", Data ~> tcont ~> o ~> tsetter ~> o)
                      ,("$K2", Data ~> tcont ~> o ~> tsetter ~> o)
                      ,("$Pi1", tpair ~> o)
                      ,("$Pi2", tpair ~> Data ~> tcont ~> o)
                      ,("$Pi2i", tpair ~> tcont ~> o)
                      ,("$Cerr", tcont)
                      ,("$Lift", (Data ~> tpair) ~> (o ~> tsetter ~> o) ~> tcont)
                      ,("$D", Data ~> tsetter)
                      ,("$Terr", tpair)
                      ]
      --
      tsetter = Data ~> tcont ~> o
      tcont = Data ~> o
      tpair = (o ~> tsetter ~> o) ~> o
      rules = mkRSFDRules [pair, k1, k2, pi1, pi2, pi2i, cerr, lift, d, terr]
