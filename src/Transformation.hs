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

data DataMap = DataMap { dmErr  :: Term
                       , dmNum  :: Int -> Term
                       , dmCtxt :: Term -> Term
                       , dmNumCount  :: Int
                       , dmCtxts :: [Term]
                       }

createCases :: (Term -> Term) -> DataMap -> (Int -> Term) -> (Term -> Term) -> [Term]
createCases wrapper dm intRes ctxtRes = [wrapper (dmErr dm)] ++ intcases ++ termcases
  where
    intcases  = map intRes [1..dmNumCount dm]
    termcases = map ctxtRes $ dmCtxts dm


wPMRStoRSFD :: Monad m => PMRS -> m RSFD
wPMRStoRSFD pmrs = mkRSFD t nt M.empty rules "HS"
    where
      pair = RSFDRule "HPair" ["x","y","f"] (app (var "f") [var "x", var "y"])
      k1   = RSFDRule "HK1" ["n","c","x1","x2"] (var "x1")
      k2   = RSFDRule "HK2" ["n","c","x1","x2"] (app (var "x2") [var "n", var "c"])
      pi1  = RSFDRule "HPi1" ["p"] (app (var "p") [app (nonterminal "HK1") [derr, nonterminal "HCerr"]])
      pi2  = RSFDRule "HPi2" ["p", "n", "c"] (app (var "p") [app (nonterminal "HK2") [var "n", var "c"]])
      pi2i = RSFDRule "HPi2i" ["p", "c"] (app (var "p") [app (nonterminal "HK2") [dnumber maxheight, var "c"]]) -- Replace 5 with real value
      cerr = RSFDRule "HCerr" ["d"] (terminal "herr")
      lift = RSFDRule "HLift" ["c", "f", "d"] (app (var "c") [var "d", var "f"])
      d    = RSFDRule "HD" ["d", "n", "c"] (app (var "c") [var "d"])
      terr = RSFDRule "HTerr" ["f"] (app (nonterminal "HPair") [terminal "herr", (app (nonterminal "HD") [derr]), var "f"])
      s    = RSFDRule "HS" [] (app (nonterminal "HPi1") [nonterminal "S"])
      --

      --
      t  = M.fromList [("herr", o)] `M.union` getTerminals pmrs
      fix_nt = M.fromList [("HPair", o ~> tsetter ~> tpair)
                      ,("HK1", Data ~> tcont ~> o ~> tsetter ~> o)
                      ,("HK2", Data ~> tcont ~> o ~> tsetter ~> o)
                      ,("HPi1", tpair ~> o)
                      ,("HPi2", tpair ~> Data ~> tcont ~> o)
                      ,("HPi2i", tpair ~> tcont ~> o)
                      ,("HCerr", tcont)
                      ,("HLift", (Data ~> tpair) ~> (o ~> tsetter ~> o) ~> tcont)
                      ,("HD", Data ~> tsetter)
                      ,("HTerr", tpair)
                      ,("HS", o)
                      ,("S", tpair) -- Remove
                      ]
      tk_nt = M.unions $ map createNTforT $ M.toList $ getTerminals pmrs
      tk_rules = concat $ map (createRulesForT dm) $ M.toList $ getTerminals pmrs
      --
      nt = tk_nt `M.union` fix_nt
      --
      rules = mkRSFDRules $ [pair, k1, k2, pi1, pi2, pi2i, cerr, lift, d, terr, s] ++ tk_rules
      --
      maxheight = 5
      -- The mapping is:
      -- error -> D 0
      -- numbers up to n -> D 1 --> D n
      -- contexts -> D n+1 ... D ||p||+n+1
      dctxt :: Term -> Term
      dctxt t = D 6
      --
      dnumber :: Int -> Term
      dnumber n = D n
      --
      derr :: Term
      derr = D 0
      --
      dm = DataMap derr dnumber dctxt 5 [terminal "herr"] -- TODO Fix number and contexts

tsetter :: Sort
tsetter = Data ~> tcont ~> o

tcont :: Sort
tcont = Data ~> o

tpair :: Sort
tpair = (o ~> tsetter ~> o) ~> o

mkPair :: Term -> Term -> Term -> Term
mkPair x y f = app (nonterminal "HPair") [x,y,f]

mkPi1 :: Term -> Term
mkPi1 t = app (nonterminal "HPi1") [t]

mkPi2 :: Term -> Term -> Term -> Term
mkPi2 p n c = app (nonterminal "HPi2") [p,n,c] 

mkD :: Term -> Term
mkD d = app (nonterminal "HD") [d]

createNTforT :: (Symbol, Sort) -> RankedAlphabet
createNTforT (k,Base) = M.singleton (tk k) tpair
createNTforT (k,srt)  = ra
  where
    n   = ar srt
    ra  = M.fromList $ [tk0, tk1] ++ tki ++ [tkcase]
    stk = tk k
    tk0 = (stk, sortFromList $ replicate (n+1) tpair)
    tk1 = (stk ++ "_1", sortFromList $ replicate n tpair ++ [tsetter])
    tki = map mkTki $ [2..n]
    mkTki i = let tp = sortFromList $ [Data] ++ replicate (n-i+1) tpair ++ [tcont] ++ replicate (i-1) Data ++ [o] in
              (stk ++ "_" ++ show i, tp)
    tkcase = (stk ++ "_case", sortFromList $ [tcont] ++ replicate n Data ++ [o])

createParamList :: Int -> [String]
createParamList n = zipWith pairUp (repeat "x") [1..n]
  where
    pairUp x i = x ++ show i

tk :: String -> String
tk k = "HT_" ++ k

createRulesForT :: DataMap -> (Symbol, Sort) -> [RSFDRule]
createRulesForT dm (k,Base) = return $ RSFDRule (tk k) ["f"] (mkPair (sToSymbol k) (dmCtxt dm (terminal k)) (var "f"))
createRulesForT dm (k,srt)  = rules
  where
    rules = [tk0,tk1] ++ tki ++ tkn ++ [tkcase]
    n     = ar srt
    stk   = tk k
    cont d = app (var "c") [d]
    conte = const (cont $ dmErr dm)
    --
    tk0     = RSFDRule stk (tk0xs ++ ["f"]) tk0body
    tk0xs   = createParamList n
    tk0body = mkPair tk0left tk0right (var "f")
    tk0left = app (terminal k) $ map (mkPi1 . var) tk0xs
    tk0right = app (nonterminal (stk ++ "_1")) $ map var tk0xs
    --
    tk1     = RSFDRule (stk ++ "_1") tk1xs tk1body
    tk1xs   = tk0xs ++ ["m","c"]
    tk1body = mkCase "m" $ createCases cont dm tk1numbers conte
    --
    tk1numbers :: Int -> Term
    tk1numbers 1 = cont $ (dmCtxt dm) (terminal k)
    tk1numbers m = let m' = dmNum dm (m-1) in
                   let x2_xn = map var $ tail tk0xs in
                   let body = if n == 1
                              then app (nonterminal $ stk ++ "_case") [var "c"]
                              else app (nonterminal $ stk ++ "_2") ([m'] ++ x2_xn ++ [var "c"])
                   -- We know that there is at least one, because
                   -- there is a case checking whether the sort is base (which
                   -- corresponds to arity 0)
                   in mkPi2 (var "x1") m' body
    --
    tki     = []
    --
    tkn     = if n == 1
              then []
              else return $ RSFDRule (stk ++ "_" ++ show n) tknxs tknbody
    tknxs   = ["m", tkn_xn, "c"] ++ tkndis
    tkndis  = map (\i -> "d" ++ show i) [1..n-1]
    tkn_xn  = "x" ++ show n
    tknbody = let c = (app (nonterminal $ stk ++ "_case") $ [var "c"] ++ map var tkndis) in
              mkPi2 (var tkn_xn) (var "m") c
    --
    tkcase     = RSFDRule (stk ++ "_case") tkcasexs tkcasebody
    tkcasexs   = ["c"] ++ map (\i -> "d" ++ show i) [1..n]
    tkcasebody = cont $ dmErr dm -- TODO Do real case distinction.
