{-# LANGUAGE TypeSynonymInstances,FlexibleInstances #-}
module HORS where

import Control.Monad
import Data.Maybe (isNothing)

import qualified Data.Map as M
import qualified Data.MultiMap as MM

import Text.Printf (printf)

import Term
import Sorts
import CommonRS
import Automaton


data HORSRule = HORSRule Symbol [String] Term
	deriving (Eq,Ord)

type HORSRules = Rules HORSRule

instance Show HORSRule where
  show (HORSRule f xs body) = unwords $ filter (not . null) [show f, unwords xs,"=>",show body]

horsRules :: [HORSRule] -> HORSRules
horsRules lst = MM.fromList $ map fPairUp lst
  where
    fPairUp r@(HORSRule f _ _) = (f,r)

data HORS = HORS RankedAlphabet RankedAlphabet HORSRules Symbol

mkHORS :: Monad m => RankedAlphabet -> RankedAlphabet -> HORSRules -> Symbol -> m HORS
mkHORS t nt rs s = do
  let rules = concat $ MM.elems rs
  forM_ rules $ \r@(HORSRule _ _ b) -> do
    let bnd = M.unions [t, nt]
    srt <- typeCheck bnd $ b
    if srt == o
      then return ()
      else fail ("The body of the rule " ++ show r ++ " is not of sort o but of sort " ++ show srt)
  when (not $ MM.member rs s) $ fail ("No rule for the start symbol: " ++ show s)
  return $ HORS t nt rs s

brFold :: Symbol -> [Term] -> Term
brFold br ts = foldl1 (\ack t -> app (terminal br) [t, ack]) ts

-- | Given a branching symbol and a list of rules
-- returns the variable adjusted branching term that
-- is the deterministic version of all the rule bodies.
det :: Symbol -> [HORSRule] -> HORSRule
det _ [a] = a
det br rules@((HORSRule f xs _):_) = HORSRule f xs t'
  where
    t' = brFold br $ map extract rules
    xsTerm = map var xs
    extract (HORSRule _ ys t) = substAll (zip ys xsTerm) t


-- | Create a deterministic HORS by introducing
-- a br terminal symbol for branches.
determinizeHORS :: Monad m => HORS -> m HORS
determinizeHORS (HORS t nt rs s) = mkHORS t' nt (MM.fromMap res) s
  where
    br  = "br__br"
    t'  = M.insert br (o ~> o ~> o) t
    res = M.map (\rules -> [det br rules]) $ MM.toMap rs

type Path = [(Symbol, Int)]

-- | A configuration consists of the current term, state of the automaton and path
-- in the tree (as an automaton may eat terminal heads!)
data Config = Config Term State Path

instance Show Config where
  show (Config t s p) = printf "(%s,%s,%s)" (show t) s (show p)

-- | Initial configuration node.
initialCfg :: HORS -> ATT -> Config
initialCfg (HORS _ _ _ s) (ATT _ q0) = Config (nonterminal s) q0 []

-- | Extracts a counterexample for a given deterministic HORS
-- and automaton. This only works if there IS a counterexample.
-- Otherwise this function DOES NOT TERMINATE.
findCEx :: HORS -> ATT -> Path
findCEx hors att =
  funCExFix hors att [initialCfg hors att]

funCExFix :: HORS -> ATT -> [Config] -> Path
funCExFix hors att cfgs =
  let result = fullStep hors att cfgs in
  case result of
    Left path -> reverse path
    Right cfgs' -> funCExFix hors att cfgs'

-- | One configuration step. Must be deterministic!
stepReduction :: HORS -> Config -> Config
stepReduction h c@(Config t q p) =
  case t of
    App (Nt n) ts -> Config (reduce h (n,ts)) q p
    _ -> c

fullStep :: HORS -> ATT -> [Config] -> Either Path [Config]
fullStep hors att cfgs = fmap concat $ mapM f cfgs
  where
    f :: Config -> Either Path [Config]
    f cfg = stepAutomaton att $ stepReduction hors cfg

-- | Given an automaton and a configuration returns
-- a list of configurations that describe the automaton splits
-- if the head symbol of the configuration is a terminal.
-- (a t1 ... tn, q, p) --> [(t1, q1, p.1),...,(tn, qn, p.n)]
stepAutomaton :: ATT -> Config -> Either Path [Config]
stepAutomaton att c@(Config t q p) =
  case t of
    -- is it a terminal head?
    App (T s) ts ->
      let maybeQs = attTransition att s q in
      case maybeQs of
        Just qs -> return $ zipWith3 (\ti qi i -> Config ti qi ((s,i) : p)) ts qs [1..]
        Nothing -> Left p
    _ -> return $ [c]

-- | Given a set of rules and a term of the form (F t1 ... tn)
-- the function returns the set of terms that it can be reduced to.
-- The set might be empty!
reduce :: HORS -> (Symbol,[Term]) -> Term
reduce (HORS _ _ rs _) (s,ts) =
  case matchingRules rs s of
    [r] -> applyRule ts r
    []  -> error "Error in HORS: no reduction possible"
    _   -> error "Nondeterministic HORS"

-- | Given a rule and a list of arguments
-- applies the rule.
applyRule :: [Term] -> HORSRule -> Term
applyRule ts (HORSRule _ xs t) = substAll (zip xs ts) t
