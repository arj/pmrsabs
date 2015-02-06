module Automaton (
  ATT(..),
  State,
  mkATT,
  attTransition,
  PrettyPrint(..),
  attStates,
  Quantifier(..),
  attAddBr
) where

import Data.List
import Data.MultiMap (MultiMap)
import qualified Data.MultiMap as M
import Data.Set (Set)
import qualified Data.Set as S
import Text.Printf (printf)

import Aux
import Sorts

type State = String
type Delta = MultiMap (State, Symbol) (Set (Int,State))

data ATT = ATT Delta State

mkATT :: Delta -> State -> ATT
mkATT d q0 = ATT d q0

instance PrettyPrint ATT where
  prettyPrint att = "%BEGINA\n" ++ show att ++ "\n%ENDA"

-- | Give string representations of transitions for the ATT.
showRules :: Delta -> String
showRules delta = intercalate "\n" $ map f $ M.toList delta
  where
    f ((q,s),qs) = printf "%s %s -> %s." q s (showQs qs)
    showQs qs = intercalate " " $ map (uncurry $ printf "(%i,%s)") $ S.toList qs

-- | Extract the set of states (as a list, but no doubles guaranteed)
-- used in the automaton.
attStates :: ATT -> [State]
attStates (ATT delta state) = S.toList states
  where
    states = deltaStates `S.union` S.singleton state
    deltaStates = foldl f S.empty $ M.toList delta
    --
    f ack ((q,_),qs) = S.unions [S.map snd qs, S.singleton q, ack]

instance Show ATT where
  show (ATT delta q0) =
    let (delta1, delta2) = M.partitionWithKey (\(q,_) _ -> q == q0) delta in
    let d1string = showRules delta1 in
    let d2string = showRules delta2 in
    case d2string of
      [] -> d1string
      _  -> d1string ++ "\n" ++ d2string

-- | Given an ATT, a symbol and a state returns the next states
-- of the automaton if there is a transition.
attTransition :: ATT -> Symbol -> State -> [[(Int, State)]]
attTransition (ATT delta _) t q = map S.toList $ M.lookup (q,t) delta

data Quantifier = Existential
                | Universal

-- | Adds a branching symbol for every state in the automaton.
-- If the quantifier is existential, then
-- all nondeterministic paths must be true
-- otherwise only one (real nondeterminism).
attAddBr :: Quantifier -> Symbol -> ATT -> ATT
attAddBr quantifier br att@(ATT delta q0) = ATT delta' q0
  where
    delta'  = delta `M.union` brDelta
    brDelta = M.unions $ map addBr qs
    qs = attStates att
    --
    addBr :: State -> MultiMap (State, Symbol) (Set (Int,State))
    addBr q = case quantifier of
      Universal -> M.singleton (q,br) $ S.fromList [(1,q),(2,q)]
      Existential -> M.fromList [((q,br), S.singleton (1,q)), ((q,br), S.singleton (2,q))]
