module Automaton

where

import Data.List
import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Set as S
import Text.Printf (printf)

import Aux
import Sorts

type State = String
type Delta = Map (State, Symbol) [State]

data ATT = ATT Delta State

mkATT :: Delta -> State -> ATT
mkATT d q0 = ATT d q0

instance PrettyPrint ATT where
  prettyPrint att = "%BEGINA\n" ++ show att ++ "\n%ENDA"

showRules :: Delta -> String
showRules delta = intercalate "\n" $ map f $ M.toList delta
  where
  	f ((q,s),qs) = printf "%s %s -> %s." q s (showQs qs)
  	showQs qs = intercalate " " qs 

-- | Extract the set of states used in the automaton
attStates :: ATT -> [State]
attStates (ATT delta state) = S.toList states
  where
  	states = deltaStates `S.union` S.singleton state
  	deltaStates = foldl f S.empty $ M.toList delta
  	--
  	f ack ((q,_),qs) = S.unions [S.fromList qs, S.singleton q, ack] 

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
attTransition :: ATT -> Symbol -> State -> Maybe [State]
attTransition (ATT delta _) t q = M.lookup (q,t) delta

attAddBr :: Symbol -> ATT -> ATT
attAddBr br (ATT delta q0) = ATT delta' q0
  where
    delta'  = delta `M.union` brDelta
    brDelta = M.fromList $ map (\q -> ((q,br), [q,q])) qs
    --
    qs = S.toList $ foldl f S.empty $ M.toList delta
    f ack ((q,_),_) = S.insert q ack