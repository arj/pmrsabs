module Term (
	Head(..), Term(App),

	app, var, terminal, nonterminal, symbol, ssToSymbol, headToTerm,
	fv, subst, substAll, subterms, subterms', getN
	) where

import Sorts
import Data.Set(Set)
import Data.Char (isUpper, isLower)
import qualified Data.Set as S

type Var = String

data Head a = Var Var
          | Nt (SortedSymbol a)
          | T (SortedSymbol a)
          deriving (Eq,Ord)

instance Show a => Show (Head a) where
	show (Var x) = x
	show (Nt (SortedSymbol s _)) = s -- ++ ":" ++ show sort
	show (T  (SortedSymbol s _))  = s -- ++ ":" ++ show sort

headToTerm :: Head a -> Term a
headToTerm h = App h []

data Term a = App (Head a) [Term a]
            | Case Int [Term a] -- Only for RSFD
            | D Int -- Only for RSFD
  deriving (Eq,Ord)

instance Show a => Show (Term a) where
	show (App h []) = show h
	show (App h lst) = "(" ++ show h ++ " " ++ unwords (map show lst) ++ ")"
	show (Case x ti) = "_case " ++ show x ++ " " ++ unwords (map show ti)
	show (D i) = show i

fv :: Term a -> Set Var
fv (App (Var x) ts) = S.insert x $ S.unions $ map fv ts
fv (App _ ts) = S.unions $ map fv ts

app :: Term a -> [Term a] -> Term a
app (App h ts1) ts2 = App h (ts1 ++ ts2)

var :: String -> Term a
var x = App (Var x) []

nonterminal :: String -> Sort a -> Term a
nonterminal s srt = App (Nt (SortedSymbol s srt)) []

terminal :: String -> Sort a -> Term a
terminal s srt = App (T (SortedSymbol s srt)) []

ssToSymbol :: SortedSymbol a -> Term a
ssToSymbol (SortedSymbol s srt) = symbol s srt

symbol :: String -> Sort a -> Term a
symbol s@(c:_) srt
  | isUpper c = nonterminal s srt
  | isLower c = terminal s srt

subterms :: Ord a => Term a -> Set (Term a)
subterms t@(App _ ts) = S.insert t $ S.unions $ map subterms ts

-- | Lists all subterms who's head is either a variable or a non-terminal.
subterms' :: Ord a => Term a -> Set (Term a)
subterms' t@(App h ts) = case h of
	Var _ -> S.insert t rest
	Nt  _ -> S.insert t rest
	T   _ -> rest
  where
  	rest = S.unions $ map subterms ts

getN :: Ord a => Term a -> Set (SortedSymbol a)
getN t@(App (Nt a) ts) = S.insert a $ S.unions $ map getN ts
getN t@(App _      ts) = S.unions $ map getN ts

subst :: Var -> Term a -> Term a -> Term a
subst x v (App h@(Var y) ts)
	| x == y    = app v $ map (subst x v) ts
	| otherwise = App h $ map (subst x v) ts
subst x v (App h ts) = App h $ map (subst x v) ts

substAll :: [(Var, Term a)] -> Term a -> Term a
substAll lst term = foldl (\ack (v,t) -> subst v t ack) term lst