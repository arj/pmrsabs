module Term (
	Head(..), Term(App),

	app, var, terminal, nonterminal, symbol, ssToSymbol, headToTerm,
	fv, subst, subterms
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
  deriving (Eq,Ord)

instance Show a => Show (Term a) where
	show (App h []) = show h
	show (App h lst) = "(" ++ show h ++ " " ++ unwords (map show lst) ++ ")"

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

subterms :: Term a -> Set (Term a)
subterms = undefined

subst :: Var -> Term a -> Term a -> Term a
subst x v (App h@(Var y) ts)
	| x == y    = app v $ map (subst x v) ts
	| otherwise = App h $ map (subst x v) ts
subst x v (App h ts) = App h $ map (subst x v) ts