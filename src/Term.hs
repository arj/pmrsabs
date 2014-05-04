module Term (
  Head(..), Term(App), TypeBinding,

  app, var, terminal, nonterminal, symbol, ssToSymbol, headToTerm,
  fv, subst, substAll, subterms, subterms', getN,
  typeCheck
  ) where

import Sorts
import Data.Set (Set)
import Data.Char (isUpper, isLower)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M
import Control.Monad

type Var = String

data Head = Var Var
          | Nt SortedSymbol
          | T SortedSymbol
          deriving (Eq,Ord)

instance Show Head where
  show (Var x) = x
  show (Nt s)  = show s -- ++ ":" ++ show sort
  show (T  s)  = show s -- ++ ":" ++ show sort

headToTerm :: Head -> Term
headToTerm h = App h []

data Term = App Head [Term]
            | Case Int [Term] -- Only for RSFD
            | D Int -- Only for RSFD
  deriving (Eq,Ord)

instance Show Term where
  show (App h []) = show h
  show (App h lst) = "(" ++ show h ++ " " ++ unwords (map show lst) ++ ")"
  show (Case x ti) = "_case " ++ show x ++ " " ++ unwords (map show ti)
  show (D i) = show i

fv :: Term -> Set Var
fv (App (Var x) ts) = S.insert x $ S.unions $ map fv ts
fv (App _ ts) = S.unions $ map fv ts

app :: Term -> [Term] -> Term
app (App h ts1) ts2 = App h (ts1 ++ ts2)

var :: String -> Term
var x = App (Var x) []

nonterminal :: String -> Sort -> Term
nonterminal s srt = App (Nt (SortedSymbol s srt)) []

terminal :: String -> Sort -> Term
terminal s srt = App (T (SortedSymbol s srt)) []

ssToSymbol :: SortedSymbol -> Term
ssToSymbol (SortedSymbol s srt) = symbol s srt

symbol :: String -> Sort -> Term
symbol s@(c:_) srt
  | isUpper c = nonterminal s srt
  | isLower c = terminal s srt

sortOf :: Head -> Maybe Sort
sortOf (Var _)                 = Nothing
sortOf (Nt (SortedSymbol _ s)) = Just s
sortOf (T  (SortedSymbol _ s)) = Just s

subterms :: Term -> Set Term
subterms t@(App _ ts) = S.insert t $ S.unions $ map subterms ts

-- | Lists all subterms who's head is either a variable or a non-terminal.
subterms' :: Term -> Set Term
subterms' t@(App h ts) = case h of
  Var _ -> S.insert t rest
  Nt  _ -> S.insert t rest
  T   _ -> rest
  where
    rest = S.unions $ map subterms ts

getN :: Term -> Set SortedSymbol
getN t@(App (Nt a) ts) = S.insert a $ S.unions $ map getN ts
getN t@(App _      ts) = S.unions $ map getN ts

subst :: Var -> Term -> Term -> Term
subst x v (App h@(Var y) ts)
  | x == y    = app v $ map (subst x v) ts
  | otherwise = App h $ map (subst x v) ts
subst x v (App h ts) = App h $ map (subst x v) ts

substAll :: [(Var, Term)] -> Term -> Term
substAll lst term = foldl (\ack (v,t) -> subst v t ack) term lst

type TypeBinding = Map String Sort

typeCheck :: Monad m => TypeBinding -> Term -> m Sort
typeCheck bnd t@(App smb ts) = do
  srt <- getSort smb
  if length ts > ar srt then
    fail ("Symbol " ++ show smb ++ " has arity " ++ show (ar srt) ++
      " but is applied to " ++ show (length ts) ++ " arguments")
  else do
    typesTs <- mapM (typeCheck bnd) ts
    let expTypes = sortToList srt
    forM_ (zip expTypes typesTs) $ \(t1,t2) -> do
      if t1 == t2
        then return ()
        else fail ("A subterm of " ++ show t ++ " should have type " ++ show t1 ++ " but has type " ++ show t2 ++
          "\nType environment: " ++ show bnd ++
          "\nExp types: " ++ show expTypes ++
          "\nInf types: " ++ show typesTs)
    return $ sortFromList $ drop (1 + length ts) expTypes
  where
    getSort (Var x) = maybe (fail ("Unknown variable " ++ show x)) return $ M.lookup x bnd
    getSort s       = maybe (fail ("Cannot get sort of " ++ show s)) return $ sortOf s
