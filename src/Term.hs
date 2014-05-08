{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Term (
  Head(..), Term(..), TypeBinding,

  app, var, terminal, nonterminal, symbol, sToSymbol, ssToSymbol, headToTerm,
  fv, subst, substAll, subterms, subterms', getN, replaceVarsBy,
  replaceNt, replaceNtMany, typeCheck, caseVars, height,

  isMatching, isMatchingErr, runM, runIsMatching
  ) where

import Aux
import Sorts
import Data.Set (Set)
import Data.Char (isUpper, isLower)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M
import Control.Monad
import Control.Monad.Error

type Var = String

data Head = Var Var
          | Nt String
          | T String
          deriving (Eq,Ord)

instance Show Head where
  show (Var x) = x
  show (Nt s)  = s -- ++ ":" ++ show sort
  show (T  s)  = s -- ++ ":" ++ show sort

headToTerm :: Head -> Term
headToTerm h = App h []

data Term = App Head [Term]
            | Case String [Term] -- Only for RSFD
            | D Int -- Only for RSFD
  deriving (Eq,Ord)

instance Show Term where
  show (App h []) = show h
  show (App h lst) = "(" ++ show h ++ " " ++ unwords (map show lst) ++ ")"
  show (Case x ti) = "_case " ++ x ++ " " ++ unwords (map show ti)
  show (D i) = show i

fv :: Term -> Set Var
fv (App (Var x) ts) = S.insert x $ S.unions $ map fv ts
fv (App _ ts)       = S.unions $ map fv ts
fv (Case _ ts)      = S.unions $ map fv ts
fv (D _)            = S.empty

app :: Term -> [Term] -> Term
app (App h ts1) ts2 = App h (ts1 ++ ts2)

var :: String -> Term
var x = App (Var x) []

nonterminal :: String -> Term
nonterminal s = App (Nt s) []

terminal :: String -> Term
terminal s = App (T s) []

ssToSymbol :: SortedSymbol -> Term
ssToSymbol (SortedSymbol s _) = symbol s

sToSymbol :: Symbol -> Term
sToSymbol s = symbol s

symbol :: String -> Term
symbol s@(c:_)
  | isUpper c = nonterminal s
  | isLower c = terminal s

--sortOf :: Head -> Maybe Sort
--sortOf (Var _)                 = Nothing
--sortOf (Nt (SortedSymbol _ s)) = Just s
--sortOf (T  (SortedSymbol _ s)) = Just s

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

getN :: Term -> Set Symbol
getN (App (Nt a) ts) = S.insert a $ S.unions $ map getN ts
getN (App _      ts) = S.unions $ map getN ts

subst :: Var -> Term -> Term -> Term
subst x v (App h@(Var y) ts)
  | x == y    = app v $ map (subst x v) ts
  | otherwise = App h $ map (subst x v) ts
subst x v (App h ts) = App h $ map (subst x v) ts

substAll :: [(Var, Term)] -> Term -> Term
substAll lst term = foldl (\ack (v,t) -> subst v t ack) term lst

replaceVarsBy :: String -> Term -> Term
-- ^ replaceVarsBy "_" t replaces all variables with "_".
replaceVarsBy x (App (Var _) ts) = App (Var x) $ map (replaceVarsBy x) ts
replaceVarsBy x (App t       ts) = App t       $ map (replaceVarsBy x) ts

type TypeBinding = Map String Sort

typeCheck :: Monad m => TypeBinding -> Term -> m Sort
typeCheck _   t@(Case _ []) = fail ("Case statement has no body: " ++ show t)
typeCheck bnd t@(Case x ts) = do
  let typeX = bnd M.! x
  when (typeX /= Data) $ fail ("In term " ++ show t ++ " the case variable must be of type d, but it is of type " ++ show typeX ++ " Binding: " ++ show bnd)
  typeTs <- mapM (typeCheck bnd) ts
  when (not $ allTheSame typeTs) $ fail ("In term " ++ show t ++ " the different branches have different types, namely: " ++ show typeTs)
  return $ head typeTs
typeCheck _     (D _)        = return Data
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
    getSort (Var x) = maybe (fail ("Unknown variable " ++ show x  )) return $ M.lookup x bnd
    --getSort s = maybe (fail ("Cannot get sort of " ++ show s)) return $ --sortOf s
    getSort s@(Nt f ) = maybe (fail ("Cannot get sort of " ++ show s ++ " bnd:" ++ show bnd)) return $ M.lookup f bnd
    getSort s@(T  f ) = maybe (fail ("Cannot get sort of " ++ show s ++ " bnd:" ++ show bnd)) return $ M.lookup f bnd

-- | Replaces nonterminals, i.e. call a function for each nonterminal and
-- providing its arguments and create a new term instead.
replaceNt :: (Symbol -> [Term] -> Term) -> Term -> Term
replaceNt f term = head $ replaceNtMany (\s t -> [f s t]) term

-- | Replaces nonterminals, i.e. call a function for each nonterminal and
-- providing its arguments and create a new term instead.
replaceNtMany :: (Symbol -> [Term] -> [Term]) -> Term -> [Term]
replaceNtMany f (App (Nt s) ts) = [ app h res | h <- (f s ts), res <- map (replaceNtMany f) ts]
replaceNtMany f (App h      ts) = [ App h res | res <- map (replaceNtMany f) ts]

caseVars :: Term -> Set String
-- ^ Returns all variables that are used in a case expression.
caseVars (App _ ts ) = S.unions $ map caseVars ts
caseVars (D _      ) = S.empty
caseVars (Case x ts) = S.insert x $ S.unions $ map caseVars ts

height :: Term -> Int
-- ^ /O(n)/ Returns the height of a term.
height (App _ ts ) = succ $ maximum $ 0 : map height ts
height (Case _ ts) = succ $ maximum $ 0 : map height ts
height (D _      ) = 1

-- | Checks if a given pattern is matched by a term.
-- The pattern may only consist of variables and terminal
-- symbols. The term may only consist of terminal symbols.
isMatching :: Term -> Term -> Maybe [(String,Term)]
isMatching (App (Var x) [] ) t@(App (T _ ) _  ) = return [(x,t)]
isMatching (App (T f1 ) ts1)   (App (T f2) ts2) =
  if f1 /= f2
    then Nothing
    else do
      bnd <- mapM (uncurry isMatching) (zip ts1 ts2)
      return $ concat bnd
isMatching p _ = error (show p ++ " is no valid pattern") -- TODO Use ErrorT instead of Error!

---------------------------------------------------------
---------------------------------------------------------
---------------------------------------------------------

data MatchingError = MEInvalidPattern Term
                   | MEUndefined String
                   deriving (Show)

instance Error MatchingError where
  noMsg  = MEUndefined ""
  strMsg = MEUndefined

newtype Matcher a = M {
  runM :: ErrorT MatchingError Maybe a
} deriving (Monad, MonadError MatchingError)

-- | Checks if a given pattern is matched by a term.
-- The pattern may only consist of variables and terminal
-- symbols. The term may only consist of terminal symbols.
isMatchingErr :: Term -> Term -> Matcher [(String,Term)]
isMatchingErr (App (Var x) [] ) t@(App (T _ ) _  ) = return [(x,t)]
isMatchingErr (App (T f1 ) ts1)   (App (T f2) ts2) =
  if f1 /= f2
    then M (lift Nothing)
    else do
      bnd <- mapM (uncurry isMatchingErr) (zip ts1 ts2)
      return $ concat bnd
isMatchingErr p _ = throwError (MEInvalidPattern p)

runIsMatching :: Matcher a -> Either MatchingError (Maybe a)
runIsMatching m = case runErrorT (runM m) of
                    (Just (Left  r)) -> Left  r
                    (Just (Right r)) -> Right (Just r)
                    (Nothing)        -> Right Nothing