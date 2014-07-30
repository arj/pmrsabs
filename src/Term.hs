{-# LANGUAGE GeneralizedNewtypeDeriving, BangPatterns #-}

module Term (
  Head(..), Term(..), TypeBinding, Var,

  app,var, mkCase, terminal, nonterminal, symbol, sToSymbol, ssToSymbol, headToTerm,
  fv, fv', subst, substAll, substTerminal, subterms, subterms', getN, replaceVarsBy,
  typeCheck, caseVars, height, maxHeight, heightCut, terminalSigma,

  isTerminalHead, isNTHead, prefixTerms,
  isUsingCase, isUsingD, isNotContainingN,
  isMatching, isMatchingErr,

  runM, runIsMatching, pNtHead, ntCut, trees, trees'
  ) where

import Data.List
import Data.Set (Set)
import Data.Char (isUpper, isLower)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M
import Control.Monad
import Control.Monad.Error

import Aux
import Sorts

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
  show (Case x ti) = "(_case " ++ show (length ti) ++ " " ++ x ++ " " ++ unwords (map show ti) ++ ")"
  show (D i) = show i

fv :: Term -> Set Var
fv (App (Var x) ts) = S.insert x $ S.unions $ map fv ts
fv (App _ ts)       = S.unions $ map fv ts
fv (Case _ ts)      = S.unions $ map fv ts
fv (D _)            = S.empty

fv' :: Term -> [Var]
fv' = S.toList . fv

app :: Term -> [Term] -> Term
app (App h ts1) ts2 = App h (ts1 ++ ts2)

var :: String -> Term
var x = App (Var x) []

mkCase :: String -> [Term] -> Term
mkCase s ts = Case s ts

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

prefixTerms :: String -> Term -> Set Term
prefixTerms v (App h ts) = S.insert (App h ts') $ S.unions $ map (prefixTerms v) ts
  where
    ts' = replicate (length ts) $ var v

pNtHead :: Term -> Bool
pNtHead (App (Nt _) _) = True
pNtHead _              = False

getN :: Term -> Set Symbol
getN (App (Nt a) ts) = S.insert a $ S.unions $ map getN ts
getN (App _      ts) = S.unions $ map getN ts

isTerminalHead :: Term -> Bool
isTerminalHead (App (T _) _) = True
isTerminalHead _             = False

isNTHead :: Term -> Bool
isNTHead (App (Nt _) _) = True
isNTHead _             = False

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

substTerminal :: Symbol -> Term -> Term -> Term
substTerminal k tk (App h@(T k') ts)
  | k == k'    = app tk $ map (substTerminal k tk) ts
  | otherwise = App h $ map (substTerminal k tk) ts
substTerminal k tk (App h ts) = App h $ map (substTerminal k tk) ts

-- | Checks whether the term contains a case expression.
isUsingCase :: Term -> Bool
isUsingCase (App _ ts) = any isUsingCase ts
isUsingCase (Case _ _) = True
isUsingCase (D _) = False

-- | Checks whether the term contains a D expression.
isUsingD :: Term -> Bool
isUsingD (App _ ts) = any isUsingD ts
isUsingD (Case _ ts) = any isUsingD ts
isUsingD (D _) = True

-- | Checks whether the given term does not contain nonterminal symbols.
isNotContainingN :: Term -> Bool
isNotContainingN t = S.null $ getN t

---------------------------------------------------------

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
      " but is applied to " ++ show (length ts) ++ " arguments.\nEnvironment: " ++ show bnd)
  else
    if null ts
      then return srt
      else do
        typesTs <- mapM (typeCheck bnd) ts
        let inferedArgType = sortFromList typesTs
        let expArgType = sortFromList $ take (length ts) $ sortToList srt
        let retType = sortFromList $ drop (length ts) $ sortToList srt 
        if inferedArgType == expArgType
            then return retType
            else fail ("Type error!\nTerm: " ++ show t ++ "\nExpected argument type: " ++
                       show expArgType ++ "\nInferred argument type: " ++ show inferedArgType ++
                       "\nTypes involved:\n" ++ (intercalate "\n" $ zipWith (\ a b -> "\t" ++ show a ++ ": " ++ show b) ts typesTs) ++
                       "\n\t" ++ show smb ++ ": " ++ show srt ++
                       "\nType environment: " ++ show bnd)
  where
    getSort (Var x) = maybe (fail ("Unknown variable " ++ show x  )) return $ M.lookup x bnd
    getSort s@(Nt f ) = maybe (fail ("Cannot get sort of " ++ show s ++ " bnd:" ++ show bnd)) return $ M.lookup f bnd
    getSort s@(T  f ) = maybe (fail ("Cannot get sort of " ++ show s ++ " bnd:" ++ show bnd)) return $ M.lookup f bnd

-- | Returns all variables that are used in a case expression.
caseVars :: Term -> Set String
caseVars (App _ ts ) = S.unions $ map caseVars ts
caseVars (D _      ) = S.empty
caseVars (Case x ts) = S.insert x $ S.unions $ map caseVars ts

-- | /O(n)/ Returns the height of a term.
height :: Term -> Int
height (App (Var _) []) = 0
height (App _ ts ) = succ $ maximum $ 0 : map height ts
height (Case _ ts) = succ $ maximum $ 0 : map height ts
height (D _      ) = 1

-- | Returns the maximal height of the trees listed.
maxHeight :: [Term] -> Int
maxHeight = maximum . map height

-- | Cuts a given term at height n.
-- For data values or case the function behaves
-- like the id function.
heightCut :: Int -> Term -> Term
heightCut 0 _ = var "_"
heightCut n (App t ts) = App t $ map (heightCut (n-1)) ts
heightCut _ t = t

-- | Checks if a given pattern is matched by a term.
-- The pattern may only consist of variables and terminal
-- symbols. The term may only consist of terminal symbols.
-- Variables are expected to be unique. If they are not,
-- variables might be mapped twice to different terms.
isMatching :: Term -> Term -> Maybe [(String,Term)]
isMatching (App (Var x) [] ) t                = return [(x,t)]
isMatching (App (T f1 ) ts1) (App (T f2) ts2) =
  if f1 /= f2
    then Nothing
    else do
      bnd <- mapM (uncurry isMatching) (zip ts1 ts2)
      return $ concat bnd
isMatching (App (T   _) _ ) (App (Nt _) _)  = Nothing
isMatching p t = error (show p ++ "/" ++ show t ++ " is no valid pattern") -- TODO Use ErrorT instead of error!

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
isMatchingErr (App (Var x) [] ) t@(App (T _) _)  = return [(x,t)]
isMatchingErr (App (T f1 ) ts1) (App (T f2) ts2) =
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

---------------------------------------------------------------------
---------------------------------------------------------------------
---------------------------------------------------------------------

-- | Replaces all nonterminals with a terminal _|_ (bottom).
ntCut :: Term -> Term
ntCut (App (Nt _) _ ) = terminal "_|_"
ntCut (App h      ts) = App h $ map ntCut ts
ntCut (D d)           = D d
ntCut (Case x ts)     = Case x $ map ntCut ts

-- | Creates the set of terminals created
-- from symbols of arity n.
terminalSigma :: Int -> RankedAlphabet -> [Term]
terminalSigma n ra = map terminal $ M.keys $ sigmaN n ra

-- | Creates all possible contexts from the ranked alphabet ra
-- of height n.
-- Careful if arity of terminal symbols in ra is larger than 1 this
-- explodes rather fast (exponential!)
trees' :: RankedAlphabet -> Int -> [Term]
trees' _  0 = []
trees' ra 1 = map createApp $ M.toList ra -- terminalSigma 0 ra
  where
    createApp (t,srt) = app (terminal t) $ replicate (ar srt) $ var "_"
trees' ra n = ctxts ++ trees' ra 1
  where
    ctxtsPred :: [Term]
    ctxtsPred = trees' ra (n-1)
    ctxts :: [Term]
    ctxts = concat $ map enlargeCtxt tNot0
    --
    enlargeCtxt :: (Symbol, Sort) -> [Term]
    enlargeCtxt (k,srt) = map (app (terminal k)) $ replicateM (ar srt) ctxtsPred
    --
    tNot0 = M.toList $ removeSigma0 ra

-- | Same as trees' but returns a set.
trees :: RankedAlphabet -> Int -> Set Term
trees ra n = S.fromList $ trees' ra n
