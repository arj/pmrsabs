module Parser where

import Data.List (elem)
import Control.Monad (liftM, forM)
import Control.Monad.State
import Control.Applicative ((<$>))
import Text.ParserCombinators.Parsec hiding (State)
import Text.Printf (printf)
import Data.Char (isUpper)
import Data.Map ((!))
import qualified Data.Map as M (unions, insert, fromList, toList, empty, singleton, union)
import qualified Data.Set as S (toList, unions, insert)
import qualified Data.SetMap as SM
import Debug.Trace (trace)

import PMRS
import HORS
import Sorts (Symbol, o, Sort(..), sortFromList, substTB, unify)
import Term (Term(..), var, app, terminal, nonterminal, TypeBinding, TypeConstraints, bump, getT)

data GenericRule = GRPMRS String [String] GenericTerm GenericTerm
                 | GRHORS String [String] GenericTerm

instance Show GenericRule where
  show (GRPMRS f xs@(_:_) p t) = printf "%s %s |%s = %s" f (unwords xs) (show p) (show t)
  show (GRPMRS f [] p t) = printf "%s |%s = %s" f (show p) (show t)
  --
  show (GRHORS f xs@(_:_) t) = printf "%s %s = %s" f (unwords xs) (show t)
  show (GRHORS f [] t) = printf "%s = %s" f (show t)

data GenericHead = GenNT String
                 | GenTermVar String
                 deriving (Eq, Ord)

data GenericTerm = GenApp GenericHead [GenericTerm]
                 deriving (Eq, Ord)

instance Show GenericHead where
  show (GenNT s) = s
  show (GenTermVar s) = s

instance Show GenericTerm where
  show (GenApp h []) = show h
  show (GenApp h ts) = "(" ++ show h ++ " " ++ unwords (map show ts) ++ ")"

mkGenericTerm :: String -> [GenericTerm] -> GenericTerm
mkGenericTerm hd@(h1:_) terms =
  let h = if isUpper h1
          then GenNT hd
          else GenTermVar hd
  in GenApp h terms

genericTermToTerm :: [String] -> GenericTerm -> Term
genericTermToTerm xs (GenApp (GenNT n) gts) = app (nonterminal n) $ map (genericTermToTerm xs) gts
genericTermToTerm xs (GenApp (GenTermVar t) gts) =
  if t `elem` xs
    then app (var t) $ rest
    else app (terminal t) $ rest
  where
    rest = map (genericTermToTerm xs) gts

assignFreshVar :: Symbol -> State Int (Symbol, Sort)
assignFreshVar x = do
  i <- show <$> bump
  return (x, SVar $ "t" ++ i)

initialTypeBindings :: GenericRule -> State Int TypeBinding
initialTypeBindings (GRHORS f xs t) = do
  tcXs <- mapM assignFreshVar xs
  tcTs <- mapM assignFreshVar $ S.toList $ getT $ genericTermToTerm xs t
  let args = map snd tcXs
  let tcF  = (f, sortFromList $ args ++ [o])
  return $ M.fromList $ tcF : tcXs ++ tcTs

typer :: [GenericRule] -> TypeBinding
typer rs = evalState (typer' rs) 0

typer' :: [GenericRule] -> State Int TypeBinding
typer' rs = do
  tb <- M.unions <$> mapM initialTypeBindings rs
  tcs <- mapM (typerInner tb) rs
  let constraints = S.unions tcs
  let sbst = unify $ S.toList constraints
  return $ M.fromList $ substTB sbst $ M.toList tb

typerInner :: TypeBinding -> GenericRule -> State Int TypeConstraints
typerInner gamma (GRHORS _ xs t') = do
  let t = genericTermToTerm xs t'
  (retVar, gamma') <- createConstraints gamma t
  return $ S.insert (retVar,o) gamma'

createConstraints :: TypeBinding -> Term -> State Int (Sort, TypeConstraints)
createConstraints gamma (App h ts) = do
  let hType = gamma ! (show h) -- TODO Error handling!
  (symbols, gammas) <- unzip <$> mapM (createConstraints gamma) ts
  x <- show <$> bump
  let ret = SVar $ "t" ++ x
  let hType2 = sortFromList $ symbols ++ [ret]
  return $ (ret, S.insert (hType, hType2) $ S.unions gammas)

pmrsFromGenericRules :: [GenericRule] -> PMRS
pmrsFromGenericRules = undefined

horsFromGenericRules :: [GenericRule] -> HORS
horsFromGenericRules rules = mkUntypedHORS rs s
  where
    (GRHORS s _ _)  = head rules
    rs = horsRules $ map transformRule rules
    transformRule (GRHORS f xs t) = HORSRule f xs $ genericTermToTerm xs t

nonterm :: GenParser Char st String
nonterm = do
  f <- upper
  r <- many alphaNum
  spaces
  return $ f : r

termOrvar :: GenParser Char st String
termOrvar = do
  f <- lower
  r <- many alphaNum
  spaces
  return $ f : r

ruleSep :: GenParser Char st ()
ruleSep = do
  string "->" <|> string "="
  spaces

parensTerm :: GenParser Char st GenericTerm
parensTerm = between (char '(' >> spaces) (char ')' >> spaces) term'

term :: GenParser Char st GenericTerm
term =
  parensTerm <|> term'

hdTerm :: GenParser Char st GenericTerm
hdTerm = (nonterm <|> termOrvar) >>= \h -> return $ mkGenericTerm h []

term' :: GenParser Char st GenericTerm
term' = do
  hd  <- (nonterm <|> termOrvar)
  terms <- many (hdTerm <|> parensTerm)
  spaces
  return $ mkGenericTerm hd terms

pmrsRule :: GenParser Char st GenericRule
pmrsRule = do
  s  <- nonterm
  xs <- many termOrvar
  spaces
  string "|"
  pattern <- term
  ruleSep
  t <- term
  return $ GRPMRS s xs pattern t

horsRule :: GenParser Char st GenericRule
horsRule = do
  s  <- nonterm
  xs <- many termOrvar
  ruleSep
  t <- term
  return $ GRHORS s xs t

hors :: GenParser Char st [GenericRule]
hors = do
  string "%BEGING"
  newline
  spaces
  r <- endBy1 (try horsRule) (char '.' >> newline >> spaces)
  string "%ENDG"
  eof
  --return $ horsFromGenericRules r
  return r

pmrs :: GenParser Char st [GenericRule]
pmrs = do
  string "%BEGINPMRS"
  newline
  spaces
  r <- endBy1 (((try horsRule) <|> pmrsRule)) (char '.' >> newline >> spaces)
  string "%ENDPMRS"
  eof
  --return $ pmrsFromGenericRules r
  return r


--parsePMRS :: String -> Either ParseError PMRS
--parsePMRS = parse pmrs "(unknown)"
--
--parseHORS :: String -> Either ParseError HORS
--parseHORS = parse hors "(unknown)"