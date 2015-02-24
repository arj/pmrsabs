module Parser where

import Control.Monad.State
import Control.Arrow (first)
import Control.Applicative ((<$>))
import Text.ParserCombinators.Parsec hiding (State)
import Text.Printf (printf)
import Data.Char (isUpper)
import Data.Map ((!))
import qualified Data.Map as M (unions, fromList, toList, partitionWithKey)
import Data.MultiMap (MultiMap)
import qualified Data.MultiMap as MM
import Data.Set (Set)
import qualified Data.Set as S (toList, unions, insert, fromList)

import Aux (traceIt)
import Automaton (ATT,mkATT)
import PMRS
import HORS
import Sorts (Symbol, o, Sort(..), sortFromList, substTB, unify, closeRankedAlphabet)
import Term (Term(..), var, app, terminal, nonterminal, TypeBinding, TypeConstraints, bump, getT, fv')

data GenericRule = GRPMRS String [String] GenericTerm GenericTerm
                 | GRHORS String [String] GenericTerm

isGRPMRS :: GenericRule -> Bool
isGRPMRS (GRPMRS _ _ _ _) = True
isGRPMRS (GRHORS _ _ _) = False

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

genericPatternToPattern :: GenericTerm -> Term
genericPatternToPattern (GenApp (GenTermVar t) gts) =
  case t of
    '!':x -> app (var x) $ rest
    _ -> app (terminal t) $ rest
  where
    rest = map genericPatternToPattern gts
genericPatternToPattern t = error $ "Nonterminals in patterns are not allowed: " ++ (show t)

assignFreshVar :: Symbol -> State Int (Symbol, Sort)
assignFreshVar x = do
  i <- show <$> bump
  return (x, SVar $ "t" ++ i)

typer :: [GenericRule] -> TypeBinding
typer rs = closeRankedAlphabet $ evalState (typer' rs) 0

initialTypeBindings :: GenericRule -> State Int TypeBinding
initialTypeBindings (GRHORS f xs t) = do
  tcXs <- mapM assignFreshVar xs
  tcTs <- mapM assignFreshVar $ S.toList $ getT $ genericTermToTerm xs t
  let args = map snd tcXs
  let tcF  = (f, sortFromList $ args ++ [o])
  return $ M.fromList $ tcF : tcXs ++ tcTs
initialTypeBindings (GRPMRS f xs p t) = do
  tcXs <- mapM assignFreshVar xs
  tcTs <- mapM assignFreshVar $ S.toList $ getT $ genericTermToTerm xs t
  let args = map snd tcXs
  let tcF  = (f, sortFromList $ args ++ [o])
  let tcP = zip (fv' $ genericPatternToPattern p) (repeat o)
  return $ M.fromList $ tcF : tcXs ++ tcTs ++ tcP

typer' :: [GenericRule] -> State Int TypeBinding
typer' rs = do
  tb <- M.unions <$> mapM initialTypeBindings rs
  tcs <- mapM (typerInner tb) rs
  let constraints = S.unions tcs
  let eithersbst = unify $ S.toList constraints
  case eithersbst of
    Left err -> error $ "Error in typer\n" ++ show tb ++ "\n" ++ show constraints ++ "\n" ++ err
    Right sbst -> return $ M.fromList $ substTB sbst $ M.toList tb

typerInner :: TypeBinding -> GenericRule -> State Int TypeConstraints
typerInner gamma (GRHORS _ xs t') = do
  let t = genericTermToTerm xs t'
  (retVar, gamma') <- createConstraints gamma t
  return $ S.insert (retVar,o) gamma'

createConstraints :: TypeBinding -> Term -> State Int (Sort, TypeConstraints)
createConstraints gamma (App h ts) = do
  let hType = gamma ! (show h) -- TODO Error handling!
  (symbols, gammas) <- unzip <$> mapM (createConstraints gamma) ts
  alpha <- show <$> bump
  let ret = SVar $ "t" ++ alpha
  let hType2 = sortFromList $ symbols ++ [ret]
  return $ (ret, S.insert (hType, hType2) $ S.unions gammas)

pmrsFromGenericRules :: [GenericRule] -> PMRS
pmrsFromGenericRules rules = mkPMRSErr nt t rs s
  where
    (nt, t)         = M.partitionWithKey isNonterminalBinding $ typer rules
    (GRHORS s _ _)  = head rules
    rs = listToRules $ map transformRule rules
    transformRule (GRHORS f xs t) = PMRSRule f xs Nothing $ genericTermToTerm xs t
    transformRule (GRPMRS f xs p t) = PMRSRule f xs (Just $ genericPatternToPattern p) $ genericTermToTerm xs t

horsFromGenericRules :: [GenericRule] -> HORS
horsFromGenericRules rules = mkHORSErr t nt rs s
  where
    (nt, t)         = M.partitionWithKey isNonterminalBinding $ typer rules
    (GRHORS s _ _)  = head rules
    rs = mkHorsRules $ map transformRule rules
    transformRule (GRHORS f xs trm) = HORSRule f xs $ genericTermToTerm xs trm

isNonterminalBinding :: Symbol -> a -> Bool
isNonterminalBinding (x:_) _ = isUpper x

attFromGenericRules :: [(String,String,[(Int, String)])] -> ATT
attFromGenericRules rs = mkATT delta q0
  where
    (q0,_,_) = head rs
    --
    delta :: MultiMap (String, String) (Set (Int, String))
    delta = MM.fromList $ map f rs
    --
    f :: (String, String, [(Int, String)]) -> ((String, String), Set (Int,String))
    f (q,a,qs) = ((q,a),S.fromList qs)

identifier :: GenParser Char st String
identifier = many (alphaNum <|> char '_')

nonterm :: GenParser Char st String
nonterm = do
  f <- upper <|> char '!'
  r <- identifier
  spaces
  return $ f : r

termOrvar :: GenParser Char st String
termOrvar = do
  f <- lower
  r <- identifier
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

parseGenericHors :: GenParser Char st [GenericRule]
parseGenericHors = do
  string "%BEGING"
  newline
  spaces
  r <- endBy1 (try horsRule) (char '.' >> newline >> spaces)
  string "%ENDG"
  return r

parseHors :: GenParser Char st HORS
parseHors = horsFromGenericRules <$> parseGenericHors

parseGenericPmrs :: GenParser Char st [GenericRule]
parseGenericPmrs = do
  string "%BEGINPMRS"
  newline
  spaces
  r <- endBy1 (((try horsRule) <|> pmrsRule)) (char '.' >> newline >> spaces)
  string "%ENDPMRS"
  return r

parsePmrs :: GenParser Char st PMRS
parsePmrs = pmrsFromGenericRules <$> parseGenericPmrs

parseQ :: GenParser Char st String
parseQ = do
  q <- many1 alphaNum
  spaces
  return q

parseIntQ :: GenParser Char st (String, String)
parseIntQ = do
  iq <- between (char '(' >> spaces) (char ')' >> spaces) $ do
    i <- many1 digit
    spaces
    string ","
    spaces
    q <- many1 alphaNum
    return (i,q)
  return iq

attRule :: GenParser Char st (String, String, [(Int, String)])
attRule = do
  q <- parseQ
  a <- termOrvar
  ruleSep
  qs <- many parseIntQ
  let qs' = map (first read) qs
  return (q,a,qs')

parseAtt :: GenParser Char st ATT
parseAtt = do
  string "%BEGINA"
  newline
  spaces
  r <- endBy1 (attRule) (char '.' >> newline >> spaces)
  string "%ENDA"
  return $ attFromGenericRules r

data TG = THORS HORS
  | TPMRS PMRS
  deriving (Show)

parseHORSATT :: GenParser Char st (HORS, ATT)
parseHORSATT = do
  hors <- parseHors
  spaces
  att <- parseAtt
  return (hors, att)

parseTreeGrammarATT :: GenParser Char st (TG, ATT)
parseTreeGrammarATT = do
  grammar <- try (parseHors >>= return . THORS) <|> (parsePmrs >>= return . TPMRS)
  spaces
  att <- parseAtt
  return (grammar, att)

parsePMRSHORSATT :: GenParser Char st (PMRS, HORS, ATT)
parsePMRSHORSATT = do
      pmrs <- parsePmrs
      spaces
      hors <- parseHors
      spaces
      att  <- parseAtt
      return (pmrs, hors, att)

parseHORSATTfromFile :: FilePath -> IO (Either ParseError (HORS,ATT))
parseHORSATTfromFile = parseFromFile parseHORSATT

parseTreeGrammarATTfromFile :: FilePath -> IO (Either ParseError (TG,ATT))
parseTreeGrammarATTfromFile = parseFromFile parseTreeGrammarATT

parsePMRSHORSATTfromFile :: FilePath -> IO (Either ParseError (PMRS, HORS, ATT))
parsePMRSHORSATTfromFile = parseFromFile parsePMRSHORSATT