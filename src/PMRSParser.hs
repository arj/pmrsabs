module PMRSParser where

import PMRS
import Term hiding (nonterminal)
import Text.ParserCombinators.Parsec
import Data.Char

type GenericRule = (String, [String], Maybe String, GenericTerm)

data GenericHead = GenNT String
                 | GenTermVar String
                 deriving (Eq, Ord)

data GenericTerm = GenApp GenericHead [GenericTerm]
								 deriving (Eq, Ord)

instance Show GenericHead where
	show (GenNT s) = "~:" ++ s ++ ":~"
	show (GenTermVar s) = "~:" ++ s ++ ":~"

instance Show GenericTerm where
	show (GenApp h []) = show h
	show (GenApp h ts) = "(" ++ show h ++ " " ++ unwords (map show ts) ++ ")"

mkGenericTerm :: String -> [GenericTerm] -> GenericTerm
mkGenericTerm hd@(h1:_) terms =
	let h = if isUpper h1
		then GenNT hd
		else GenTermVar hd
	in GenApp h terms

pmrsFromGenericRules :: [GenericRule] -> PMRS
pmrsFromGenericRules = undefined

pmrs :: GenParser Char st PMRS
pmrs =
	do string "%BEGING"
	   r <- many rule
	   string "%ENDG"
	   eof
	   return $ pmrsFromGenericRules r

nonterminal :: GenParser Char st String
nonterminal = do
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

ruleSep = do
	string "->" <|> string "="
	spaces

term =
	between (char '(' >> spaces) (char ')' >> spaces) term' <|> term'

term' = do
  head  <- (nonterminal <|> termOrvar)
  terms <- many term
  spaces
  return $ mkGenericTerm head terms

rule = do
	s  <- nonterminal
	xs <- many termOrvar
	ruleSep
	t <- term
	return (s, xs, Nothing, t)

parsePMRS :: String -> Either ParseError PMRS
parsePMRS = parse pmrs "(unknown)"