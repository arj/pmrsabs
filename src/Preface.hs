{-# LANGUAGE ScopedTypeVariables #-}

module Preface (
	ATT(..), Answer(..),
	check,
	version
) where

import Control.Exception (try, IOException)
import Control.Concurrent (threadDelay)
import System.IO
import System.IO.Temp
import System.Process (readProcess)
import Text.Regex (mkRegex, matchRegex)

import Aux
import PMRS
import Term

data ATT = ATT

instance PrettyPrint ATT where
	prettyPrint _ = "%BEGINA\nq0 a->.\n%ENDA\n"

class PrettyPrint a => PrefaceGrammar a where

instance PrefaceGrammar PMRS where

--prefacePath :: String
--prefacePath = "/home/jakobro/work/impl/PrefaceModelchecker/Preface/Preface/bin/Debug/Preface.exe"

data Answer = Accepted
            | Rejected Term

-- | Calls Preface which checks whether the given ATT accepts
-- the tree produced by the grammar and returns.
check :: PrefaceGrammar a => FilePath -> a -> ATT -> IO (Either IOError Answer)
check preface grammar att =
	withSystemTempFile "preface.input" $ \path h -> do
		hPutStr h input
		hFlush h
		--out <- catch (evaluate $ readProcess prefacePath [path] "") $ \(e :: IOError) -> Left e
		_out <- readProcess preface [path] ""
		threadDelay 50000000
		return $ Right Accepted
  where
		input = prettyPrint grammar ++ "\n" ++ prettyPrint att

-- | Extract the preface version string.
version :: FilePath -> IO (Maybe String)
version preface = do
	res <- try (readProcess preface ["-v"] "") :: IO (Either IOException String)
	case res of
		Left  _ -> return Nothing
		Right s -> return $ extractVersion s

-- | Tries to extract a version string of the form "Version 1.0"
-- from a given string.
extractVersion :: String -> Maybe String
extractVersion s = do
	x <- matchRegex (mkRegex "Version: ([0123456789]\\.[0123456789])") s
	return $ head x
