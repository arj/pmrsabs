{-# LANGUAGE ScopedTypeVariables #-}

module Preface (
	ATT(..), Answer(..),
	check,
	version
) where

import Control.Exception (try, IOException, catch)
-- import Control.Concurrent (threadDelay)
import Control.Monad (liftM)
import System.IO
import System.IO.Temp
import System.Process (readProcess)
import Text.Regex (mkRegex, matchRegex)

import Aux
import PMRS
import RSFD
import Term

data ATT = ATT

instance PrettyPrint ATT where
	prettyPrint _ = "%BEGINA\nq0 cons-> q1 q0.\nq1 s -> q2.\nq2 z ->.%ENDA\n"

class PrettyPrint a => PrefaceGrammar a where

instance PrefaceGrammar PMRS where
instance PrefaceGrammar RSFD where

--prefacePath :: String
--prefacePath = "/home/jakobro/work/impl/PrefaceModelchecker/Preface/Preface/bin/Debug/Preface.exe"

prefaceFileName :: String
prefaceFileName = "Preface.exe"

data Answer = Accepted
            | Rejected Term

-- | Calls Preface which checks whether the given ATT accepts
-- the tree produced by the grammar and returns.
check :: PrefaceGrammar a => a -> ATT -> IO (Either IOError String)
check grammar att =
	withSystemTempFile "preface.input" $ \path h -> do
		hPutStr h input
		hFlush h
		catch (liftM Right $ readProcess prefaceFileName [path] "") $ \(e :: IOError) -> return $ Left e
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
	x <- matchRegex (mkRegex "Version: ([[:digit:]]\\.[[:digit:]])") s
	return $ head x
