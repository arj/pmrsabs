{-# LANGUAGE ScopedTypeVariables #-}

module Preface where

import Aux
import PMRS
import Term

import Control.Exception
import Control.Concurrent (threadDelay)
import System.IO
import System.IO.Temp
import System.Process (readProcess)
import Debug.Trace (trace)

data ATT = ATT

instance PrettyPrint ATT where
	prettyPrint _ = "%BEGINA\nq0 a->.\n%ENDA\n"

class PrettyPrint a => PrefaceGrammar a where

instance PrefaceGrammar PMRS where

prefacePath :: String
prefacePath = "/home/jakobro/work/impl/PrefaceModelchecker/Preface/Preface/bin/Debug/Preface.exe"

data Answer = Accepted
            | Rejected Term

-- | Calls Preface which checks whether the given ATT accepts
-- the tree produced by the grammar and returns.
preface :: PrefaceGrammar a => a -> ATT -> IO (Either IOError Answer)
preface grammar att =
	withSystemTempFile "preface.input" $ \path h -> do
		hPutStr h input
		hFlush h
		--out <- catch (evaluate $ readProcess prefacePath [path] "") $ \(e :: IOError) -> Left e
		out <- readProcess prefacePath [path] ""
		threadDelay 50000000
		return $ Right Accepted
  where
		input = prettyPrint grammar ++ "\n" ++ prettyPrint att