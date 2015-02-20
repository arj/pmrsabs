{-# LANGUAGE ScopedTypeVariables, OverloadedStrings #-}

module Preface (
  ATT(..),
  check,
  version,
  versionCheck,
  PrefaceOutput(..),
  problemResult,
  problemCertificate,
  SchemeData(..),
  AutomatonData(..),
  ProblemData(..),
  PerformanceData(..),
  CertificateData(..)
) where

import Control.Exception (try, IOException, catch)
import Control.Monad (liftM, mzero)
import Control.Applicative ((<$>),(<*>))
import Control.Arrow (second)
import Data.Aeson (decode, Value(..), FromJSON(..),(.:),(.:?))
import Data.ByteString.Lazy.Char8 (pack)
import Data.Maybe (fromJust)
import qualified Data.HashMap.Strict as HM
import System.IO (hPutStr, hFlush)
import System.IO.Temp (withSystemTempFile)
import System.Process (readProcess)
import Text.Regex (mkRegex, matchRegex)
import qualified Data.Text as T

import Aux
import PMRS
import HORS
import RSFD
import Term
import Automaton

class PrettyPrint a => PrefaceGrammar a where

instance PrefaceGrammar PMRS where
instance PrefaceGrammar RSFD where
instance PrefaceGrammar HORS where

-- | Calls Preface which checks whether the given ATT accepts
-- the tree produced by the grammar and returns.
check :: PrefaceGrammar a => FilePath -> a -> ATT -> IO (Either IOError PrefaceOutput)
check prefaceDir grammar att =
  withSystemTempFile "preface.input" $ \path h -> do
    hPutStr h input
    hFlush h
    res <- catch (liftM Right $ readProcess prefaceDir ["--json", "--witness", "-c", path] "") $ \(e :: IOError) -> return $ Left e
    return $ fromJust <$> parsePrefaceOutput <$> res
  where
    input = prettyPrint grammar ++ "\n" ++ prettyPrint att

-- | Extract the preface version string.
version :: FilePath -> IO (Maybe [Int])
version preface = do
  res <- try (readProcess preface ["-v"] "") :: IO (Either IOException String)
  case res of
    Left  _ -> return Nothing
    Right s -> return $ extractVersion s

-- | Tries to extract a version string of the form "Version 1.0"
-- from a given string.
extractVersion :: String -> Maybe [Int]
extractVersion s = do
  x <- matchRegex (mkRegex "Version: ([[:digit:]])\\.([[:digit:]])") s
  return $ map read x

-- | Checks if a given version is at least the same as the
-- required version.
versionCheck :: [Int] -> [Int] -> Bool
versionCheck expversion foundversion= all id res
  where
    res = zipWith (>=) foundversion expversion


-- * Output Parser

data PrefaceOutput = PrefaceOutput
  { poVersion :: T.Text
  , poScheme :: SchemeData
  , poAutomaton :: AutomatonData
  , poProblem :: ProblemData
  , poPerformance :: PerformanceData
  , poCertificate :: Maybe CertificateData
  } deriving Show

problemResult :: PrefaceOutput -> Bool
problemResult po =
  case poDecision $ poProblem po of
    "Accepted" -> True
    "Rejected" -> False

problemCertificate :: PrefaceOutput -> [(T.Text, T.Text)]
problemCertificate po = cdTypes $ fromJust $ poCertificate po

data SchemeData = SchemeData
  { sdRules :: T.Text -- TODO Int
  , sdOrder :: T.Text
  , sdArity :: T.Text
  , sdSize  :: T.Text
  } deriving Show

data AutomatonData = AutomatonData
  { adStates :: T.Text
  , adTransitions :: T.Text
  } deriving Show

data ProblemData = ProblemData
  { poDecision :: T.Text
  } deriving Show

data PerformanceData = PerformanceData
  { poTime :: T.Text
  } deriving Show

data CertificateData = CertificateData
  { cdTypes :: [(T.Text, T.Text)]
  } deriving Show

instance FromJSON PrefaceOutput where
  parseJSON (Object v) = PrefaceOutput <$>
                         v .: "Version" <*>
                         v .: "Scheme" <*>
                         v .: "Automaton" <*>
                         v .: "Problem" <*>
                         v .: "Performance" <*>
                         v .:? "Certificate"
  parseJSON _ = mzero

instance FromJSON SchemeData where
  parseJSON (Object v) = SchemeData <$>
                         v .: "Rules" <*>
                         v .: "Order" <*>
                         v .: "Arity" <*>
                         v .: "Size"
  parseJSON _ = mzero

instance FromJSON AutomatonData where
  parseJSON (Object v) = AutomatonData <$>
                         v .: "States" <*>
                         v .: "Transitions"
  parseJSON _ = mzero

instance FromJSON ProblemData where
  parseJSON (Object v) = ProblemData <$>
                         v .: "Decision"
  parseJSON _ = mzero

instance FromJSON PerformanceData where
  parseJSON (Object _) = return $ PerformanceData "" -- TODO
  parseJSON _ = mzero

instance FromJSON CertificateData where
  parseJSON (Object v) = do
    let valueToString (String txt) = txt
    return $ CertificateData $ map (second valueToString) $ HM.toList v
  parseJSON _ = mzero

parsePrefaceOutput :: String -> Maybe PrefaceOutput
parsePrefaceOutput s = decode $ pack s
