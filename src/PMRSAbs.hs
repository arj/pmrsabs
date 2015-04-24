{-# LANGUAGE BangPatterns #-}

import System.Exit (exitWith, ExitCode(..))

import Control.Monad (when)
import Data.Maybe (isNothing, fromJust)
import Data.List (intercalate)
import System.Environment (getArgs)

import Text.ParserCombinators.Parsec (ParseError)

import Aux (prettyPrint)
import Automaton (ATT())
import PMRS (PMRS())
import HORS (HORS(), startSymbol, stepNDHORS)
import Options
import Examples ()
import PMRSVerification (verifyPMRS, verifyHORS, verifyInput, Result(..))
import Parser (parseHORSATTfromFile, parseHORSfromFile, parseHORSATTfromFile, parsePMRSHORSATTfromFile)
import Term (Term, ntCut, isValue)
import qualified Preface as P
import qualified WPMRSTransformer ()

putErr :: String -> IO ()
putErr s = error $ "Error: " ++ s

prefaceVersionCheck :: [Flag] -> IO ([Int], FilePath)
prefaceVersionCheck flags = do
  let prefaceDir = getPrefaceDir flags
  x <- P.version prefaceDir
  when (isNothing x) $ putErr "Preface.exe not found"
  --
  when (not $ P.versionCheck [1,3] (fromJust x)) $ putErr "Preface version of at least 1.3 required."
  return (fromJust x, prefaceDir)


errParse :: Int
errParse = 1

errReject :: Int
errReject = 10

data GrammarFile
  = GFPMRS PMRS HORS ATT
  | GFHORS HORS ATT

parseInputFile :: FilePath -> IO (Either [ParseError] GrammarFile)
parseInputFile file = do
  resPmrs <- parsePMRSHORSATTfromFile file
  case resPmrs of
    Left errPmrs -> do
      resHors <- parseHORSATTfromFile file
      case resHors of
        Left errHors -> return $ Left [errPmrs, errHors]
        Right (hors, att) -> return $ Right $ GFHORS hors att
    Right (pmrs,hors,att) -> return $ Right $ GFPMRS pmrs hors att

loop :: HORS -> Term -> IO ()
loop hors t = do
  getChar
  let t' = stepNDHORS hors 1 t
  print $ t --ntCut t'
  case isValue t of
    False -> loop hors t'
    True -> return ()

main :: IO ()
main = do
  (flags, files) <- getArgs >>= pmrsabsOptions
  let existential = isExistential flags
  let verbose s = when (isVerbose flags) $ putStrLn s
  let output s = when (not $ isQuiet flags) $ putStrLn s
  --
  verbose "PMRS Modelchecker Version 1.0"
  when (length files < 1) $ putErr "One filename expected."
  --
  (prefaceVersion, prefaceDir) <- prefaceVersionCheck flags
  verbose $ "Preface version: " ++ (intercalate "." $ map show $ prefaceVersion)
  --
  let file = head files
  let mode = getMode flags
  --
  verbose $ "Parsing: " ++ file
  --
  case mode of
    MEval -> do
      verbose "Evaluation mode (requires HORS)"
      parseResult <- parseHORSfromFile file
      case parseResult of
        Left e -> putErr $ "Error reading " ++ file ++ ": " ++ show e ++ "\n\nEvaluation mode requires a HORS!"
        Right hors -> do
          putStrLn "Press <Enter> to step through derivation."
          loop hors (startSymbol hors)
          exitWith ExitSuccess
    --
    MModelcheck -> do
      verbose "Verification mode (requires PMRS, HORS, ATT or HORS, ATT (nondeterminism allowed))"
      --
      res <- parseInputFile file
      case res of
        Left err -> do
          let str = intercalate "\n\n" $ map show err
          putErr $ "File could neither be parsed as PMRS,HORS,ATT nor as HORS,ATT.\nParse errors (each try) are:\n\n" ++ str
          exitWith $ ExitFailure errParse
        --
        Right (GFPMRS pmrs hors att) -> do
          when (hasTransform flags) $ do
            (dhors, datt) <- verifyInput pmrs hors att
            putStrLn $ prettyPrint dhors
            putStrLn $ prettyPrint datt
            exitWith ExitSuccess
          --
          verbose "PMRS verification mode"
          result <- verifyPMRS verbose prefaceDir pmrs hors att
          output $ show result
          case result of
            RSuccess -> exitWith ExitSuccess
            RError _ -> exitWith $ ExitFailure errReject
        --
        Right (GFHORS hors att) -> do
          verbose "HORS verification mode"
          result <- verifyHORS verbose prefaceDir existential hors att
          output $ show result
          case result of
            RSuccess -> exitWith ExitSuccess
            RError _ -> exitWith $ ExitFailure errReject