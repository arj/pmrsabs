import Control.Monad (when)
import Data.Maybe (isNothing, fromJust)
import Data.List (intercalate)
import System.TimeIt
import System.Environment
import Text.Printf (printf)

import           Abstraction ()
import           PMRS ()
import           Sorts ()
import           Term ()
import HORS (determinizeUntypedHORS, findCEx, removeBrFromCEx)
import Automaton
import Options
--import           PMRSParser
import Preface as P
import HORS ()
import WPMRSTransformer
import Parser (parseHORSATTfromFile)
--import Transformation
import GenericRecursionScheme ()

putErr :: String -> IO ()
putErr s = error $ "Error: " ++ s

prefaceVersionCheck :: [Flag] -> IO ([Int], FilePath)
prefaceVersionCheck flags = do
  let prefaceDir = getPrefaceDir flags
  x <- P.version prefaceDir
  when (isNothing x) $ putErr "Preface.exe not found"
  --
  when (not $ versionCheck [1,3] (fromJust x)) $ putErr "Preface version of at least 1.3 required."
  return (fromJust x, prefaceDir)

main :: IO ()
main = do
  (flags, files) <- getArgs >>= pmrsabsOptions
  let verbose s = when (isVerbose flags) $ putStrLn s
  --
  verbose "PMRS Modelchecker Version 1.0"
  when (length files < 1) $ putErr "One filename expected."
  --
  (prefaceVersion, prefaceDir) <- prefaceVersionCheck flags
  verbose $ "Preface version: " ++ (intercalate "." $ map show $ prefaceVersion)
  --

  let file = head files
  verbose $ "Parsing: " ++ file
  --
  parseResult <- parseHORSATTfromFile file
  case parseResult of
    Left e -> putErr $ "Error reading " ++ file ++ ": " ++ show e
    Right (hors,att) -> do
      verbose "Determinizing HORS"
      (horsTime, dethors) <- timeItT $ return $ determinizeUntypedHORS hors
      verbose $ printf " (%6.4fs)" horsTime

      let detatt = attAddBr "br__br" att

      verbose "Calling Preface"    
      (checkTime, result) <- timeItT $ check prefaceDir dethors detatt
      verbose $ printf " (%6.4fs)" checkTime

      case result of
        Left e -> putStrLn $ "Error running Preface: " ++ show e
        Right e -> do
          putStr "Accepted: "
          let res = problemResult e
          print $ res
          (cexTime,cex) <- timeItT $ return $ removeBrFromCEx "br__br" $ findCEx dethors detatt
          when (not res) $ putStrLn (printf "Counterexample (%6.4fs): %s" cexTime (show cex))