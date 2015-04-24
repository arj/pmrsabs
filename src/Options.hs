module Options (
    Flag(),
    getPrefaceDir,
    isVerbose,
    isExistential,
    isRunOnly,
    isQuiet,
    hasTransform,
    pmrsabsOptions,
    getMode,
    Mode(..)
) where

import System.Console.GetOpt (getOpt, OptDescr(..), ArgDescr(..), ArgOrder(..), usageInfo)

data Flag 
  = Verbose
  | DoExistential
  | Version 
  | PrefaceDir String
  | RunHORS
  | Quiet
  | Transform
  deriving (Eq, Show)

options :: [OptDescr Flag]
options =
    [ Option ['v']     ["verbose"] (NoArg Verbose)       "print more information"
    , Option ['V','?'] ["version"] (NoArg Version)       "show version number"
    , Option ['e'] ["existential"] (NoArg DoExistential)       "Property holds if true for some trees of the language"
    , Option []     ["preface"]  (ReqArg PrefaceDir "DIR")   "Location of Preface (if not given, 'Preface.exe' is used)"
    , Option ['r'] ["run"] (NoArg RunHORS) "Function as an evaluator for HORS"
    , Option ['q'] ["quiet"] (NoArg Quiet) "Only produces error messages. Does not cancel verbose."
    , Option ['t'] ["transform"] (NoArg Transform) "Just transform given PMRS into a D-HORS and print"
    ]

data Mode
  = MEval
  | MModelcheck
  deriving (Eq)

getMode :: [Flag] -> Mode
getMode flags =
    if isRunOnly flags
      then MEval
      else MModelcheck

getPrefaceDir :: [Flag] -> String
getPrefaceDir [] = "Preface.exe"
getPrefaceDir (PrefaceDir dir:_) = dir
getPrefaceDir (_:xs) = getPrefaceDir xs

hasFlag :: Flag -> [Flag] -> Bool
hasFlag flg flags = any ((==) flg) flags

hasTransform :: [Flag] -> Bool
hasTransform = hasFlag Transform

isVerbose :: [Flag] -> Bool
isVerbose flg = any ((==) Verbose) flg

isExistential :: [Flag] -> Bool
isExistential flg = any ((==) DoExistential) flg

isQuiet :: [Flag] -> Bool
isQuiet flg = any ((==) Quiet) flg

isRunOnly :: [Flag] -> Bool
isRunOnly flg = any ((==) RunHORS) flg

pmrsabsOptions :: [String] -> IO ([Flag], [String])
pmrsabsOptions argv = 
      case getOpt Permute options argv of
         (o,n,[]  ) -> return (o,n)
         (_,_,errs) -> ioError (userError (concat errs ++ usageInfo header options))
     where header = "Usage: pmrsabs [OPTION...] inputfile"