module Options (
    Flag(),
    getPrefaceDir,
    isVerbose,
    isExistential,
    isRunOnly,
    pmrsabsOptions
) where

import System.Console.GetOpt (getOpt, OptDescr(..), ArgDescr(..), ArgOrder(..), usageInfo)

data Flag 
    = Verbose
    | DoExistential
    | Version 
    | PrefaceDir String
    | RunHORS
    deriving (Eq, Show)

options :: [OptDescr Flag]
options =
    [ Option ['v']     ["verbose"] (NoArg Verbose)       "print more information"
    , Option ['V','?'] ["version"] (NoArg Version)       "show version number"
    , Option ['e'] ["existential"] (NoArg DoExistential)       "Property holds if true for some trees of the language"
    , Option []     ["preface"]  (ReqArg PrefaceDir "DIR")   "Location of Preface"
    , Option ['r'] ["run"] (NoArg RunHORS) "Interpreter for HORS"
    ]

getPrefaceDir :: [Flag] -> String
getPrefaceDir [] = "Preface.exe"
getPrefaceDir (PrefaceDir dir:_) = dir
getPrefaceDir (_:xs) = getPrefaceDir xs

isVerbose :: [Flag] -> Bool
isVerbose [] = False
isVerbose (Verbose:_) = True
isVerbose (_:t) = isVerbose t

isExistential :: [Flag] -> Bool
isExistential [] = False
isExistential (DoExistential:_) = True
isExistential (_:t) = isExistential t

isRunOnly :: [Flag] -> Bool
isRunOnly flg = any ((==) RunHORS) flg

pmrsabsOptions :: [String] -> IO ([Flag], [String])
pmrsabsOptions argv = 
      case getOpt Permute options argv of
         (o,n,[]  ) -> return (o,n)
         (_,_,errs) -> ioError (userError (concat errs ++ usageInfo header options))
     where header = "Usage: pmrsabs [OPTION...] inputfiles..."