module Options where

import System.Console.GetOpt

data Flag 
    = Verbose
    | Version 
    | PrefaceDir String
    deriving Show

options :: [OptDescr Flag]
options =
    [ Option ['v']     ["verbose"] (NoArg Verbose)       "print more information"
    , Option ['V','?'] ["version"] (NoArg Version)       "show version number"
    , Option []     ["preface"]  (ReqArg PrefaceDir "DIR")   "Location of Preface"
    ]

getPrefaceDir :: [Flag] -> String
getPrefaceDir [] = "Preface.exe"
getPrefaceDir (PrefaceDir dir:_) = dir
getPrefaceDir (_:xs) = getPrefaceDir xs

pmrsabsOptions :: [String] -> IO ([Flag], [String])
pmrsabsOptions argv = 
      case getOpt Permute options argv of
         (o,n,[]  ) -> return (o,n)
         (_,_,errs) -> ioError (userError (concat errs ++ usageInfo header options))
     where header = "Usage: pmrsabs [OPTION...] inputfiles..."