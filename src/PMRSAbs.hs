import Control.Monad (when)
import Data.Maybe (isNothing, fromJust)

import           Abstraction ()
import           Examples ()
import           PMRS ()
import           Sorts ()
import           Term ()
--import           PMRSParser
import Preface as P
import HORS ()
import Transformation ()
import GenericRecursionScheme ()

main :: IO ()
main = do
	putStrLn "PMRS Modelchecker Version 1.0"
	x <- P.version "Preface.exe"
	when (isNothing x) (error "Preface.exe not found")
	putStrLn $ "- Preface version: " ++ fromJust x