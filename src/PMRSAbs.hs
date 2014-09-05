import Control.Monad (when, forM_)
import Data.Maybe (isNothing, fromJust)
import Data.List (intercalate)
import System.TimeIt
import System.Environment
import Text.Printf (printf)

import qualified Data.Map as M

import           Abstraction ()
import           Examples (exampleDetWpmrs,horsndet)
import           PMRS ()
import           Sorts ()
import           Term ()
import HORS (determinizeHORS, findCEx, removeBrFromCEx)
import Automaton
import Options
--import           PMRSParser
import Preface as P
import HORS ()
import Transformation
import GenericRecursionScheme ()


main :: IO ()
main = do
	(args, _files) <- getArgs >>= pmrsabsOptions
	let prefaceDir = getPrefaceDir args
	putStrLn "PMRS Modelchecker Version 1.0"
	x <- P.version prefaceDir
	when (isNothing x) (error "Preface.exe not found")
	putStrLn $ "- Preface version: " ++ (intercalate "." $ map show $ fromJust x)
	when (not $ versionCheck [1,3] (fromJust x)) $ error "Preface version of at least 1.3 required."
	--
	putStr $   "- Determinizing HORS"
	(horsTime, hors) <- timeItT $ horsndet >>= determinizeHORS
	putStrLn $ printf " (%6.4fs)" horsTime

	--
	putStr $ "- Calling Preface"	
	let delta = M.fromList [(("q0", "cons"),["q1","q0"]),(("q0", "nil"),[]),{--(("q1","z"),[]),--}(("q1","s"),["q1"])]
	let att = attAddBr "br__br" $ ATT delta "q0"
	(checkTime, result) <- timeItT $ check prefaceDir hors att
	putStrLn $ printf " (%6.4fs)" checkTime
	--
	case result of
		Left e -> putStrLn $ "Error running Preface: " ++ show e
		Right e -> do
			putStr "- Accepted: "
			let res = problemResult e
			print $ res
			-- when (not res) $ putStr "- Certificate: " >> forM_ (problemCertificate e) print
			when (not res) $ putStrLn ("- Counterexample: " ++ (show $ removeBrFromCEx "br__br" $ findCEx hors att))
