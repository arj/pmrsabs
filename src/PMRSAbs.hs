import Control.Monad (when, forM_)
import Data.Maybe (isNothing, fromJust)
import Data.List (intercalate)
import System.TimeIt
import System.Environment
import Text.Printf (printf)

import           Abstraction ()
import           Examples (exampleDetWpmrs)
import           PMRS ()
import           Sorts ()
import           Term ()
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
	putStr $   "- Transforming to RSFD"
	(rsfdTime, rsfd) <- timeItT $ exampleDetWpmrs >>= wPMRStoRSFD
	putStrLn $ printf " (%6.4fs)" rsfdTime

	--
	putStr $ "- Calling Preface"
	(checkTime, result) <- timeItT $ check prefaceDir rsfd ATT
	putStrLn $ printf " (%6.4fs)" checkTime
	--
	case result of
		Left e -> putStrLn $ "Error running Preface: " ++ show e
		Right e -> do
			putStr "- Accepted: "
			let res = problemResult e
			print $ res
			when (not res) $ putStr "- Certificate: " >> forM_ (problemCertificate e) print
