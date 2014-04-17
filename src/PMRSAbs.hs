import           Abstraction
import           Examples
import           PMRS
import           Sorts
import           Term

--import Data.MultiMap (MultiMap)
import qualified Data.MultiMap as MM

import           Data.Set      (Set)
import qualified Data.Set      as S

tpe :: Term ()
tpe = var "phi"

ntF :: SortedSymbol ()
ntF = SortedSymbol "F" $ Base ()

ntS :: SortedSymbol ()
ntS = SortedSymbol "S" $ Base ()

rule1 :: Rule ()
rule1 = Rule {ruleF = ntF, ruleVars = ["x1","x2"], rulePattern = Nothing, ruleBody = tpe}

pmrs1 :: PMRS ()
pmrs1 = PMRS S.empty S.empty MM.empty ntS


example5_1 :: Set (Term ())
example5_2 :: Set (Term ())
example5_3 :: Set (Term ())
(example5_1,example5_2,example5_3) = example5

main :: IO ()
main = do
	putStrLn "Test"
	print rule1
	print pmrs1
	--print $ wPMRS pmrs1
	--print $ sPMRS pmrs1
	print example5_1
	print example5_2
	print example5_3
	print example2pmrs
	print exampleRmatch
