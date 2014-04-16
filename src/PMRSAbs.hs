import PMRS
import Term
import Sorts
import Abstraction
import Data.Set
import Examples

tpe :: Term ()
tpe = var "phi"

ntF :: SortedSymbol ()
ntF = SortedSymbol "F" $ Base ()

ntS :: SortedSymbol ()
ntS = SortedSymbol "S" $ Base ()

rule1 :: Rule ()
rule1 = Rule {ruleF = ntF, ruleVars = ["x1","x2"], rulePattern = Nothing, ruleBody = tpe}

pmrs1 :: PMRS ()
pmrs1 = PMRS empty empty empty empty ntS

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