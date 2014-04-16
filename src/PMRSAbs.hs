import PMRS
import Data.Set

tpe :: Term ()
tpe = App (Var "phi") []

ntF :: SortedSymbol ()
ntF = SS "F" (Base ())

ntS :: SortedSymbol ()
ntS = SS "S" (Base ())

rule1 :: Rule ()
rule1 = Rule {ruleF = ntF, ruleVars = ["x1","x2"], rulePattern = Nothing, ruleBody = tpe}

pmrs1 :: PMRS ()
pmrs1 = PMRS empty empty empty empty ntS

main :: IO ()
main = do
	putStrLn "Test"
	print rule1
	print pmrs1