import           Abstraction
import           Examples hiding (main)
import           PMRS
import           Sorts
import           Term
import           PMRSParser

--import Data.MultiMap (MultiMap)
import qualified Data.MultiMap as MM

import           Data.Set      (Set)
import qualified Data.Set      as S

import           Data.Map      (Map)
import qualified Data.Map      as M

tpe :: Term
tpe = var "phi"

ntF :: SortedSymbol
ntF = SortedSymbol "F" $ Base

rule1 :: PMRSRule
rule1 = PMRSRule (ssF ntF) ["x1","x2"] Nothing tpe

pmrs1 :: Monad m => m PMRS
pmrs1 = mkPMRS M.empty M.empty MM.empty "S"


example5_1 :: Set Term
example5_2 :: Set Term
example5_3 :: Set Term
(example5_1,example5_2,example5_3) = example5

main :: IO ()
main = do
	--putStrLn "Test"
	--print rule1
	--print pmrs1
	--print $ wPMRS pmrs1
	--print $ sPMRS pmrs1
	--print example5_1
	--print example5_2
	--print example5_3
	--print example2pmrs
	res <- exampleRmatch
	print res