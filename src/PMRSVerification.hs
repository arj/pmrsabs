module PMRSVerification where

import Aux (prettyPrint)
import Automaton (ATT, determinizeATT, Quantifier(..))
import Abstraction as Abs
import HORS (HORS(..), CEx, determinizeHORS, findCEx, removeBrFromCEx)
import PMRS (PMRS, addHORS)
import Preface as P (check, problemResult)
import WPMRSTransformer as WT (fromPMRS)

data Result = RSuccess
            | RError CEx PMRS HORS

instance Show Result where
  show RSuccess = "Successfull"
  show (RError cex wpmrs hors) = "Invalid: " ++ show cex ++ "\n" ++ prettyPrint wpmrs ++ "\n" ++ prettyPrint hors

verifyInput :: PMRS -> HORS -> ATT -> IO (HORS, ATT)
verifyInput pmrs hors att = do
  pmrshors <- addHORS pmrs hors
  wpmrs    <- Abs.wPMRS (horsStart hors) pmrshors
  wpmrsAsHors    <- WT.fromPMRS wpmrs
  detWpmrsAsHors <- determinizeHORS wpmrsAsHors
  let detAtt = determinizeATT Existential "br__br" att
  return $ (detWpmrsAsHors, detAtt)

-- | Verifies a given PMRS with a HORS input against an ATT.
-- The result might be spurious.
verify :: FilePath -> PMRS -> HORS -> ATT -> IO Result
verify prefaceDir pmrs hors att = do
  pmrshors <- addHORS pmrs hors
  wpmrs    <- Abs.wPMRS (horsStart hors) pmrshors
  wpmrsAsHors    <- WT.fromPMRS wpmrs
  detWpmrsAsHors <- determinizeHORS wpmrsAsHors
  let detAtt = determinizeATT Existential "br__br" att
  res <- P.check prefaceDir detWpmrsAsHors detAtt
  case fmap (P.problemResult) res of
    Left msg -> error $ show msg
    Right True -> return RSuccess
    Right False ->
      let cex = removeBrFromCEx "br__br" $ findCEx detWpmrsAsHors detAtt in
      return $ RError cex wpmrs wpmrsAsHors