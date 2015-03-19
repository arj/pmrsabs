module PMRSVerification where

import Automaton (ATT, determinizeATT, Quantifier(..))
import Abstraction as Abs
import HORS (HORS(..), CEx, determinizeHORS, findCEx, removeBrFromCEx)
import PMRS (PMRS, addHORS)
import Preface as P (check, problemResult)
import WPMRSTransformer as WT (fromPMRS)

data Result = RSuccess
            | RError CEx

instance Show Result where
  show RSuccess = "Successfull"
  show (RError cex) = "Counterexample: " ++ show cex

verifyInput :: PMRS -> HORS -> ATT -> IO (HORS, ATT)
verifyInput pmrs hors att = do
  pmrshors <- addHORS pmrs hors
  wpmrs    <- Abs.wPMRS (horsStart hors) pmrshors
  wpmrsAsHors    <- WT.fromPMRS wpmrs
  detWpmrsAsHors <- determinizeHORS wpmrsAsHors
  let detAtt = determinizeATT Universal "br__br" att
  return $ (detWpmrsAsHors, detAtt)

-- | Verifies a given PMRS with a HORS input against an ATT.
-- The result might be spurious.
verifyPMRS :: (String -> IO ()) -> FilePath -> PMRS -> HORS -> ATT -> IO Result
verifyPMRS verbose prefaceDir pmrs hors att = do
  --
  verbose "Combining PMRS and HORS"
  pmrshors <- addHORS pmrs hors
  --
  verbose "Transforming PMRS+HORS to wPMRS"
  wpmrs    <- Abs.wPMRS (horsStart hors) pmrshors
  --
  verbose "wPMRS to HORS"
  wpmrsAsHors    <- WT.fromPMRS wpmrs
  --
  verbose "Determinizing HORS"
  detWpmrsAsHors <- determinizeHORS wpmrsAsHors
  --
  verbose "Determinizing ATT"
  let detAtt = determinizeATT Universal "br__br" att
  --
  verbose "Calling Preface"
  res <- P.check prefaceDir detWpmrsAsHors detAtt
  --
  case fmap (P.problemResult) res of
    Left msg -> error $ show msg
    Right True -> return RSuccess
    Right False -> do
      verbose "Searching for counter example"
      let cex = removeBrFromCEx "br__br" $ findCEx detWpmrsAsHors detAtt
      return $ RError cex

verifyHORS ::  (String -> IO ()) -> FilePath -> Bool -> HORS -> ATT -> IO Result
verifyHORS verbose prefaceDir existential hors att = do
  --
  verbose "Determinizing HORS"
  detHors <- determinizeHORS hors
  --
  verbose "Determinizing ATT"
  let quantifier = if existential then Existential else Universal
  let detAtt = determinizeATT quantifier "br__br" att -- TODO Existential option?
  --
  verbose "Calling Preface"
  res <- P.check prefaceDir detHors detAtt
  --
  case fmap (P.problemResult) res of
    Left msg -> error $ show msg
    Right True -> return RSuccess
    Right False -> do
      verbose "Searching for counter example"
      let cex = removeBrFromCEx "br__br" $ findCEx detHors detAtt
      return $ RError cex