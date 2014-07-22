{-# LANGUAGE TypeSynonymInstances,FlexibleInstances #-}
module HORS where

import Term
import Sorts
import CommonRS

import Control.Monad

import qualified Data.Map as M
import qualified Data.MultiMap as MM

data HORSRule = HORSRule Symbol [String] Term
	deriving (Eq,Ord)

type HORSRules = Rules HORSRule

instance Show HORSRule where
  show (HORSRule f xs body) = unwords $ filter (not . null) [show f, unwords xs,"=>",show body]

data HORS = HORS RankedAlphabet RankedAlphabet HORSRules Symbol

mkHORS :: Monad m => RankedAlphabet -> RankedAlphabet -> HORSRules -> Symbol -> m HORS
mkHORS t nt rs s = do
  let rules = concat $ MM.elems rs
  forM_ rules $ \r@(HORSRule _ _ b) -> do
    let bnd = M.unions [t, nt]
    srt <- typeCheck bnd $ b
    if srt == o
      then return ()
      else fail ("The body of the rule " ++ show r ++ " is not of sort o but of sort " ++ show srt)
  when (not $ MM.member rs s) $ fail ("No rule for the start symbol: " ++ show s)
  return $ HORS t nt rs s