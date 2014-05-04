{-# LANGUAGE ScopedTypeVariables #-}
module Examples
--(
--  example5,
--  example2pmrs,
--  exampleRmatch
--)
where

import           Abstraction
import           PMRS
import           Sorts
import           Term
import           RSFD

import           Data.Set      (Set)
import qualified Data.Set      as S

import Data.SetMap (SetMap)
import qualified Data.SetMap as SM

import Control.Monad


example5 = (example5_1, example5_2, example5_3)
  where
    x :: Term
    x = var "x"
    y :: Term
    y = var "y"
    z :: Term
    z = var "z"
    n :: Term
    n = symbol "N" o
    b :: Term
    b = symbol "b" o
    f :: Term
    f = symbol "F" o
    g :: Term
    g = symbol "G" o
    c :: Term
    c = symbol "c" o
    a :: Term
    a = symbol "a" o

    s1 :: Binding
    s1 = SM.fromList [("x", app y [b])
                     ,("x",n)
                     ,("y",app f [z])
                     ,("z",a)]

    s2 :: Binding
    s2 = SM.fromList [("x", app f [y,z])
                     ,("y",z)
                     ,("y",a)
                     ,("z",b)]

    example5_1 :: Set Term
    example5_1 = substHead s1 $ app x [c]

    example5_2 :: Set Term
    example5_2 = substHead s2 $ app x [c]

    example5_3 :: Set Term
    example5_3 = substHead s2 $ app f [x, app g [x]]

m    = var "m"
a    = var "a"
b    = var "b"
x    = var "x"
xs   = var "xs"
varn = var "n"
p    = var "p"
phi  = var "phi"
psi  = var "psi"
--
sszero   = SortedSymbol "zero" o
ssone    = SortedSymbol "one" o
sstrue   = SortedSymbol "true" o
ssfalse  = SortedSymbol "false" o
ssnil    = SortedSymbol "nil" o
sscons   = SortedSymbol "cons" $ o ~> o ~> o
ssz      = SortedSymbol "z" o
sss      = SortedSymbol "s" $ o ~> o
ssNz     = SortedSymbol "Nz" $ o ~> o
ssFilter = SortedSymbol "Filter" $ (o ~> o) ~> o ~> o
ssS      = SortedSymbol "S" o
ssN      = SortedSymbol "N" o
ssListN  = SortedSymbol "ListN" o
ssMap2   = SortedSymbol "Map2" $ (o ~> o) ~> (o ~> o) ~> o ~> o
ssKZero  = SortedSymbol "KZero" $ o ~> o
ssKOne   = SortedSymbol "KOne"  $ o ~> o
--
ssMain = SortedSymbol "Main" $ o ~> o
ssIf   = SortedSymbol "If" $ o ~> o ~> o ~> o
--
true   = ssToSymbol sstrue
false  = ssToSymbol ssfalse
nil    = ssToSymbol ssnil
cons   = ssToSymbol sscons
z      = ssToSymbol ssz
s      = ssToSymbol sss
nz     = ssToSymbol ssNz
nFilter = ssToSymbol ssFilter
main   = ssToSymbol ssMain
sif    = ssToSymbol ssIf
nS     = ssToSymbol ssS
n      = ssToSymbol ssN
listN  = ssToSymbol ssListN
zero   = ssToSymbol sszero
one    = ssToSymbol ssone
kzero  = ssToSymbol ssKZero
kone   = ssToSymbol ssKOne
map2   = ssToSymbol ssMap2
--
mkIf a b cond = app sif [a,b,cond]
mkCons x xs = app cons [x,xs]
mkFilter p xs = app nFilter [p,xs]
mkMap2 phi psi lst = app map2 [phi,psi,lst]

example2pmrs :: Monad m => m PMRS
example2pmrs = mkPMRS sigma nonterminals r ssMain
  where
    sigma :: RankedAlphabet
    sigma = mkRankedAlphabet [sstrue
                 ,ssfalse
                 ,ssnil
                 ,sscons
                 ,ssz
                 ,sss
                 ]
    nonterminals :: RankedAlphabet
    nonterminals = mkRankedAlphabet [ssMain
                                ,ssIf
                                ,ssNz
                                ,ssFilter
                                ,ssS
                                ,ssN
                                ,ssListN]
    r :: PMRSRules
    r = listToRules [PMRSRule ssMain [] (Just m) $ app nFilter [nz, m]
                   ,PMRSRule ssIf ["a","b"] (Just true) $ a
                   ,PMRSRule ssIf ["a","b"] (Just false) $ b
                   ,PMRSRule ssNz [] (Just z) $ false
                   ,PMRSRule ssNz [] (Just $ app s [varn]) $ true
                   ,PMRSRule ssFilter ["p"] (Just nil) $ nil
                   ,PMRSRule ssFilter ["p"] (Just $ app cons [x,xs]) $
                        mkIf (mkCons x $ mkFilter p xs) (mkFilter p xs) (app p [x])
                   ,PMRSRule ssS [] Nothing $ listN
                   ,PMRSRule ssN  [] Nothing $ z
                   ,PMRSRule ssN  [] Nothing $ app s [n]
                   ,PMRSRule ssListN  [] Nothing $ nil
                   ,PMRSRule ssListN  [] Nothing $ mkCons n listN
                   ]

example8pmrs :: Monad m => m PMRS
example8pmrs = mkPMRS sigma nonterminals r ssMain
  where
    sigma = mkRankedAlphabet [ssnil
                 ,sscons
                 ,sszero
                 ,ssone
                 ]
    nonterminals = mkRankedAlphabet [ssMain
                                ,ssMap2
                                ,ssKZero
                                ,ssKOne]
    r = listToRules [PMRSRule ssMain [] (Just m) $ mkMap2 kzero kone m
                    ,PMRSRule ssMap2 ["phi","psi"] (Just nil) $ nil
                    ,PMRSRule ssMap2 ["phi","psi"] (Just $ app cons [x,xs]) $
                        mkCons (app phi [x]) (mkMap2 psi phi xs)
                    ,PMRSRule ssKZero ["x_1"] Nothing zero
                    ,PMRSRule ssKOne  ["x_2"] Nothing one
                    --
                    ,PMRSRule ssS [] Nothing nil
                    ,PMRSRule ssS [] Nothing $ mkCons kzero nS
                    ]


exampleRmatch :: Monad m => m Binding
exampleRmatch = do
    rs <- liftM getRules $ example2pmrs
    let bnd = S.fromList [(m, nS)]
        t1  = mkCons n listN
        t2  = mkCons x xs
    return $ rmatch rs t1 t2 bnd
  where
    
    
