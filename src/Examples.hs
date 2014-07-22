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
    n = symbol "N"
    b :: Term
    b = symbol "b"
    f :: Term
    f = symbol "F"
    g :: Term
    g = symbol "G"
    c :: Term
    c = symbol "c"
    a :: Term
    a = symbol "a"

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
c    = var "c"
x    = var "x"
xs   = var "xs"
varn = var "n"
p    = var "p"
phi  = var "phi"
psi  = var "psi"
--
ssfoo    = SortedSymbol "foo" o
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
sS       = "S"
ssS      = SortedSymbol sS o
ssN      = SortedSymbol "N" o
ssListN  = SortedSymbol "ListN" o
ssMap2   = SortedSymbol "Map2" $ (o ~> o) ~> (o ~> o) ~> o ~> o
ssKZero  = SortedSymbol "KZero" $ o ~> o
ssKOne   = SortedSymbol "KOne"  $ o ~> o
--
sMain  = "Main"
ssMain = SortedSymbol sMain $ o ~> o
ssIf   = SortedSymbol "If" $ o ~> o ~> o ~> o
--
foo     = ssToSymbol ssfoo
true    = ssToSymbol sstrue
false   = ssToSymbol ssfalse
nil     = ssToSymbol ssnil
cons    = ssToSymbol sscons
z       = ssToSymbol ssz
s       = ssToSymbol sss
nz      = ssToSymbol ssNz
nFilter = ssToSymbol ssFilter
main    = ssToSymbol ssMain
sif     = ssToSymbol ssIf
nS      = ssToSymbol ssS
n       = ssToSymbol ssN
listN   = ssToSymbol ssListN
zero    = ssToSymbol sszero
one     = ssToSymbol ssone
kzero   = ssToSymbol ssKZero
kone    = ssToSymbol ssKOne
map2    = ssToSymbol ssMap2
--
mkIf a b cond = app sif [a,b,cond]
mkCons x xs = app cons [x,xs]
mkFilter p xs = app nFilter [p,xs]
mkMap2 phi psi lst = app map2 [phi,psi,lst]

mains = app main [nS]

example2pmrs :: Monad m => m PMRS
example2pmrs = mkPMRS sigma nonterminals r sMain
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
    r = listToRules [PMRSRule "Main" ["m"] Nothing $ app nFilter [nz, m]
                   ,PMRSRule "If" ["a","b"] (Just true) $ a
                   ,PMRSRule "If" ["a","b"] (Just false) $ b
                   ,PMRSRule "Nz" [] (Just z) $ false
                   ,PMRSRule "Nz" [] (Just $ app s [c]) $ true
                   ,PMRSRule "Filter" ["p"] (Just nil) $ nil
                   ,PMRSRule "Filter" ["p"] (Just $ app cons [x,app cons [foo,xs]]) $
                        mkIf (mkCons x $ mkFilter p xs) (mkFilter p xs) (app p [x])
                   ,PMRSRule "S" [] Nothing $ listN
                   ,PMRSRule "N"  [] Nothing $ z
                   ,PMRSRule "N"  [] Nothing $ app s [n]
                   ,PMRSRule "ListN"  [] Nothing $ nil
                   ,PMRSRule "ListN"  [] Nothing $ mkCons n listN
                   ]

example2wpmrs :: Monad m => m PMRS
example2wpmrs = do
    pmrs <- example2pmrs
    wPMRS sS pmrs

example8pmrs :: Monad m => m PMRS
example8pmrs = mkPMRS sigma nonterminals r sMain
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
    r = listToRules [PMRSRule "Main" [] (Just m) $ mkMap2 kzero kone m
                    ,PMRSRule "Map2" ["phi","psi"] (Just nil) $ nil
                    ,PMRSRule "Map2" ["phi","psi"] (Just $ app cons [x,xs]) $
                        mkCons (app phi [x]) (mkMap2 psi phi xs)
                    ,PMRSRule "KZero" ["x_1"] Nothing zero
                    ,PMRSRule "KOne"  ["x_2"] Nothing one
                    --
                    ,PMRSRule "S" [] Nothing nil
                    ,PMRSRule "S" [] Nothing $ mkCons zero nS
                    ]


exampleRmatch :: Monad m => m Binding
exampleRmatch = do
    rs <- liftM getRules $ example2pmrs
    let bnd = S.fromList [(m, nS)]
        t1  = mkCons n listN
        t2  = mkCons x xs
    return $ rmatch rs t1 t2 bnd
  where
    
    
