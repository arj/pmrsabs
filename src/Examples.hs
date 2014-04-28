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


example5 = (example5_1, example5_2, example5_3)
  where
    x :: Term ()
    x = var "x"
    y :: Term ()
    y = var "y"
    z :: Term ()
    z = var "z"
    n :: Term ()
    n = symbol "N" o
    b :: Term ()
    b = symbol "b" o
    f :: Term ()
    f = symbol "F" o
    g :: Term ()
    g = symbol "G" o
    c :: Term ()
    c = symbol "c" o
    a :: Term ()
    a = symbol "a" o

    s1 :: Binding ()
    s1 = SM.fromList [("x", app y [b])
                     ,("x",n)
                     ,("y",app f [z])
                     ,("z",a)]

    s2 :: Binding ()
    s2 = SM.fromList [("x", app f [y,z])
                     ,("y",z)
                     ,("y",a)
                     ,("z",b)]

    example5_1 :: Set (Term ())
    example5_1 = substHead s1 $ app x [c]

    example5_2 :: Set (Term ())
    example5_2 = substHead s2 $ app x [c]

    example5_3 :: Set (Term ())
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
ssFilter = SortedSymbol "Filter" $ o ~> o ~> o
ssS      = SortedSymbol "S" o
ssN      = SortedSymbol "N" o
ssListN  = SortedSymbol "ListN" o
ssMap2   = SortedSymbol "Map2" $ (o ~> o) ~> (o ~> o) ~> o ~> o
ssKZero  = SortedSymbol "KZero" $ o ~> o
ssKOne   = SortedSymbol "KOne"  $ o ~> o
--
ssMain = SortedSymbol "Main" $ o ~> o
ssIf   = SortedSymbol "If" $ o ~> o ~> o
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

example2pmrs :: PMRS ()
example2pmrs = PMRS sigma nonterminals r ssMain
  where
    sigma :: Set (SortedSymbol ())
    sigma = S.fromList [sstrue
                 ,ssfalse
                 ,ssnil
                 ,sscons
                 ,ssz
                 ,sss
                 ]
    nonterminals :: Set (SortedSymbol ())
    nonterminals = S.fromList [ssMain
                                ,ssIf
                                ,ssNz
                                ,ssFilter
                                ,ssS
                                ,ssN
                                ,ssListN]
    r :: Rules ()
    r = listToRules [Rule ssMain [] (Just m) $ app nFilter [nz, m]
                   ,Rule ssIf ["a","b"] (Just true) $ a
                   ,Rule ssIf ["a","b"] (Just false) $ b
                   ,Rule ssNz [] (Just z) $ false
                   ,Rule ssNz [] (Just $ app s [varn]) $ true
                   ,Rule ssFilter ["p"] (Just nil) $ nil
                   ,Rule ssFilter ["p"] (Just $ app cons [x,xs]) $
                        mkIf (mkCons x $ mkFilter p xs) (mkFilter p xs) (app p [x])
                   ,Rule ssS [] Nothing $ listN
                   ,Rule ssN  [] Nothing $ z
                   ,Rule ssN  [] Nothing $ app s [n]
                   ,Rule ssListN  [] Nothing $ nil
                   ,Rule ssListN  [] Nothing $ mkCons n listN
                   ]

example8pmrs :: PMRS ()
example8pmrs = PMRS sigma nonterminals r ssMain
  where
    sigma = S.fromList [ssnil
                 ,sscons
                 ,sszero
                 ,ssone
                 ]
    nonterminals = S.fromList [ssMain
                                ,ssMap2
                                ,ssKZero
                                ,ssKOne]
    r = listToRules [Rule ssMain [] (Just m) $ mkMap2 kzero kone m
                    ,Rule ssMap2 ["phi","psi"] (Just nil) $ nil
                    ,Rule ssMap2 ["phi","psi"] (Just $ app cons [x,xs]) $
                        mkCons (app phi [x]) (mkMap2 psi phi xs)
                    ,Rule ssKZero ["x_1"] Nothing zero
                    ,Rule ssKOne  ["x_2"] Nothing one
                    --
                    ,Rule ssS [] Nothing nil
                    ,Rule ssS [] Nothing $ mkCons kzero nS
                    ]


exampleRmatch :: Binding ()
exampleRmatch = xi
  where
    --bnd = S.fromList [(p, nz), (x, n)]
    --t1  = (app p [x])
    --t2  = true
    bnd = S.fromList [(m, nS)]
    t1  = mkCons n listN
    t2  = mkCons x xs
    xi  = rmatch (PMRS.rules example2pmrs) t1 t2 bnd
