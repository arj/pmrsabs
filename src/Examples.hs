{-# LANGUAGE ScopedTypeVariables #-}
module Examples (
  example5,
  example2pmrs,
  exampleRmatch
  ) where

import           Abstraction
import           PMRS
import           Sorts
import           Term

import           Data.Set      (Set)
import qualified Data.Set      as S

--import Data.MultiMap (MultiMap)
import qualified Data.MultiMap as MM


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
    s1 = MM.fromList [("x", app y [b])
                     ,("x",n)
                     ,("y",app f [z])
                     ,("z",a)]

    s2 :: Binding ()
    s2 = MM.fromList [("x", app f [y,z])
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
--
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
--
mkIf a b cond = app sif [a,b,cond]
mkCons x xs = app cons [x,xs]
mkFilter p xs = app nFilter [p,xs]

example2pmrs :: PMRS ()
example2pmrs = PMRS sigma nonterminals r ssS
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
    --r :: Set (Rule a)
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
