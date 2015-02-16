{-# LANGUAGE ScopedTypeVariables #-}
module Examples

where

import           Data.Set      (Set)
import qualified Data.Set      as S
import qualified Data.SetMap as SM
import qualified Data.Map as M
import           Control.Monad (liftM)

import Data.MultiMap (MultiMap)
import qualified Data.MultiMap as MM

import           Abstraction
import           PMRS
import HORS
import           Sorts
import           Term
import Automaton


example5 :: (Set Term, Set Term, Set Term)
example5 = (example5_1, example5_2, example5_3)
  where
    f :: Term
    f = symbol "F"
    g :: Term
    g = symbol "G"

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

m :: Term
m    = var "m"

a:: Term
a    = var "a"

b :: Term
b    = var "b"

c :: Term
c    = var "c"

x :: Term
x    = var "x"

y :: Term
y = var "y"

xs :: Term
xs   = var "xs"

varn :: Term
varn = var "n"

p :: Term
p    = var "p"

phi :: Term
phi  = var "phi"

psi :: Term
psi  = var "psi"

ssfoo :: SortedSymbol
ssfoo    = SortedSymbol "foo" o

sszero :: SortedSymbol
sszero   = SortedSymbol "zero" o

ssone :: SortedSymbol
ssone    = SortedSymbol "one" o

sstrue :: SortedSymbol
sstrue   = SortedSymbol "true" o

ssfalse :: SortedSymbol
ssfalse  = SortedSymbol "false" o

ssnil :: SortedSymbol
ssnil    = SortedSymbol "nil" o

sscons :: SortedSymbol
sscons   = SortedSymbol "cons" $ o ~> o ~> o

ssz :: SortedSymbol
ssz      = SortedSymbol "z" o

sss :: SortedSymbol
sss      = SortedSymbol "s" $ o ~> o

ssNz :: SortedSymbol
ssNz     = SortedSymbol "Nz" $ o ~> o

ssFilter :: SortedSymbol
ssFilter = SortedSymbol "Filter" $ (o ~> o) ~> o ~> o

sS :: String
sS = "S"

ssS :: SortedSymbol
ssS = SortedSymbol sS o

ssN :: SortedSymbol
ssN = SortedSymbol "N" o

ssListN :: SortedSymbol
ssListN = SortedSymbol "ListN" o

ssMap2 :: SortedSymbol
ssMap2  = SortedSymbol "Map2" $ (o ~> o) ~> (o ~> o) ~> o ~> o

ssKZero :: SortedSymbol
ssKZero = SortedSymbol "KZero" $ o ~> o

ssKOne :: SortedSymbol
ssKOne = SortedSymbol "KOne"  $ o ~> o

sMain :: String
sMain = "Main"

ssMain :: SortedSymbol
ssMain = SortedSymbol sMain $ o ~> o

ssIf :: SortedSymbol
ssIf   = SortedSymbol "If" $ o ~> o ~> o ~> o

foo :: Term
foo     = ssToSymbol ssfoo
true :: Term
true    = ssToSymbol sstrue
false :: Term
false   = ssToSymbol ssfalse
nil :: Term
nil     = ssToSymbol ssnil
cons :: Term
cons    = ssToSymbol sscons
z :: Term
z       = ssToSymbol ssz
s :: Term
s       = ssToSymbol sss
nz :: Term
nz      = ssToSymbol ssNz
nFilter :: Term
nFilter = ssToSymbol ssFilter
main :: Term
main    = ssToSymbol ssMain
sif :: Term
sif     = ssToSymbol ssIf
nS :: Term
nS      = ssToSymbol ssS
n :: Term
n       = ssToSymbol ssN
listN :: Term
listN   = ssToSymbol ssListN
zero :: Term
zero    = ssToSymbol sszero
one :: Term
one     = ssToSymbol ssone
kzero :: Term
kzero   = ssToSymbol ssKZero
kone :: Term
kone    = ssToSymbol ssKOne
map2 :: Term
map2    = ssToSymbol ssMap2

mkIf :: Term -> Term -> Term -> Term
mkIf t1 t2 cond = app sif [t1,t2,cond]

mkCons :: Term -> Term -> Term
mkCons v rest = app cons [v,rest]

mkFilter :: Term -> Term -> Term
mkFilter predicate lst = app nFilter [predicate,lst]

mkMap2 :: Term -> Term -> Term -> Term
mkMap2 pred1 pred2 lst = app map2 [pred1, pred2 ,lst]

mains :: Term
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
                   ,PMRSRule "Filter" ["p"] (Just $ mkCons x xs) $
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
                                ,ssKOne
                                ,ssS]
    r = listToRules [PMRSRule "Main" ["m"] Nothing $ mkMap2 kzero kone m
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
    
exampleDetWpmrs :: Monad m => m PMRS
exampleDetWpmrs = mkPMRS sigma nonterminals r "S"
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
                   ,PMRSRule "Filter" ["p"] (Just $ mkCons x xs) $
                        mkIf (mkCons n $ mkFilter p listN) (mkFilter p listN) (app p [n])
                   ,PMRSRule "S" [] Nothing $ app main [listN]
                   ,PMRSRule "N"  [] Nothing $ app s [z]
                   ,PMRSRule "ListN"  [] Nothing $ mkCons n listN
                   ]

att1 :: ATT
att1 = ATT (MM.fromList
  [(("q0","a"),S.fromList [(1,"q1"),(2,"q2")])
  ,(("q0","cons"),S.fromList [(1,"q0"),(2,"q1")])
  ]
  ) "q0"

hors1 :: Monad m => m HORS
hors1 = mkHORS sigma nonterminals r "S"
  where
    sigma :: RankedAlphabet
    sigma = mkRankedAlphabet [sscons
                 ,ssz
                 ,sss
                 ]
    nonterminals :: RankedAlphabet
    nonterminals = mkRankedAlphabet [ssS
                                ,ssN
                                ,ssListN]
    r :: HORSRules
    r = mkHorsRules [HORSRule "S" [] $ listN
                  ,HORSRule "N"  [] $ app s [z]
                  ,HORSRule "ListN" [] $ mkCons n listN
                  ]
horsndet :: Monad m => m HORS
horsndet = mkHORS sigma nonterminals r "S"
  where
    sigma :: RankedAlphabet
    sigma = mkRankedAlphabet [sscons
                 ,ssz
                 ,sss
                 ,ssnil
                 ]
    nonterminals :: RankedAlphabet
    nonterminals = mkRankedAlphabet [ssS
                                ,ssN
                                ,ssListN]
    r :: HORSRules
    r = mkHorsRules [HORSRule "S" [] $ listN
                  ,HORSRule "N"  [] $ app s [n]
                  ,HORSRule "N"  [] $ z
                  ,HORSRule "ListN" [] $ mkCons n listN
                  ,HORSRule "ListN" [] $ nil
                  ]
