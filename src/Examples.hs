module Examples (
	example5_1, example5_2, example5_3
	) where

import Term
import Sorts
import Abstraction

import Data.Set (Set)
--import qualified Data.Set as S

--import Data.MultiMap (MultiMap)
import qualified Data.MultiMap as MM

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