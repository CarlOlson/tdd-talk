module Main
import Data.Vect
%default total

-- Example 1: Peano Numbers
data Peano =
  Zero
| Succ Peano

one : Peano
one = Succ Zero

two : Peano
two = Succ one

pred : Peano -> Peano
pred Zero = Zero
pred (Succ x) = x

padd : Peano -> Peano -> Peano
padd Zero y = y
padd (Succ x) y = Succ (padd x y)

onePlusOnuEqualsTwo : (padd Main.one Main.one) = Main.two
onePlusOnuEqualsTwo = Refl

xPlusZeroEqualsOne : (x : Peano) -> (padd Zero x) = x
xPlusZeroEqualsOne x = Refl


-- Example 2: List & Vector Reversal
listReverse : List t -> List t
listReverse [] = []
listReverse (x :: xs) = (listReverse xs) ++ [x]

plusOne : (len : Nat) -> S len = len + 1
plusOne Z = Refl
plusOne (S k) = rewrite plusOne k in Refl

vectReverse : Vect n t -> Vect n t
vectReverse [] = []
vectReverse {n=S n} (x :: xs) =
  rewrite plusOne n in (vectReverse xs) ++ [x]
