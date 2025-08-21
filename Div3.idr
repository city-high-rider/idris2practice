module Demos.Div3

import Data.Fin
import Data.Nat
import Decidable.Equality

infixr 8 <:

||| Represent a natural number as base 10, e.g.
||| 421 = 1 + 10 * (2 + 10 * (4))
public export
data Decimal : (representing : Nat) -> Type where
  MostSig : (digit : Fin 10) -> Decimal (finToNat digit)
  (<:) : (digit : Fin 10) -> (rest : Decimal k) -> Decimal (finToNat digit + 10 * k) 

||| Try to increment a digit. If there is no overflow, return the new digit and proof that it is indeed
||| the successor of the old one. Otherwise, return a proof that the digit was 9.
||| This implementation prioritizes simplicity above all else...
public export total
nudge : (d : Fin 10) -> Either (x ** finToNat {n = 10} x = S (finToNat d)) (d = 9)
nudge 0 = Left (1 ** Refl)
nudge 1 = Left (2 ** Refl)
nudge 2 = Left (3 ** Refl)
nudge 3 = Left (4 ** Refl)
nudge 4 = Left (5 ** Refl)
nudge 5 = Left (6 ** Refl)
nudge 6 = Left (7 ** Refl)
nudge 7 = Left (8 ** Refl)
nudge 8 = Left (9 ** Refl)
nudge 9 = Right Refl

public export total
bump_no_carry : Decimal k -> (newDigit : Fin 10) -> finToNat newDigit = S (finToNat digit) -> Decimal (S (plus (finToNat digit) (10 * k)))
bump_no_carry rest newDigit prf = let ans = newDigit <: rest in replace
  {p = (\target => Decimal (plus target (10*k)))} prf ans

-- The following three functions are made solely to prove the insanity required by bump_carry
public export total
abhorrence : (k : Nat) -> (depth : Nat) -> Nat
abhorrence k 0 = S (plus k 0)
abhorrence k (S j) = S (plus k (abhorrence k j))

public export total
delight : (k : Nat) -> (depth : Nat) -> Nat
delight k 0 = plus k 0
delight k (S j) = plus k (delight k j)

public export total
soothe : {d : Nat} -> abhorrence k d = S (plus d (delight k d))
soothe {d = 0} = Refl
soothe {d = (S j)} = rewrite soothe {k = k, d = j} in
                             rewrite sym (plusSuccRightSucc k (plus j (delight k j))) in
                                     rewrite plusAssociative j k (delight k j) in
                                             rewrite plusCommutative j k in
                                                     rewrite sym (plusAssociative k j (delight k j)) in Refl

public export total
bump_carry : Decimal (abhorrence k 9) -> Decimal (plus 10 (delight k 9))
bump_carry x = let res = soothe {k = k, d = 9} in rewrite sym res in x

||| Given a decimal view of x, produce a decimal view of S x.
public export total
bump : Decimal x -> Decimal (S x)
bump (MostSig digit) = case nudge digit of
                            Right Refl => 0 <: MostSig 1
                            (Left (newDigit ** prf)) => rewrite sym prf in MostSig newDigit
bump (digit <: rest) = case nudge digit of
                            (Left ((newDigit ** prf))) => bump_no_carry rest newDigit prf
                            (Right Refl) => let ans = 0 <: (bump rest) in bump_carry ans

||| Convert a natural number x to a decimal view of x.
||| Note: this is insanely slow
public export total
decimal : (x : Nat) -> Decimal x
decimal 0 = MostSig 0
decimal (S k) = bump (decimal k)

||| The sum of a number's digits.
public export total
sumDigits : Decimal k -> Nat
sumDigits (MostSig digit) = finToNat digit
sumDigits (digit <: rest) = finToNat digit + sumDigits rest

||| Count how many digits are in a number.
public export total
numDigits : Decimal k -> Nat
numDigits (MostSig digit) = 1
numDigits (digit <: rest) = 1 + numDigits rest

||| Count how many digits match a predicate
public export total
countThe : Decimal k -> (Fin 10 -> Bool) -> Nat
countThe (MostSig digit) pred = if pred digit then 1 else 0
countThe (digit <: rest) pred = if pred digit then 1 + countThe rest pred else countThe rest pred

||| A proof that a number is a perfect square. To construct it, you need the root.
public export total
data Square : Nat -> Type where
  Root : (x : Nat) -> Square (x * x)

||| Proof a number is divisible by n
total
divides : (a : Nat) -> (b : Nat) -> Type
a `divides` b = (k ** k * a = b)

public export total
puzzle : (d : Decimal k) -> numDigits d = 400 -> (d `countThe` (==1)) = 200 -> (d `countThe` (==2)) = 200 -> Not (Square k)
puzzle d nd400 hundred1s hundred2s kSquare = ?puzzle_rhs
