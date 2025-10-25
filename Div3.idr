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
soothe {d = (S j)} =
  rewrite soothe {k = k, d = j} in
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

||| Proof that a is congruent to b mod n
total
congMod : Nat -> Nat -> Nat -> Type
congMod n a b = (j ** a = b + j * n)

||| if a = c mod n and b = d mod n, then a * b = c * d mod n
total
congOverMul : {n, a, b, c, d : Nat} -> congMod n a c -> congMod n b d -> congMod n (a * b) (c * d)
congOverMul ((s ** aWithS)) ((t ** bWithT)) =
  -- a*b = cd + kn 
  rewrite aWithS in
  rewrite bWithT in
  -- (c + sn) * (d + tn) = cd + kn
  rewrite multDistributesOverPlusRight (c + s*n) d (t * n) in
  -- (c+sn)*d + (c+sn)*tn = cd + kn
  rewrite multDistributesOverPlusLeft c (s*n) d in
  -- (cd + (sn)d) + ((c+sn)*tn) = cd + kn
  rewrite sym (plusAssociative (c*d) ((s*n)*d) ((c+s*n)*(t*n))) in
  -- cd + ((sn)d + ((c + sn) * tn)) = cd + kn
  rewrite multAssociative (c+s*n) t n in
  -- cd + ((sn)d + (((c + sn) * t) * n)) = cd + kn
  rewrite multCommutative s n in
  -- cd + ((ns)d + (((c + sn) * t) * n)) = cd + kn
  rewrite sym (multAssociative n s d) in
  -- cd + (n(sd) + (((c + sn) * t) * n)) = cd + kn
  rewrite multCommutative n (s*d) in
  -- cd + ((sd)n + (((c + sn) * t) * n)) = cd + kn
  rewrite sym (multDistributesOverPlusLeft (s*d) ((c+(n*s))*t) n) in
  -- cd + ((sd + ((c + ns) * t)) * n) = cd + kn
  -- where k = (sd + ((c + ns) * t))
  (((s*d)+((c+(n*s))*t)) ** Refl)


||| 10 = 1 mod 3
total
tenCong1In3 : congMod 3 10 1
tenCong1In3 = (3 ** Refl)

||| Any power of 10 is congruent to 1 mod 3
total
power10C1Mod3 : {p : Nat} -> congMod 3 (power 10 p) 1
power10C1Mod3 {p = 0} = (0 ** Refl)
power10C1Mod3 {p = (S k)} = 
  -- We need to swap the *10 to the right, otherwise Idris will be too helpful and expand this as 
  -- a bunch of plusses, which we don't want as we're trying to distribute congruence over multiplication.
  rewrite multCommutative 10 (power 10 k) in
    congOverMul {n=3, a=(power 10 k), b=10, c=1, d=1} power10C1Mod3 tenCong1In3 

||| if a = c mod n and b = d mod n, then a + b = a' + b' mod n
||| i.e. congruence is preserved under addition.
total
congOverPlus : {n,a,b,c,d : Nat} -> congMod n a c -> congMod n b d -> congMod n (a + b) (c + d)
congOverPlus ((s ** aWithS)) ((t ** bWithT)) = 
  rewrite aWithS in
  rewrite bWithT in
  -- (c + sn) + (d + tn) = (c+d) + kn
  rewrite sym (plusAssociative c (s*n) (d + t*n)) in
  -- c + (sn + (d + tn)) = (c+d) + kn
  rewrite plusCommutative (s*n) (d+t*n) in
  -- c + ((d + tn) + sn) = (c+d) + kn
  rewrite sym (plusAssociative d (t*n) (s * n)) in
  -- c + (d + (tn + sn)) = (c+d) + kn
  rewrite plusAssociative c d (t*n + s*n) in
  -- (c + d) + (tn + sn) = (c+d) + kn
  rewrite sym (multDistributesOverPlusLeft t s n) in
  -- (c + d) + (t + s)n = (c+d) + kn
  -- where k = t + s
  ((t+s) ** Refl)

total
nestedMultSwap : (left : Nat) -> (center : Nat) -> (right : Nat) -> (left*center)*right = (left*right)*center
nestedMultSwap left center right=
  rewrite sym (multAssociative left center right) in
  rewrite multCommutative center right in
  rewrite multAssociative left right center in Refl

total
factor3from9 : (a : Nat) -> a * 9 = (a*3)*3
factor3from9 a =
  rewrite sym (multAssociative a 3 3) in Refl

||| a number is equal to the sum of its digits mod 3.
total
kCongDigits3 : (d : Decimal n) -> congMod 3 n (sumDigits d)
kCongDigits3 (MostSig digit) = (0 ** rewrite plusZeroRightNeutral (finToNat digit) in Refl)
kCongDigits3 (digit <: rest) = let (h ** prf) = kCongDigits3 rest in
  rewrite prf in
  rewrite multCommutative 10 (sumDigits rest + h*3) in
  rewrite multDistributesOverPlusLeft (sumDigits rest) (h*3) 10 in
  rewrite multRightSuccPlus (sumDigits rest) 9 in
  rewrite sym (plusAssociative (sumDigits rest) ((sumDigits rest) * 9) ((h*3)*10)) in
  rewrite plusAssociative (finToNat digit) (sumDigits rest) ((sumDigits rest)*9 + (h*3)*10) in
  rewrite nestedMultSwap h 3 10 in
  rewrite factor3from9 (sumDigits rest) in
  rewrite sym (multDistributesOverPlusLeft (mult (sumDigits rest) 3) (mult h 10) 3) in
  ((plus (mult (sumDigits rest) 3) (mult h 10)) ** Refl)

total
sumDigitsDiv3NumDiv3 : {n : Nat} -> (d : Decimal n) -> 3 `divides` sumDigits d -> 3 `divides` n
sumDigitsDiv3NumDiv3 (MostSig digit) ((t ** sdWithT)) = rewrite sym sdWithT in (t ** Refl)
sumDigitsDiv3NumDiv3 (digit <: rest) ((t ** sdWithT)) = ?h
{-
The proof will be by contradiction.
Suppose K is a square. Then there must be a root R such that K = R * R.

There are 400 digits in the decimal representation of K. 200 of them are 1s, and 200 of them are 2s.
Therefore, the sum of the digits of K is 600.

Since the sum of the digits of K is 600, which is divisible by 3, it means that K is divisible by 3.
Therefore there is some T such that K = 3*T

Since the sum of the digits of K is 600, which is not divisible by 9, it means that K is not divisible by 9.

Since 3 is prime and it divides K, which is R * R, that means 3 must also divide R.

Since 3 divides R, there is some S such that R = 3S.

By substitution, K = (3S) * (3S) or K = 9*(s*s)

Therefore, K is divisible by 9. This contradicts the previous statement which says K is not divisible by 9.

We have reached a contradiction - this means K cannot be square, as required. QED
-}

public export total
puzzle : (d : Decimal k) -> numDigits d = 400 -> (d `countThe` (==1)) = 200 -> (d `countThe` (==2)) = 200 -> Not (Square k)
puzzle d nd400 hundred1s hundred2s kSquare = ?puzzle_rhs
