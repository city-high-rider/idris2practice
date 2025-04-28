module T6Q2

import Data.Nat
import Decidable.Equality

%default total

data MoreThan : Nat -> Nat -> Type where
  SucGTZ : NonZero k -> k `MoreThan` Z
  Bump : x `MoreThan` y -> S x `MoreThan` S y

data StrictlyIncreasing : (Nat -> Nat) -> Type where
  Indeed : (f : Nat -> Nat) -> (prfGen : (x,y : Nat) -> x `MoreThan` y -> f x `MoreThan` f y) -> StrictlyIncreasing f

zeroIsSmallest : Not (Z `MoreThan` x)
zeroIsSmallest (SucGTZ SIsNonZero) impossible

voidBump : Not (a `MoreThan` b) -> Not (S a `MoreThan` S b)
voidBump f (Bump x) = f x

voidBumpN : (n : Nat) -> Not (n `MoreThan` n)
voidBumpN 0 = zeroIsSmallest
voidBumpN (S k) = voidBump (voidBumpN k)

gtNotEq : {a,b : _} -> a `MoreThan` b -> Not (a = b)
gtNotEq x Refl = voidBumpN b x

gtTransitive : a `MoreThan` b -> b `MoreThan` c -> a `MoreThan` c
gtTransitive (SucGTZ x) (SucGTZ y) = SucGTZ x
gtTransitive (Bump x) (SucGTZ y) = SucGTZ SIsNonZero
gtTransitive (Bump x) (Bump y) = Bump (gtTransitive x y)

gtNonzeroGtOne : NonZero b -> MoreThan a b -> MoreThan a 1
gtNonzeroGtOne SIsNonZero (Bump (SucGTZ x)) = Bump (SucGTZ x)
gtNonzeroGtOne SIsNonZero (Bump (Bump x)) = Bump (SucGTZ SIsNonZero)

strongerTransitivity : a `MoreThan` b -> b `MoreThan` c -> a `MoreThan` (S c)
strongerTransitivity x (SucGTZ y) = gtNonzeroGtOne y x
strongerTransitivity (SucGTZ x) (Bump j) impossible
strongerTransitivity (Bump x) (Bump j) = Bump (strongerTransitivity x j)

data CompResult : (x : Nat) -> (bound : Nat) -> Type where
  Equal : (prf : x = bound) -> CompResult x bound
  BGTX : (prf : bound `MoreThan` x) -> CompResult x bound
  XGTB : (prf : x `MoreThan` bound) -> CompResult x bound

bumpCompResult : CompResult a b -> CompResult (S a) (S b)
bumpCompResult (Equal Refl) = Equal Refl
bumpCompResult (BGTX prf) = BGTX (Bump prf)
bumpCompResult (XGTB prf) = XGTB (Bump prf)

compTo : (x : Nat) -> (b : Nat) -> CompResult x b
compTo 0 0 = Equal Refl
compTo 0 (S k) = BGTX (SucGTZ SIsNonZero)
compTo (S k) 0 = XGTB (SucGTZ SIsNonZero)
compTo (S k) (S j) = bumpCompResult (compTo k j)

{-
Want to show: If f is strictly increasing, for any target t, there is some x such that f x > t.
We can do this by induction on t.
Base case: t = 0. Is there some x s.t f(x) > 0? Yes. Consider f(1). It must be bigger than zero.
Inductive case: If we know that there is some input x so that f(x) > t, consider f(x + 1).
Because the function is strictly increasing, this has to be bigger than t + 1.
-}

-- Base case:
randomLemma : a = b -> c `MoreThan` a -> c `MoreThan` b
randomLemma Refl x = x

itsInTheFuckingName : {a : _} -> Not (a = 0) -> NonZero a
itsInTheFuckingName {a = 0} f = void (f Refl)
itsInTheFuckingName {a = (S k)} f = SIsNonZero

fOneGtZ : StrictlyIncreasing f -> f 1 `MoreThan` 0
fOneGtZ (Indeed f prfGen) =
  let fOneGtFZero : (f 1 `MoreThan` f 0) = prfGen 1 0 (SucGTZ SIsNonZero) in
      case f 0 `decEq` 0 of
           (Yes prf) => randomLemma prf fOneGtFZero
           (No contra) => let fZNonZero : (NonZero (f 0)) = itsInTheFuckingName contra
                              fZGtZ : (f 0 `MoreThan` 0) = SucGTZ fZNonZero in gtTransitive fOneGtFZero fZGtZ

-- Inductive step:
succIncreases : {x : _} -> S x `MoreThan` x
succIncreases {x = 0} = SucGTZ SIsNonZero
succIncreases {x = (S k)} = Bump succIncreases

argBumpMeansOutputBump : {x, t : _} -> StrictlyIncreasing f -> f x `MoreThan` t -> f (S x) `MoreThan` (S t)
argBumpMeansOutputBump (Indeed f prfGen) z = let
  bumpedXMore : (S x `MoreThan` x) = succIncreases
  soOutputMore : (f (S x) `MoreThan` f x) = prfGen (S x) x bumpedXMore
  in strongerTransitivity soOutputMore z

-- Put them together:

alwaysExceeds : StrictlyIncreasing f -> (t : Nat) -> (input ** f input `MoreThan` t)
alwaysExceeds sif 0 = (1 ** fOneGtZ sif)
alwaysExceeds sif (S k) = let (prev ** prevProof) = sif `alwaysExceeds` k
                                            in (S prev ** argBumpMeansOutputBump sif prevProof)

{-
Now we can use this to see if something is in the range of the function.

What we want is, given a target, either a proof that there exists some x s.t. f(x) = target
OR a proof otherwise (which is equivalent to forall x. f(x) /= target)

We find some bound s.t. f(bound) > target and check f(x) for every x up to the bound.
This is total because we do a finite amount of checks, since the bound is some natural number.

If we can find the f(x) we are looking for, we are done and can return that. Otherwise, we build
up a catalog of evidence (this is what FailedUpTo encodes) that every input we've tried so far
has failed. e.g. f(0) /= target, f(1) /= target, f(2) /= target, ... f(bound) /= target.

Thus, if we do not find a suitable x in our search, we know that no number less than or equal
to the bound will work. Likewise, since f is strictly increasing, we know that no number greater
than the bound will work either. So we conclude that no input gives us our desired target, i.e.
target is not in the range of the function.
-}

data FailedUpTo : (f : Nat -> Nat) -> (target : Nat) -> (n : Nat) -> Type where
  ZFails : (zDoesntWork : Not (f Z = target)) -> FailedUpTo f target Z
  SFails : (prior : FailedUpTo f target k) -> (curDoesntWork : Not (f (S k) = target)) -> FailedUpTo f target (S k)

descend : (target : Nat) -> (from : Nat) -> (f : Nat -> Nat) -> Either (input ** f input = target) (FailedUpTo f target from)
descend target 0 f = case f 0 `decEq` target of
                          (Yes prf) => Left (0 ** prf)
                          (No contra) => Right (ZFails contra)
descend target (S k) f = case f (S k) `decEq` target of
                              (Yes prf) => Left (S k ** prf)
                              (No contra) => case descend target k f of
                                                  (Left works) => Left works
                                                  (Right doesnt) => Right (SFails doesnt contra)

cantOvershoot : {x : _} -> StrictlyIncreasing f -> (target : Nat) -> (upper : Nat) -> (prf : f upper `MoreThan` target) -> (x `MoreThan` upper -> Not (f x = target))
cantOvershoot (Indeed f prfGen) target upper prf = (\sg, sm =>
  let fXGtFUpper : (f x `MoreThan` f upper) = prfGen x upper sg
      fXGtTarget : (f x `MoreThan` target) = gtTransitive fXGtFUpper prf
  in gtNotEq fXGtTarget sm)

stepDown : {k : _} -> S k `MoreThan` x -> Either (k = x) (k `MoreThan` x)
stepDown (SucGTZ SIsNonZero) = case k of
                                    Z => Left Refl
                                    S n => Right (SucGTZ SIsNonZero)
stepDown (Bump p) = case k of
                         Z => void (zeroIsSmallest p)
                         S n => case stepDown p of
                                     (Left Refl) => Left Refl
                                     (Right y) => Right (Bump y)

getCounterEx : FailedUpTo f target k -> Not (f k = target)
getCounterEx (ZFails zDoesntWork) prf = zDoesntWork prf
getCounterEx (SFails prior curDoesntWork) prf = curDoesntWork prf

interpFail : {x : _} -> FailedUpTo f target x -> (x `MoreThan` input -> Not (f input = target))
-- This case is impossible, we need to help Idris see that.
-- We know x is more than some number, so it cannot be 0 because 0 is not more than anything.
interpFail {x = 0} _ z _ = void (zeroIsSmallest z)
interpFail {x = (S k)} (SFails prior _) z prf =
  case stepDown z of
       (Left Refl) => getCounterEx prior prf
       (Right y) => interpFail prior y prf

inRange : (target : Nat) -> StrictlyIncreasing f -> Dec (input ** f input = target)
inRange target sif@(Indeed f prfGen) = 
  let (bound ** fBoundGtTarget) = sif `alwaysExceeds` target
  in case descend target bound f of
    (Left success) => Yes success
    (Right failures) => No (\(x ** fXIsTarget) => case x `compTo` bound of
                 (Equal Refl) => getCounterEx failures fXIsTarget
                 (BGTX boundGtX) => interpFail failures boundGtX fXIsTarget
                 (XGTB xGtBound) => let counter = cantOvershoot sif target bound fBoundGtTarget
                                    in counter xGtBound fXIsTarget)

sIncreases : StrictlyIncreasing S
sIncreases = Indeed S (\x => \y => \z => Bump z)
