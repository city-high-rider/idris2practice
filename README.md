# idris2practice

A repository of various programs and proofs I have written to get practice with Idris2.

## Contents:

`MultiArg.idr` - Contains a variadic function that computes the sum of its arguments. This demonstrates that you can write well-typed variadic functions using dependent types. Right now it is a bit inconvenient to use, since you have to declare how many things you want to add using the first argument, e.g.
```idris2
addThese 3 10 15 5
-- Evaluates to 10 + 15 + 5 = 30.

addThese _ 10 15 5
-- Type error
```
Ideally, the first argument should be implicit and left to Idris to figure out. Maybe a good exercise to try in the future. I'm not sure if it's possible or not, but I feel like it should be.

`T6Q2.idr` - "If `f` : Nat -> Nat is computable and strictly increasing, show that the range of `f` is computable." Translating to Idris, it means that I need to model what it means for a function to be strictly increasing and write a function that, given a target `t`, either:
- Returns a natural number `x` and a proof that `f(x) = t`
- Returns a proof that there does not exist an `x` such that `f(x) = t`.

The file contains this funtion, and related lemmas. Since this is for practice, I also decided to implement my own model for the strictly greater than relation `>` instead of using the one from `Data.Nat`. Therefore, a good chunk of the proof is showing properties of `>`, e.g. transitivity, `0 > x` is uninhabited, etc.

`Div3.idr` - "Can there exist a number consisting of exactly 200 '1's and 200 '2's in any order that is a perfect square?" The answer is no, and I am trying to prove that in this module. It was a lot harder than expected, but I am also learning a lot. **this one's a work in progress.**
