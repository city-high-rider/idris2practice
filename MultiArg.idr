module MultiArg

%default total

addNType : Nat -> Type
addNType 0 = Nat
addNType (S k) = Nat -> addNType k

addTheseHelper : (answerSoFar : Nat) -> (howMany : Nat) -> addNType howMany
addTheseHelper answerSoFar 0 = answerSoFar
addTheseHelper answerSoFar (S k) = (\next => addTheseHelper (answerSoFar + next) k)

addThese : (howMany : Nat) -> addNType howMany 
addThese = addTheseHelper 0

