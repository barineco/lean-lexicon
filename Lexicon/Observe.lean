import Lexicon.Search

/-!
# Observe
Observation layer that reduces search results to comparable values.
-/

namespace Lexicon

def countReachable
    (fuel : Nat)
    (choices : List Axiom)
    (marking : Marking)
    (goal : SearchGoal) : Nat :=
  (searchAll fuel choices marking goal).length

def chooseShorter
    (best : Option (List String))
    (candidate : List String) : Option (List String) :=
  match best with
  | none => some candidate
  | some current =>
      if candidate.length < current.length then
        some candidate
      else
        some current

def shortestPath
    (fuel : Nat)
    (choices : List Axiom)
    (marking : Marking)
    (goal : SearchGoal) : Option (List String) :=
  (searchAll fuel choices marking goal).foldl chooseShorter none

def unreachableGoals
    (fuel : Nat)
    (choices : List Axiom)
    (marking : Marking)
    (goals : List SearchGoal) : List SearchGoal :=
  goals.filter fun goal => shortestPath fuel choices marking goal |>.isNone

def coverageReport
    (fuel : Nat)
    (choices : List Axiom)
    (marking : Marking)
    (goals : List SearchGoal) : List (SearchGoal × Bool) :=
  goals.map fun goal => (goal, (shortestPath fuel choices marking goal).isSome)

end Lexicon
