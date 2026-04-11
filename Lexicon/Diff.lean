import Lexicon.Materialize
import Lexicon.Observe

/-!
# Diff
Observe how annotation table diffs affect goal coverage.
-/

namespace Lexicon

def CoverageDelta := SearchGoal × Bool × Bool

def coverageDiff
    (fuel : Nat)
    (beforeChoices afterChoices : List Axiom)
    (marking : Marking)
    (goals : List SearchGoal) : List CoverageDelta :=
  let before := coverageReport fuel beforeChoices marking goals
  let after := coverageReport fuel afterChoices marking goals
  List.zipWith
    (fun lhs rhs => (lhs.fst, lhs.snd, rhs.snd))
    before
    after

def tableCoverageDiff
    (fuel : Nat)
    (codes : List LexiconCode)
    (beforeEntries afterEntries : List (String × Annotation))
    (marking : Marking)
    (goals : List SearchGoal) : List CoverageDelta :=
  coverageDiff fuel
    (materializeAll codes beforeEntries)
    (materializeAll codes afterEntries)
    marking
    goals

def newlyReachableGoals (diffs : List CoverageDelta) : List SearchGoal :=
  diffs.filterMap fun (goal, before, after) =>
    if (!before && after) then some goal else none

def newlyUnreachableGoals (diffs : List CoverageDelta) : List SearchGoal :=
  diffs.filterMap fun (goal, before, after) =>
    if (before && !after) then some goal else none

end Lexicon
