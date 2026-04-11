import Lexicon.Materialize
import Lexicon.Search
import Lexicon.Observe
import Lexicon.VendoredSearchDemo

/-!
# ObserveDemo
Demo scenarios for observation-layer queries over vendored axioms.
-/

namespace Lexicon

def observeGoals : List SearchGoal := [
  [Fact.datum "profileViewDetailed"],
  [Fact.datum "feedViewPost[]"],
  [Fact.datum "notification[]"]
]

def vendoredReachableProfileCount : Nat :=
  countReachable 2 vendoredDemoAxioms ∅ [Fact.datum "profileViewDetailed"]

def vendoredShortestProfilePath : Option (List String) :=
  shortestPath 2 vendoredDemoAxioms ∅ [Fact.datum "profileViewDetailed"]

def vendoredCoverage : List (SearchGoal × Bool) :=
  coverageReport 2 vendoredDemoAxioms ∅ observeGoals

def vendoredUnreachableGoals : List SearchGoal :=
  unreachableGoals 2 vendoredDemoAxioms ∅ observeGoals

def selectedVendoredCoverage : List (SearchGoal × Bool) :=
  coverageReport 2 selectedVendoredAxioms ∅ observeGoals

def selectedVendoredUnreachableGoals : List SearchGoal :=
  unreachableGoals 2 selectedVendoredAxioms ∅ observeGoals

end Lexicon
