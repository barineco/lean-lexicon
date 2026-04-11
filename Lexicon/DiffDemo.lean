import Lexicon.AnnotationTable
import Lexicon.Diff
import Lexicon.Generated.Vendored
import Lexicon.ObserveDemo
import Lexicon.VendoredSearchDemo

/-!
# DiffDemo
Demo scenarios comparing annotation table diffs and their coverage impact.
-/

namespace Lexicon

def withoutSessionTable : List (String × Annotation) :=
  demoAnnotationTable.filter fun entry =>
    entry.fst != "com.atproto.server.createSession"

def demoCoverageDiff : List CoverageDelta :=
  tableCoverageDiff 2
    Lexicon.Generated.vendoredCodes
    withoutSessionTable
    demoAnnotationTable
    ∅
    observeGoals

def goalsNewlyReachableWithSession : List SearchGoal :=
  newlyReachableGoals demoCoverageDiff

def goalsLostWithoutSession : List SearchGoal :=
  newlyUnreachableGoals demoCoverageDiff

def selectedVsFullCoverageDiff : List CoverageDelta :=
  coverageDiff 2 selectedVendoredAxioms vendoredDemoAxioms ∅ observeGoals

def goalsOnlyInFullVendored : List SearchGoal :=
  newlyReachableGoals selectedVsFullCoverageDiff

def goalsLostInSelectedVendored : List SearchGoal :=
  newlyUnreachableGoals selectedVsFullCoverageDiff

end Lexicon
