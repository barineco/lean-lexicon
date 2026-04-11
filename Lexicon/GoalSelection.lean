import Lexicon.DiffDemo
import Lexicon.ObserveDemo
import Lexicon.Reachability

/-!
# GoalSelection
Classify observed goals into trivial / nontrivial / unreachable to select theorem targets.
-/

namespace Lexicon

def trivialObservationGoal : SearchGoal :=
  [Fact.datum "repoCommitStream"]

def unreachableObservationGoal : SearchGoal :=
  [Fact.datum "missingObservation"]

def goalSelectionTargets : List SearchGoal :=
  trivialObservationGoal :: observeGoals ++ [unreachableObservationGoal]

def goalSelectionCoverage : List (SearchGoal × Bool) :=
  coverageReport 2 vendoredDemoAxioms ∅ goalSelectionTargets

def trivialGoals : List SearchGoal :=
  coverageReport 1 vendoredDemoAxioms ∅ goalSelectionTargets
    |>.filterMap fun (goal, reachable) => if reachable then some goal else none

def structurallyUnreachableGoals : List SearchGoal :=
  unreachableGoals 2 vendoredDemoAxioms ∅ goalSelectionTargets

def theoremCandidateGoals : List SearchGoal :=
  goalsNewlyReachableWithSession

theorem profileReachableAfterCreateSession :
    reachesGoalBy ∅ [createSessionAxiom, profileAxiom] {Fact.datum "profileViewDetailed"} := by
  refine ⟨profileAxiom.fire (createSessionAxiom.fire ∅), ?_, ?_⟩
  · refine ReachesBy.cons createSessionAxiom [profileAxiom] ∅
      (createSessionAxiom.fire ∅)
      (profileAxiom.fire (createSessionAxiom.fire ∅))
      ?_
      ?_
    · simp [step, Axiom.enabled?, RequirementExpr.check, createSessionAxiom,
        createSession, Axiom.fire]
    · refine ReachesBy.cons profileAxiom [] (createSessionAxiom.fire ∅)
        (profileAxiom.fire (createSessionAxiom.fire ∅))
        (profileAxiom.fire (createSessionAxiom.fire ∅))
        ?_
        ?_
      · simp [step, Axiom.enabled?, RequirementExpr.check, profileAxiom, authSelfRead,
          createSessionAxiom, createSession, Axiom.fire, TouchExpr.tokens]
      · exact ReachesBy.nil _
  · intro fact hfact
    have hfact' : fact = Fact.datum "profileViewDetailed" := by
      simpa using hfact
    subst fact
    simp [profileAxiom, createSessionAxiom, Axiom.fire, authSelfRead, createSession,
      TouchExpr.tokens]

end Lexicon
