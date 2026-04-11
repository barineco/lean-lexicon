import Lexicon.Interpretation

/-!
# Reachability
Minimal model for checking whether a goal is reachable from a marking, instead of enumerating per-endpoint requirements.
-/

namespace Lexicon

abbrev Goal := Finset Fact

def satisfies (marking : Marking) (goal : Goal) : Prop :=
  ∀ fact ∈ goal, fact ∈ marking

def step (ax : Axiom) (marking : Marking) : Option Marking :=
  if ax.enabled? marking then
    some (ax.fire marking)
  else
    none

def reachesInOne (ax : Axiom) (marking : Marking) (goal : Goal) : Prop :=
  ∃ marking', step ax marking = some marking' ∧ satisfies marking' goal

inductive ReachesBy : Marking → List Axiom → Marking → Prop where
  | nil (marking : Marking) : ReachesBy marking [] marking
  | cons
      (ax : Axiom)
      (axs : List Axiom)
      (start mid finish : Marking)
      (hstep : step ax start = some mid)
      (hrest : ReachesBy mid axs finish) :
      ReachesBy start (ax :: axs) finish

def reachesGoalBy (start : Marking) (axs : List Axiom) (goal : Goal) : Prop :=
  ∃ finish, ReachesBy start axs finish ∧ satisfies finish goal

theorem step_preserves_marking
    {ax : Axiom}
    {start finish : Marking}
    (hstep : step ax start = some finish) :
    start ⊆ finish := by
  unfold step at hstep
  split_ifs at hstep
  · injection hstep with hfinish
    subst hfinish
    exact subset_fire ax start

theorem ReachesBy.start_subset_finish
    {start finish : Marking}
    {axs : List Axiom}
    (hreaches : ReachesBy start axs finish) :
    start ⊆ finish := by
  induction hreaches with
  | nil marking =>
      intro fact hfact
      exact hfact
  | cons ax axs start mid finish hstep hrest ih =>
      intro fact hfact
      exact ih (step_preserves_marking hstep hfact)

def profileGoal : Goal := {Fact.datum "profileViewDetailed"}

example : satisfies
    (profileAxiom.fire {Fact.capability "access_jwt", Fact.selfKey "actor"})
    profileGoal := by
  intro fact hfact
  have hfact' : fact = Fact.datum "profileViewDetailed" := by
    simpa [profileGoal] using hfact
  subst fact
  simp [profileAxiom, Axiom.fire, authSelfRead, TouchExpr.tokens]

example : reachesInOne
    profileAxiom
    {Fact.capability "access_jwt", Fact.selfKey "actor"}
    profileGoal := by
  refine ⟨profileAxiom.fire {Fact.capability "access_jwt", Fact.selfKey "actor"}, ?_, ?_⟩
  · simp [step, Axiom.enabled?, RequirementExpr.check, profileAxiom, authSelfRead, Axiom.fire]
  · intro fact hfact
    have hfact' : fact = Fact.datum "profileViewDetailed" := by
      simpa [profileGoal] using hfact
    subst fact
    simp [profileAxiom, Axiom.fire, authSelfRead, TouchExpr.tokens]

example : ¬ reachesInOne profileAxiom ∅ profileGoal := by
  intro h
  rcases h with ⟨marking', hstep, _⟩
  simp [step, Axiom.enabled?, RequirementExpr.check, profileAxiom, authSelfRead] at hstep

example : reachesGoalBy ∅ [createSessionAxiom, profileAxiom] profileGoal := by
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
      simpa [profileGoal] using hfact
    subst fact
    simp [profileAxiom, createSessionAxiom, Axiom.fire, authSelfRead, createSession,
      TouchExpr.tokens]

end Lexicon
