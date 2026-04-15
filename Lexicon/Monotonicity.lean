import Lexicon.Reachability
import Lexicon.Transition

/-!
# Monotonicity
The system is a monotone Petri net (no inhibitor arcs). Guard checks and firing are monotone
with respect to marking inclusion, placing it within the class of well-structured transition
systems where reachability is decidable.

## RichTransition monotonicity
RichTransition.fire (with consumes) is also monotone: if m₁ ⊆ m₂ then
(m₁ \ C) ∪ P ⊆ (m₂ \ C) ∪ P. This extends the WSTS membership to the
consume-aware model matching the Rust solver's Execute mode.
-/

namespace Lexicon

/-- RequirementExpr.check is monotone: enlarging the marking preserves enabledness. -/
theorem RequirementExpr.check_mono
    {m₁ m₂ : Marking}
    (hsub : m₁ ⊆ m₂)
    (req : RequirementExpr)
    (h : req.check m₁ = true) :
    req.check m₂ = true := by
  induction req with
  | trivial => rfl
  | capability cap =>
    simp [RequirementExpr.check] at h ⊢
    exact hsub h
  | datum token =>
    simp [RequirementExpr.check] at h ⊢
    exact hsub h
  | ownershipSelf key =>
    simp [RequirementExpr.check] at h ⊢
    exact hsub h
  | and lhs rhs ih_lhs ih_rhs =>
    simp [RequirementExpr.check, Bool.and_eq_true] at h ⊢
    exact ⟨ih_lhs h.1, ih_rhs h.2⟩

/-- Axiom.enabled? is monotone: enlarging the marking preserves enabledness. -/
theorem Axiom.enabled_mono
    {m₁ m₂ : Marking}
    (hsub : m₁ ⊆ m₂)
    (ax : Axiom)
    (h : ax.enabled? m₁ = true) :
    ax.enabled? m₂ = true := by
  exact RequirementExpr.check_mono hsub ax.annotation.requires h

/-- Axiom.fire is monotone: enlarging the marking enlarges the result. -/
theorem Axiom.fire_mono
    {m₁ m₂ : Marking}
    (hsub : m₁ ⊆ m₂)
    (ax : Axiom) :
    ax.fire m₁ ⊆ ax.fire m₂ := by
  intro fact hfact
  simp [Axiom.fire] at hfact ⊢
  rcases hfact with h | h
  · exact Or.inl (hsub h)
  · exact Or.inr h

/-- step is monotone: if a step succeeds on m₁ ⊆ m₂, it also succeeds on m₂ with a larger result. -/
theorem step_mono
    {m₁ m₂ : Marking}
    (hsub : m₁ ⊆ m₂)
    (ax : Axiom)
    {r₁ : Marking}
    (hstep : step ax m₁ = some r₁) :
    ∃ r₂, step ax m₂ = some r₂ ∧ r₁ ⊆ r₂ := by
  simp only [step] at hstep ⊢
  split at hstep
  case isTrue h₁ =>
    injection hstep with hr₁
    subst hr₁
    have h₂ : ax.enabled? m₂ = true := Axiom.enabled_mono hsub ax h₁
    rw [if_pos h₂]
    exact ⟨ax.fire m₂, rfl, Axiom.fire_mono hsub ax⟩
  case isFalse h₁ =>
    contradiction

/-- The system has no inhibitor arcs: RequirementExpr contains only positive membership tests.
    This is witnessed by check_mono. A system with inhibitor arcs would have a guard that
    becomes false when a token is added, violating monotonicity. -/
theorem no_inhibitor_arcs
    (req : RequirementExpr) {m₁ m₂ : Marking}
    (hsub : m₁ ⊆ m₂) (h : req.check m₁ = true) :
    req.check m₂ = true :=
  RequirementExpr.check_mono hsub req h

/-! ## RichTransition monotonicity (consume-aware model) -/

/-- RichTransition.enabled? is monotone: enlarging the marking preserves enabledness.
    Since enabled? checks requires ⊆ m, and m₁ ⊆ m₂ implies (requires ⊆ m₁) → (requires ⊆ m₂). -/
theorem RichTransition.enabled_mono
    {m₁ m₂ : Marking}
    (hsub : m₁ ⊆ m₂)
    (rt : RichTransition)
    (h : rt.enabled? m₁ = true) :
    rt.enabled? m₂ = true := by
  simp only [RichTransition.enabled?, decide_eq_true_eq] at h ⊢
  exact Finset.Subset.trans h hsub

/-- Finset.sdiff is monotone on the left: m₁ ⊆ m₂ → m₁ \ C ⊆ m₂ \ C. -/
private theorem sdiff_subset_of_subset
    {m₁ m₂ C : Finset Fact}
    (hsub : m₁ ⊆ m₂) :
    m₁ \ C ⊆ m₂ \ C := by
  intro x hx
  simp [Finset.mem_sdiff] at hx ⊢
  exact ⟨hsub hx.1, hx.2⟩

/-- RichTransition.fire is monotone: enlarging the marking enlarges the result.
    fire = (m \ consumes) ∪ produces, and m₁ ⊆ m₂ → (m₁ \ C) ⊆ (m₂ \ C)
    → (m₁ \ C) ∪ P ⊆ (m₂ \ C) ∪ P. -/
theorem RichTransition.fire_mono
    {m₁ m₂ : Marking}
    (hsub : m₁ ⊆ m₂)
    (rt : RichTransition) :
    rt.fire m₁ ⊆ rt.fire m₂ := by
  intro fact hfact
  simp only [RichTransition.fire, Finset.mem_union] at hfact ⊢
  rcases hfact with h | h
  · exact Or.inl (sdiff_subset_of_subset hsub h)
  · exact Or.inr h

/-- Rich step: fire a RichTransition if enabled. -/
def richStep (rt : RichTransition) (marking : Marking) : Option Marking :=
  if rt.enabled? marking then
    some (rt.fire marking)
  else
    none

/-- richStep is monotone: if it succeeds on m₁ ⊆ m₂, it also succeeds on m₂
    with a larger result. -/
theorem richStep_mono
    {m₁ m₂ : Marking}
    (hsub : m₁ ⊆ m₂)
    (rt : RichTransition)
    {r₁ : Marking}
    (hstep : richStep rt m₁ = some r₁) :
    ∃ r₂, richStep rt m₂ = some r₂ ∧ r₁ ⊆ r₂ := by
  simp only [richStep] at hstep ⊢
  split at hstep
  case isTrue h₁ =>
    injection hstep with hr₁
    subst hr₁
    have h₂ : rt.enabled? m₂ = true := RichTransition.enabled_mono hsub rt h₁
    rw [if_pos h₂]
    exact ⟨rt.fire m₂, rfl, RichTransition.fire_mono hsub rt⟩
  case isFalse h₁ =>
    contradiction

/-- The consume-aware system also has no inhibitor arcs: RichTransition.enabled?
    checks only positive membership (requires ⊆ m), so adding facts never
    disables a transition. -/
theorem rich_no_inhibitor_arcs
    (rt : RichTransition) {m₁ m₂ : Marking}
    (hsub : m₁ ⊆ m₂) (h : rt.enabled? m₁ = true) :
    rt.enabled? m₂ = true :=
  RichTransition.enabled_mono hsub rt h

end Lexicon
