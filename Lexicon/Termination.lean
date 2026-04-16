import Lexicon.Monotonicity
import Mathlib.Data.Finset.Powerset

/-!
# Termination

Visited-set-based termination of the consume-aware (RichTransition) solver.

The Rust solver tracks visited markings to prune already-explored states,
ensuring termination despite consumes-induced cycles (e.g. A consumes X / produces Y,
B consumes Y / produces X). This module proves:

1. `RichReachesBy`: inductive path for consume-aware transitions
2. Universe closure: `fire` keeps markings within a finite fact universe
3. Visited-set bound: at most 2^|U| distinct markings over universe U
4. Consumes cycle detection: concrete A/B cycle returns to a visited marking
-/

namespace Lexicon

/-! ## RichReachesBy: consume-aware path -/

/-- Inductive path for RichTransition, analogous to ReachesBy. -/
inductive RichReachesBy : Marking → List RichTransition → Marking → Prop where
  | nil (marking : Marking) : RichReachesBy marking [] marking
  | cons
      (rt : RichTransition)
      (rts : List RichTransition)
      (start mid finish : Marking)
      (hstep : richStep rt start = some mid)
      (hrest : RichReachesBy mid rts finish) :
      RichReachesBy start (rt :: rts) finish

/-- Goal reachability via RichTransition paths. -/
def richReachesGoalBy (start : Marking) (rts : List RichTransition) (goal : Goal) : Prop :=
  ∃ finish, RichReachesBy start rts finish ∧ satisfies finish goal

/-! ## Universe closure -/

/-- RichTransition.fire preserves universe membership. -/
theorem fire_within_universe (rt : RichTransition) (m U : Finset Fact)
    (hm : m ⊆ U) (hp : rt.produces ⊆ U) :
    rt.fire m ⊆ U := by
  intro fact hfact
  simp only [RichTransition.fire, Finset.mem_union, Finset.mem_sdiff] at hfact
  rcases hfact with ⟨hm_fact, _⟩ | hp_fact
  · exact hm hm_fact
  · exact hp hp_fact

/-- All markings along a RichReachesBy path stay within universe U,
    provided the initial marking and all transitions' produces are within U. -/
theorem richReachesBy_within_universe
    (U : Finset Fact)
    {start finish : Marking} {path : List RichTransition}
    (hreach : RichReachesBy start path finish) :
    start ⊆ U → (∀ rt ∈ path, rt.produces ⊆ U) → finish ⊆ U := by
  induction hreach with
  | nil _ => intro h _; exact h
  | cons rt rts s mid f hstep hrest ih =>
    intro hstart hpath
    apply ih
    · simp only [richStep] at hstep
      split at hstep
      case isTrue _ =>
        injection hstep with hmid
        subst hmid
        apply fire_within_universe
        · exact hstart
        · exact hpath rt (.head ..)
      case isFalse _ => contradiction
    · intro rt' hrt'
      exact hpath rt' (.tail _ hrt')

/-! ## Visited-set termination bound -/

/-- The number of distinct markings within universe U is bounded by 2^|U|. -/
theorem visited_card_le_powerset (U : Finset Fact) (visited : Finset Marking)
    (h : ∀ m ∈ visited, m ⊆ U) :
    visited.card ≤ 2 ^ U.card := by
  calc visited.card
      ≤ U.powerset.card := Finset.card_le_card (fun m hm => Finset.mem_powerset.mpr (h m hm))
    _ = 2 ^ U.card := Finset.card_powerset U

/-- Termination measure: remaining capacity of the visited set. -/
def searchGap (U : Finset Fact) (visited : Finset Marking) : ℕ :=
  2 ^ U.card - visited.card

/-- Adding a new in-universe marking strictly decreases the search gap,
    proving termination via well-founded recursion on this measure. -/
theorem searchGap_decreases (U : Finset Fact) (visited : Finset Marking) (m : Marking)
    (hm_new : m ∉ visited) (hm_sub : m ⊆ U)
    (hvisited : ∀ v ∈ visited, v ⊆ U) :
    searchGap U (insert m visited) < searchGap U visited := by
  unfold searchGap
  have hvisited' : ∀ v ∈ insert m visited, v ⊆ U := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hm_sub
    · exact hvisited v hv
  have h1 := visited_card_le_powerset U visited hvisited
  have h2 := visited_card_le_powerset U (insert m visited) hvisited'
  have h3 : visited.card < (insert m visited).card :=
    Finset.card_lt_card (Finset.ssubset_insert hm_new)
  omega

/-! ## Consumes cycle detection -/

/-- Transition A: requires and consumes X, produces Y. -/
def cycleA : RichTransition where
  requires := {Fact.datum "X"}
  produces := {Fact.datum "Y"}
  consumes := {Fact.datum "X"}

/-- Transition B: requires and consumes Y, produces X. -/
def cycleB : RichTransition where
  requires := {Fact.datum "Y"}
  produces := {Fact.datum "X"}
  consumes := {Fact.datum "Y"}

/-- Firing A from {X} yields {Y}: X is consumed, Y is produced. -/
theorem cycleA_fire :
    cycleA.fire {Fact.datum "X"} = ({Fact.datum "Y"} : Marking) := by
  ext fact
  simp only [RichTransition.fire, cycleA, Finset.mem_union, Finset.mem_sdiff,
    Finset.mem_singleton]
  constructor
  · rintro (⟨rfl, h⟩ | rfl)
    · exact absurd rfl h
    · rfl
  · rintro rfl; exact Or.inr rfl

/-- Firing B from {Y} yields {X}: Y is consumed, X is produced. -/
theorem cycleB_fire :
    cycleB.fire {Fact.datum "Y"} = ({Fact.datum "X"} : Marking) := by
  ext fact
  simp only [RichTransition.fire, cycleB, Finset.mem_union, Finset.mem_sdiff,
    Finset.mem_singleton]
  constructor
  · rintro (⟨rfl, h⟩ | rfl)
    · exact absurd rfl h
    · rfl
  · rintro rfl; exact Or.inr rfl

/-- The A;B cycle returns to the initial marking {X}. -/
theorem consumes_cycle_revisits :
    cycleB.fire (cycleA.fire {Fact.datum "X"}) = ({Fact.datum "X"} : Marking) := by
  rw [cycleA_fire, cycleB_fire]

/-- Visited-set detects the cycle: if {X} is in visited, the marking after A;B is in visited. -/
theorem consumes_cycle_detected
    (visited : Finset Marking)
    (h : ({Fact.datum "X"} : Marking) ∈ visited) :
    cycleB.fire (cycleA.fire {Fact.datum "X"}) ∈ visited := by
  rw [consumes_cycle_revisits]; exact h

end Lexicon
