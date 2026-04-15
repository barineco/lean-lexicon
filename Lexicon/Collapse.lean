import Lexicon.Transition
import Lexicon.Witness

/-!
# Collapse

## The hierarchy that does not exist

The apparent levels Lex1 < Lex2 < Lex3 < … are not a hierarchy of
computational expressiveness.  There is exactly one real boundary:

  **Lex0 (types, objects) / Lex1 (endpoints, morphisms)**

Above Lex1, everything collapses.  The evidence is already present in
the existing definitions:

- `TypedTransition.seq` returns `TypedTransition`.
  Composing morphisms does not ascend a level.

- `branch_is_dispatch_then_seq` (Transition.lean) decomposes `if` into
  `TypeExpr.dispatch` (a Lex0 operation on union types) followed by
  `seq` (a Lex1 composition).  Branching is not a new primitive.

- `searchAll` enumerates all paths.  Each path is a `List Axiom`,
  a sequence of Lex1 morphisms.  The collection of paths is the
  **pre-expanded** form of any `if` expression.

No new types, tags, or structures are needed to express this.
The collapse is a consequence of closure, not a theorem about labels.

## What a "functor" really is

A "functor" (Lex2 operation) is a complex `if`: a morphism whose
internal branching we choose to observe.  A "morph" (Lex1 primitive)
is the same thing with its branching hidden.  The distinction is
**observational granularity**, not computational kind.

`searchAll` makes this explicit: it takes an opaque goal and returns
the enumerated branches.  The result is a `List (List String)`:
a flat list of Lex1 paths.  No Lex2 structure survives the enumeration.

## What this module proves

1. `ReachesBy.append`: reachability witnesses compose (concatenation).
2. `collapse_sound`: search over primitives yields reachability witnesses.
3. `paths_reach_same_goal`: all recipes from `searchAll` reach the goal.
4. `composite_decomposes_two`: any 2-step composite is a `ReachesBy`.
-/

namespace Lexicon

/-! ## Reachability is compositional -/

/-- ReachesBy is preserved under list concatenation: sequential
    composition of reachability witnesses. -/
theorem ReachesBy.append
    {start mid finish : Marking}
    {axs1 axs2 : List Axiom}
    (h1 : ReachesBy start axs1 mid)
    (h2 : ReachesBy mid axs2 finish) :
    ReachesBy start (axs1 ++ axs2) finish := by
  induction h1 with
  | nil _ => exact h2
  | cons ax axs s m _f hstep _hrest ih =>
    exact ReachesBy.cons ax (axs ++ axs2) s m finish
      hstep (ih h2)

/-! ## Search over primitives is complete for all "levels" -/

/-- Soundness: if BFS search finds a recipe over primitives, it is
    a reachability witness, regardless of the "level" at which the
    goal was conceived. -/
theorem collapse_sound
    (primitives : List Axiom)
    (depth : Nat)
    (start : Marking)
    (goal : SearchGoal)
    (recipe : List String)
    (h : search depth primitives start goal = some recipe) :
    RecipeWitness start goal recipe :=
  search_sound h

/-- All recipes from searchAll are reachability witnesses: the
    enumerated branches of any "if" are each valid Lex1 paths. -/
theorem paths_reach_same_goal
    (primitives : List Axiom)
    (depth : Nat)
    (start : Marking)
    (goal : SearchGoal)
    (recipe : List String)
    (h : recipe ∈ searchAll depth primitives start goal) :
    RecipeWitness start goal recipe :=
  searchAll_sound h

/-! ## Composites decompose into primitive steps -/

/-- A composite built from two axioms decomposes as a two-step
    ReachesBy. -/
theorem composite_decomposes_two
    (ax1 ax2 : Axiom)
    (start : Marking)
    (h1 : ax1.enabled? start = true)
    (h2 : ax2.enabled? (ax1.fire start) = true)
    (goal : Goal)
    (hgoal : satisfies (ax2.fire (ax1.fire start)) goal) :
    reachesGoalBy start [ax1, ax2] goal := by
  refine ⟨ax2.fire (ax1.fire start), ?_, hgoal⟩
  exact ReachesBy.cons ax1 [ax2] start (ax1.fire start) _
    (by simp [step, h1])
    (ReachesBy.cons ax2 [] (ax1.fire start)
      (ax2.fire (ax1.fire start)) _
      (by simp [step, h2])
      (ReachesBy.nil _))

end Lexicon
