import Lexicon.Reachability

/-!
# Search
Bounded proof search over axiom-annotated marking space.
-/

namespace Lexicon

abbrev SearchGoal := List Fact

def satisfies? (marking : Marking) (goal : SearchGoal) : Bool :=
  goal.all fun fact => fact ∈ marking

def search
    (fuel : Nat)
    (choices : List Axiom)
    (marking : Marking)
    (goal : SearchGoal) : Option (List String) :=
  if satisfies? marking goal then
    some []
  else
    match fuel with
    | 0 => none
    | fuel + 1 =>
        choices.findSome? fun ax =>
          if ax.enabled? marking then
            match search fuel choices (ax.fire marking) goal with
            | some plan => some (ax.code.nsid :: plan)
            | none => none
          else
            none

mutual

def searchAll
    (fuel : Nat)
    (choices : List Axiom)
    (marking : Marking)
    (goal : SearchGoal) : List (List String) :=
  if satisfies? marking goal then
    [[]]
  else
    match fuel with
    | 0 => []
    | fuel + 1 => searchAllFromChoices fuel choices marking goal

def searchAllFromChoices
    (fuel : Nat)
    (choices : List Axiom)
    (marking : Marking)
    (goal : SearchGoal) : List (List String) :=
  match choices with
  | [] => []
  | ax :: rest =>
      let here :=
        if ax.enabled? marking then
          (searchAll fuel rest (ax.fire marking) goal).map fun plan =>
            ax.code.nsid :: plan
        else
          []
      here ++ searchAllFromChoices fuel rest marking goal

end

def authChoices : List Axiom := [createSessionAxiom, profileAxiom]

def profileSearchGoal : SearchGoal := [Fact.datum "profileViewDetailed"]

example : search 0 authChoices ∅ profileSearchGoal = none := by
  simp [search, satisfies?, profileSearchGoal]

example : search 2 authChoices ∅ profileSearchGoal =
    some ["com.atproto.server.createSession", "app.bsky.actor.getProfile"] := by
  simp [search, satisfies?, authChoices, profileSearchGoal, Axiom.enabled?,
    RequirementExpr.check, createSessionAxiom, createSession, profileAxiom, authSelfRead,
    createSessionCode, getProfile, Axiom.fire, TouchExpr.tokens]

example : search 2 [profileAxiom] ∅ profileSearchGoal = none := by
  simp [search, satisfies?, profileSearchGoal, Axiom.enabled?, RequirementExpr.check,
    profileAxiom, authSelfRead, Axiom.fire, TouchExpr.tokens]

def authCandidates0 : List (List String) :=
  searchAll 0 authChoices ∅ profileSearchGoal

def authCandidates1 : List (List String) :=
  searchAll 1 authChoices ∅ profileSearchGoal

def authCandidates2 : List (List String) :=
  searchAll 2 authChoices ∅ profileSearchGoal

def authCandidatesWithoutSession : List (List String) :=
  searchAll 2 [profileAxiom] ∅ profileSearchGoal

end Lexicon
