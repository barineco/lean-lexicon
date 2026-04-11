import Lexicon.Search

/-!
# Witness
Recipe witness construction and soundness proofs for search and searchAll.
-/

namespace Lexicon

def goalOfSearchGoal (goal : SearchGoal) : Goal :=
  goal.toFinset

def RecipeWitness
    (start : Marking)
    (goal : SearchGoal)
    (recipeNames : List String) : Prop :=
  ∃ axs : List Axiom,
    axs.map (·.code.nsid) = recipeNames ∧
    reachesGoalBy start axs (goalOfSearchGoal goal)

theorem satisfies_goalOfSearchGoal_of_satisfies?
    {marking : Marking}
    {goal : SearchGoal}
    (hsat : satisfies? marking goal = true) :
    satisfies marking (goalOfSearchGoal goal) := by
  intro fact hfact
  have hmem : fact ∈ goal := by
    simpa [goalOfSearchGoal] using hfact
  simpa using (List.all_eq_true.mp hsat) fact hmem

theorem search_sound :
    ∀ {fuel : Nat} {choices : List Axiom} {marking : Marking}
      {goal : SearchGoal} {recipe : List String},
      search fuel choices marking goal = some recipe →
      RecipeWitness marking goal recipe
  | fuel, choices, marking, goal, recipe, hsearch => by
      unfold search at hsearch
      by_cases hsat : satisfies? marking goal
      · simp [hsat] at hsearch
        subst recipe
        refine ⟨[], by simp, ?_⟩
        refine ⟨marking, ReachesBy.nil _, ?_⟩
        exact satisfies_goalOfSearchGoal_of_satisfies? hsat
      · simp [hsat] at hsearch
        cases fuel with
        | zero =>
            simp at hsearch
        | succ fuel =>
            rcases List.exists_of_findSome?_eq_some hsearch with ⟨ax, hax_mem, hax⟩
            by_cases henabled : ax.enabled? marking
            · have hmatch :
                  (if ax.enabled? marking then
                    match search fuel choices (ax.fire marking) goal with
                    | some plan => some (ax.code.nsid :: plan)
                    | none => none
                  else
                    none) = some recipe := hax
              rw [henabled] at hmatch
              cases hplanSearch : search fuel choices (ax.fire marking) goal with
              | none =>
                  simp [hplanSearch] at hmatch
              | some plan =>
                  simp [hplanSearch] at hmatch
                  subst recipe
                  rcases search_sound hplanSearch with ⟨axs, hnames, hgoal⟩
                  refine ⟨ax :: axs, by simp [hnames], ?_⟩
                  rcases hgoal with ⟨finish, hreaches, hsatisfies⟩
                  refine ⟨finish, ?_, hsatisfies⟩
                  refine ReachesBy.cons ax axs marking (ax.fire marking) finish ?_ hreaches
                  simp [step, henabled]
            · simp [henabled] at hax

mutual

theorem searchAll_sound :
    ∀ {fuel : Nat} {choices : List Axiom} {marking : Marking}
      {goal : SearchGoal} {recipe : List String},
      recipe ∈ searchAll fuel choices marking goal →
      RecipeWitness marking goal recipe
  | fuel, choices, marking, goal, recipe, hmem => by
      unfold searchAll at hmem
      by_cases hsat : satisfies? marking goal
      · simp [hsat] at hmem
        subst recipe
        refine ⟨[], by simp, ?_⟩
        refine ⟨marking, ReachesBy.nil _, ?_⟩
        exact satisfies_goalOfSearchGoal_of_satisfies? hsat
      · simp [hsat] at hmem
        cases fuel with
        | zero =>
            simp at hmem
        | succ fuel =>
            exact searchAllFromChoices_sound hmem

theorem searchAllFromChoices_sound :
    ∀ {fuel : Nat} {choices : List Axiom} {marking : Marking}
      {goal : SearchGoal} {recipe : List String},
      recipe ∈ searchAllFromChoices fuel choices marking goal →
      RecipeWitness marking goal recipe
  | fuel, choices, marking, goal, recipe, hmem => by
      cases choices with
      | nil =>
          simp [searchAllFromChoices] at hmem
      | cons ax rest =>
          unfold searchAllFromChoices at hmem
          by_cases henabled : ax.enabled? marking
          · simp [henabled] at hmem
            rcases hmem with ⟨plan, hplan_mem, rfl⟩ | hrest_mem
            · rcases searchAll_sound hplan_mem with ⟨axs, hnames, hgoal⟩
              refine ⟨ax :: axs, by simp [hnames], ?_⟩
              rcases hgoal with ⟨finish, hreaches, hsatisfies⟩
              refine ⟨finish, ?_, hsatisfies⟩
              refine ReachesBy.cons ax axs marking (ax.fire marking) finish ?_ hreaches
              simp [step, henabled]
            · exact searchAllFromChoices_sound hrest_mem
          · simp [henabled] at hmem
            exact searchAllFromChoices_sound hmem

end

theorem profileSearchReturnsWitness :
    search 2 authChoices ∅ profileSearchGoal =
      some ["com.atproto.server.createSession", "app.bsky.actor.getProfile"] := by
  simp [search, satisfies?, authChoices, profileSearchGoal, Axiom.enabled?,
    RequirementExpr.check, createSessionAxiom, createSession, profileAxiom, authSelfRead,
    createSessionCode, getProfile, Axiom.fire, TouchExpr.tokens]

theorem profileSearchWitnessFromSearch :
    RecipeWitness
      ∅
      profileSearchGoal
      ["com.atproto.server.createSession", "app.bsky.actor.getProfile"] := by
  exact search_sound profileSearchReturnsWitness

theorem profileRecipeWitness :
    RecipeWitness
      ∅
      profileSearchGoal
      ["com.atproto.server.createSession", "app.bsky.actor.getProfile"] := by
  exact profileSearchWitnessFromSearch

theorem profileSearchAllWitness :
    RecipeWitness
      ∅
      profileSearchGoal
      ["com.atproto.server.createSession", "app.bsky.actor.getProfile"] := by
  have hcandidates :
      authCandidates2 =
        [["com.atproto.server.createSession", "app.bsky.actor.getProfile"]] := by
    simp [authCandidates2, searchAll, searchAllFromChoices, authChoices, profileSearchGoal,
      satisfies?, Axiom.enabled?, RequirementExpr.check, createSessionAxiom, createSession,
      profileAxiom, authSelfRead, createSessionCode, getProfile, Axiom.fire,
      TouchExpr.tokens]
  have hmem :
      ["com.atproto.server.createSession", "app.bsky.actor.getProfile"] ∈ authCandidates2 := by
    rw [hcandidates]
    simp
  exact searchAll_sound (fuel := 2) (choices := authChoices) (marking := ∅)
    (goal := profileSearchGoal) hmem

end Lexicon
