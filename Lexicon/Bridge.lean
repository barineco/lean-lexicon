import Lean.Data.Json
import Lexicon.ConstraintProfiles
import Lexicon.Witness

/-!
# Bridge
JSON bridge artifact import, resolution, compatibility verification, and realization proofs.
-/

namespace Lexicon

open Lean (FromJson ToJson fromJson? Json)

inductive BridgeMode where
  | search
  | searchAll
  deriving DecidableEq, Repr, FromJson, ToJson

structure RawBridgeCase where
  goal : String
  choices : List String
  fuel : Nat
  mode : BridgeMode
  recipes : List (List String)
  deriving Repr, FromJson, ToJson

abbrev BridgeArtifact := List RawBridgeCase

structure BridgeCase where
  goalId : String
  fuel : Nat
  mode : BridgeMode
  recipes : List (List String)
  deriving Repr

def BridgeCase.realizedBy
    (bridge : BridgeCase)
    (start : Marking)
    (choices : List Axiom)
    (goal : SearchGoal) : Prop :=
  match bridge.mode with
  | .search =>
      ∃ recipe,
        bridge.recipes = [recipe] ∧
        search bridge.fuel choices start goal = some recipe
  | .searchAll =>
      ∀ recipe ∈ bridge.recipes, recipe ∈ searchAll bridge.fuel choices start goal

structure ImportedBridgeCase where
  goalId : String
  choices : List String
  fuel : Nat
  mode : BridgeMode
  recipes : List (List String)
  deriving Repr

structure ResolvedBridgeCase where
  bridge : BridgeCase
  choices : List Axiom
  goal : SearchGoal

inductive BridgeImportError where
  | unknownGoal : String → BridgeImportError
  | unknownChoice : String → BridgeImportError
  deriving DecidableEq, Repr

def Registry (α : Type) := List (String × α)

def lookupRegistry? (registry : Registry α) (key : String) : Option α :=
  (registry.find? fun entry => entry.fst = key).map Prod.snd

def goalRegistry : Registry SearchGoal :=
  [("self_profile_from_login", profileSearchGoal),
    ("feed_options", feedOptionsGoal)]

def choiceRegistry : Registry Axiom :=
  [("com.atproto.server.createSession", createSessionAxiom),
    ("app.bsky.actor.getProfile", profileAxiom),
    ("app.bsky.feed.getActorLikes", actorLikesAxiom),
    ("app.bsky.feed.getAuthorFeed", authorFeedAxiom),
    ("app.bsky.feed.getTimeline", timelineAxiom)]

def registryKeys (registry : Registry α) : List String :=
  registry.map Prod.fst

def missingKeys (registry : Registry α) (keys : List String) : List String :=
  keys.filter fun key => lookupRegistry? registry key |>.isNone

def missingGoalIds (bridge : ImportedBridgeCase) : List String :=
  missingKeys goalRegistry [bridge.goalId]

def missingChoiceIds (bridge : ImportedBridgeCase) : List String :=
  missingKeys choiceRegistry bridge.choices

def resolveGoalId : String → Option SearchGoal :=
  lookupRegistry? goalRegistry

def resolveChoice : String → Option Axiom :=
  lookupRegistry? choiceRegistry

def resolveChoices : List String → Except BridgeImportError (List Axiom)
  | [] => .ok []
  | nsid :: rest => do
      let ax <- match resolveChoice nsid with
        | some ax => .ok ax
        | none => .error (.unknownChoice nsid)
      let axs <- resolveChoices rest
      pure (ax :: axs)

def importBridgeCase (bridge : ImportedBridgeCase) :
    Except BridgeImportError ResolvedBridgeCase := do
  let goal <- match resolveGoalId bridge.goalId with
    | some goal => .ok goal
    | none => .error (.unknownGoal bridge.goalId)
  let choices <- resolveChoices bridge.choices
  pure {
    bridge := {
      goalId := bridge.goalId
      fuel := bridge.fuel
      mode := bridge.mode
      recipes := bridge.recipes
    }
    choices := choices
    goal := goal
  }

def importFailure? (bridge : ImportedBridgeCase) : Option BridgeImportError :=
  match importBridgeCase bridge with
  | .ok _ => none
  | .error err => some err

def shapeCompatible (bridge : ImportedBridgeCase) : Prop :=
  ∃ resolved, importBridgeCase bridge = .ok resolved

def semanticallyCompatible (bridge : ImportedBridgeCase) : Prop :=
  ∃ resolved, importBridgeCase bridge = .ok resolved ∧
    ∀ recipe ∈ resolved.bridge.recipes, RecipeWitness ∅ resolved.goal recipe

def fullyCompatible (bridge : ImportedBridgeCase) : Prop :=
  ∃ resolved, importBridgeCase bridge = .ok resolved ∧
    resolved.bridge.realizedBy ∅ resolved.choices resolved.goal

inductive BridgeCompatibility where
  | fullyCompatible
  | semanticallyCompatible
  | shapeCompatible
  | incompatible
  deriving DecidableEq, Repr

structure BridgeReport where
  compatibility : BridgeCompatibility
  importFailure : Option BridgeImportError
  missingGoalIds : List String
  missingChoiceIds : List String
  deriving Repr

structure BridgeArtifactEntryReport where
  raw : RawBridgeCase
  imported : ImportedBridgeCase
  report : BridgeReport
  deriving Repr

def RawBridgeCase.toImportedBridgeCase (raw : RawBridgeCase) : ImportedBridgeCase where
  goalId := raw.goal
  choices := raw.choices
  fuel := raw.fuel
  mode := raw.mode
  recipes := raw.recipes

noncomputable def bridgeCompatibility (bridge : ImportedBridgeCase) : BridgeCompatibility := by
  classical
  exact
    if fullyCompatible bridge then
      .fullyCompatible
    else if semanticallyCompatible bridge then
      .semanticallyCompatible
    else if shapeCompatible bridge then
      .shapeCompatible
    else
      .incompatible

noncomputable def reportBridge (bridge : ImportedBridgeCase) : BridgeReport where
  compatibility := bridgeCompatibility bridge
  importFailure := importFailure? bridge
  missingGoalIds := missingGoalIds bridge
  missingChoiceIds := missingChoiceIds bridge

noncomputable def reportRawBridgeCase (raw : RawBridgeCase) : BridgeArtifactEntryReport where
  raw := raw
  imported := raw.toImportedBridgeCase
  report := reportBridge raw.toImportedBridgeCase

noncomputable def reportBridgeArtifact (artifact : BridgeArtifact) :
    List BridgeArtifactEntryReport :=
  artifact.map reportRawBridgeCase

def parseBridgeArtifact (contents : String) : Except String BridgeArtifact := do
  let json <- Json.parse contents
  fromJson? json

noncomputable def reportBridgeArtifactString
    (contents : String) : Except String (List BridgeArtifactEntryReport) := do
  let artifact <- parseBridgeArtifact contents
  pure (reportBridgeArtifact artifact)

def loadBridgeArtifact
    (path : System.FilePath) : IO (Except String BridgeArtifact) := do
  let contents <- IO.FS.readFile path
  pure (parseBridgeArtifact contents)

noncomputable def loadBridgeArtifactReports
    (path : System.FilePath) : IO (Except String (List BridgeArtifactEntryReport)) := do
  let contents <- IO.FS.readFile path
  pure (reportBridgeArtifactString contents)

theorem BridgeCase.witnesses
    {bridge : BridgeCase}
    {start : Marking}
    {choices : List Axiom}
    {goal : SearchGoal}
    (hrealized : bridge.realizedBy start choices goal) :
    ∀ recipe ∈ bridge.recipes, RecipeWitness start goal recipe := by
  cases hmode : bridge.mode with
  | search =>
      simp [BridgeCase.realizedBy, hmode] at hrealized
      rcases hrealized with ⟨recipe0, hrecipes, hsearch⟩
      intro recipe hmem
      rw [hrecipes] at hmem
      simp at hmem
      subst recipe
      exact search_sound hsearch
  | searchAll =>
      simp [BridgeCase.realizedBy, hmode] at hrealized
      intro recipe hmem
      exact searchAll_sound (hrealized recipe hmem)

-- ══════════════════════════════════════════════════════════════════════════════
-- Bridge case definitions
-- ══════════════════════════════════════════════════════════════════════════════

def selfProfileBridge : BridgeCase where
  goalId := "self_profile_from_login"
  fuel := 2
  mode := .search
  recipes := [["com.atproto.server.createSession", "app.bsky.actor.getProfile"]]

def feedOptionsBridge : BridgeCase where
  goalId := "feed_options"
  fuel := 2
  mode := .searchAll
  recipes :=
    [["com.atproto.server.createSession", "app.bsky.feed.getActorLikes"],
      ["com.atproto.server.createSession", "app.bsky.feed.getAuthorFeed"],
      ["com.atproto.server.createSession", "app.bsky.feed.getTimeline"]]

-- ══════════════════════════════════════════════════════════════════════════════
-- Bridge realization proofs
-- ══════════════════════════════════════════════════════════════════════════════

theorem selfProfileBridgeRealized :
    selfProfileBridge.realizedBy ∅ authChoices profileSearchGoal := by
  refine ⟨["com.atproto.server.createSession", "app.bsky.actor.getProfile"], ?_, ?_⟩
  · rfl
  · simpa [selfProfileBridge] using profileSearchReturnsWitness

theorem selfProfileBridgeWitness :
    RecipeWitness
      ∅
      profileSearchGoal
      ["com.atproto.server.createSession", "app.bsky.actor.getProfile"] := by
  exact BridgeCase.witnesses selfProfileBridgeRealized _ (by simp [selfProfileBridge])

theorem feedOptionsBridgeRealized :
    feedOptionsBridge.realizedBy ∅ feedOptionChoices feedOptionsGoal := by
  intro recipe hmem
  rw [feedOptionsBridge] at hmem
  have hcandidates :
      searchAll 2 feedOptionChoices ∅ feedOptionsGoal =
        [["com.atproto.server.createSession", "app.bsky.feed.getActorLikes"],
          ["com.atproto.server.createSession", "app.bsky.feed.getAuthorFeed"],
          ["com.atproto.server.createSession", "app.bsky.feed.getTimeline"]] := by
    simpa [feedOptionCandidates] using exactFeedOptions
  simp [feedOptionsBridge]
  rw [hcandidates]
  simpa using hmem

theorem feedOptionsBridgeWitnesses :
    ∀ recipe ∈ feedOptionsBridge.recipes,
      RecipeWitness ∅ feedOptionsGoal recipe := by
  exact BridgeCase.witnesses feedOptionsBridgeRealized

-- ══════════════════════════════════════════════════════════════════════════════
-- Imported bridge cases
-- ══════════════════════════════════════════════════════════════════════════════

def importedSelfProfile : ImportedBridgeCase where
  goalId := "self_profile_from_login"
  choices := ["com.atproto.server.createSession", "app.bsky.actor.getProfile"]
  fuel := 2
  mode := .search
  recipes := [["com.atproto.server.createSession", "app.bsky.actor.getProfile"]]

def importedUnknownChoice : ImportedBridgeCase where
  goalId := "self_profile_from_login"
  choices := ["com.atproto.server.createSession", "app.bsky.actor.getPreferences"]
  fuel := 2
  mode := .search
  recipes := [["com.atproto.server.createSession", "app.bsky.actor.getProfile"]]

def importedUnknownGoal : ImportedBridgeCase where
  goalId := "unknown_goal"
  choices := ["com.atproto.server.createSession", "app.bsky.actor.getProfile"]
  fuel := 2
  mode := .search
  recipes := [["com.atproto.server.createSession", "app.bsky.actor.getProfile"]]

def importedFeedOptions : ImportedBridgeCase where
  goalId := "feed_options"
  choices :=
    ["com.atproto.server.createSession", "app.bsky.feed.getActorLikes",
      "app.bsky.feed.getAuthorFeed", "app.bsky.feed.getTimeline"]
  fuel := 2
  mode := .searchAll
  recipes := feedOptionsBridge.recipes

def importedSelfProfileResolved : ResolvedBridgeCase where
  bridge := selfProfileBridge
  choices := authChoices
  goal := profileSearchGoal

def importedFeedOptionsResolved : ResolvedBridgeCase where
  bridge := feedOptionsBridge
  choices := feedOptionChoices
  goal := feedOptionsGoal

-- ══════════════════════════════════════════════════════════════════════════════
-- Registry resolution helper lemmas
-- ══════════════════════════════════════════════════════════════════════════════

theorem resolveGoalId_selfProfile :
    resolveGoalId "self_profile_from_login" = some profileSearchGoal := by
  simp [resolveGoalId, lookupRegistry?, goalRegistry]

theorem resolveChoice_createSession :
    resolveChoice "com.atproto.server.createSession" = some createSessionAxiom := by
  simp [resolveChoice, lookupRegistry?, choiceRegistry]

theorem resolveChoice_profile :
    resolveChoice "app.bsky.actor.getProfile" = some profileAxiom := by
  simp [resolveChoice, lookupRegistry?, choiceRegistry]

theorem resolveChoice_actorLikes :
    resolveChoice "app.bsky.feed.getActorLikes" = some actorLikesAxiom := by
  simp [resolveChoice, lookupRegistry?, choiceRegistry]

theorem resolveChoice_authorFeed :
    resolveChoice "app.bsky.feed.getAuthorFeed" = some authorFeedAxiom := by
  simp [resolveChoice, lookupRegistry?, choiceRegistry]

theorem resolveChoice_timeline :
    resolveChoice "app.bsky.feed.getTimeline" = some timelineAxiom := by
  simp [resolveChoice, lookupRegistry?, choiceRegistry]

theorem resolveChoice_unknownProfilePreference :
    resolveChoice "app.bsky.actor.getPreferences" = none := by
  simp [resolveChoice, lookupRegistry?, choiceRegistry]

theorem resolveChoices_authChoices :
    resolveChoices
        ["com.atproto.server.createSession", "app.bsky.actor.getProfile"] =
      .ok authChoices := by
  unfold resolveChoices
  rw [resolveChoice_createSession]
  simp
  unfold resolveChoices
  rw [resolveChoice_profile]
  rfl

theorem resolveChoices_unknownProfilePreference :
    resolveChoices
        ["com.atproto.server.createSession", "app.bsky.actor.getPreferences"] =
      .error (.unknownChoice "app.bsky.actor.getPreferences") := by
  unfold resolveChoices
  rw [resolveChoice_createSession]
  simp
  unfold resolveChoices
  rw [resolveChoice_unknownProfilePreference]
  rfl

theorem resolveGoalId_feedOptions :
    resolveGoalId "feed_options" = some feedOptionsGoal := by
  simp [resolveGoalId, lookupRegistry?, goalRegistry]

theorem resolveGoalId_unknownGoal :
    resolveGoalId "unknown_goal" = none := by
  simp [resolveGoalId, lookupRegistry?, goalRegistry]

theorem resolveChoices_feedOptionChoices :
    resolveChoices
        ["com.atproto.server.createSession", "app.bsky.feed.getActorLikes",
          "app.bsky.feed.getAuthorFeed", "app.bsky.feed.getTimeline"] =
      .ok feedOptionChoices := by
  unfold resolveChoices
  rw [resolveChoice_createSession]
  simp
  unfold resolveChoices
  rw [resolveChoice_actorLikes]
  simp
  unfold resolveChoices
  rw [resolveChoice_authorFeed]
  simp
  unfold resolveChoices
  rw [resolveChoice_timeline]
  rfl

-- ══════════════════════════════════════════════════════════════════════════════
-- Import proofs
-- ══════════════════════════════════════════════════════════════════════════════

theorem import_importedSelfProfile :
    importBridgeCase importedSelfProfile =
      .ok importedSelfProfileResolved := by
  simp only [importBridgeCase, importedSelfProfile, importedSelfProfileResolved]
  rw [resolveGoalId_selfProfile, resolveChoices_authChoices]
  rfl

theorem import_importedUnknownChoice :
    importBridgeCase importedUnknownChoice =
      .error (.unknownChoice "app.bsky.actor.getPreferences") := by
  simp only [importBridgeCase, importedUnknownChoice]
  rw [resolveGoalId_selfProfile, resolveChoices_unknownProfilePreference]
  rfl

theorem import_importedUnknownGoal :
    importBridgeCase importedUnknownGoal =
      .error (.unknownGoal "unknown_goal") := by
  simp only [importBridgeCase, importedUnknownGoal]
  rw [resolveGoalId_unknownGoal]
  rfl

theorem import_importedFeedOptions :
    importBridgeCase importedFeedOptions =
      .ok importedFeedOptionsResolved := by
  simp only [importBridgeCase, importedFeedOptions, importedFeedOptionsResolved]
  rw [resolveGoalId_feedOptions, resolveChoices_feedOptionChoices]
  rfl

-- ══════════════════════════════════════════════════════════════════════════════
-- Compatibility proofs
-- ══════════════════════════════════════════════════════════════════════════════

theorem importedSelfProfileSemanticallyCompatible :
    semanticallyCompatible importedSelfProfile := by
  refine ⟨importedSelfProfileResolved, import_importedSelfProfile, ?_⟩
  intro recipe hmem
  rw [importedSelfProfileResolved, selfProfileBridge] at hmem
  simp at hmem
  subst recipe
  exact selfProfileBridgeWitness

theorem importedSelfProfileFullyCompatible :
    fullyCompatible importedSelfProfile := by
  refine ⟨importedSelfProfileResolved, import_importedSelfProfile, ?_⟩
  simpa [importedSelfProfileResolved] using selfProfileBridgeRealized

theorem importedFeedOptionsSemanticallyCompatible :
    semanticallyCompatible importedFeedOptions := by
  refine ⟨importedFeedOptionsResolved, import_importedFeedOptions, ?_⟩
  intro recipe hmem
  simpa [importedFeedOptionsResolved] using
    feedOptionsBridgeWitnesses recipe hmem

theorem importedFeedOptionsFullyCompatible :
    fullyCompatible importedFeedOptions := by
  refine ⟨importedFeedOptionsResolved, import_importedFeedOptions, ?_⟩
  simpa [importedFeedOptionsResolved] using feedOptionsBridgeRealized

-- ══════════════════════════════════════════════════════════════════════════════
-- Generic error lemmas
-- ══════════════════════════════════════════════════════════════════════════════

theorem not_shapeCompatible_of_import_error
    {bridge : ImportedBridgeCase}
    (herr : ∃ err, importBridgeCase bridge = .error err) :
    ¬ shapeCompatible bridge := by
  intro hshape
  rcases herr with ⟨err, herr⟩
  rcases hshape with ⟨resolved, himport⟩
  rw [herr] at himport
  contradiction

theorem not_semanticallyCompatible_of_import_error
    {bridge : ImportedBridgeCase}
    (herr : ∃ err, importBridgeCase bridge = .error err) :
    ¬ semanticallyCompatible bridge := by
  intro hsem
  rcases hsem with ⟨resolved, himport, _⟩
  rcases herr with ⟨err, herr⟩
  rw [herr] at himport
  contradiction

theorem not_fullyCompatible_of_import_error
    {bridge : ImportedBridgeCase}
    (herr : ∃ err, importBridgeCase bridge = .error err) :
    ¬ fullyCompatible bridge := by
  intro hfull
  rcases hfull with ⟨resolved, himport, _⟩
  rcases herr with ⟨err, herr⟩
  rw [herr] at himport
  contradiction

theorem fullyCompatible_implies_semanticallyCompatible
    {bridge : ImportedBridgeCase}
    (hfull : fullyCompatible bridge) :
    semanticallyCompatible bridge := by
  rcases hfull with ⟨resolved, himport, hrealized⟩
  refine ⟨resolved, himport, ?_⟩
  exact BridgeCase.witnesses hrealized

-- ══════════════════════════════════════════════════════════════════════════════
-- BridgeCaseSpec: consolidated per-case verification
-- ══════════════════════════════════════════════════════════════════════════════

structure BridgeCaseSpec where
  imported : ImportedBridgeCase
  expectedCompatibility : BridgeCompatibility
  expectedMissingGoalIds : List String
  expectedMissingChoiceIds : List String
  expectedImportFailure : Option BridgeImportError

def BridgeCaseSpec.verified (spec : BridgeCaseSpec) : Prop :=
  bridgeCompatibility spec.imported = spec.expectedCompatibility ∧
  missingGoalIds spec.imported = spec.expectedMissingGoalIds ∧
  missingChoiceIds spec.imported = spec.expectedMissingChoiceIds ∧
  importFailure? spec.imported = spec.expectedImportFailure

def selfProfileSpec : BridgeCaseSpec where
  imported := importedSelfProfile
  expectedCompatibility := .fullyCompatible
  expectedMissingGoalIds := []
  expectedMissingChoiceIds := []
  expectedImportFailure := none

def feedOptionsSpec : BridgeCaseSpec where
  imported := importedFeedOptions
  expectedCompatibility := .fullyCompatible
  expectedMissingGoalIds := []
  expectedMissingChoiceIds := []
  expectedImportFailure := none

def unknownChoiceSpec : BridgeCaseSpec where
  imported := importedUnknownChoice
  expectedCompatibility := .incompatible
  expectedMissingGoalIds := []
  expectedMissingChoiceIds := ["app.bsky.actor.getPreferences"]
  expectedImportFailure := some (.unknownChoice "app.bsky.actor.getPreferences")

def unknownGoalSpec : BridgeCaseSpec where
  imported := importedUnknownGoal
  expectedCompatibility := .incompatible
  expectedMissingGoalIds := ["unknown_goal"]
  expectedMissingChoiceIds := []
  expectedImportFailure := some (.unknownGoal "unknown_goal")

theorem selfProfileSpec_verified : selfProfileSpec.verified := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- bridgeCompatibility
    classical
    simp [selfProfileSpec, bridgeCompatibility, importedSelfProfileFullyCompatible]
  · -- missingGoalIds
    simp [selfProfileSpec, missingGoalIds, missingKeys, goalRegistry, lookupRegistry?,
      importedSelfProfile]
  · -- missingChoiceIds
    simp [selfProfileSpec, missingChoiceIds, missingKeys, choiceRegistry, lookupRegistry?,
      importedSelfProfile]
  · -- importFailure?
    simp [selfProfileSpec, importFailure?, import_importedSelfProfile]

theorem feedOptionsSpec_verified : feedOptionsSpec.verified := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · classical
    simp [feedOptionsSpec, bridgeCompatibility, importedFeedOptionsFullyCompatible]
  · simp [feedOptionsSpec, missingGoalIds, missingKeys, goalRegistry, lookupRegistry?,
      importedFeedOptions]
  · simp [feedOptionsSpec, missingChoiceIds, missingKeys, choiceRegistry, lookupRegistry?,
      importedFeedOptions]
  · simp [feedOptionsSpec, importFailure?, import_importedFeedOptions]

theorem unknownChoiceSpec_verified : unknownChoiceSpec.verified := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- bridgeCompatibility
    classical
    have herr :
        ∃ err, importBridgeCase importedUnknownChoice = .error err := by
      exact ⟨.unknownChoice "app.bsky.actor.getPreferences", import_importedUnknownChoice⟩
    have hfull : ¬ fullyCompatible importedUnknownChoice :=
      not_fullyCompatible_of_import_error herr
    have hsem : ¬ semanticallyCompatible importedUnknownChoice :=
      not_semanticallyCompatible_of_import_error herr
    have hshape : ¬ shapeCompatible importedUnknownChoice :=
      not_shapeCompatible_of_import_error herr
    simp [unknownChoiceSpec, bridgeCompatibility, hfull, hsem, hshape]
  · simp [unknownChoiceSpec, missingGoalIds, missingKeys, goalRegistry, lookupRegistry?,
      importedUnknownChoice]
  · simp [unknownChoiceSpec, missingChoiceIds, missingKeys, choiceRegistry, lookupRegistry?,
      importedUnknownChoice]
  · simp [unknownChoiceSpec, importFailure?, import_importedUnknownChoice]

theorem unknownGoalSpec_verified : unknownGoalSpec.verified := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · classical
    have herr :
        ∃ err, importBridgeCase importedUnknownGoal = .error err := by
      exact ⟨.unknownGoal "unknown_goal", import_importedUnknownGoal⟩
    have hfull : ¬ fullyCompatible importedUnknownGoal :=
      not_fullyCompatible_of_import_error herr
    have hsem : ¬ semanticallyCompatible importedUnknownGoal :=
      not_semanticallyCompatible_of_import_error herr
    have hshape : ¬ shapeCompatible importedUnknownGoal :=
      not_shapeCompatible_of_import_error herr
    simp [unknownGoalSpec, bridgeCompatibility, hfull, hsem, hshape]
  · simp [unknownGoalSpec, missingGoalIds, missingKeys, goalRegistry, lookupRegistry?,
      importedUnknownGoal]
  · simp [unknownGoalSpec, missingChoiceIds, missingKeys, choiceRegistry, lookupRegistry?,
      importedUnknownGoal]
  · simp [unknownGoalSpec, importFailure?, import_importedUnknownGoal]

-- ══════════════════════════════════════════════════════════════════════════════
-- Raw bridge cases
-- ══════════════════════════════════════════════════════════════════════════════

def rawSelfProfile : RawBridgeCase where
  goal := "self_profile_from_login"
  choices := importedSelfProfile.choices
  fuel := importedSelfProfile.fuel
  mode := importedSelfProfile.mode
  recipes := importedSelfProfile.recipes

def rawFeedOptions : RawBridgeCase where
  goal := "feed_options"
  choices := importedFeedOptions.choices
  fuel := importedFeedOptions.fuel
  mode := importedFeedOptions.mode
  recipes := importedFeedOptions.recipes

theorem rawSelfProfileImported :
    rawSelfProfile.toImportedBridgeCase = importedSelfProfile := by
  rfl

theorem rawFeedOptionsImported :
    rawFeedOptions.toImportedBridgeCase = importedFeedOptions := by
  rfl

theorem rawSelfProfileReport :
    (reportRawBridgeCase rawSelfProfile).report =
      reportBridge importedSelfProfile := by
  rfl

theorem rawFeedOptionsReport :
    (reportRawBridgeCase rawFeedOptions).report =
      reportBridge importedFeedOptions := by
  rfl

end Lexicon
