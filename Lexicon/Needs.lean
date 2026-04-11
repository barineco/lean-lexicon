import Lexicon.Witness
import Lexicon.ConstraintProfiles
import Lexicon.NonRecoverability
import Lexicon.RequirementSatisfaction

/-!
# Needs
Minimal layer connecting UI-side `needs` to recipe witnesses and source taxonomy.
-/

namespace Lexicon

structure NeedWitness where
  start : Marking
  needs : SearchGoal
  recipe : List String
  witness : RecipeWitness start needs recipe

structure NeedPlan where
  name : String
  witness : NeedWitness
  sourceKinds : List RequirementSourceKind
  boundary : RequirementBoundary

inductive BlockedReason where
  | missingUserFact : Fact → BlockedReason
  | missingRecipeStep : SearchGoal → BlockedReason
  | prunedByBoundary : RequirementBoundary → BlockedReason
  deriving DecidableEq, Repr

structure BlockedNeed where
  name : String
  start : Marking
  needs : SearchGoal
  sourceKinds : List RequirementSourceKind
  boundary : RequirementBoundary
  reason : BlockedReason
  missingFacts : List Fact
  availableRecipes : List (List String)

inductive NeedAssessment where
  | satisfiable : NeedPlan → NeedAssessment
  | blocked : BlockedNeed → NeedAssessment

inductive NeedDisposition where
  | alreadySatisfied
  | witnessAvailable
  | recoverableByRecipe
  | needsUserAction
  deriving DecidableEq, Repr

def classifyBlockedReason : BlockedReason → NeedDisposition
  | .missingUserFact _ => .needsUserAction
  | .missingRecipeStep _ => .recoverableByRecipe
  | .prunedByBoundary _ => .needsUserAction

def assessmentDisposition : NeedAssessment → NeedDisposition
  | .satisfiable plan =>
      if plan.witness.recipe = [] then .alreadySatisfied else .witnessAvailable
  | .blocked need => classifyBlockedReason need.reason

def sourceKindsHaveRecoveryPotential (kinds : List RequirementSourceKind) : Bool :=
  kinds.any RequirementSourceKind.isRecipeRecoverable

structure NeedClusterBridge where
  assessment : NeedAssessment
  cluster : NonrecoverableCluster

structure NeedRecoveryBridge where
  assessment : NeedAssessment
  cluster : RecoverableCluster

-- ============================================================================
-- Spec structures
-- ============================================================================

structure SatisfiableScreenSpec where
  plan : NeedPlan
  expectedDisposition : NeedDisposition
  expectedBoundary : RequirementBoundary
  expectedSources : List RequirementSourceKind

def SatisfiableScreenSpec.verified (spec : SatisfiableScreenSpec) : Prop :=
  assessmentDisposition (.satisfiable spec.plan) = spec.expectedDisposition ∧
  spec.plan.boundary = spec.expectedBoundary ∧
  spec.plan.sourceKinds = spec.expectedSources

structure BlockedScreenSpec where
  need : BlockedNeed
  expectedDisposition : NeedDisposition
  expectedBoundary : RequirementBoundary
  expectedReason : BlockedReason
  expectedRecovery : Bool

def BlockedScreenSpec.verified (spec : BlockedScreenSpec) : Prop :=
  assessmentDisposition (.blocked spec.need) = spec.expectedDisposition ∧
  spec.need.boundary = spec.expectedBoundary ∧
  spec.need.reason = spec.expectedReason ∧
  sourceKindsHaveRecoveryPotential spec.need.sourceKinds = spec.expectedRecovery

structure ClusterBridgeSpec where
  bridge : NeedClusterBridge
  need : BlockedNeed
  expectedDisposition : NeedDisposition
  hasInvisibleDiscriminator : Bool

def ClusterBridgeSpec.verified (spec : ClusterBridgeSpec) : Prop :=
  spec.bridge.cluster.goal = spec.need.needs ∧
  spec.bridge.cluster.boundary = spec.need.boundary ∧
  assessmentDisposition spec.bridge.assessment = spec.expectedDisposition ∧
  (spec.hasInvisibleDiscriminator = true →
    clusterHasInvisibleDiscriminator spec.bridge.cluster)

structure RecoveryBridgeSpec where
  bridge : NeedRecoveryBridge
  need : BlockedNeed
  expectedDisposition : NeedDisposition

def RecoveryBridgeSpec.verified (spec : RecoveryBridgeSpec) : Prop :=
  spec.bridge.cluster.goal = spec.need.needs ∧
  spec.bridge.cluster.boundary = spec.need.boundary ∧
  assessmentDisposition spec.bridge.assessment = spec.expectedDisposition ∧
  clusterNeedsRecovery spec.bridge.cluster

-- ============================================================================
-- Screen-specific data definitions (preserved)
-- ============================================================================

def profileScreenNeedPlan : NeedPlan where
  name := "ProfileScreen"
  witness := {
    start := ∅
    needs := profileSearchGoal
    recipe := ["com.atproto.server.createSession", "app.bsky.actor.getProfile"]
    witness := profileRecipeWitness
  }
  sourceKinds := actorSourceKinds
  boundary := actorBoundary

def prefetchedProfileRecipeWitness :
    RecipeWitness
      {Fact.datum "profileViewDetailed"}
      profileSearchGoal
      [] := by
  refine ⟨[], rfl, ?_⟩
  refine ⟨{Fact.datum "profileViewDetailed"}, ?_, ?_⟩
  · exact ReachesBy.nil _
  · intro fact hfact
    have hfact' : fact = Fact.datum "profileViewDetailed" := by
      simpa [goalOfSearchGoal, profileSearchGoal] using hfact
    subst fact
    simp

def prefetchedProfileNeedPlan : NeedPlan where
  name := "PrefetchedProfileScreen"
  witness := {
    start := {Fact.datum "profileViewDetailed"}
    needs := profileSearchGoal
    recipe := []
    witness := prefetchedProfileRecipeWitness
  }
  sourceKinds := [RequirementSourceKind.marked]
  boundary := prefetchedProfileBoundary

def composerRecipeWitness :
    RecipeWitness
      selfWriteInputs
      selfWriteGoal
      ["com.atproto.server.createSession",
       "internal.ownership.deriveRepo",
       "com.atproto.repo.createRecord"] := by
  refine ⟨[createSessionAxiom, ownershipBridgeAxiom, createRecordAxiomFor .all], ?_, ?_⟩
  · simp [createSessionAxiom, createSessionCode, ownershipBridgeAxiom, ownershipBridgeCode,
      createRecordAxiomFor, createRecordCode]
  refine ⟨(createRecordAxiomFor .all).fire
      (ownershipBridgeAxiom.fire (createSessionAxiom.fire selfWriteInputs)), ?_, ?_⟩
  · refine ReachesBy.cons createSessionAxiom [ownershipBridgeAxiom, createRecordAxiomFor .all]
      selfWriteInputs
      (createSessionAxiom.fire selfWriteInputs)
      ((createRecordAxiomFor .all).fire
        (ownershipBridgeAxiom.fire (createSessionAxiom.fire selfWriteInputs)))
      ?_
      ?_
    · simp [step, Axiom.enabled?, RequirementExpr.check, createSessionAxiom, createSession,
        Axiom.fire]
    · refine ReachesBy.cons ownershipBridgeAxiom [createRecordAxiomFor .all]
        (createSessionAxiom.fire selfWriteInputs)
        (ownershipBridgeAxiom.fire (createSessionAxiom.fire selfWriteInputs))
        ((createRecordAxiomFor .all).fire
          (ownershipBridgeAxiom.fire (createSessionAxiom.fire selfWriteInputs)))
        ?_
        ?_
      · simp [step, Axiom.enabled?, RequirementExpr.check, ownershipBridgeAxiom,
          createSessionAxiom, createSession, ownershipBridgeCode, Axiom.fire, TouchExpr.tokens]
      · refine ReachesBy.cons (createRecordAxiomFor .all) []
          (ownershipBridgeAxiom.fire (createSessionAxiom.fire selfWriteInputs))
          ((createRecordAxiomFor .all).fire
            (ownershipBridgeAxiom.fire (createSessionAxiom.fire selfWriteInputs)))
          ((createRecordAxiomFor .all).fire
            (ownershipBridgeAxiom.fire (createSessionAxiom.fire selfWriteInputs)))
          ?_
          ?_
        · simp [step, Axiom.enabled?, RequirementExpr.check, createRecordAxiomFor,
            recordCreateInputAnnotation, ownershipBridgeAxiom, createSessionAxiom, createSession,
            selfWriteInputs, createRecordCode, ownershipBridgeCode, Axiom.fire, TouchExpr.tokens]
        · exact ReachesBy.nil _
  · intro fact hfact
    have hfact' : fact = Fact.datum "repoRecordCreated" := by
      simpa [goalOfSearchGoal, selfWriteGoal] using hfact
    subst fact
    simp [createRecordAxiomFor, recordCreateInputAnnotation, ownershipBridgeAxiom,
      createSessionAxiom, createSession, selfWriteInputs, Axiom.fire, TouchExpr.tokens]

def composerScreenNeedPlan : NeedPlan where
  name := "ComposerScreen"
  witness := {
    start := selfWriteInputs
    needs := selfWriteGoal
    recipe := ["com.atproto.server.createSession",
      "internal.ownership.deriveRepo",
      "com.atproto.repo.createRecord"]
    witness := composerRecipeWitness
  }
  sourceKinds := repoSourceKinds
  boundary := repoBoundary

def needPlans : List NeedPlan :=
  [prefetchedProfileNeedPlan, profileScreenNeedPlan, composerScreenNeedPlan]

def foreignRepoBlockedChoices : List Axiom :=
  [createSessionAxiom, nrForeignRepoReadAxiom]

def foreignRepoBlockedCandidates : List (List String) :=
  searchAll 2 foreignRepoBlockedChoices ∅ repoViewGoal

def foreignRepoBlockedNeed : BlockedNeed where
  name := "ForeignRepoScreen"
  start := ∅
  needs := repoViewGoal
  sourceKinds := sourceKinds directSelectionSources
  boundary := directSelectionBoundary
  reason := .missingUserFact (Fact.datum "selected.repo")
  missingFacts := [Fact.datum "selected.repo"]
  availableRecipes := foreignRepoBlockedCandidates

def foreignRepoBlockedAssessment : NeedAssessment :=
  .blocked foreignRepoBlockedNeed

def foreignThreadBlockedChoices : List Axiom :=
  [createSessionAxiom, nrForeignThreadReadAxiom]

def foreignThreadBlockedCandidates : List (List String) :=
  searchAll 2 foreignThreadBlockedChoices ∅ threadViewGoal

def foreignThreadBlockedNeed : BlockedNeed where
  name := "ForeignThreadScreen"
  start := ∅
  needs := threadViewGoal
  sourceKinds := [RequirementSourceKind.user]
  boundary := RequirementBoundary.pruningOnly
  reason := .missingUserFact (Fact.datum "selected.actor")
  missingFacts := [Fact.datum "selected.actor"]
  availableRecipes := foreignThreadBlockedCandidates

def foreignThreadBlockedAssessment : NeedAssessment :=
  .blocked foreignThreadBlockedNeed

def deferredComposerNeed : BlockedNeed where
  name := "DeferredComposerScreen"
  start := selfWriteInputs
  needs := selfWriteGoal
  sourceKinds := repoSourceKinds
  boundary := repoBoundary
  reason := .missingRecipeStep [Fact.selfKey "repo"]
  missingFacts := [Fact.selfKey "repo"]
  availableRecipes := selfWriteCandidates .all

def deferredComposerAssessment : NeedAssessment :=
  .blocked deferredComposerNeed

def deferredOwnRepoNeed : BlockedNeed where
  name := "DeferredOwnRepoScreen"
  start := ∅
  needs := ownRepoGoal
  sourceKinds := repoSourceKinds
  boundary := repoBoundary
  reason := .missingRecipeStep [Fact.selfKey "repo"]
  missingFacts := [Fact.selfKey "repo"]
  availableRecipes := ownRepoCandidates .ownership

def deferredOwnRepoAssessment : NeedAssessment :=
  .blocked deferredOwnRepoNeed

def foreignRepoBridge : NeedClusterBridge where
  assessment := foreignRepoBlockedAssessment
  cluster := repoReadCluster

def foreignThreadBridge : NeedClusterBridge where
  assessment := foreignThreadBlockedAssessment
  cluster := threadReadCluster

def deferredComposerBridge : NeedRecoveryBridge where
  assessment := deferredComposerAssessment
  cluster := selfWriteRecoveryCluster

def deferredOwnRepoBridge : NeedRecoveryBridge where
  assessment := deferredOwnRepoAssessment
  cluster := ownRepoRecoveryCluster

def repoBoundaryBlockedNeed : BlockedNeed where
  name := "RepoBoundaryScreen"
  start := ∅
  needs := repoViewGoal
  sourceKinds := []
  boundary := RequirementBoundary.pruningOnly
  reason := .prunedByBoundary RequirementBoundary.pruningOnly
  missingFacts := []
  availableRecipes := codeOnlyRepoViewCandidates

def repoBoundaryBlockedAssessment : NeedAssessment :=
  .blocked repoBoundaryBlockedNeed

def repoBoundaryBridge : NeedClusterBridge where
  assessment := repoBoundaryBlockedAssessment
  cluster := repoReadCluster

def threadBoundaryBlockedNeed : BlockedNeed where
  name := "ThreadBoundaryScreen"
  start := ∅
  needs := threadViewGoal
  sourceKinds := []
  boundary := RequirementBoundary.pruningOnly
  reason := .prunedByBoundary RequirementBoundary.pruningOnly
  missingFacts := []
  availableRecipes := codeOnlyThreadViewCandidates

def threadBoundaryBlockedAssessment : NeedAssessment :=
  .blocked threadBoundaryBlockedNeed

def threadBoundaryBridge : NeedClusterBridge where
  assessment := threadBoundaryBlockedAssessment
  cluster := threadReadCluster

def needAssessments : List NeedAssessment :=
  [ .satisfiable prefetchedProfileNeedPlan
  , .satisfiable profileScreenNeedPlan
  , .satisfiable composerScreenNeedPlan
  , deferredOwnRepoAssessment
  , deferredComposerAssessment
  , threadBoundaryBlockedAssessment
  , repoBoundaryBlockedAssessment
  , foreignThreadBlockedAssessment
  , foreignRepoBlockedAssessment
  ]

-- ============================================================================
-- Spec instances for satisfiable screens
-- ============================================================================

def profileScreenSpec : SatisfiableScreenSpec where
  plan := profileScreenNeedPlan
  expectedDisposition := .witnessAvailable
  expectedBoundary := .recoverableByRecipe
  expectedSources := [.user, .yielded]

def prefetchedProfileSpec : SatisfiableScreenSpec where
  plan := prefetchedProfileNeedPlan
  expectedDisposition := .alreadySatisfied
  expectedBoundary := .alreadySatisfied
  expectedSources := [.marked]

def composerScreenSpec : SatisfiableScreenSpec where
  plan := composerScreenNeedPlan
  expectedDisposition := .witnessAvailable
  expectedBoundary := .recoverableByRecipe
  expectedSources := [.derivedOwnership, .yielded, .user]

theorem profileScreenVerified : profileScreenSpec.verified := by
  refine ⟨rfl, rfl, rfl⟩

theorem prefetchedProfileVerified : prefetchedProfileSpec.verified := by
  refine ⟨rfl, rfl, rfl⟩

theorem composerScreenVerified : composerScreenSpec.verified := by
  refine ⟨rfl, rfl, rfl⟩

-- ============================================================================
-- Spec instances for blocked screens
-- ============================================================================

def deferredComposerSpec : BlockedScreenSpec where
  need := deferredComposerNeed
  expectedDisposition := .recoverableByRecipe
  expectedBoundary := .recoverableByRecipe
  expectedReason := .missingRecipeStep [Fact.selfKey "repo"]
  expectedRecovery := true

def deferredOwnRepoSpec : BlockedScreenSpec where
  need := deferredOwnRepoNeed
  expectedDisposition := .recoverableByRecipe
  expectedBoundary := .recoverableByRecipe
  expectedReason := .missingRecipeStep [Fact.selfKey "repo"]
  expectedRecovery := true

def foreignRepoSpec : BlockedScreenSpec where
  need := foreignRepoBlockedNeed
  expectedDisposition := .needsUserAction
  expectedBoundary := .pruningOnly
  expectedReason := .missingUserFact (Fact.datum "selected.repo")
  expectedRecovery := false

def foreignThreadSpec : BlockedScreenSpec where
  need := foreignThreadBlockedNeed
  expectedDisposition := .needsUserAction
  expectedBoundary := .pruningOnly
  expectedReason := .missingUserFact (Fact.datum "selected.actor")
  expectedRecovery := false

def repoBoundarySpec : BlockedScreenSpec where
  need := repoBoundaryBlockedNeed
  expectedDisposition := .needsUserAction
  expectedBoundary := .pruningOnly
  expectedReason := .prunedByBoundary .pruningOnly
  expectedRecovery := false

def threadBoundarySpec : BlockedScreenSpec where
  need := threadBoundaryBlockedNeed
  expectedDisposition := .needsUserAction
  expectedBoundary := .pruningOnly
  expectedReason := .prunedByBoundary .pruningOnly
  expectedRecovery := false

theorem deferredComposerVerified : deferredComposerSpec.verified := by
  refine ⟨rfl, rfl, rfl, rfl⟩

theorem deferredOwnRepoVerified : deferredOwnRepoSpec.verified := by
  refine ⟨rfl, rfl, rfl, rfl⟩

theorem foreignRepoVerified : foreignRepoSpec.verified := by
  refine ⟨rfl, rfl, rfl, rfl⟩

theorem foreignThreadVerified : foreignThreadSpec.verified := by
  refine ⟨rfl, rfl, rfl, rfl⟩

theorem repoBoundaryVerified : repoBoundarySpec.verified := by
  refine ⟨rfl, rfl, rfl, rfl⟩

theorem threadBoundaryVerified : threadBoundarySpec.verified := by
  refine ⟨rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- Spec instances for cluster bridges
-- ============================================================================

def foreignRepoBridgeSpec : ClusterBridgeSpec where
  bridge := foreignRepoBridge
  need := foreignRepoBlockedNeed
  expectedDisposition := .needsUserAction
  hasInvisibleDiscriminator := true

def foreignThreadBridgeSpec : ClusterBridgeSpec where
  bridge := foreignThreadBridge
  need := foreignThreadBlockedNeed
  expectedDisposition := .needsUserAction
  hasInvisibleDiscriminator := true

def repoBoundaryBridgeSpec : ClusterBridgeSpec where
  bridge := repoBoundaryBridge
  need := repoBoundaryBlockedNeed
  expectedDisposition := .needsUserAction
  hasInvisibleDiscriminator := true

def threadBoundaryBridgeSpec : ClusterBridgeSpec where
  bridge := threadBoundaryBridge
  need := threadBoundaryBlockedNeed
  expectedDisposition := .needsUserAction
  hasInvisibleDiscriminator := true

theorem foreignRepoBridgeVerified : foreignRepoBridgeSpec.verified := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro _
  exact repoReadClusterHasInvisibleDiscriminator

theorem foreignThreadBridgeVerified : foreignThreadBridgeSpec.verified := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro _
  exact threadReadClusterHasInvisibleDiscriminator

theorem repoBoundaryBridgeVerified : repoBoundaryBridgeSpec.verified := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro _
  exact repoReadClusterHasInvisibleDiscriminator

theorem threadBoundaryBridgeVerified : threadBoundaryBridgeSpec.verified := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  intro _
  exact threadReadClusterHasInvisibleDiscriminator

-- ============================================================================
-- Spec instances for recovery bridges
-- ============================================================================

def deferredComposerBridgeSpec : RecoveryBridgeSpec where
  bridge := deferredComposerBridge
  need := deferredComposerNeed
  expectedDisposition := .recoverableByRecipe

def deferredOwnRepoBridgeSpec : RecoveryBridgeSpec where
  bridge := deferredOwnRepoBridge
  need := deferredOwnRepoNeed
  expectedDisposition := .recoverableByRecipe

theorem deferredComposerBridgeVerified : deferredComposerBridgeSpec.verified := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  exact selfWriteRecoveryClusterNeedsRecovery

theorem deferredOwnRepoBridgeVerified : deferredOwnRepoBridgeSpec.verified := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  exact ownRepoRecoveryClusterNeedsRecovery

-- ============================================================================
-- Structural lemmas (universally quantified — preserved)
-- ============================================================================

theorem satisfiableAssessmentsExposeWitness :
    ∀ plan : NeedPlan,
      plan.witness.recipe ≠ [] →
      assessmentDisposition (.satisfiable plan) = NeedDisposition.witnessAvailable := by
  intro plan hrecipe
  simp [assessmentDisposition, hrecipe]

theorem missingRecipeStepMeansRecoverable :
    ∀ goal : SearchGoal,
      classifyBlockedReason (.missingRecipeStep goal) =
        NeedDisposition.recoverableByRecipe := by
  intro goal
  rfl

theorem missingUserFactMeansNeedsUserAction :
    ∀ fact : Fact,
      classifyBlockedReason (.missingUserFact fact) =
        NeedDisposition.needsUserAction := by
  intro fact
  rfl

theorem prunedBoundaryMeansNeedsUserAction :
    ∀ boundary : RequirementBoundary,
      classifyBlockedReason (.prunedByBoundary boundary) =
        NeedDisposition.needsUserAction := by
  intro boundary
  rfl

-- ============================================================================
-- Search result lemmas (real computation — preserved)
-- ============================================================================

theorem foreignThreadBlockedCandidatesEmpty :
    foreignThreadBlockedCandidates = [] := by
  simp [foreignThreadBlockedCandidates, foreignThreadBlockedChoices, threadViewGoal, searchAll,
    searchAllFromChoices, satisfies?, Axiom.enabled?, RequirementExpr.check, createSessionAxiom,
    createSessionCode, createSession, nrForeignThreadReadAxiom, nrForeignThreadReadCode,
    Axiom.fire, TouchExpr.tokens]

theorem foreignRepoBlockedCandidatesEmpty :
    foreignRepoBlockedCandidates = [] := by
  simp [foreignRepoBlockedCandidates, foreignRepoBlockedChoices, repoViewGoal, searchAll,
    searchAllFromChoices, satisfies?, Axiom.enabled?, RequirementExpr.check, createSessionAxiom,
    createSessionCode, createSession, nrForeignRepoReadAxiom, nrForeignRepoReadCode,
    Axiom.fire, TouchExpr.tokens]

-- ============================================================================
-- Specific recipe computation theorems (preserved)
-- ============================================================================

theorem deferredComposerScreenHasRecoveryRecipe :
    deferredComposerNeed.availableRecipes =
      [["com.atproto.server.createSession",
        "internal.ownership.deriveRepo",
        "com.atproto.repo.createRecord"]] := by
  exact allEnablesSelfWrite

theorem deferredOwnRepoScreenHasRecoveryRecipe :
    deferredOwnRepoNeed.availableRecipes =
      [["com.atproto.server.createSession",
        "internal.ownership.deriveRepo",
        "internal.repo.describeSelf"]] := by
  exact ownershipEnablesOwnRepoRead

theorem repoBoundaryScreenShowsCodeOnlyCandidates :
    repoBoundaryBlockedNeed.availableRecipes =
      [ ["internal.repo.getSelfView"]
      , ["internal.repo.getForeignView"]
      ] := by
  exact codeOnlyRepoViewAmbiguous

theorem threadBoundaryScreenShowsCodeOnlyCandidates :
    threadBoundaryBlockedNeed.availableRecipes =
      [ ["internal.feed.getSelfThread"]
      , ["internal.feed.getForeignThread"]
      ] := by
  exact codeOnlyThreadViewAmbiguous

-- ============================================================================
-- Integration / summary theorems (rewritten to use specs)
-- ============================================================================

theorem missingFactAndBoundaryPruningAreDistinctBlockedReasons :
    foreignRepoBlockedNeed.reason ≠ repoBoundaryBlockedNeed.reason := by
  intro h
  injection h

theorem blockedForeignScreensShareNonrecoverableStructure :
    foreignRepoBridge.cluster.boundary = RequirementBoundary.pruningOnly ∧
    assessmentDisposition foreignRepoBridge.assessment = NeedDisposition.needsUserAction ∧
    clusterHasInvisibleDiscriminator foreignRepoBridge.cluster ∧
    foreignThreadBridge.cluster.boundary = RequirementBoundary.pruningOnly ∧
    assessmentDisposition foreignThreadBridge.assessment = NeedDisposition.needsUserAction ∧
    clusterHasInvisibleDiscriminator foreignThreadBridge.cluster := by
  exact ⟨rfl, rfl, repoReadClusterHasInvisibleDiscriminator,
    rfl, rfl, threadReadClusterHasInvisibleDiscriminator⟩

theorem repoBoundaryAndForeignRepoNeedDifferentExplanations :
    assessmentDisposition repoBoundaryBridge.assessment = NeedDisposition.needsUserAction ∧
    assessmentDisposition foreignRepoBridge.assessment = NeedDisposition.needsUserAction ∧
    repoBoundaryBlockedNeed.reason =
      .prunedByBoundary RequirementBoundary.pruningOnly ∧
    foreignRepoBlockedNeed.reason =
      .missingUserFact (Fact.datum "selected.repo") := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem boundaryScreensShareNonrecoverableStructure :
    repoBoundaryBridge.cluster.boundary = RequirementBoundary.pruningOnly ∧
    assessmentDisposition repoBoundaryBridge.assessment = NeedDisposition.needsUserAction ∧
    clusterHasInvisibleDiscriminator repoBoundaryBridge.cluster ∧
    threadBoundaryBridge.cluster.boundary = RequirementBoundary.pruningOnly ∧
    assessmentDisposition threadBoundaryBridge.assessment = NeedDisposition.needsUserAction ∧
    clusterHasInvisibleDiscriminator threadBoundaryBridge.cluster := by
  exact ⟨rfl, rfl, repoReadClusterHasInvisibleDiscriminator,
    rfl, rfl, threadReadClusterHasInvisibleDiscriminator⟩

theorem recoverableScreensShareRecoveryStructure :
    deferredComposerBridge.cluster.boundary = RequirementBoundary.recoverableByRecipe ∧
    assessmentDisposition deferredComposerBridge.assessment =
      NeedDisposition.recoverableByRecipe ∧
    clusterNeedsRecovery deferredComposerBridge.cluster ∧
    deferredOwnRepoBridge.cluster.boundary = RequirementBoundary.recoverableByRecipe ∧
    assessmentDisposition deferredOwnRepoBridge.assessment =
      NeedDisposition.recoverableByRecipe ∧
    clusterNeedsRecovery deferredOwnRepoBridge.cluster := by
  exact ⟨rfl, rfl, selfWriteRecoveryClusterNeedsRecovery,
    rfl, rfl, ownRepoRecoveryClusterNeedsRecovery⟩

theorem recoverableScreensAlsoCarryRecoverableSources :
    sourceKindsHaveRecoveryPotential deferredComposerNeed.sourceKinds = true ∧
    assessmentDisposition deferredComposerBridge.assessment =
      NeedDisposition.recoverableByRecipe ∧
    sourceKindsHaveRecoveryPotential deferredOwnRepoNeed.sourceKinds = true ∧
    assessmentDisposition deferredOwnRepoBridge.assessment =
      NeedDisposition.recoverableByRecipe := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem markedScreensAreAlreadySatisfied :
    prefetchedProfileNeedPlan.sourceKinds = [RequirementSourceKind.marked] ∧
    assessmentDisposition (.satisfiable prefetchedProfileNeedPlan) =
      NeedDisposition.alreadySatisfied := by
  exact ⟨rfl, rfl⟩

theorem needsBridgesSeparateRecoveryFromUserAction :
    assessmentDisposition deferredComposerBridge.assessment =
      NeedDisposition.recoverableByRecipe ∧
    assessmentDisposition deferredOwnRepoBridge.assessment =
      NeedDisposition.recoverableByRecipe ∧
    assessmentDisposition foreignRepoBridge.assessment =
      NeedDisposition.needsUserAction ∧
    assessmentDisposition foreignThreadBridge.assessment =
      NeedDisposition.needsUserAction := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem userOnlyForeignScreensNeedUserAction :
    sourceKindsHaveRecoveryPotential foreignRepoBlockedNeed.sourceKinds = false ∧
    assessmentDisposition foreignRepoBridge.assessment =
      NeedDisposition.needsUserAction ∧
    sourceKindsHaveRecoveryPotential foreignThreadBlockedNeed.sourceKinds = false ∧
    assessmentDisposition foreignThreadBridge.assessment =
      NeedDisposition.needsUserAction := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem blockedNeedsCanBeRepresented :
    ∃ assessment : NeedAssessment, assessment = foreignRepoBlockedAssessment := by
  exact ⟨foreignRepoBlockedAssessment, rfl⟩

theorem needAssessmentsContainBothWitnessAndBlockedCases :
    needAssessments =
      [ .satisfiable prefetchedProfileNeedPlan
      , .satisfiable profileScreenNeedPlan
      , .satisfiable composerScreenNeedPlan
      , .blocked deferredOwnRepoNeed
      , .blocked deferredComposerNeed
      , .blocked threadBoundaryBlockedNeed
      , .blocked repoBoundaryBlockedNeed
      , .blocked foreignThreadBlockedNeed
      , .blocked foreignRepoBlockedNeed
      ] := by
  rfl

end Lexicon
