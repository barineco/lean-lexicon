import Lexicon.Search
import Lexicon.ConstraintProfiles
import Lexicon.RequirementSatisfaction

/-!
# NonRecoverability
Demonstrate that annotation constraints are non-recoverable from a code-only view via behavioral differences between same-code axioms.
-/

namespace Lexicon

def codeOnlyProfileAxiom : Axiom where
  code := getProfile
  refined := refine getProfile
  annotation := { requires := .trivial, touches := .emitDatum "profileViewDetailed" }

def sameCodeOnly (lhs rhs : Axiom) : Prop :=
  lhs.code = rhs.code

theorem codeOnlyProfile_reaches_in_one :
    reachesInOne codeOnlyProfileAxiom ∅ profileGoal := by
  refine ⟨codeOnlyProfileAxiom.fire ∅, ?_, ?_⟩
  · simp [codeOnlyProfileAxiom, step, Axiom.enabled?, RequirementExpr.check, Axiom.fire]
  · intro fact hfact
    have hfact' : fact = Fact.datum "profileViewDetailed" := by
      simpa [profileGoal] using hfact
    subst fact
    simp [codeOnlyProfileAxiom, Axiom.fire, TouchExpr.tokens]

theorem guardedProfile_does_not_reach_in_one :
    ¬ reachesInOne profileAxiom ∅ profileGoal := by
  intro h
  rcases h with ⟨marking', hstep, _⟩
  simp [step, Axiom.enabled?, RequirementExpr.check, profileAxiom, authSelfRead] at hstep

theorem profileConstraintNonrecoverable :
    ∃ axLoose axGuarded,
      sameCodeOnly axLoose axGuarded ∧
      reachesInOne axLoose ∅ profileGoal ∧
      ¬ reachesInOne axGuarded ∅ profileGoal := by
  refine ⟨codeOnlyProfileAxiom, profileAxiom, rfl, ?_, ?_⟩
  · exact codeOnlyProfile_reaches_in_one
  · exact guardedProfile_does_not_reach_in_one

def sameCodeShape (lhs rhs : LexiconCode) : Prop :=
  lhs.kind = rhs.kind ∧ lhs.input = rhs.input ∧ lhs.output = rhs.output

def nrOwnershipBridgeCode : LexiconCode where
  nsid := "internal.ownership.deriveRepo"
  kind := .query
  input := .object []
  output := .object []

def nrOwnershipBridgeAxiom : Axiom where
  code := nrOwnershipBridgeCode
  refined := refine nrOwnershipBridgeCode
  annotation := {
    requires := .and (.capability "access_jwt") (.ownershipSelf "actor")
    touches := .emitSelf "repo"
  }

def nrSelfRepoReadCode : LexiconCode where
  nsid := "internal.repo.getSelfView"
  kind := .query
  input := .object [("repo", .atom .token)]
  output := .object [("view", .atom .token)]

def nrForeignRepoReadCode : LexiconCode where
  nsid := "internal.repo.getForeignView"
  kind := .query
  input := .object [("repo", .atom .token)]
  output := .object [("view", .atom .token)]

def nrSelfRepoReadAxiom : Axiom where
  code := nrSelfRepoReadCode
  refined := refine nrSelfRepoReadCode
  annotation := {
    requires := .and (.capability "access_jwt") (.ownershipSelf "repo")
    touches := .emitDatum "repoView"
  }

def nrForeignRepoReadAxiom : Axiom where
  code := nrForeignRepoReadCode
  refined := refine nrForeignRepoReadCode
  annotation := {
    requires := .and (.capability "access_jwt") (.datum "selected.repo")
    touches := .emitDatum "repoView"
  }

def codeOnlyAxiom (ax : Axiom) : Axiom where
  code := ax.code
  refined := ax.refined
  annotation := {
    requires := .trivial
    touches := ax.annotation.touches
  }

def repoViewGoal : SearchGoal := [Fact.datum "repoView"]

def guardedRepoViewChoices : List Axiom :=
  [createSessionAxiom, nrOwnershipBridgeAxiom, nrSelfRepoReadAxiom, nrForeignRepoReadAxiom]

def codeOnlyRepoViewChoices : List Axiom :=
  [codeOnlyAxiom nrSelfRepoReadAxiom, codeOnlyAxiom nrForeignRepoReadAxiom]

def guardedRepoViewCandidates : List (List String) :=
  searchAll 3 guardedRepoViewChoices ∅ repoViewGoal

def codeOnlyRepoViewCandidates : List (List String) :=
  searchAll 1 codeOnlyRepoViewChoices ∅ repoViewGoal

theorem repoReadEndpointsHaveSameCodeShape :
    sameCodeShape nrSelfRepoReadCode nrForeignRepoReadCode := by
  simp [sameCodeShape, nrSelfRepoReadCode, nrForeignRepoReadCode]

theorem codeOnlyRepoViewAmbiguous :
    codeOnlyRepoViewCandidates =
      [ ["internal.repo.getSelfView"]
      , ["internal.repo.getForeignView"]
      ] := by
  simp [codeOnlyRepoViewCandidates, codeOnlyRepoViewChoices, codeOnlyAxiom, repoViewGoal,
    searchAll, searchAllFromChoices, satisfies?, Axiom.enabled?, RequirementExpr.check,
    nrSelfRepoReadAxiom, nrSelfRepoReadCode, nrForeignRepoReadAxiom, nrForeignRepoReadCode,
    Axiom.fire, TouchExpr.tokens]

theorem guardedRepoViewUnique :
    guardedRepoViewCandidates =
      [[ "com.atproto.server.createSession"
       , "internal.ownership.deriveRepo"
       , "internal.repo.getSelfView"
       ]] := by
  simp [guardedRepoViewCandidates, guardedRepoViewChoices, repoViewGoal, searchAll,
    searchAllFromChoices, satisfies?, Axiom.enabled?, RequirementExpr.check,
    createSessionAxiom, createSessionCode, createSession, nrOwnershipBridgeAxiom,
    nrOwnershipBridgeCode, nrSelfRepoReadAxiom, nrSelfRepoReadCode, nrForeignRepoReadAxiom,
    nrForeignRepoReadCode, Axiom.fire, TouchExpr.tokens]

theorem codeOnlyLeavesSpuriousRepoCandidate :
    codeOnlyRepoViewCandidates.length > guardedRepoViewCandidates.length := by
  simp [codeOnlyRepoViewAmbiguous, guardedRepoViewUnique]

structure NonrecoverableCluster where
  goal : SearchGoal
  codeOnlyCandidates : List (List String)
  guardedCandidates : List (List String)
  boundary : RequirementBoundary

def NonrecoverableCluster.spuriousCandidates
    (cluster : NonrecoverableCluster) : List (List String) :=
  cluster.codeOnlyCandidates.filter fun recipe =>
    recipe ∉ cluster.guardedCandidates

def repoReadCluster : NonrecoverableCluster where
  goal := repoViewGoal
  codeOnlyCandidates := codeOnlyRepoViewCandidates
  guardedCandidates := guardedRepoViewCandidates
  boundary := directSelectionBoundary

theorem repoReadClusterHasSpuriousCandidate :
    repoReadCluster.spuriousCandidates =
      [ ["internal.repo.getSelfView"]
      , ["internal.repo.getForeignView"]
      ] := by
  simp [NonrecoverableCluster.spuriousCandidates, repoReadCluster,
    codeOnlyRepoViewAmbiguous, guardedRepoViewUnique]

theorem repoReadClusterIsNonrecoverable :
    repoReadCluster.spuriousCandidates ≠ [] := by
  simp [repoReadClusterHasSpuriousCandidate]

theorem repoReadClusterIsPruningBoundary :
    repoReadCluster.boundary = RequirementBoundary.pruningOnly := by
  rfl

def nrSelfThreadReadCode : LexiconCode where
  nsid := "internal.feed.getSelfThread"
  kind := .query
  input := .object [("uri", .atom .token)]
  output := .object [("thread", .atom .token)]

def nrForeignThreadReadCode : LexiconCode where
  nsid := "internal.feed.getForeignThread"
  kind := .query
  input := .object [("uri", .atom .token)]
  output := .object [("thread", .atom .token)]

def nrSelfThreadReadAxiom : Axiom where
  code := nrSelfThreadReadCode
  refined := refine nrSelfThreadReadCode
  annotation := {
    requires := .and (.capability "access_jwt") (.ownershipSelf "actor")
    touches := .emitDatum "threadView"
  }

def nrForeignThreadReadAxiom : Axiom where
  code := nrForeignThreadReadCode
  refined := refine nrForeignThreadReadCode
  annotation := {
    requires := .and (.capability "access_jwt") (.datum "selected.actor")
    touches := .emitDatum "threadView"
  }

def threadViewGoal : SearchGoal := [Fact.datum "threadView"]

def guardedThreadViewChoices : List Axiom :=
  [createSessionAxiom, nrSelfThreadReadAxiom, nrForeignThreadReadAxiom]

def codeOnlyThreadViewChoices : List Axiom :=
  [codeOnlyAxiom nrSelfThreadReadAxiom, codeOnlyAxiom nrForeignThreadReadAxiom]

def guardedThreadViewCandidates : List (List String) :=
  searchAll 2 guardedThreadViewChoices ∅ threadViewGoal

def codeOnlyThreadViewCandidates : List (List String) :=
  searchAll 1 codeOnlyThreadViewChoices ∅ threadViewGoal

def threadReadCluster : NonrecoverableCluster where
  goal := threadViewGoal
  codeOnlyCandidates := codeOnlyThreadViewCandidates
  guardedCandidates := guardedThreadViewCandidates
  boundary := directSelectionBoundary

theorem threadReadEndpointsHaveSameCodeShape :
    sameCodeShape nrSelfThreadReadCode nrForeignThreadReadCode := by
  simp [sameCodeShape, nrSelfThreadReadCode, nrForeignThreadReadCode]

theorem codeOnlyThreadViewAmbiguous :
    codeOnlyThreadViewCandidates =
      [ ["internal.feed.getSelfThread"]
      , ["internal.feed.getForeignThread"]
      ] := by
  simp [codeOnlyThreadViewCandidates, codeOnlyThreadViewChoices, codeOnlyAxiom, threadViewGoal,
    searchAll, searchAllFromChoices, satisfies?, Axiom.enabled?, RequirementExpr.check,
    nrSelfThreadReadAxiom, nrSelfThreadReadCode, nrForeignThreadReadAxiom, nrForeignThreadReadCode,
    Axiom.fire, TouchExpr.tokens]

theorem guardedThreadViewUnique :
    guardedThreadViewCandidates =
      [["com.atproto.server.createSession", "internal.feed.getSelfThread"]] := by
  simp [guardedThreadViewCandidates, guardedThreadViewChoices, threadViewGoal, searchAll,
    searchAllFromChoices, satisfies?, Axiom.enabled?, RequirementExpr.check,
    createSessionAxiom, createSessionCode, createSession, nrSelfThreadReadAxiom,
    nrSelfThreadReadCode, nrForeignThreadReadAxiom, nrForeignThreadReadCode,
    Axiom.fire, TouchExpr.tokens]

theorem threadReadClusterHasSpuriousCandidate :
    threadReadCluster.spuriousCandidates =
      [ ["internal.feed.getSelfThread"]
      , ["internal.feed.getForeignThread"]
      ] := by
  simp [NonrecoverableCluster.spuriousCandidates, threadReadCluster,
    codeOnlyThreadViewAmbiguous, guardedThreadViewUnique]

theorem threadReadClusterIsPruningBoundary :
    threadReadCluster.boundary = RequirementBoundary.pruningOnly := by
  rfl

def clusterIsOverapprox (cluster : NonrecoverableCluster) : Prop :=
  cluster.guardedCandidates.length < cluster.codeOnlyCandidates.length

def clusterHasInvisibleDiscriminator (cluster : NonrecoverableCluster) : Prop :=
  cluster.boundary = RequirementBoundary.pruningOnly ∧
  cluster.spuriousCandidates ≠ [] ∧
  clusterIsOverapprox cluster

theorem repoReadClusterOverapproximated :
    clusterIsOverapprox repoReadCluster := by
  simp [clusterIsOverapprox, codeOnlyRepoViewAmbiguous, guardedRepoViewUnique, repoReadCluster]

theorem threadReadClusterOverapproximated :
    clusterIsOverapprox threadReadCluster := by
  simp [clusterIsOverapprox, codeOnlyThreadViewAmbiguous, guardedThreadViewUnique,
    threadReadCluster]

theorem pruningBoundaryCanOverapproximate :
    repoReadCluster.boundary = RequirementBoundary.pruningOnly ∧
    clusterIsOverapprox repoReadCluster ∧
    threadReadCluster.boundary = RequirementBoundary.pruningOnly ∧
    clusterIsOverapprox threadReadCluster := by
  constructor
  · exact repoReadClusterIsPruningBoundary
  constructor
  · exact repoReadClusterOverapproximated
  constructor
  · exact threadReadClusterIsPruningBoundary
  · exact threadReadClusterOverapproximated

theorem repoReadClusterHasInvisibleDiscriminator :
    clusterHasInvisibleDiscriminator repoReadCluster := by
  refine ⟨repoReadClusterIsPruningBoundary, repoReadClusterIsNonrecoverable, ?_⟩
  exact repoReadClusterOverapproximated

theorem threadReadClusterHasInvisibleDiscriminator :
    clusterHasInvisibleDiscriminator threadReadCluster := by
  refine ⟨threadReadClusterIsPruningBoundary, ?_, ?_⟩
  · simp [threadReadClusterHasSpuriousCandidate]
  · exact threadReadClusterOverapproximated

theorem pruningOnlyClustersSharePattern :
    sameCodeShape nrSelfRepoReadCode nrForeignRepoReadCode ∧
    clusterHasInvisibleDiscriminator repoReadCluster ∧
    sameCodeShape nrSelfThreadReadCode nrForeignThreadReadCode ∧
    clusterHasInvisibleDiscriminator threadReadCluster := by
  refine ⟨repoReadEndpointsHaveSameCodeShape, repoReadClusterHasInvisibleDiscriminator,
    threadReadEndpointsHaveSameCodeShape, threadReadClusterHasInvisibleDiscriminator⟩

structure RecoverableCluster where
  goal : SearchGoal
  baselineCandidates : List (List String)
  enrichedCandidates : List (List String)
  boundary : RequirementBoundary

def clusterNeedsRecovery (cluster : RecoverableCluster) : Prop :=
  cluster.baselineCandidates.length < cluster.enrichedCandidates.length

def selfWriteRecoveryCluster : RecoverableCluster where
  goal := selfWriteGoal
  baselineCandidates := selfWriteCandidates .ownership
  enrichedCandidates := selfWriteCandidates .all
  boundary := repoBoundary

def ownRepoRecoveryCluster : RecoverableCluster where
  goal := ownRepoGoal
  baselineCandidates := ownRepoCandidates .selfId
  enrichedCandidates := ownRepoCandidates .ownership
  boundary := repoBoundary

theorem selfWriteRecoveryClusterNeedsRecovery :
    clusterNeedsRecovery selfWriteRecoveryCluster := by
  simp [clusterNeedsRecovery, selfWriteRecoveryCluster,
    ownershipStillBlocksSelfWrite, allEnablesSelfWrite]

theorem ownRepoRecoveryClusterNeedsRecovery :
    clusterNeedsRecovery ownRepoRecoveryCluster := by
  simp [clusterNeedsRecovery, ownRepoRecoveryCluster,
    selfIdBlocksOwnRepoRead, ownershipEnablesOwnRepoRead]

theorem selfWriteRecoveryClusterBoundary :
    selfWriteRecoveryCluster.boundary = RequirementBoundary.recoverableByRecipe := by
  rfl

theorem ownRepoRecoveryClusterBoundary :
    ownRepoRecoveryCluster.boundary = RequirementBoundary.recoverableByRecipe := by
  rfl

theorem recoverableBoundaryCanUnlockCandidates :
    selfWriteRecoveryCluster.boundary = RequirementBoundary.recoverableByRecipe ∧
    clusterNeedsRecovery selfWriteRecoveryCluster := by
  exact ⟨selfWriteRecoveryClusterBoundary, selfWriteRecoveryClusterNeedsRecovery⟩

theorem recoverableClustersShareUnlockPattern :
    selfWriteRecoveryCluster.boundary = RequirementBoundary.recoverableByRecipe ∧
    clusterNeedsRecovery selfWriteRecoveryCluster ∧
    ownRepoRecoveryCluster.boundary = RequirementBoundary.recoverableByRecipe ∧
    clusterNeedsRecovery ownRepoRecoveryCluster := by
  constructor
  · exact selfWriteRecoveryClusterBoundary
  constructor
  · exact selfWriteRecoveryClusterNeedsRecovery
  constructor
  · exact ownRepoRecoveryClusterBoundary
  · exact ownRepoRecoveryClusterNeedsRecovery

end Lexicon
