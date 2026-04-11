import Lexicon.Search

/-!
# ConstraintProfiles
Constraint toggle experiments fixed as small profile diffs in Lean.
-/

namespace Lexicon

inductive ConstraintProfile where
  | exact
  | subtype
  | selfId
  | ownership
  | all
  deriving DecidableEq, Repr

def subtypeProfileAnnotation : Annotation where
  requires := .capability "access_jwt"
  touches := .emitDatum "profileViewDetailed"

def profileAxiomFor : ConstraintProfile → Axiom
  | .exact =>
      { code := getProfile
        refined := refine getProfile
        annotation := minimal }
  | .subtype =>
      { code := getProfile
        refined := refine getProfile
        annotation := subtypeProfileAnnotation }
  | .selfId => profileAxiom
  | .ownership => profileAxiom
  | .all => profileAxiom

def profileChoicesFor (profile : ConstraintProfile) : List Axiom :=
  [createSessionAxiom, profileAxiomFor profile]

def selfProfileCandidates (profile : ConstraintProfile) : List (List String) :=
  searchAll 2 (profileChoicesFor profile) ∅ profileSearchGoal

def ownershipBridgeCode : LexiconCode where
  nsid := "internal.ownership.deriveRepo"
  kind := .query
  input := .object []
  output := .object []

def ownershipBridgeAxiom : Axiom where
  code := ownershipBridgeCode
  refined := refine ownershipBridgeCode
  annotation := {
    requires := .and (.capability "access_jwt") (.ownershipSelf "actor")
    touches := .emitSelf "repo"
  }

def ownRepoReadCode : LexiconCode where
  nsid := "internal.repo.describeSelf"
  kind := .query
  input := .object []
  output := .object []

def ownRepoReadAxiom : Axiom where
  code := ownRepoReadCode
  refined := refine ownRepoReadCode
  annotation := {
    requires := .and (.capability "access_jwt") (.ownershipSelf "repo")
    touches := .emitDatum "repoOwnedView"
  }

def ownRepoGoal : SearchGoal := [Fact.datum "repoOwnedView"]

def ownRepoChoicesFor : ConstraintProfile → List Axiom
  | .ownership => [createSessionAxiom, ownershipBridgeAxiom, ownRepoReadAxiom]
  | .all => [createSessionAxiom, ownershipBridgeAxiom, ownRepoReadAxiom]
  | _ => [createSessionAxiom, ownRepoReadAxiom]

def ownRepoCandidates (profile : ConstraintProfile) : List (List String) :=
  searchAll 3 (ownRepoChoicesFor profile) ∅ ownRepoGoal

def createRecordCode : LexiconCode where
  nsid := "com.atproto.repo.createRecord"
  kind := .procedure
  input := .object [("record", .atom .token)]
  output := .object [("uri", .atom .token)]

def recordCreateUnknownAnnotation : Annotation where
  requires := .and (.capability "access_jwt")
    (.and (.ownershipSelf "repo") (.datum "unknown.record"))
  touches := .emitDatum "repoRecordCreated"

def recordCreateInputAnnotation : Annotation where
  requires := .and (.capability "access_jwt")
    (.and (.ownershipSelf "repo") (.datum "input.record"))
  touches := .emitDatum "repoRecordCreated"

def createRecordAxiomFor : ConstraintProfile → Axiom
  | .all =>
      { code := createRecordCode
        refined := refine createRecordCode
        annotation := recordCreateInputAnnotation }
  | _ =>
      { code := createRecordCode
        refined := refine createRecordCode
        annotation := recordCreateUnknownAnnotation }

def selfWriteInputs : Marking := {Fact.datum "input.record"}

def selfWriteGoal : SearchGoal := [Fact.datum "repoRecordCreated"]

def selfWriteChoicesFor : ConstraintProfile → List Axiom
  | .ownership => [createSessionAxiom, ownershipBridgeAxiom, createRecordAxiomFor .ownership]
  | .all => [createSessionAxiom, ownershipBridgeAxiom, createRecordAxiomFor .all]
  | profile => [createSessionAxiom, createRecordAxiomFor profile]

def selfWriteCandidates (profile : ConstraintProfile) : List (List String) :=
  searchAll 3 (selfWriteChoicesFor profile) selfWriteInputs selfWriteGoal

def actorLikesCode : LexiconCode where
  nsid := "app.bsky.feed.getActorLikes"
  kind := .query
  input := .object []
  output := .object []

def authorFeedCode : LexiconCode where
  nsid := "app.bsky.feed.getAuthorFeed"
  kind := .query
  input := .object []
  output := .object []

def timelineCode : LexiconCode where
  nsid := "app.bsky.feed.getTimeline"
  kind := .query
  input := .object []
  output := .object []

def feedOptionAnnotation : Annotation where
  requires := .capability "access_jwt"
  touches := .emitDatum "feedOptionView"

def actorLikesAxiom : Axiom where
  code := actorLikesCode
  refined := refine actorLikesCode
  annotation := feedOptionAnnotation

def authorFeedAxiom : Axiom where
  code := authorFeedCode
  refined := refine authorFeedCode
  annotation := feedOptionAnnotation

def timelineAxiom : Axiom where
  code := timelineCode
  refined := refine timelineCode
  annotation := feedOptionAnnotation

def feedOptionsGoal : SearchGoal := [Fact.datum "feedOptionView"]

def feedOptionChoices : List Axiom :=
  [createSessionAxiom, actorLikesAxiom, authorFeedAxiom, timelineAxiom]

def feedOptionCandidates (_profile : ConstraintProfile) : List (List String) :=
  searchAll 2 feedOptionChoices ∅ feedOptionsGoal

theorem exactProfileBlocksSelfProfile :
    selfProfileCandidates .exact = [] := by
  simp [selfProfileCandidates, profileChoicesFor, profileAxiomFor, searchAll,
    searchAllFromChoices, satisfies?, profileSearchGoal, Axiom.enabled?, RequirementExpr.check,
    createSessionAxiom, createSession, Axiom.fire, minimal, TouchExpr.tokens]

theorem subtypeProfileEnablesSelfProfile :
    selfProfileCandidates .subtype =
      [["com.atproto.server.createSession", "app.bsky.actor.getProfile"]] := by
  simp [selfProfileCandidates, profileChoicesFor, profileAxiomFor, subtypeProfileAnnotation,
    searchAll, searchAllFromChoices, satisfies?, profileSearchGoal,
    Axiom.enabled?, RequirementExpr.check,
    createSessionAxiom, createSession, createSessionCode, getProfile,
    Axiom.fire, TouchExpr.tokens]

theorem subtypeIsFirstReachableProfile :
    selfProfileCandidates .exact = [] ∧
    selfProfileCandidates .subtype ≠ [] := by
  constructor
  · exact exactProfileBlocksSelfProfile
  · simp [subtypeProfileEnablesSelfProfile]

theorem selfIdBlocksOwnRepoRead :
    ownRepoCandidates .selfId = [] := by
  simp [ownRepoCandidates, ownRepoChoicesFor, ownRepoGoal, searchAll, searchAllFromChoices,
    satisfies?, Axiom.enabled?, RequirementExpr.check, createSessionAxiom, createSession,
    ownRepoReadAxiom, ownRepoReadCode, Axiom.fire, TouchExpr.tokens]

theorem ownershipEnablesOwnRepoRead :
    ownRepoCandidates .ownership =
      [["com.atproto.server.createSession",
        "internal.ownership.deriveRepo",
        "internal.repo.describeSelf"]] := by
  simp [ownRepoCandidates, ownRepoChoicesFor, ownRepoGoal, searchAll, searchAllFromChoices,
    satisfies?, Axiom.enabled?, RequirementExpr.check, createSessionAxiom, createSession,
    ownershipBridgeAxiom, ownershipBridgeCode, ownRepoReadAxiom, ownRepoReadCode,
    createSessionCode, Axiom.fire, TouchExpr.tokens]

theorem ownershipStillBlocksSelfWrite :
    selfWriteCandidates .ownership = [] := by
  simp [selfWriteCandidates, selfWriteChoicesFor, selfWriteInputs, selfWriteGoal, searchAll,
    searchAllFromChoices, satisfies?, Axiom.enabled?, RequirementExpr.check, createSessionAxiom,
    createSession, createRecordAxiomFor, createRecordCode, recordCreateUnknownAnnotation,
    ownershipBridgeAxiom, ownershipBridgeCode, Axiom.fire, TouchExpr.tokens]

theorem allEnablesSelfWrite :
    selfWriteCandidates .all =
      [["com.atproto.server.createSession",
        "internal.ownership.deriveRepo",
        "com.atproto.repo.createRecord"]] := by
  simp [selfWriteCandidates, selfWriteChoicesFor, selfWriteInputs, selfWriteGoal, searchAll,
    searchAllFromChoices, satisfies?, Axiom.enabled?, RequirementExpr.check, createSessionAxiom,
    createSession, createRecordAxiomFor, createRecordCode, recordCreateInputAnnotation,
    ownershipBridgeAxiom, ownershipBridgeCode, createSessionCode, Axiom.fire, TouchExpr.tokens]

theorem recordInputAddsSelfWrite :
    selfWriteCandidates .ownership = [] ∧
    selfWriteCandidates .all ≠ [] := by
  constructor
  · exact ownershipStillBlocksSelfWrite
  · simp [allEnablesSelfWrite]

theorem exactFeedOptions :
    feedOptionCandidates .exact =
      [ ["com.atproto.server.createSession", "app.bsky.feed.getActorLikes"]
      , ["com.atproto.server.createSession", "app.bsky.feed.getAuthorFeed"]
      , ["com.atproto.server.createSession", "app.bsky.feed.getTimeline"]
      ] := by
  simp [feedOptionCandidates, feedOptionChoices, feedOptionsGoal, searchAll,
    searchAllFromChoices, satisfies?, Axiom.enabled?, RequirementExpr.check,
    createSessionAxiom, createSession, createSessionCode, actorLikesAxiom, actorLikesCode,
    authorFeedAxiom, authorFeedCode, timelineAxiom, timelineCode, feedOptionAnnotation,
    Axiom.fire, TouchExpr.tokens]

theorem feedOptionsStableAcrossProfiles :
    feedOptionCandidates .exact = feedOptionCandidates .all := by
  simp [feedOptionCandidates]

end Lexicon
