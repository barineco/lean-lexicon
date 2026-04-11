import Lexicon.Interpretation

/-!
# RequirementSatisfaction
Interpret requirements as source-origin semantics rather than field enumeration.
-/

namespace Lexicon

inductive RequirementSourceKind where
  | user
  | marked
  | derivedSubtype
  | derivedOwnership
  | derivedSelfId
  | yielded
  | yieldedThenDerived
  deriving DecidableEq, Repr

inductive RequirementSource where
  | userSupplied : Fact → RequirementSource
  | alreadyMarked : Fact → RequirementSource
  | derived : String → Fact → RequirementSource
  | yieldedBy : String → Fact → RequirementSource
  deriving DecidableEq, Repr

def classifySource : RequirementSource → RequirementSourceKind
  | .userSupplied _ => .user
  | .alreadyMarked _ => .marked
  | .derived tag _ =>
      if tag = "subtype" then .derivedSubtype
      else if tag = "ownership-bridge" then .derivedOwnership
      else if tag = "self-id" then .derivedSelfId
      else .yieldedThenDerived
  | .yieldedBy _ _ => .yielded

def sourceKinds (sources : List RequirementSource) : List RequirementSourceKind :=
  sources.map classifySource

def RequirementSource.fact : RequirementSource → Fact
  | .userSupplied fact => fact
  | .alreadyMarked fact => fact
  | .derived _ fact => fact
  | .yieldedBy _ fact => fact

def sourceFacts : List RequirementSource → Marking
  | [] => ∅
  | source :: rest => insert source.fact (sourceFacts rest)

def semanticMarking (marking : Marking) (sources : List RequirementSource) : Marking :=
  marking ∪ sourceFacts sources

def RequirementExpr.SatisfiedBy
    (req : RequirementExpr)
    (marking : Marking)
    (sources : List RequirementSource) : Prop :=
  req.Holds (semanticMarking marking sources)

def inputFieldNames (code : LexiconCode) : List String :=
  match code.input with
  | .object fields => fields.map Prod.fst
  | _ => []

def createSessionSemanticSources : List RequirementSource :=
  [ .yieldedBy createSessionCode.nsid (Fact.capability "access_jwt")
  , .yieldedBy createSessionCode.nsid (Fact.selfKey "actor")
  ]

theorem profileRequirementsSatisfiedByCreateSession :
    authSelfRead.requires.SatisfiedBy ∅ createSessionSemanticSources := by
  simp [RequirementExpr.SatisfiedBy, RequirementExpr.Holds, semanticMarking,
    sourceFacts, createSessionSemanticSources, authSelfRead, RequirementSource.fact]

theorem accessJwtIsNotAGetProfileInputField :
    "accessJwt" ∉ inputFieldNames getProfile := by
  simp [inputFieldNames, getProfile]

theorem semanticRequirementExceedsFieldEnumeration :
    authSelfRead.requires.SatisfiedBy ∅ createSessionSemanticSources ∧
    "accessJwt" ∉ inputFieldNames getProfile := by
  exact ⟨profileRequirementsSatisfiedByCreateSession, accessJwtIsNotAGetProfileInputField⟩

def actorLookupCode : LexiconCode where
  nsid := "app.bsky.actor.getProfile"
  kind := .query
  input := .object [("actor", .atom .string)]
  output := .object [("profile", .atom .token)]

def actorSemanticSources : List RequirementSource :=
  [ .userSupplied (Fact.datum "input.actor")
  , .yieldedBy createSessionCode.nsid (Fact.capability "access_jwt")
  ]

def actorSourceKinds : List RequirementSourceKind :=
  sourceKinds actorSemanticSources

def actorRequirement : RequirementExpr :=
  .and (.capability "access_jwt") (.datum "input.actor")

theorem actorRequirementSatisfied :
    actorRequirement.SatisfiedBy ∅ actorSemanticSources := by
  simp [RequirementExpr.SatisfiedBy, RequirementExpr.Holds, actorRequirement, semanticMarking,
    sourceFacts, actorSemanticSources, RequirementSource.fact]

theorem accessJwtIsNotAnActorLookupInputField :
    "accessJwt" ∉ inputFieldNames actorLookupCode := by
  simp [inputFieldNames, actorLookupCode]

def repoWriteCode : LexiconCode where
  nsid := "com.atproto.repo.createRecord"
  kind := .procedure
  input := .object [("record", .atom .token)]
  output := .object [("uri", .atom .token)]

def repoSemanticSources : List RequirementSource :=
  [ .derived "ownership-bridge" (Fact.selfKey "repo")
  , .yieldedBy createSessionCode.nsid (Fact.capability "access_jwt")
  , .userSupplied (Fact.datum "input.record")
  ]

def repoSourceKinds : List RequirementSourceKind :=
  sourceKinds repoSemanticSources

def repoRequirement : RequirementExpr :=
  .and (.capability "access_jwt")
    (.and (.ownershipSelf "repo") (.datum "input.record"))

theorem repoRequirementSatisfied :
    repoRequirement.SatisfiedBy ∅ repoSemanticSources := by
  simp [RequirementExpr.SatisfiedBy, RequirementExpr.Holds, repoRequirement, semanticMarking,
    sourceFacts, repoSemanticSources, RequirementSource.fact]

theorem repoIsNotARepoWriteInputField :
    "repo" ∉ inputFieldNames repoWriteCode := by
  simp [inputFieldNames, repoWriteCode]

def threadReadCode : LexiconCode where
  nsid := "app.bsky.feed.getPostThread"
  kind := .query
  input := .object [("depth", .atom .integer)]
  output := .object [("thread", .atom .token)]

def uriSemanticSources : List RequirementSource :=
  [ .yieldedBy repoWriteCode.nsid (Fact.datum "uri")
  , .yieldedBy createSessionCode.nsid (Fact.capability "access_jwt")
  ]

def uriSourceKinds : List RequirementSourceKind :=
  sourceKinds uriSemanticSources

inductive RequirementBoundary where
  | alreadySatisfied
  | recoverableByRecipe
  | pruningOnly
  deriving DecidableEq, Repr

def RequirementSourceKind.isRecipeRecoverable : RequirementSourceKind → Bool
  | .user => false
  | .marked => false
  | .derivedSubtype => true
  | .derivedOwnership => true
  | .derivedSelfId => true
  | .yielded => true
  | .yieldedThenDerived => true

def hasMarkedSource (sources : List RequirementSource) : Bool :=
  sources.any (fun source => classifySource source = .marked)

def hasRecipeRecoverableSource (sources : List RequirementSource) : Bool :=
  sources.any (fun source => (classifySource source).isRecipeRecoverable)

def classifyBoundary (sources : List RequirementSource) : RequirementBoundary :=
  if hasMarkedSource sources then
    .alreadySatisfied
  else if hasRecipeRecoverableSource sources then
    .recoverableByRecipe
  else
    .pruningOnly

def actorBoundary : RequirementBoundary :=
  classifyBoundary actorSemanticSources

def repoBoundary : RequirementBoundary :=
  classifyBoundary repoSemanticSources

def uriBoundary : RequirementBoundary :=
  classifyBoundary uriSemanticSources

def directSelectionSources : List RequirementSource :=
  [.userSupplied (Fact.datum "selected.repo")]

def directSelectionBoundary : RequirementBoundary :=
  classifyBoundary directSelectionSources

def prefetchedProfileSources : List RequirementSource :=
  [.alreadyMarked (Fact.datum "profileViewDetailed")]

def prefetchedProfileBoundary : RequirementBoundary :=
  classifyBoundary prefetchedProfileSources

def uriRequirement : RequirementExpr :=
  .and (.capability "access_jwt") (.datum "uri")

theorem uriRequirementSatisfied :
    uriRequirement.SatisfiedBy ∅ uriSemanticSources := by
  simp [RequirementExpr.SatisfiedBy, RequirementExpr.Holds, uriRequirement, semanticMarking,
    sourceFacts, uriSemanticSources, RequirementSource.fact]

theorem uriIsNotAThreadReadInputField :
    "uri" ∉ inputFieldNames threadReadCode := by
  simp [inputFieldNames, threadReadCode]

theorem actorExampleExceedsFieldEnumeration :
    actorRequirement.SatisfiedBy ∅ actorSemanticSources ∧
    "accessJwt" ∉ inputFieldNames actorLookupCode := by
  exact ⟨actorRequirementSatisfied, accessJwtIsNotAnActorLookupInputField⟩

theorem actorExampleSourceKinds :
    actorSourceKinds = [RequirementSourceKind.user, RequirementSourceKind.yielded] := by
  rfl

theorem actorBoundaryRecoverable :
    actorBoundary = RequirementBoundary.recoverableByRecipe := by
  rfl

theorem actorHasRecipeRecoverableSource :
    hasRecipeRecoverableSource actorSemanticSources = true := by
  rfl

theorem repoExampleExceedsFieldEnumeration :
    repoRequirement.SatisfiedBy ∅ repoSemanticSources ∧
    "repo" ∉ inputFieldNames repoWriteCode := by
  exact ⟨repoRequirementSatisfied, repoIsNotARepoWriteInputField⟩

theorem repoExampleSourceKinds :
    repoSourceKinds =
      [ RequirementSourceKind.derivedOwnership
      , RequirementSourceKind.yielded
      , RequirementSourceKind.user
      ] := by
  rfl

theorem repoBoundaryRecoverable :
    repoBoundary = RequirementBoundary.recoverableByRecipe := by
  rfl

theorem repoHasRecipeRecoverableSource :
    hasRecipeRecoverableSource repoSemanticSources = true := by
  rfl

theorem uriExampleExceedsFieldEnumeration :
    uriRequirement.SatisfiedBy ∅ uriSemanticSources ∧
    "uri" ∉ inputFieldNames threadReadCode := by
  exact ⟨uriRequirementSatisfied, uriIsNotAThreadReadInputField⟩

theorem uriExampleSourceKinds :
    uriSourceKinds = [RequirementSourceKind.yielded, RequirementSourceKind.yielded] := by
  rfl

theorem uriBoundaryRecoverable :
    uriBoundary = RequirementBoundary.recoverableByRecipe := by
  rfl

theorem uriHasRecipeRecoverableSource :
    hasRecipeRecoverableSource uriSemanticSources = true := by
  rfl

theorem directSelectionUsesOnlyUserSources :
    sourceKinds directSelectionSources = [RequirementSourceKind.user] := by
  rfl

theorem directSelectionHasNoRecipeRecoverableSource :
    hasRecipeRecoverableSource directSelectionSources = false := by
  rfl

theorem directSelectionBoundaryPruningOnly :
    directSelectionBoundary = RequirementBoundary.pruningOnly := by
  rfl

theorem prefetchedProfileUsesMarkedSource :
    sourceKinds prefetchedProfileSources = [RequirementSourceKind.marked] := by
  rfl

theorem prefetchedProfileBoundaryAlreadySatisfied :
    prefetchedProfileBoundary = RequirementBoundary.alreadySatisfied := by
  rfl

theorem pruningBoundaryCanComeFromUserOnlySources :
    sourceKinds directSelectionSources = [RequirementSourceKind.user] ∧
    hasRecipeRecoverableSource directSelectionSources = false ∧
    directSelectionBoundary = RequirementBoundary.pruningOnly := by
  exact ⟨directSelectionUsesOnlyUserSources, directSelectionHasNoRecipeRecoverableSource,
    directSelectionBoundaryPruningOnly⟩

theorem alreadySatisfiedBoundaryCanComeFromMarkedSources :
    sourceKinds prefetchedProfileSources = [RequirementSourceKind.marked] ∧
    prefetchedProfileBoundary = RequirementBoundary.alreadySatisfied := by
  exact ⟨prefetchedProfileUsesMarkedSource, prefetchedProfileBoundaryAlreadySatisfied⟩

end Lexicon
