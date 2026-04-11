import Lexicon.Interpretation
import Mathlib.Data.Finset.Image

/-!
# Transition
Sequential composition and equivalence of axioms viewed as marking transitions.
-/

namespace Lexicon

/-! ## Transition: abstract transition over Markings -/

/-- A transition over markings: a guard condition paired with a state-transforming effect. -/
structure Transition where
  guard : Marking → Bool
  effect : Marking → Marking

/-- Project an Axiom into a Transition. -/
def Axiom.toTransition (ax : Axiom) : Transition where
  guard := ax.enabled?
  effect := ax.fire

/-! ## Sequential composition -/

/-- Sequential composition: fire t1 then t2; guard requires t1 enabled and t2 enabled after t1's effect. -/
def Transition.seq (t1 t2 : Transition) : Transition where
  guard m := t1.guard m && t2.guard (t1.effect m)
  effect m := t2.effect (t1.effect m)

instance : HMul Transition Transition Transition where
  hMul := Transition.seq

/-! ## Equivalence -/

/-- Transition equivalence: guard and effect agree on all markings. -/
def Transition.equiv (t1 t2 : Transition) : Prop :=
  (∀ m, t1.guard m = t2.guard m) ∧ (∀ m, t1.effect m = t2.effect m)

scoped infixl:50 " ≈ₜ " => Transition.equiv

/-! ## Associativity -/

/-- Sequential composition is associative. -/
theorem Transition.seq_assoc (t1 t2 t3 : Transition) :
    (t1.seq t2).seq t3 ≈ₜ t1.seq (t2.seq t3) := by
  constructor
  · intro m
    simp [seq, Bool.and_assoc]
  · intro m
    simp [seq]

/-! ## Identity and unit laws -/

/-- Identity transition: always enabled, leaves marking unchanged. -/
def Transition.id : Transition where
  guard _ := true
  effect m := m

/-- Left unit law: id ; t is equivalent to t. -/
theorem Transition.id_seq (t : Transition) : Transition.id.seq t ≈ₜ t := by
  constructor
  · intro m; simp [seq, id]
  · intro m; simp [seq, id]

/-- Right unit law: t ; id is equivalent to t. -/
theorem Transition.seq_id (t : Transition) : t.seq Transition.id ≈ₜ t := by
  constructor
  · intro m; simp [seq, id]
  · intro m; simp [seq, id]

/-! ## Example: createSession ; getProfile -/

/-- Transition projection of createSession. -/
def createSessionT : Transition := createSessionAxiom.toTransition

/-- Transition projection of getProfile. -/
def profileT : Transition := profileAxiom.toTransition

/-- createSession ; getProfile fires from the empty marking. -/
theorem createSession_then_profile_fires :
    (createSessionT.seq profileT).guard ∅ = true := by
  simp [Transition.seq, createSessionT, profileT,
    Axiom.toTransition, Axiom.enabled?, Axiom.fire,
    RequirementExpr.check, createSessionAxiom, profileAxiom,
    createSession, authSelfRead, TouchExpr.tokens]

/-- getProfile alone is blocked from the empty marking. -/
theorem profile_alone_blocked :
    profileT.guard ∅ = false := by
  simp [profileT, Axiom.toTransition, Axiom.enabled?,
    RequirementExpr.check, profileAxiom, authSelfRead]

/-! ## Composition equivalence: getTimeline is equivalent to getFollows ; map(getAuthorFeed) -/

/-- getFollows: requires session, produces follows data. -/
def getFollowsT : Transition where
  guard m := Fact.capability "access_jwt" ∈ m
  effect m := m ∪ {Fact.datum "follows"}

/-- getAuthorFeed: requires session, produces author feed data. -/
def getAuthorFeedT : Transition where
  guard m := Fact.capability "access_jwt" ∈ m
  effect m := m ∪ {Fact.datum "authorFeed"}

/-- getTimeline: requires session, produces follows and feed simultaneously (internally equivalent to getFollows + map(getAuthorFeed)). -/
def getTimelineT : Transition where
  guard m := Fact.capability "access_jwt" ∈ m
  effect m := m ∪ {Fact.datum "follows", Fact.datum "authorFeed"}

/-- Marking-level map: a data-flow operation transparent to tokens (identity on Marking). -/
def Transition.mapT (t : Transition) : Transition := t

/-- map is transparent at the Marking level. -/
theorem Transition.mapT_equiv (t : Transition) : t.mapT ≈ₜ t :=
  ⟨fun _ => rfl, fun _ => rfl⟩

/-- Guard helper: membership in m implies membership in m union s. -/
private theorem guard_absorb {m : Marking} {a : Fact} {s : Finset Fact}
    (h : (a ∈ m : Bool) = true) : (a ∈ (m ∪ s) : Bool) = true := by
  simp [Finset.mem_union]
  left
  exact of_decide_eq_true h

/-- getTimeline is equivalent to getFollows ; map(getAuthorFeed). -/
theorem timeline_equiv_follows_then_feed :
    getTimelineT ≈ₜ getFollowsT.seq getAuthorFeedT.mapT := by
  show getTimelineT ≈ₜ getFollowsT.seq getAuthorFeedT
  refine ⟨fun m => ?_, fun m => ?_⟩
  · -- guard: access_jwt ∈ m = (access_jwt ∈ m && access_jwt ∈ m ∪ {follows})
    simp only [getTimelineT, getFollowsT, getAuthorFeedT, Transition.seq]
    by_cases h : Fact.capability "access_jwt" ∈ m <;> simp [h, Finset.mem_union]
  · -- effect: m ∪ {follows, authorFeed} = (m ∪ {follows}) ∪ {authorFeed}
    simp only [getTimelineT, getFollowsT, getAuthorFeedT, Transition.seq]
    ext x
    simp [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]

/-! ## RichTransition: concrete requires/produces/consumes transitions -/

/-- Concrete transition directly corresponding to axiom.kdl requires/produces/consumes. -/
structure RichTransition where
  requires : Finset Fact
  produces : Finset Fact
  consumes : Finset Fact

/-- RichTransition guard expressed as Finset.Subset (Prop version). -/
def RichTransition.enabled (rt : RichTransition) (m : Marking) : Prop :=
  rt.requires ⊆ m

/-- RichTransition guard (Bool version): checks whether all required facts are in the marking. -/
def RichTransition.enabled? (rt : RichTransition) (m : Marking) : Bool :=
  decide (rt.requires ⊆ m)

/-- RichTransition effect: remove consumed facts and add produced facts. -/
def RichTransition.fire (rt : RichTransition) (m : Marking) : Marking :=
  (m \ rt.consumes) ∪ rt.produces

/-- Convert a RichTransition to a Transition. -/
def RichTransition.asTransition (rt : RichTransition) : Transition where
  guard := rt.enabled?
  effect := rt.fire

/-! ### Example: refresh token consumption and regeneration -/

/-- createSession: callable without tokens; produces access_jwt and refresh_token. -/
def createSessionR : RichTransition where
  requires := ∅
  produces := {Fact.capability "access_jwt", Fact.capability "refresh_token"}
  consumes := ∅

/-- refreshSession: consumes refresh_token and produces a new access_jwt (linear use). -/
def refreshSessionR : RichTransition where
  requires := {Fact.capability "refresh_token"}
  produces := {Fact.capability "access_jwt"}
  consumes := {Fact.capability "refresh_token"}

/-- After createSession the marking contains access_jwt and refresh_token. -/
theorem createSession_produces :
    createSessionR.fire ∅ = {Fact.capability "access_jwt", Fact.capability "refresh_token"} := by
  simp [RichTransition.fire, createSessionR, Finset.empty_sdiff]

/-- After refreshSession, refresh_token is removed from the marking. -/
theorem refresh_consumes_token :
    Fact.capability "refresh_token" ∉
      refreshSessionR.fire {Fact.capability "access_jwt", Fact.capability "refresh_token"} := by
  simp [RichTransition.fire, refreshSessionR, Finset.mem_union, Finset.mem_sdiff,
    Finset.mem_singleton, Finset.mem_insert]

/-- After refreshSession, access_jwt remains in the marking. -/
theorem refresh_preserves_access :
    Fact.capability "access_jwt" ∈
      refreshSessionR.fire {Fact.capability "access_jwt", Fact.capability "refresh_token"} := by
  simp [RichTransition.fire, refreshSessionR, Finset.mem_union, Finset.mem_sdiff,
    Finset.mem_singleton, Finset.mem_insert]

/-- Double refresh is impossible: the guard is false on the post-refresh marking. -/
theorem double_refresh_blocked :
    refreshSessionR.enabled?
      (refreshSessionR.fire
        {Fact.capability "access_jwt", Fact.capability "refresh_token"}) = false := by
  simp [RichTransition.enabled?, RichTransition.fire, refreshSessionR,
    Finset.subset_iff, Finset.mem_union, Finset.mem_sdiff,
    Finset.mem_singleton, Finset.mem_insert]

/-! ## TimedMarking: time-constrained tokens -/

/-- Timed fact: a Fact augmented with an expiry. -/
structure TimedFact where
  fact : Fact
  expiry : Nat  -- expiry (discrete time)
  deriving DecidableEq, Repr

/-- Time-constrained marking. -/
abbrev TimedMarking := Finset TimedFact

/-- Extract only the tokens active at time t. -/
def TimedMarking.activeAt (tm : TimedMarking) (t : Nat) : Finset Fact :=
  (tm.filter (fun tf => t < tf.expiry)).image TimedFact.fact

/-- Time-constrained transition: requires-check depends on current time. -/
structure TimedTransition where
  requires : Finset Fact
  produces : List (Fact × Nat)  -- (fact, ttl) pairs
  consumes : Finset Fact

/-- Whether a fact is active at time t. -/
def TimedFact.activeAt (tf : TimedFact) (t : Nat) : Bool :=
  t < tf.expiry

/-- Time-constrained guard: all required facts must be active at time t. -/
def TimedTransition.enabled (tt : TimedTransition) (tm : TimedMarking) (t : Nat) : Bool :=
  decide (∀ req ∈ tt.requires, ∃ tf ∈ tm, tf.fact == req && tf.activeAt t)

/-! ### Example: modeling token expiry -/

/-- access_jwt is active at time 100. -/
example : (TimedFact.mk (Fact.capability "access_jwt") 3600).activeAt 100 = true := by
  decide

/-- access_jwt has expired at time 3601. -/
example : (TimedFact.mk (Fact.capability "access_jwt") 3600).activeAt 3601 = false := by
  decide

/-- activeAt filter: at time 3601, access_jwt is gone and only refresh_token remains. -/
theorem timed_filter_expiry :
    ({⟨Fact.capability "access_jwt", 3600⟩,
      ⟨Fact.capability "refresh_token", 86400⟩} : TimedMarking).filter
        (fun tf => tf.activeAt 3601)
    = {⟨Fact.capability "refresh_token", 86400⟩} := by
  ext ⟨f, e⟩
  simp [TimedFact.activeAt, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨h | h, hlt⟩
    · cases h; omega
    · exact h
  · intro h; exact ⟨Or.inr h, by cases h; omega⟩

/-! ## CapabilityType: absorbing existence constraints into the Petri net -/

/-- Capability type: the set of operations permitted on a type. -/
structure CapabilityType where
  typeName : String
  allowed : List String   -- permitted operation names

/-- Whether an operation is permitted. -/
def CapabilityType.permits (cap : CapabilityType) (op : String) : Bool :=
  cap.allowed.any (· == op)

/-- Example: SigningKey permits only sign and verify. -/
def signingKeyCap : CapabilityType where
  typeName := "SigningKey"
  allowed := ["sign", "verify"]

/-- sign is permitted. -/
example : signingKeyCap.permits "sign" = true := by decide

/-- display is denied. -/
example : signingKeyCap.permits "display" = false := by decide

/-- Core of capability type absorption: denied operations get an unreachable token in requires, making their guard permanently false. -/
theorem denied_op_always_blocked (cap : CapabilityType) (op : String)
    (h : cap.permits op = false) (m : Marking)
    (unreachable : Fact.capability (cap.typeName ++ ".__denied." ++ op) ∉ m) :
    ¬ ({Fact.capability (cap.typeName ++ ".__denied." ++ op)} : Finset Fact) ⊆ m :=
  fun hsub => unreachable (hsub (Finset.mem_singleton.mpr rfl))

/-! ## TypedTransition: unified token flow and type flow -/

/-- Typed transition: pairs token flow (guard/effect) with type flow (inputType/outputType). -/
structure TypedTransition where
  transition : Transition
  inputType : TypeExpr
  outputType : TypeExpr

/-- Construct a TypedTransition from an Axiom; token flow from annotation, type flow from code. -/
def Axiom.toTypedTransition (ax : Axiom) : TypedTransition where
  transition := ax.toTransition
  inputType := ax.code.input
  outputType := ax.code.output

/-! ### Typed composition: type compatibility -/

/-- Precondition for typed composition: the predecessor's output type must match the successor's input type. -/
def TypedTransition.composable (t1 t2 : TypedTransition) : Prop :=
  t1.outputType = t2.inputType

/-- Typed sequential composition: token flow via Transition.seq, type flow from t1.input to t2.output. -/
def TypedTransition.seq (t1 t2 : TypedTransition) : TypedTransition where
  transition := t1.transition.seq t2.transition
  inputType := t1.inputType
  outputType := t2.outputType

/-! ### Example: typed composition of createSession and getProfile -/

/-- Typed transition for createSession. -/
def createSessionTT : TypedTransition :=
  createSessionAxiom.toTypedTransition

/-- Typed transition for getProfile. -/
def profileTT : TypedTransition :=
  profileAxiom.toTypedTransition

/-- Composed transition type: createSession's input type to getProfile's output type. -/
example : (createSessionTT.seq profileTT).inputType =
    .object [("identifier", .atom .string), ("password", .atom .string)] := by
  rfl

example : (createSessionTT.seq profileTT).outputType =
    .object [("handle", .atom .string)] := by
  rfl

/-! ### Associativity of typed composition -/

/-- Typed composition is associative (type flow perspective). -/
theorem TypedTransition.seq_inputType_assoc (t1 t2 t3 : TypedTransition) :
    ((t1.seq t2).seq t3).inputType = (t1.seq (t2.seq t3)).inputType := by
  rfl

theorem TypedTransition.seq_outputType_assoc (t1 t2 t3 : TypedTransition) :
    ((t1.seq t2).seq t3).outputType = (t1.seq (t2.seq t3)).outputType := by
  rfl

/-- Typed composition inherits associativity of token flow. -/
theorem TypedTransition.seq_assoc (t1 t2 t3 : TypedTransition) :
    ((t1.seq t2).seq t3).transition ≈ₜ (t1.seq (t2.seq t3)).transition :=
  Transition.seq_assoc _ _ _

/-! ## Codegen functoriality: abstract framework
Codegen should be a functor F from the Lexicon category (with TypedTransition as morphisms) to the target language category; the functor conditions are defined as a structure.
-/

/-- Abstract target language: types and operations that codegen emits into. -/
structure TargetLang where
  /-- Target language type. -/
  TargetType : Type
  /-- Target language operation (morphism). -/
  TargetOp : Type
  /-- Operation composition. -/
  compose : TargetOp → TargetOp → TargetOp
  /-- Identity operation. -/
  identity : TargetOp

/-- Codegen functor structure: a mapping from the Lexicon category to the target language category. -/
structure CodegenFunctor (target : TargetLang) where
  /-- Type mapping: converts Lexicon TypeExpr to a target language type. -/
  mapType : TypeExpr → target.TargetType
  /-- Morphism mapping: converts TypedTransition to a target language operation. -/
  mapOp : TypedTransition → target.TargetOp
  /-- Identity preservation: mapping the Lexicon identity yields the target identity. -/
  preservesId : ∀ ty,
    mapOp ⟨Transition.id, ty, ty⟩ = target.identity
  /-- Composition preservation: mapping a Lexicon composition yields the target composition. -/
  preservesComp : ∀ t1 t2,
    mapOp (t1.seq t2) = target.compose (mapOp t1) (mapOp t2)

/-! ### Corollary: a functor preserves semantic equalities
If a CodegenFunctor exists, equalities in Lexicon hold in the target language as well.
-/

/-- A functor preserves equality: if two TypedTransitions are equal, their images are equal. -/
theorem codegen_preserves_eq {target : TargetLang} (F : CodegenFunctor target)
    (t1 t2 : TypedTransition) (h : t1 = t2) :
    F.mapOp t1 = F.mapOp t2 :=
  congrArg F.mapOp h

/-! ## Type-level branching: branching is type projection
Runtime branching over a union output is not a new computational primitive but a composition of TypeExpr.dispatch with the corresponding handler transition.
-/

/-- Collection of per-variant handlers for a union type. -/
structure BranchHandler where
  handlers : List (String × TypedTransition)

/-- Compose a union-producing transition with the handler for the given variant tag. -/
def TypedTransition.branch (t : TypedTransition) (bh : BranchHandler) (tag : String) :
    Option TypedTransition := do
  -- Dispatch the union to get the variant type for the tag
  let variantType ← t.outputType.dispatch tag
  -- Look up the handler for this tag
  let (_, handler) ← bh.handlers.find? (fun p => p.1 == tag)
  -- Compose the transition with the handler
  some (t.seq handler)

/-! ### Example: applyWrites branching
Type-level representation of the PDS applyWrites handler discovered during H7 verification.
-/

/-- applyWrites transition: produces an ApplyWriteAction union from input parameters. -/
def applyWritesT : TypedTransition where
  transition := Transition.id  -- token flow simplified
  inputType := .object [("writes", .array (.atom .token))]
  outputType := applyWriteAction  -- union: create | update | delete

/-- create handler: processes a write containing a record. -/
def createHandler : TypedTransition where
  transition := Transition.id
  inputType := .object [("collection", .atom .string), ("rkey", .atom .string),
                         ("record", .atom .token)]
  outputType := .object [("uri", .atom .string), ("cid", .atom .string)]

/-- delete handler: processes a deletion without a record. -/
def deleteHandler : TypedTransition where
  transition := Transition.id
  inputType := .object [("collection", .atom .string), ("rkey", .atom .string)]
  outputType := .object [("uri", .atom .string)]

def writeHandlers : BranchHandler where
  handlers := [("create", createHandler), ("delete", deleteHandler)]

/-- Branching on "create" yields the composition applyWrites ; createHandler. -/
theorem branch_create_output :
    (applyWritesT.branch writeHandlers "create").map TypedTransition.outputType
    = some (.object [("uri", .atom .string), ("cid", .atom .string)]) := by
  rfl

/-- Branching on "delete" yields applyWrites ; deleteHandler (outputType differs from create: no cid field). -/
theorem branch_delete_output :
    (applyWritesT.branch writeHandlers "delete").map TypedTransition.outputType
    = some (.object [("uri", .atom .string)]) := by
  rfl

/-- Branching is dispatch then seq: runtime match is not a new primitive but TypeExpr.dispatch composed with seq. -/
theorem branch_is_dispatch_then_seq (t : TypedTransition) (bh : BranchHandler) (tag : String)
    (variantType : TypeExpr) (handler : TypedTransition)
    (hd : t.outputType.dispatch tag = some variantType)
    (hh : bh.handlers.find? (fun p => p.1 == tag) = some (tag, handler)) :
    t.branch bh tag = some (t.seq handler) := by
  simp [TypedTransition.branch, hd, hh]

end Lexicon
