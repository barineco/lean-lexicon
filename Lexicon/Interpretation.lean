import Mathlib.Data.Finset.Basic
import Lexicon.Canonical

/-!
# Interpretation
Minimal model giving marking-level semantics from code and annotations.
-/

namespace Lexicon

inductive Fact where
  | capability : String → Fact
  | selfKey : String → Fact
  | datum : String → Fact
  deriving DecidableEq, Repr

abbrev Marking := Finset Fact

def RequirementExpr.Holds (marking : Marking) : RequirementExpr → Prop
  | .trivial => True
  | .capability cap => .capability cap ∈ marking
  | .datum token => .datum token ∈ marking
  | .ownershipSelf key => .selfKey key ∈ marking
  | .and lhs rhs => lhs.Holds marking ∧ rhs.Holds marking

def RequirementExpr.check (marking : Marking) : RequirementExpr → Bool
  | .trivial => true
  | .capability cap => Fact.capability cap ∈ marking
  | .datum token => Fact.datum token ∈ marking
  | .ownershipSelf key => Fact.selfKey key ∈ marking
  | .and lhs rhs => lhs.check marking && rhs.check marking

def TouchExpr.tokens : TouchExpr → Finset Fact
  | .none => ∅
  | .emitCapability cap => {Fact.capability cap}
  | .emitSelf key => {Fact.selfKey key}
  | .emitDatum token => {Fact.datum token}
  | .and lhs rhs => lhs.tokens ∪ rhs.tokens

abbrev Axiom := Canonical

def Axiom.enabled (ax : Axiom) (marking : Marking) : Prop :=
  ax.annotation.requires.Holds marking

def Axiom.enabled? (ax : Axiom) (marking : Marking) : Bool :=
  ax.annotation.requires.check marking

def Axiom.fire (ax : Axiom) (marking : Marking) : Marking :=
  marking ∪ ax.annotation.touches.tokens

theorem subset_fire (ax : Axiom) (marking : Marking) :
    marking ⊆ ax.fire marking := by
  intro fact hfact
  simp [Axiom.fire, hfact]

theorem touch_mem_fire (ax : Axiom) (marking : Marking) (token : String)
    (h : Fact.datum token ∈ ax.annotation.touches.tokens) :
    Fact.datum token ∈ ax.fire marking := by
  simp [Axiom.fire, h]

def profileAxiom : Axiom where
  code := getProfile
  refined := refine getProfile
  annotation := authSelfRead

def createSessionCode : LexiconCode where
  nsid := "com.atproto.server.createSession"
  kind := .procedure
  input := .object [("identifier", .atom .string), ("password", .atom .string)]
  output := .object [("accessJwt", .atom .string), ("did", .atom .string)]

def createSessionAxiom : Axiom where
  code := createSessionCode
  refined := refine createSessionCode
  annotation := createSession

example : profileAxiom.enabled {Fact.capability "access_jwt", Fact.selfKey "actor"} := by
  simp [profileAxiom, Axiom.enabled, RequirementExpr.Holds, authSelfRead]

example : Fact.datum "profileViewDetailed" ∈
    profileAxiom.fire {Fact.capability "access_jwt", Fact.selfKey "actor"} := by
  simp [profileAxiom, Axiom.fire, authSelfRead, TouchExpr.tokens]

example : Fact.capability "access_jwt" ∈ createSessionAxiom.fire ∅ := by
  simp [createSessionAxiom, Axiom.fire, createSession, TouchExpr.tokens]

example : Fact.selfKey "actor" ∈ createSessionAxiom.fire ∅ := by
  simp [createSessionAxiom, Axiom.fire, createSession, TouchExpr.tokens]

end Lexicon
