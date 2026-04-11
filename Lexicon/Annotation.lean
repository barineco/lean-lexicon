import Lexicon.Basic

/-!
# Annotation
Minimal requirement and effect annotations beyond what the Lexicon type structure can express.
-/

namespace Lexicon

inductive RequirementExpr where
  | trivial
  | capability : String → RequirementExpr
  | datum : String → RequirementExpr
  | ownershipSelf : String → RequirementExpr
  | and : RequirementExpr → RequirementExpr → RequirementExpr
  deriving DecidableEq, Repr

inductive TouchExpr where
  | none
  | emitCapability : String → TouchExpr
  | emitSelf : String → TouchExpr
  | emitDatum : String → TouchExpr
  | and : TouchExpr → TouchExpr → TouchExpr
  deriving DecidableEq, Repr

structure Annotation where
  requires : RequirementExpr
  touches : TouchExpr
  deriving Repr

def minimal : Annotation where
  requires := .trivial
  touches := .none

def authSelfRead : Annotation where
  requires := .and (.capability "access_jwt") (.ownershipSelf "actor")
  touches := .emitDatum "profileViewDetailed"

def createSession : Annotation where
  requires := .trivial
  touches := .and (.emitCapability "access_jwt") (.emitSelf "actor")

end Lexicon
