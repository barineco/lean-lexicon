import Mathlib.Data.List.Basic

/-!
# Basic
Minimal structures for the code-level representation of Lexicon endpoints.
-/

namespace Lexicon

inductive EndpointKind where
  | query
  | procedure
  | subscription
  deriving DecidableEq, Repr

inductive Atom where
  | bool
  | integer
  | string
  | token
  deriving DecidableEq, Repr

inductive TypeExpr where
  | atom : Atom → TypeExpr
  | array : TypeExpr → TypeExpr
  | object : List (String × TypeExpr) → TypeExpr
  | union : List (String × TypeExpr) → TypeExpr     -- tagged union (oneOf)
  | optional : TypeExpr → TypeExpr                   -- required=#false
  | enum : List String → TypeExpr                    -- known-values
  | format : String → TypeExpr → TypeExpr            -- format=did etc.
  deriving Repr

/-! ### TypeExpr operations
Field-level operations on object types, enabling structural type tracking through TypedTransition composition.
-/

/-- Project a field from an object type; returns none if not found. -/
def TypeExpr.project : TypeExpr → String → Option TypeExpr
  | .object fields, name => fields.lookup name
  | _, _ => none

/-- Add a field to an object type; does not overwrite existing fields. -/
def TypeExpr.extend : TypeExpr → String → TypeExpr → TypeExpr
  | .object fields, name, ty =>
      if fields.any (fun f => f.1 == name)
      then .object fields
      else .object (fields ++ [(name, ty)])
  | other, _, _ => other

/-- Merge two object types; the right-hand side takes precedence. -/
def TypeExpr.merge : TypeExpr → TypeExpr → TypeExpr
  | .object fields1, .object fields2 => .object (fields1 ++ fields2)
  | _, other => other

/-- Transform the element type of an array (type-level map). -/
def TypeExpr.mapArray (f : TypeExpr → TypeExpr) : TypeExpr → TypeExpr
  | .array elem => .array (f elem)
  | other => other

/-- List all field names of an object type. -/
def TypeExpr.fieldNames : TypeExpr → List String
  | .object fields => fields.map Prod.fst
  | _ => []

/-! ### Union (sum) type operations
Union discriminant branches (5 found in PDS/BGS during H7 verification) expressed at the type level.
-/

/-- List all variant names of a union type. -/
def TypeExpr.variants : TypeExpr → List String
  | .union cases => cases.map Prod.fst
  | _ => []

/-- Look up a variant's type in a union by name. -/
def TypeExpr.variant : TypeExpr → String → Option TypeExpr
  | .union cases, name => cases.lookup name
  | _, _ => none

/-- Add a variant to a union type. -/
def TypeExpr.addVariant : TypeExpr → String → TypeExpr → TypeExpr
  | .union cases, name, ty => .union (cases ++ [(name, ty)])
  | other, _, _ => other

/-- Type-level dispatch: select a type by union variant name (H7 "branching is type projection"). -/
def TypeExpr.dispatch : TypeExpr → String → Option TypeExpr
  | .union cases, tag => cases.lookup tag
  | _, _ => none

/-! ### Properties of TypeExpr operations -/

/-! ### Examples: verifying TypeExpr operations -/

/-- Example: field projection. -/
example : (TypeExpr.object [("handle", .atom .string), ("did", .atom .string)]).project "handle"
    = some (.atom .string) := by rfl

/-- Example: field extension. -/
example : (TypeExpr.object [("a", .atom .string)]).extend "b" (.atom .integer)
    = .object [("a", .atom .string), ("b", .atom .integer)] := by rfl

/-- Example: type merging. -/
example : (TypeExpr.object [("a", .atom .string)]).merge (.object [("b", .atom .integer)])
    = .object [("a", .atom .string), ("b", .atom .integer)] := by rfl

/-- Example: array map. -/
example : (TypeExpr.array (.atom .string)).mapArray (fun _ => .atom .integer)
    = .array (.atom .integer) := by rfl

/-- Example union type: ApplyWriteAction (discriminant branch found in PDS during H7). -/
def applyWriteAction : TypeExpr :=
  .union [("create", .object [("collection", .atom .string), ("rkey", .atom .string),
                               ("record", .atom .token)]),
          ("update", .object [("collection", .atom .string), ("rkey", .atom .string),
                               ("record", .atom .token)]),
          ("delete", .object [("collection", .atom .string), ("rkey", .atom .string)])]

/-- Dispatch: retrieve the type for the "create" variant. -/
example : applyWriteAction.dispatch "create" =
    some (.object [("collection", .atom .string), ("rkey", .atom .string),
                   ("record", .atom .token)]) := by rfl

/-- Dispatch: the "delete" variant has no record field. -/
example : applyWriteAction.dispatch "delete" =
    some (.object [("collection", .atom .string), ("rkey", .atom .string)]) := by rfl

/-- Variants: list of variant names. -/
example : applyWriteAction.variants = ["create", "update", "delete"] := by rfl

/-! ### Examples: optional / enum / format
Fully representing Lexicon type constraints with TypeExpr.
-/

/-- Output type for createSession, including optional fields. -/
def createSessionOutput : TypeExpr :=
  .object [
    ("accessJwt", .atom .string),
    ("refreshJwt", .atom .string),
    ("handle", .format "handle" (.atom .string)),
    ("did", .format "did" (.atom .string)),
    ("email", .optional (.atom .string)),
    ("emailConfirmed", .optional (.atom .bool)),
    ("active", .optional (.atom .bool)),
    ("status", .optional (.enum ["takendown", "suspended", "deactivated"]))
  ]

/-- Projection of an optional field: email is optional string. -/
example : createSessionOutput.project "email" =
    some (.optional (.atom .string)) := by rfl

/-- Projection of a required field: did is a format=did string. -/
example : createSessionOutput.project "did" =
    some (.format "did" (.atom .string)) := by rfl

/-- Projection of an enum field: status is an optional enum. -/
example : createSessionOutput.project "status" =
    some (.optional (.enum ["takendown", "suspended", "deactivated"])) := by rfl

/-- Union type for identifier (H7 Lex0 complement): Did | Handle. -/
def identifierType : TypeExpr :=
  .union [("did", .format "did" (.atom .string)),
          ("handle", .format "handle" (.atom .string))]

/-- Dispatch to retrieve the Did variant type. -/
example : identifierType.dispatch "did" =
    some (.format "did" (.atom .string)) := by rfl

def TypeExpr.hasArrayField : TypeExpr → Bool
  | .atom _ => false
  | .array _ => true
  | .optional inner => inner.hasArrayField
  | .enum _ => false
  | .format _ inner => inner.hasArrayField
  | .object fields | .union fields =>
      fields.any (fun field =>
        match field.snd with
        | .array _ => true
        | _ => false)

inductive Terminality where
  | point
  | list
  | stream
  deriving DecidableEq, Repr

def inferTerminality (kind : EndpointKind) (output : TypeExpr) : Terminality :=
  match kind with
  | .subscription => .stream
  | _ => if output.hasArrayField then .list else .point

structure LexiconCode where
  nsid : String
  kind : EndpointKind
  input : TypeExpr
  output : TypeExpr
  deriving Repr

def timeline : LexiconCode where
  nsid := "app.bsky.feed.getTimeline"
  kind := .query
  input := .object [("limit", .atom .integer)]
  output := .object [("feed", .array (.atom .token))]

def getProfile : LexiconCode where
  nsid := "app.bsky.actor.getProfile"
  kind := .query
  input := .object [("actor", .atom .string)]
  output := .object [("handle", .atom .string)]

example : inferTerminality timeline.kind timeline.output = .list := by
  decide

example : inferTerminality getProfile.kind getProfile.output = .point := by
  decide

end Lexicon
