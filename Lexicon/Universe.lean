import Lexicon.Interpretation
import Mathlib.Data.Fintype.EquivFin

/-!
# Universe
Encode/decode RequirementExpr as Lexicon0 record values, prove non-canonicity of the encoding, and show semantics preservation.
-/

namespace Lexicon

/-! ## LexValue: values representable in a Lexicon0 record field -/

inductive LexValue where
  | str : String → LexValue
  | num : Int → LexValue
  | bool : Bool → LexValue
  | arr : List LexValue → LexValue
  | obj : List (String × LexValue) → LexValue
  | null : LexValue
  deriving Repr

/-! ## Primary encoding: op/value/args scheme -/

def encodeRequirement : RequirementExpr → LexValue
  | .trivial => .obj [("op", .str "trivial")]
  | .capability s => .obj [("op", .str "capability"), ("value", .str s)]
  | .datum s => .obj [("op", .str "datum"), ("value", .str s)]
  | .ownershipSelf s => .obj [("op", .str "ownershipSelf"), ("value", .str s)]
  | .and l r => .obj [("op", .str "and"),
      ("args", .arr [encodeRequirement l, encodeRequirement r])]

def decodeRequirement : LexValue → Option RequirementExpr
  | .obj [("op", .str "trivial")] => some .trivial
  | .obj [("op", .str "capability"), ("value", .str s)] => some (.capability s)
  | .obj [("op", .str "datum"), ("value", .str s)] => some (.datum s)
  | .obj [("op", .str "ownershipSelf"), ("value", .str s)] => some (.ownershipSelf s)
  | .obj [("op", .str "and"), ("args", .arr [l, r])] => do
      let l' ← decodeRequirement l
      let r' ← decodeRequirement r
      some (.and l' r')
  | _ => none

theorem decode_encode_requirement (r : RequirementExpr) :
    decodeRequirement (encodeRequirement r) = some r := by
  induction r with
  | trivial => rfl
  | capability _ => rfl
  | datum _ => rfl
  | ownershipSelf _ => rfl
  | and _ _ ihl ihr => simp [encodeRequirement, decodeRequirement, ihl, ihr]

/-! ## Alternative encoding: type/content/left/right scheme -/

def encodeRequirementAlt : RequirementExpr → LexValue
  | .trivial => .obj [("type", .str "trivial")]
  | .capability s => .obj [("type", .str "capability"), ("content", .str s)]
  | .datum s => .obj [("type", .str "datum"), ("content", .str s)]
  | .ownershipSelf s => .obj [("type", .str "ownershipSelf"), ("content", .str s)]
  | .and l r => .obj [("type", .str "and"),
      ("left", encodeRequirementAlt l), ("right", encodeRequirementAlt r)]

def decodeRequirementAlt : LexValue → Option RequirementExpr
  | .obj [("type", .str "trivial")] => some .trivial
  | .obj [("type", .str "capability"), ("content", .str s)] => some (.capability s)
  | .obj [("type", .str "datum"), ("content", .str s)] => some (.datum s)
  | .obj [("type", .str "ownershipSelf"), ("content", .str s)] => some (.ownershipSelf s)
  | .obj [("type", .str "and"), ("left", l), ("right", r)] => do
      let l' ← decodeRequirementAlt l
      let r' ← decodeRequirementAlt r
      some (.and l' r')
  | _ => none

theorem decode_encode_requirement_alt (r : RequirementExpr) :
    decodeRequirementAlt (encodeRequirementAlt r) = some r := by
  induction r with
  | trivial => rfl
  | capability _ => rfl
  | datum _ => rfl
  | ownershipSelf _ => rfl
  | and _ _ ihl ihr => simp [encodeRequirementAlt, decodeRequirementAlt, ihl, ihr]

/-! ## Non-canonicity: different encodings for the same RequirementExpr -/

/-- Extract the leading field name of an encoding. -/
def LexValue.headTag : LexValue → Option String
  | .obj ((tag, _) :: _) => some tag
  | _ => none

theorem encode_headTag (r : RequirementExpr) :
    (encodeRequirement r).headTag = some "op" := by
  cases r <;> rfl

theorem encodeAlt_headTag (r : RequirementExpr) :
    (encodeRequirementAlt r).headTag = some "type" := by
  cases r <;> rfl

/-- The two encodings produce different LexValues for the same RequirementExpr (head field "op" vs "type"). -/
theorem encoding_noncanonical (r : RequirementExpr) :
    encodeRequirement r ≠ encodeRequirementAlt r := by
  intro h
  have h1 := encode_headTag r
  have h2 := encodeAlt_headTag r
  rw [h] at h1
  rw [h1] at h2
  exact absurd h2 (by decide)

/-! ## Semantics preservation
Interpreting the encoded LexValue directly yields the same result as RequirementExpr.check.
-/

def checkEncodedRequirement (marking : Marking) : LexValue → Bool
  | .obj [("op", .str "trivial")] => true
  | .obj [("op", .str "capability"), ("value", .str cap)] =>
      Fact.capability cap ∈ marking
  | .obj [("op", .str "datum"), ("value", .str token)] =>
      Fact.datum token ∈ marking
  | .obj [("op", .str "ownershipSelf"), ("value", .str key)] =>
      Fact.selfKey key ∈ marking
  | .obj [("op", .str "and"), ("args", .arr [l, r])] =>
      checkEncodedRequirement marking l && checkEncodedRequirement marking r
  | _ => false

theorem semantics_preserved (marking : Marking) (r : RequirementExpr) :
    r.check marking = checkEncodedRequirement marking (encodeRequirement r) := by
  induction r with
  | trivial => rfl
  | capability _ => simp [RequirementExpr.check, encodeRequirement, checkEncodedRequirement]
  | datum _ => simp [RequirementExpr.check, encodeRequirement, checkEncodedRequirement]
  | ownershipSelf _ => simp [RequirementExpr.check, encodeRequirement, checkEncodedRequirement]
  | and _ _ ihl ihr =>
      simp [RequirementExpr.check, encodeRequirement, checkEncodedRequirement, ← ihl, ← ihr]

/-! ## Corollary: check is preserved after roundtrip -/

theorem roundtrip_check (marking : Marking) (r : RequirementExpr)
    (r' : RequirementExpr) (h : decodeRequirement (encodeRequirement r) = some r') :
    r'.check marking = checkEncodedRequirement marking (encodeRequirement r) := by
  have := decode_encode_requirement r
  rw [this] at h
  injection h with h'
  subst h'
  exact semantics_preserved marking r

/-! ## Expressiveness limits of Lexicon0: format constraints and finiteness
RequirementExpr is infinite (via recursive .and) so no injection into finite format-constrained flat records exists.
-/

/-- and-chain: left-leaning binary tree of depth n, forming an injection Nat -> RequirementExpr. -/
def andChain : Nat → RequirementExpr
  | 0 => .trivial
  | n + 1 => .and (andChain n) .trivial

/-- andChain is injective: different depths produce different RequirementExprs. -/
theorem andChain_injective : Function.Injective andChain := by
  intro m n h
  induction m generalizing n with
  | zero =>
    cases n with
    | zero => rfl
    | succ _ => simp [andChain] at h
  | succ m ih =>
    cases n with
    | zero => simp [andChain] at h
    | succ n =>
      simp only [andChain, RequirementExpr.and.injEq] at h
      exact congrArg Nat.succ (ih h.1)

/-- RequirementExpr is infinite: an injection from Nat (andChain) exists, so no finite type can contain it. -/
instance : Infinite RequirementExpr := by
  rw [← not_finite_iff_infinite]
  intro hfin
  have : Finite Nat := Finite.of_injective andChain andChain_injective
  exact not_finite Nat

/-- No injection from RequirementExpr into a finite type exists; recursive LexValue structure (arr/obj) is required. -/
theorem no_injection_to_finite (α : Type*) [Finite α] :
    ¬ ∃ f : RequirementExpr → α, Function.Injective f := by
  intro ⟨f, hf⟩
  have : Finite RequirementExpr := Finite.of_injective f hf
  exact not_finite RequirementExpr

/-! ## Valid encoding classification
Define encoding validity via roundtrip and show that distinct valid encodings are non-equivalent.
-/

/-- A valid encoding: an encode/decode pair satisfying the roundtrip property. -/
structure ValidEncoding where
  encode : RequirementExpr → LexValue
  decode : LexValue → Option RequirementExpr
  roundtrip : ∀ r, decode (encode r) = some r

/-- Primary encoding (op/value/args) is a ValidEncoding. -/
def primaryEncoding : ValidEncoding where
  encode := encodeRequirement
  decode := decodeRequirement
  roundtrip := decode_encode_requirement

/-- Alternative encoding (type/content/left/right) is a ValidEncoding. -/
def altEncoding : ValidEncoding where
  encode := encodeRequirementAlt
  decode := decodeRequirementAlt
  roundtrip := decode_encode_requirement_alt

/-- Two ValidEncodings are equivalent if they produce the same LexValue for every input. -/
def ValidEncoding.equivalent (e1 e2 : ValidEncoding) : Prop :=
  ∀ r, e1.encode r = e2.encode r

/-- Primary and Alt are non-equivalent; encoding choice cannot be determined within Lexicon0 alone. -/
theorem primary_alt_not_equivalent :
    ¬ primaryEncoding.equivalent altEncoding :=
  fun h => absurd (h .trivial) (encoding_noncanonical .trivial)

/-! ## Phase 3: ValidEncoding1 (semantics-preserving encoding)
Extends ValidEncoding with a semantics preservation condition: interpreting the encoded LexValue must agree with the original check.
-/

/-- Semantics-preserving encoding: roundtrip plus a direct interpretation function agreeing with check. -/
structure ValidEncoding₁ extends ValidEncoding where
  checkEncoded : Marking → LexValue → Bool
  semantics : ∀ marking r,
    r.check marking = checkEncoded marking (toValidEncoding.encode r)

/-- Primary encoding lifts to ValidEncoding1 via checkEncodedRequirement and semantics_preserved. -/
def primaryEncoding₁ : ValidEncoding₁ where
  encode := encodeRequirement
  decode := decodeRequirement
  roundtrip := decode_encode_requirement
  checkEncoded := checkEncodedRequirement
  semantics := semantics_preserved

/-! ### Alt encoding semantics preservation -/

/-- Direct interpretation function for the alt encoding. -/
def checkEncodedRequirementAlt (marking : Marking) : LexValue → Bool
  | .obj [("type", .str "trivial")] => true
  | .obj [("type", .str "capability"), ("content", .str cap)] =>
      Fact.capability cap ∈ marking
  | .obj [("type", .str "datum"), ("content", .str token)] =>
      Fact.datum token ∈ marking
  | .obj [("type", .str "ownershipSelf"), ("content", .str key)] =>
      Fact.selfKey key ∈ marking
  | .obj [("type", .str "and"), ("left", l), ("right", r)] =>
      checkEncodedRequirementAlt marking l && checkEncodedRequirementAlt marking r
  | _ => false

theorem semantics_preserved_alt (marking : Marking) (r : RequirementExpr) :
    r.check marking = checkEncodedRequirementAlt marking (encodeRequirementAlt r) := by
  induction r with
  | trivial => rfl
  | capability _ => simp [RequirementExpr.check, encodeRequirementAlt, checkEncodedRequirementAlt]
  | datum _ => simp [RequirementExpr.check, encodeRequirementAlt, checkEncodedRequirementAlt]
  | ownershipSelf _ => simp [RequirementExpr.check, encodeRequirementAlt, checkEncodedRequirementAlt]
  | and _ _ ihl ihr =>
      simp [RequirementExpr.check, encodeRequirementAlt, checkEncodedRequirementAlt, ← ihl, ← ihr]

/-- Alt encoding lifts to ValidEncoding1. -/
def altEncoding₁ : ValidEncoding₁ where
  encode := encodeRequirementAlt
  decode := decodeRequirementAlt
  roundtrip := decode_encode_requirement_alt
  checkEncoded := checkEncodedRequirementAlt
  semantics := semantics_preserved_alt

/-- ValidEncoding1-level equivalence: encode functions agree. -/
def ValidEncoding₁.equivalent (e1 e2 : ValidEncoding₁) : Prop :=
  ∀ r, e1.encode r = e2.encode r

/-- Primary and alt remain non-equivalent even at ValidEncoding1 level. -/
theorem primary_alt_encoding₁_not_equivalent :
    ¬ primaryEncoding₁.equivalent altEncoding₁ :=
  fun h => absurd (h .trivial) (encoding_noncanonical .trivial)

end Lexicon
