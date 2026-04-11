import Lexicon.Annotation
import Lexicon.Refinement

/-!
# Canonical
Canonical layer combining machine-derived refinements with user-authored annotations.
-/

namespace Lexicon

structure AnnotationDelta where
  requires? : Option RequirementExpr := none
  touches? : Option TouchExpr := none
  deriving Repr

def Annotation.overlay (base : Annotation) (delta : AnnotationDelta) : Annotation where
  requires := delta.requires?.getD base.requires
  touches := delta.touches?.getD base.touches

structure Canonical where
  code : LexiconCode
  refined : Refined
  annotation : Annotation
  deriving Repr

def buildCanonical
    (code : LexiconCode)
    (base : Annotation)
    (delta : AnnotationDelta) : Canonical where
  code := code
  refined := refine code
  annotation := base.overlay delta

def profileDelta : AnnotationDelta where
  touches? := some (.emitDatum "profileViewDetailed")

def canonicalProfile : Canonical :=
  buildCanonical getProfile minimal profileDelta

example : canonicalProfile.refined.terminality = .point := by
  decide

example : canonicalProfile.annotation.requires = .trivial := by
  decide

example : canonicalProfile.annotation.touches = .emitDatum "profileViewDetailed" := by
  decide

end Lexicon
