import Lexicon.AnnotationTable
import Lexicon.Generated.Vendored
import Lexicon.Interpretation

/-!
# Materialize
Auto-generate `Axiom` values from generated code and the user-authored annotation table.
-/

namespace Lexicon

def annotate (code : LexiconCode) (annotation : Annotation) : Axiom where
  code := code
  refined := refine code
  annotation := annotation

def findCodeByNsid (nsid : String) (codes : List LexiconCode) : Option LexiconCode :=
  codes.find? (fun code => code.nsid = nsid)

def materializeEntry
    (codes : List LexiconCode)
    (entry : String × Annotation) : Option Axiom := do
  let code <- findCodeByNsid entry.fst codes
  pure (annotate code entry.snd)

def materializeAll
    (codes : List LexiconCode)
    (entries : List (String × Annotation)) : List Axiom :=
  entries.filterMap (materializeEntry codes)

def vendoredDemoAxioms : List Axiom :=
  materializeAll Lexicon.Generated.vendoredCodes demoAnnotationTable

example : vendoredDemoAxioms.length = 15 := by
  decide

end Lexicon
