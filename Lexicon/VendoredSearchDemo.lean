import Lexicon.Materialize
import Lexicon.Search

/-!
# VendoredSearchDemo
Minimal example connecting generated vendored code and user-authored annotation table to `searchAll` while keeping them separate.
-/

namespace Lexicon

def selectedVendoredCodes : List LexiconCode :=
  Lexicon.Generated.vendoredCodes.filter fun code => code.nsid ∈ demoNsids

def selectedVendoredAxioms : List Axiom :=
  materializeAll selectedVendoredCodes demoAnnotationTable

def profileSearchFromVendored : List (List String) :=
  searchAll 2 vendoredDemoAxioms ∅ [Fact.datum "profileViewDetailed"]

def timelineSearchFromVendored : List (List String) :=
  searchAll 2 vendoredDemoAxioms ∅ [Fact.datum "feedViewPost[]"]

def profileSearchFromSelectedVendored : List (List String) :=
  searchAll 2 selectedVendoredAxioms ∅ [Fact.datum "profileViewDetailed"]

def timelineSearchFromSelectedVendored : List (List String) :=
  searchAll 2 selectedVendoredAxioms ∅ [Fact.datum "feedViewPost[]"]

end Lexicon
