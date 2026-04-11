import Lexicon.Basic

/-!
# Refinement
Machine-derivable properties from the Lexicon type structure.
-/

namespace Lexicon

structure Refined where
  terminality : Terminality
  deriving Repr

def refine (code : LexiconCode) : Refined where
  terminality := inferTerminality code.kind code.output

example : (refine timeline).terminality = .list := by
  decide

example : (refine getProfile).terminality = .point := by
  decide

end Lexicon
