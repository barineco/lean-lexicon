import Lexicon.Generated.Vendored
import Lexicon.Refinement

/-!
# VendoredDemo
Minimal example connecting the generated vendored module to `refine` as input.
-/

namespace Lexicon

def vendoredCount : Nat :=
  Lexicon.Generated.vendoredCodes.length

example : vendoredCount > 0 := by
  decide

example :
    (refine Lexicon.Generated.app_bsky_feed_getTimeline).terminality = .list := by
  decide

example :
    (refine Lexicon.Generated.com_atproto_server_createSession).terminality = .point := by
  decide

example :
    (refine Lexicon.Generated.com_atproto_sync_subscribeRepos).terminality = .stream := by
  decide

end Lexicon
