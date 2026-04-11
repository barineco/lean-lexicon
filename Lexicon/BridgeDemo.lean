import Lexicon.Bridge

/-!
# BridgeDemo
Demo helpers for loading and summarizing bridge artifact compatibility reports.
-/

namespace Lexicon

def bridgeArtifactPath : System.FilePath :=
  "tmp" / "bridge-artifact.json"

def loadBridgeCases : IO (Except String BridgeArtifact) :=
  loadBridgeArtifact bridgeArtifactPath

noncomputable def loadBridgeReports :
    IO (Except String (List BridgeArtifactEntryReport)) :=
  loadBridgeArtifactReports bridgeArtifactPath

def bridgeCompatibilitySummary
    (reports : List BridgeArtifactEntryReport) :
    List (String × BridgeCompatibility) :=
  reports.map fun entry => (entry.imported.goalId, entry.report.compatibility)

noncomputable def bridgeCompatibilityReport :
    IO (Except String (List (String × BridgeCompatibility))) := do
  match ← loadBridgeReports with
  | .error err => pure (.error err)
  | .ok reports => pure (.ok (bridgeCompatibilitySummary reports))

end Lexicon
