import TetraStereo.OneCenter.LocalizedNoDoubleCheckedEvaluation

set_option autoImplicit false
namespace TetraStereo.OneCenter.LocalizedNoDoubleReference.Public
open CertifiedLocalizedCIPInput Certificate.Dependency

/-- One entry for every canonical tetrahedral candidate, retaining unresolved outcomes. -/
abbrev Report := List (Nat × Option LocalizedAuxiliaryLabel)

/-- Proposed nodes are indexed by the exact checked input they describe. Serialized proposals need
an additional decoder; this interface does not reinterpret untrusted atom indices as occurrences. -/
abbrev Proposals (input : Input) :=
  List (Node (input.certified.LocalizedCIPOccurrence (carrierFuel input)) LocalizedAuxiliaryLabel)

/-- A runtime can propose a certificate using any strategy. Its output is always checked. -/
abbrev Proposer := (input : Input) → Proposals input

/-- Bind checked facts once, then report every canonical center. Rejected proposals trigger the
proved reference fallback in `evaluateCheckedOrReference`. -/
def analyzeWithProposals (input : Input) (nodes : Proposals input) : Report :=
  let facts := evaluateCheckedOrReference input nodes
  input.certified.canonicalTetrahedralCenters.map fun center =>
    (center.val.val, lookup facts
      (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center))

/-- Any proposed certificate, accepted or rejected, gives exactly the reference report. -/
theorem analyzeWithProposals_eq_analyze (input : Input) (nodes : Proposals input) :
    analyzeWithProposals input nodes = analyze input := by
  dsimp only [analyzeWithProposals, analyze]
  rw [lookup_evaluateCheckedOrReference_eq_evaluatedState input nodes]
  rfl

/-- Source input to descriptors with automatic certificate production by default. No molecule-specific
proof is supplied by the caller. This domain excludes order-two localized source records. -/
def analyzeSource? (source : AuthoritativeChemicalInput)
    (propose : Proposer := localizedCheckedNodes) : Option Report := do
  let input ← admitSource? source
  pure (analyzeWithProposals input (propose input))

/-- The proposer cannot affect the source-level report. -/
theorem analyzeSource?_eq_reference (source : AuthoritativeChemicalInput) (propose : Proposer) :
    analyzeSource? source propose = (admitSource? source).map analyze := by
  unfold analyzeSource?
  cases observed : admitSource? source with
  | none => rfl
  | some input => simp only [analyzeWithProposals_eq_analyze]; rfl

/-- OpenSMILES plus exact coordinates indexed by the hydrogen-expanded atom list, through the same
checked admission as the reference pipeline. Parse errors and admission rejection are preserved. -/
def analyzeSmilesSpatial? (text : String) (spatial : SpatialConfiguration)
    (cycles : List AromaticCycle := []) (propose : Proposer := localizedCheckedNodes) :
    Except ParserError (Option Report) :=
  (admitSmilesSpatial? text spatial cycles).map fun admitted =>
    admitted.map fun input => analyzeWithProposals input (propose input)


theorem analyzeSmilesSpatial?_eq_reference (text : String) (spatial : SpatialConfiguration)
    (cycles : List AromaticCycle) (propose : Proposer) :
    analyzeSmilesSpatial? text spatial cycles propose =
      (admitSmilesSpatial? text spatial cycles).map (Option.map analyze) := by
  unfold analyzeSmilesSpatial?
  simp only [analyzeWithProposals_eq_analyze]

end TetraStereo.OneCenter.LocalizedNoDoubleReference.Public
