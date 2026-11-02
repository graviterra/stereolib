import TetraStereo.OneCenter.LocalizedNoDoubleCachedPublicPipeline

set_option autoImplicit false
namespace TetraStereo.OneCenter.LocalizedNoDoubleReference.EngineBridge
open CertifiedLocalizedCIPInput Certificate.Dependency

/-- Existing constitutional engine candidates, computed once per physical center. Empty later-rule
contexts mean that this proposer does not manufacture auxiliary stereochemical evidence.
`tetrahedralSpatialDescriptorAt?` calls `ligandOrderAt?`, whose comparisons use
`CIPRuleEngine.compareDigraphThenOfficialCertificate`. -/
def centerCandidates (input : Input) : List (Nat × Option LocalizedAuxiliaryLabel) :=
  input.certified.canonicalTetrahedralCenters.map fun center =>
    (center.val.val, (input.certified.tetrahedralSpatialDescriptorAt? center
      (fun _ => CIPRuleEngine.OfficialLigandRuleContext.empty)).map (fun descriptor => (.chiral descriptor : LocalizedAuxiliaryLabel)))

/-- Atom-centered answers are only proposals for occurrence-local evaluation. Duplicate provenance
is rejected by the existing real-center recognizer. The checker handles reroot and dependency differences. -/
def proposedOutcome (input : Input) (candidates : List (Nat × Option LocalizedAuxiliaryLabel))
    (target : input.certified.LocalizedCIPOccurrence (carrierFuel input)) :
    Option LocalizedAuxiliaryLabel := do
  let center ← input.certified.localizedOccurrenceDescriptorCenter? target
  lookup candidates center.val.val

/-- Attach exact dependency reference indices to the engine's proposed outcomes. This producer makes
no claim that those outcomes satisfy the localized evaluator; acceptance remains the checker's job. -/
def proposeFrom (input : Input) (candidates : List (Nat × Option LocalizedAuxiliaryLabel))
    (dependencies : input.certified.LocalizedCIPOccurrence (carrierFuel input) →
      List (input.certified.LocalizedCIPOccurrence (carrierFuel input)))
    (facts : List (Fact (input.certified.LocalizedCIPOccurrence (carrierFuel input))
      LocalizedAuxiliaryLabel)) :
    List (input.certified.LocalizedCIPOccurrence (carrierFuel input)) → Public.Proposals input
  | [] => []
  | target :: rest =>
      let outcome := proposedOutcome input candidates target
      let node : Node (input.certified.LocalizedCIPOccurrence (carrierFuel input))
          LocalizedAuxiliaryLabel :=
        { target, outcome, references := producerReferences dependencies facts target }
      node :: proposeFrom input candidates dependencies (facts ++ [(target, outcome)]) rest


def propose (input : Input) : Public.Proposals input :=
  let candidates := centerCandidates input
  let cache := LocalizedNoDoubleCachedEvaluation.buildRuntimeCache input
  let dependencies := LocalizedNoDoubleCachedEvaluation.dependenciesUsingCache input cache
  proposeFrom input candidates dependencies []
    (input.certified.localizedCertificateOrder (carrierFuel input))



def analyze (input : Input) : Public.Report :=
  CachedPublic.analyzeWithProposals input (propose input)

/-- End-to-end exactness holds even when the constitutional engine cannot resolve auxiliary labels. -/
theorem analyze_eq_reference (input : Input) :
    analyze input = LocalizedNoDoubleReference.analyze input :=
  CachedPublic.analyzeWithProposals_eq_reference input (propose input)

def analyzeSource? (source : AuthoritativeChemicalInput) : Option Public.Report :=
  CachedPublic.analyzeSource? source propose

theorem analyzeSource?_eq_reference (source : AuthoritativeChemicalInput) :
    analyzeSource? source = (admitSource? source).map LocalizedNoDoubleReference.analyze :=
  CachedPublic.analyzeSource?_eq_reference source propose

def analyzeSmilesSpatial? (text : String) (spatial : SpatialConfiguration)
    (cycles : List AromaticCycle := []) : Except ParserError (Option Public.Report) :=
  CachedPublic.analyzeSmilesSpatial? text spatial cycles propose

theorem analyzeSmilesSpatial?_eq_reference (text : String) (spatial : SpatialConfiguration)
    (cycles : List AromaticCycle) :
    analyzeSmilesSpatial? text spatial cycles =
      (admitSmilesSpatial? text spatial cycles).map (Option.map LocalizedNoDoubleReference.analyze) :=
  CachedPublic.analyzeSmilesSpatial?_eq_reference text spatial cycles propose

end TetraStereo.OneCenter.LocalizedNoDoubleReference.EngineBridge
