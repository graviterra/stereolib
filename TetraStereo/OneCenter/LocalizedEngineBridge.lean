import TetraStereo.OneCenter.LocalizedCheckedPipeline

set_option autoImplicit false
namespace TetraStereo.OneCenter.LocalizedReference.EngineBridge
open CertifiedLocalizedCIPInput Certificate.Dependency

/-- Candidates from the existing graph engine. Empty later-rule contexts introduce no invented
auxiliary labels; occurrence-local correctness is established only by certificate replay. -/
def centerCandidates (input : Input) : Report :=
  input.certified.canonicalTetrahedralCenters.map fun center =>
    (center.val.val, (input.certified.tetrahedralSpatialDescriptorAt? center
      (fun _ => CIPRuleEngine.OfficialLigandRuleContext.empty)).map
        (fun descriptor => (.chiral descriptor : LocalizedAuxiliaryLabel)))

def proposedOutcome (input : Input) (candidates : Report) (target : Occurrence input) :
    Option LocalizedAuxiliaryLabel := do
  let center ← input.certified.localizedOccurrenceDescriptorCenter? target
  lookup candidates center.val.val

def proposeFrom (input : Input) (candidates : Report) (facts : Facts input) :
    List (Occurrence input) → Nodes input
  | [] => []
  | target :: rest =>
      let outcome := proposedOutcome input candidates target
      let node : Node (Occurrence input) LocalizedAuxiliaryLabel :=
        { target, outcome, references := producerReferences (dependencies input) facts target }
      node :: proposeFrom input candidates (facts ++ [(target, outcome)]) rest

def propose (input : Input) : Nodes input :=
  proposeFrom input (centerCandidates input) []
    (input.certified.localizedCertificateOrder (carrierFuel input))

/-- The full original localized evaluator checks the engine's proposals, with a certificate-bearing
reference fallback. This module establishes semantic integration, not a runtime speed bound. -/
def evaluate (input : Input) : Evaluation input :=
  LocalizedReference.evaluate input (propose input)

def analyze (input : Input) : Report := report input (evaluate input).facts

theorem analyze_eq_reference (input : Input) : analyze input = LocalizedReference.analyze input :=
  evaluation_report_eq_reference input (evaluate input)

def analyzeSource? (source : AuthoritativeChemicalInput) : Option Report :=
  LocalizedReference.analyzeSource? source propose

theorem analyzeSource?_eq_reference (source : AuthoritativeChemicalInput) :
    analyzeSource? source = (admitSource? source).map LocalizedReference.analyze :=
  LocalizedReference.analyzeSource?_eq_reference source propose

end TetraStereo.OneCenter.LocalizedReference.EngineBridge
