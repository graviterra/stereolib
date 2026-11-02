import TetraStereo.OneCenter.LocalizedRule3CoupledTopology

set_option autoImplicit false
set_option synthInstance.maxSize 1024
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-- Constructive decision for the original finite matching relation. -/
instance localizedRule3CoupledMatchingDecidable
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey)
    (matching : input.LocalizedRule3CoupledMatching) :
    Decidable (input.DeclarativeLocalizedRule3CoupledMatching keys matching) := by
  unfold DeclarativeLocalizedRule3CoupledMatching
    DeclarativeLocalizedRule3FourWayConstitutionalTie
    DeclarativeLocalizedRule3ComplementaryPairIncidence
    DeclarativeLocalizedRule3ExactPairIncidence LocalizedRule3PhysicalUnitId.LexLt
  split <;> first | infer_instance | (split <;> infer_instance)

/-- Exhaustive matching search with a constructive filter, preserving candidate order. -/
def localizedRule3CoupledPerfectMatchingsExec
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey) :
    List input.LocalizedRule3CoupledMatching :=
  (input.localizedRule3CoupledMatchingCandidates keys).filter fun matching =>
    decide (input.DeclarativeLocalizedRule3CoupledMatching keys matching)

theorem localizedRule3CoupledPerfectMatchingsExec_eq_original
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey) :
    input.localizedRule3CoupledPerfectMatchingsExec keys =
      input.localizedRule3CoupledPerfectMatchings keys := by
  unfold localizedRule3CoupledPerfectMatchingsExec localizedRule3CoupledPerfectMatchings
  congr 1
  funext matching
  simp only [decide_eq_decide]

/-- Preserve ordinary, uniquely coupled, and ambiguous outcomes exactly. -/
def localizedRule3CoupledTopologyResolutionExec?
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey) :
    Option input.LocalizedRule3CoupledTopologyResolution :=
  match input.localizedRule3CoupledPerfectMatchingsExec keys with
  | [] => some .ordinary
  | [matching] => some (.coupled matching)
  | _ => none

theorem localizedRule3CoupledTopologyResolutionExec?_eq_original
    (input : CertifiedLocalizedCIPInput)
    (keys : List input.LocalizedRerootRecursiveRule3SpatialKey) :
    input.localizedRule3CoupledTopologyResolutionExec? keys =
      input.localizedRule3CoupledTopologyResolution? keys := by
  unfold localizedRule3CoupledTopologyResolutionExec? localizedRule3CoupledTopologyResolution?
  simp only [localizedRule3CoupledPerfectMatchingsExec_eq_original]
  rfl

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
