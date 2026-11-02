import TetraStereo.OneCenter.LocalizedDescriptorBearingRule3Executable
import TetraStereo.OneCenter.LocalizedNoDoubleDescriptorExecutable

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-! Full executable descriptor refinement. The reused four-ligand and tracked-order helpers have
unconditional equalities; no no-double-bond hypothesis is imposed by this module. -/

def localizedDescriptorKeyFrameExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    Option (input.LocalizedOccurrenceRule3Through5KeyFrame carrierFuel) := do
  let descriptorFuel := localizedDescriptorBearingRule3EvaluationFuel carrierFuel
  let rule45Fuel := localizedOccurrenceRerootEvaluationFuel carrierFuel
  let rule3Frame ← input.buildLocalizedDescriptorBearingRule3FrameExec?
    target view descriptorFuel base.cursors
  if rule3Length : rule3Frame.keys.length = 4 then
    let rule45Keys ← base.cursors.mapM
      (input.buildLocalizedRerootCompoundRule45KeyExec? target view rule45Fuel)
    if rule45Length : rule45Keys.length = 4 then
      some
        { rule3Frame
          rule3Length
          rule45Keys
          rule45Length }
    else none
  else none

def localizedDescriptorSpatialEvidenceExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    Option (input.LocalizedOccurrenceRule3Through5SpatialEvidence carrierFuel) := do
  let center ← input.localizedOccurrenceDescriptorCenter? target
  let base ← input.localizedNoDoubleFourLigandFrameExec? target
  let keys ← input.localizedDescriptorKeyFrameExec?
    target view base
  let tracked ← input.localizedNoDoubleTrackedOrderExec? keys
  let points ← tracked.highestFirst.mapM fun index =>
    input.localizedRerootCursorSpatialPoint? (base.cursorAt index)
  some { center, base, keys, tracked, points }

def localizedDescriptorExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    Option LocalizedAuxiliaryLabel := do
  let evidence ← input.localizedDescriptorSpatialEvidenceExec?
    target view
  let raw ← descriptorOfPriorityOrderedPoints? evidence.points
  some (classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons)

theorem localizedDescriptorKeyFrameExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    input.localizedDescriptorKeyFrameExec? target view base =
      input.buildLocalizedOccurrenceDescriptorBearingRule3Through5KeyFrame? target view base := by
  have rule45Eq := funext fun cursor =>
    (input.buildLocalizedRerootCompoundRule45Key?_eq_buildLocalizedRerootCompoundRule45KeyExec?
      target view (localizedOccurrenceRerootEvaluationFuel carrierFuel) cursor).symm
  simp only [localizedDescriptorKeyFrameExec?,
    buildLocalizedOccurrenceDescriptorBearingRule3Through5KeyFrame?,
    buildLocalizedDescriptorBearingRule3FrameExec?_eq_original, rule45Eq]

theorem localizedDescriptorSpatialEvidenceExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    input.localizedDescriptorSpatialEvidenceExec? target view =
      input.localizedOccurrenceDescriptorBearingRule3Through5SpatialEvidence? target view := by
  simp only [localizedDescriptorSpatialEvidenceExec?,
    localizedOccurrenceDescriptorBearingRule3Through5SpatialEvidence?,
    localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?,
    localizedNoDoubleTrackedOrderExec?_eq_safeLocalizedOccurrenceRule3Through5TrackedOrder?,
    localizedDescriptorKeyFrameExec?_eq_original]

/-- Exact equality to the existing full evaluator, for every certified localized input and view. -/
theorem localizedDescriptorExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    input.localizedDescriptorExec? target view =
      input.localizedOccurrenceDescriptorBearingRule3Through5Descriptor? target view := by
  simp only [localizedDescriptorExec?,
    localizedOccurrenceDescriptorBearingRule3Through5Descriptor?,
    localizedDescriptorSpatialEvidenceExec?_eq_original]

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
