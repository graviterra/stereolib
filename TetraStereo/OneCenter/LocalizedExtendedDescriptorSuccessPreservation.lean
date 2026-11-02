import TetraStereo.OneCenter.LocalizedExtendedRecursiveRule3Preservation
import TetraStereo.OneCenter.LocalizedExtendedShortCircuitDescriptor

set_option autoImplicit false
namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

/-- Every original successful four-ligand key frame survives unchanged, including all Rule45
keys, length evidence, Rule3 observations, topology and exclusions. -/
theorem extendedShortCircuitKeyFrame_preserves_originalExec
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    OptionSuccessRefines
      (input.localizedDescriptorKeyFrameExec? target view base)
      (input.buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame? target view base) := by
  unfold localizedDescriptorKeyFrameExec? buildLocalizedOccurrenceExtendedShortCircuitRule3Through5KeyFrame?
  apply OptionSuccessRefines.bind
    (input.extendedShortCircuitRule3Frame_preserves_originalExec target view _ base.cursors)
  intro frame
  exact .refl _

/-- Ranked geometry evidence survives in full at a fixed dependency view. -/
theorem extendedShortCircuitSpatialEvidence_preserves_originalExec
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    OptionSuccessRefines
      (input.localizedDescriptorSpatialEvidenceExec? target view)
      (input.localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence? target view) := by
  unfold localizedDescriptorSpatialEvidenceExec? localizedOccurrenceExtendedShortCircuitRule3Through5SpatialEvidence?
  apply OptionSuccessRefines.bind (.refl _)
  intro center
  apply OptionSuccessRefines.bind (.refl _)
  intro base
  apply OptionSuccessRefines.bind (input.extendedShortCircuitKeyFrame_preserves_originalExec target view base)
  intro keys
  exact .refl _

/-- The successor recursive descriptor evaluator retains every original successful descriptor.
This statement is universal in molecular input and dependency view; no readiness condition is used. -/
theorem extendedShortCircuitDescriptor_preserves_originalExec
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    OptionSuccessRefines
      (input.localizedDescriptorExec? target view)
      (input.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor? target view) := by
  unfold localizedDescriptorExec? localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor?
  apply OptionSuccessRefines.bind (input.extendedShortCircuitSpatialEvidence_preserves_originalExec target view)
  intro evidence
  exact .refl _

/-- Positive agreement with the existing proof-facing semantics at the same dependency view.
An original refusal may become a result, so this is deliberately successful-result preservation. -/
theorem extendedShortCircuitDescriptor_preserves_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (descriptor : LocalizedAuxiliaryLabel)
    (computed : input.localizedOccurrenceDescriptorBearingRule3Through5Descriptor?
      target view = some descriptor) :
    input.localizedOccurrenceExtendedShortCircuitRule3Through5Descriptor? target view = some descriptor :=
  input.extendedShortCircuitDescriptor_preserves_originalExec target view descriptor
    (by rwa [localizedDescriptorExec?_eq_original])

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
