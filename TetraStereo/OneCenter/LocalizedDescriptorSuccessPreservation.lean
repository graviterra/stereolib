import TetraStereo.OneCenter.LocalizedRecursiveRule3Preservation
import TetraStereo.OneCenter.LocalizedShortCircuitCachedPipeline

set_option autoImplicit false
namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

/-- Every original successful four-ligand key frame survives unchanged, including all Rule45
keys, length evidence, Rule3 observations, topology and exclusions. -/
theorem shortCircuitKeyFrame_preserves_originalExec
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    OptionSuccessRefines
      (input.localizedDescriptorKeyFrameExec? target view base)
      (input.buildLocalizedOccurrenceShortCircuitRule3Through5KeyFrame? target view base) := by
  unfold localizedDescriptorKeyFrameExec? buildLocalizedOccurrenceShortCircuitRule3Through5KeyFrame?
  apply OptionSuccessRefines.bind
    (input.shortCircuitRule3Frame_preserves_originalExec target view _ base.cursors)
  intro frame
  exact .refl _

/-- Ranked geometry evidence survives in full at a fixed dependency view. -/
theorem shortCircuitSpatialEvidence_preserves_originalExec
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    OptionSuccessRefines
      (input.localizedDescriptorSpatialEvidenceExec? target view)
      (input.localizedOccurrenceShortCircuitRule3Through5SpatialEvidence? target view) := by
  unfold localizedDescriptorSpatialEvidenceExec? localizedOccurrenceShortCircuitRule3Through5SpatialEvidence?
  apply OptionSuccessRefines.bind (.refl _)
  intro center
  apply OptionSuccessRefines.bind (.refl _)
  intro base
  apply OptionSuccessRefines.bind (input.shortCircuitKeyFrame_preserves_originalExec target view base)
  intro keys
  exact .refl _

/-- The successor recursive descriptor evaluator retains every original successful descriptor.
This statement is universal in molecular input and dependency view; no readiness condition is used. -/
theorem shortCircuitDescriptor_preserves_originalExec
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    OptionSuccessRefines
      (input.localizedDescriptorExec? target view)
      (input.localizedOccurrenceShortCircuitRule3Through5Descriptor? target view) := by
  unfold localizedDescriptorExec? localizedOccurrenceShortCircuitRule3Through5Descriptor?
  apply OptionSuccessRefines.bind (input.shortCircuitSpatialEvidence_preserves_originalExec target view)
  intro evidence
  exact .refl _

/-- Positive agreement with the existing proof-facing semantics at the same dependency view.
An original refusal may become a result, so this is deliberately successful-result preservation. -/
theorem shortCircuitDescriptor_preserves_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (descriptor : LocalizedAuxiliaryLabel)
    (computed : input.localizedOccurrenceDescriptorBearingRule3Through5Descriptor?
      target view = some descriptor) :
    input.localizedOccurrenceShortCircuitRule3Through5Descriptor? target view = some descriptor :=
  input.shortCircuitDescriptor_preserves_originalExec target view descriptor
    (by rwa [localizedDescriptorExec?_eq_original])

end CertifiedLocalizedCIPInput
namespace LocalizedShortCircuit

/-- Public evaluator refinement holds at every shared local dependency view. It does not assume
that the two pipelines construct the same global auxiliary state. -/
theorem evaluator_preserves_original
    (input : Input) (fuel : Nat) (target : input.certified.LocalizedCIPOccurrence fuel)
    (view : input.certified.LocalizedDependencyView target) :
    OptionSuccessRefines (LocalizedReference.evaluator input fuel target view)
      (evaluator input fuel target view) :=
  input.certified.shortCircuitDescriptor_preserves_originalExec target view

namespace Cached

/-- Materializing the carrier and child lookup retains the same positive agreement theorem. -/
theorem evaluatorUsingCache_preserves_original
    (input : Input) (cache : RuntimeCache input) (target : Occurrence input)
    (view : input.certified.LocalizedDependencyView target) :
    OptionSuccessRefines (LocalizedReference.evaluator input (carrierFuel input) target view)
      (evaluatorUsingCache input cache target view) := by
  rw [evaluatorUsingCache_eq]
  exact evaluator_preserves_original input (carrierFuel input) target view

end Cached
end LocalizedShortCircuit
end TetraStereo.OneCenter
