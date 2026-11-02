import TetraStereo.OneCenter.LocalizedRule3ShortCircuitOddNode
import TetraStereo.OneCenter.LocalizedRule3ShortNodePreservation

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-- The actual original frame builder supplies both coherence properties needed for odd-axis
shortcut preservation; callers need not provide endpoint-key assumptions. -/
theorem shortCircuitOddSpatial_preserves_originalFrame_success
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel)
    (view : input.LocalizedDependencyView target) (budget : Nat)
    (oldResult : input.LocalizedRule3OddCumuleneDescriptorBearingSpatialResult fuel)
    (computed : input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?
      target occurrence view (input.buildLocalizedDescriptorBearingRule3Frame? target view budget) =
        some oldResult) :
    ∃ result, input.localizedRule3ShortCircuitOddSpatialUnitWithExec?
      target occurrence view (input.buildLocalizedDescriptorBearingRule3Frame? target view budget) =
        some result ∧ input.localizedRule3ShortCircuitOddSpatialObservation result =
          input.localizedRule3OddCumuleneDescriptorBearingObservation oldResult := by
  let callback := input.buildLocalizedDescriptorBearingRule3Frame? target view budget
  have derived := input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?_sound
    target occurrence view callback (fun cursors frame => callback cursors = some frame)
    (fun _ _ h => h) oldResult computed
  have left := derived.2.1
  have right := derived.2.2.1
  apply input.localizedRule3ShortCircuitOddSpatialObservation_eq_of_parameterizedWith
    target occurrence view callback oldResult computed
  · exact input.endpoint_rootsExact_of_frame_rootsExact oldResult.leftCompilation
      (input.buildLocalizedDescriptorBearingRule3Frame?_rootsExact target view budget _ _
        left.2.2.2.1) left.2.2.2.2.1
  · exact input.endpoint_rootsExact_of_frame_rootsExact oldResult.rightCompilation
      (input.buildLocalizedDescriptorBearingRule3Frame?_rootsExact target view budget _ _
        right.2.2.2.1) right.2.2.2.2.1
  · exact input.endpoint_constitutionalExact_of_frame_constitutionalExact oldResult.leftCompilation
      (input.buildLocalizedDescriptorBearingRule3Frame?_constitutionalExact target view budget _ _
        left.2.2.2.1) left.2.2.2.2.1
  · exact input.endpoint_constitutionalExact_of_frame_constitutionalExact oldResult.rightCompilation
      (input.buildLocalizedDescriptorBearingRule3Frame?_constitutionalExact target view budget _ _
        right.2.2.2.1) right.2.2.2.2.1

theorem shortOddSpatialWith_callback_refines
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor fuel) → Option input.LocalizedRule3CanonicalKeyFrame)
    (refines : input.LocalizedRule3CallbackRefines before after) :
    OptionSuccessRefines
      (input.localizedRule3ShortCircuitOddSpatialUnitWithExec? target occurrence view before)
      (input.localizedRule3ShortCircuitOddSpatialUnitWithExec? target occurrence view after) := by
  unfold localizedRule3ShortCircuitOddSpatialUnitWithExec?
  apply OptionSuccessRefines.bind (.refl _)
  intro topology
  simp only [← localizedRule3ShortCircuitEndpointPriority?_eq_localizedRule3ShortCircuitEndpointPriorityExec?]
  apply OptionSuccessRefines.bind
    (input.shortEndpointWith_callback_refines target view before after refines _ _ _)
  intro left
  apply OptionSuccessRefines.bind
    (input.shortEndpointWith_callback_refines target view before after refines _ _ _)
  intro right
  exact .refl _

theorem extendedShortNodeWith_callback_refines
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor fuel) → Option input.LocalizedRule3CanonicalKeyFrame)
    (refines : input.LocalizedRule3CallbackRefines before after)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    OptionSuccessRefines
      (input.localizedRule3ExtendedShortCircuitNodeWithExec? target occurrence view before excluded)
      (input.localizedRule3ExtendedShortCircuitNodeWithExec? target occurrence view after excluded) := by
  unfold localizedRule3ExtendedShortCircuitNodeWithExec?
  cases input.localizedRule3OddRouteCertificate? occurrence with
  | none => exact input.shortNodeWith_callback_refines target occurrence view before after refines excluded
  | some certificate =>
      apply OptionSuccessRefines.bind
        (input.shortOddSpatialWith_callback_refines target occurrence view before after refines)
      intro result
      exact .refl _

theorem extendedShortNode_preserves_original_callback
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (budget : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId) :
    OptionSuccessRefines
      (input.localizedDescriptorBearingRule3NodeWith? target occurrence view
        (input.buildLocalizedDescriptorBearingRule3Frame? target view budget) excluded)
      (input.localizedRule3ExtendedShortCircuitNodeWithExec? target occurrence view
        (input.buildLocalizedDescriptorBearingRule3Frame? target view budget) excluded) := by
  let callback := input.buildLocalizedDescriptorBearingRule3Frame? target view budget
  intro observation computed
  change input.localizedRule3ExtendedShortCircuitNodeWithExec? target occurrence view callback excluded = some observation
  cases routed : input.localizedRule3OddRouteCertificate? occurrence with
  | none =>
      simpa only [localizedRule3ExtendedShortCircuitNodeWithExec?, routed] using
        (input.shortNode_preserves_original_callback target occurrence view budget excluded observation computed)
  | some certificate =>
      have oldComputed : input.localizedDescriptorBearingRule3NodeWithExec?
          target occurrence view callback excluded = some observation := by
        rw [localizedDescriptorBearingRule3NodeWithExec?_eq_original]
        exact computed
      rw [input.originalNode_eq_odd_of_routeCertificate
        target occurrence view callback excluded certificate routed] at oldComputed
      cases spatial : input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWithExec?
          target occurrence view callback with
      | none => simp [spatial] at oldComputed
      | some oldResult =>
          have oldSpatial : input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?
              target occurrence view callback = some oldResult := by
            rwa [localizedRule3OddCumuleneDescriptorBearingSpatialUnitWithExec?_eq_original] at spatial
          obtain ⟨result, next, same⟩ := input.shortCircuitOddSpatial_preserves_originalFrame_success
            target occurrence view budget oldResult oldSpatial
          simp only [spatial] at oldComputed
          by_cases omitted : (input.localizedRule3OddCumuleneDescriptorBearingObservation oldResult).physicalUnitId ∈ excluded
          · simpa [localizedRule3ExtendedShortCircuitNodeWithExec?, routed, next, same,
              callback, omitted] using oldComputed
          · simpa [localizedRule3ExtendedShortCircuitNodeWithExec?, routed, next, same,
              callback, omitted] using oldComputed

theorem extendedShortNode_preserves_original_with_refined_callback
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (budget : Nat)
    (after : List (input.LocalizedRerootCursor fuel) → Option input.LocalizedRule3CanonicalKeyFrame)
    (refines : input.LocalizedRule3CallbackRefines
      (input.buildLocalizedDescriptorBearingRule3Frame? target view budget) after)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    OptionSuccessRefines
      (input.localizedDescriptorBearingRule3NodeWith? target occurrence view
        (input.buildLocalizedDescriptorBearingRule3Frame? target view budget) excluded)
      (input.localizedRule3ExtendedShortCircuitNodeWithExec? target occurrence view after excluded) :=
  (input.extendedShortNode_preserves_original_callback target occurrence view budget excluded).trans
    (input.extendedShortNodeWith_callback_refines target occurrence view _ after refines excluded)

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
