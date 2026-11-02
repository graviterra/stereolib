import TetraStereo.OneCenter.LocalizedRule3NodeCallbackRefinement

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-- A successfully constructed ordinary-route certificate selects precisely the old node's
ordinary spatial branch. This is derived from topology computation, not an extra routing premise. -/
theorem originalNode_eq_ordinary_of_routeCertificate
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (callback : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (excluded : List input.LocalizedRule3PhysicalUnitId)
    (certificate : input.LocalizedRule3OrdinaryRouteCertificate occurrence)
    (routed : input.localizedRule3OrdinaryRouteCertificate? occurrence = some certificate) :
    input.localizedDescriptorBearingRule3NodeWithExec? target occurrence view callback excluded =
      match input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWithExec?
          target occurrence view callback with
      | none => none
      | some result =>
          let observation := input.localizedRule3DescriptorBearingObservation result
          if excluded.contains observation.physicalUnitId then some none else some (some observation) := by
  unfold localizedRule3OrdinaryRouteCertificate? at routed
  split at routed
  next edge =>
    split at routed
    next initial first second rest entry =>
      simp only [localizedDescriptorBearingRule3NodeWithExec?, dif_pos edge, entry]
      rfl
    next initial entry =>
      split at routed
      next found => contradiction
      next axis found =>
        split at routed
        next ordinary =>
          simp only [localizedDescriptorBearingRule3NodeWithExec?, dif_pos edge, entry, found,
            dif_pos ordinary]
          rfl
        next ordinary => contradiction
    next => contradiction
  next edge => contradiction

/-- Successful original nodes retain their exact optional identity-bearing observation when
ordinary endpoints gain the shortcut. Coherence comes from the actual original frame builder. -/
theorem shortNode_preserves_original_callback
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (fuel : Nat)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    OptionSuccessRefines
      (input.localizedDescriptorBearingRule3NodeWith? target occurrence view
        (input.buildLocalizedDescriptorBearingRule3Frame? target view fuel) excluded)
      (input.localizedRule3ShortCircuitNodeWithExec? target occurrence view
        (input.buildLocalizedDescriptorBearingRule3Frame? target view fuel) excluded) := by
  let callback := input.buildLocalizedDescriptorBearingRule3Frame? target view fuel
  intro observation computed
  change input.localizedRule3ShortCircuitNodeWithExec? target occurrence view callback excluded = some observation
  have oldComputed : input.localizedDescriptorBearingRule3NodeWithExec?
      target occurrence view callback excluded = some observation := by
    rw [localizedDescriptorBearingRule3NodeWithExec?_eq_original]
    exact computed
  cases routed : input.localizedRule3OrdinaryRouteCertificate? occurrence with
  | none => simpa [localizedRule3ShortCircuitNodeWithExec?, routed] using oldComputed
  | some certificate =>
      rw [input.originalNode_eq_ordinary_of_routeCertificate
        target occurrence view callback excluded certificate routed] at oldComputed
      cases spatial : input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWithExec?
          target occurrence view callback with
      | none => simp [spatial] at oldComputed
      | some oldResult =>
          have oldSpatial : input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?
              target occurrence view callback = some oldResult := by
            rwa [localizedRule3OccurrenceDescriptorBearingSpatialUnitWithExec?_eq_original] at spatial
          obtain ⟨newResult, newComputed, sameObservation⟩ :=
            input.shortCircuitSpatial_preserves_originalFrame_success
              target occurrence view fuel oldResult oldSpatial
          have newSpatial : input.localizedRule3ShortCircuitSpatialUnitWithExec?
              target occurrence view callback = some newResult := by
            rw [localizedRule3ShortCircuitSpatialUnitWithExec?_eq_localizedRule3ShortCircuitSpatialUnitWith?]
            exact newComputed
          simp only [spatial] at oldComputed
          by_cases omitted :
              (input.localizedRule3DescriptorBearingObservation oldResult).physicalUnitId ∈ excluded
          · simpa [localizedRule3ShortCircuitNodeWithExec?, routed, newSpatial,
              sameObservation, omitted] using oldComputed
          · simpa [localizedRule3ShortCircuitNodeWithExec?, routed, newSpatial,
              sameObservation, omitted] using oldComputed

/-- Combine local shortcut preservation with a recursively improved callback. -/
theorem shortNode_preserves_original_with_refined_callback
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (fuel : Nat)
    (after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (refines : input.LocalizedRule3CallbackRefines
      (input.buildLocalizedDescriptorBearingRule3Frame? target view fuel) after)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    OptionSuccessRefines
      (input.localizedDescriptorBearingRule3NodeWith? target occurrence view
        (input.buildLocalizedDescriptorBearingRule3Frame? target view fuel) excluded)
      (input.localizedRule3ShortCircuitNodeWithExec? target occurrence view after excluded) :=
  (input.shortNode_preserves_original_callback target occurrence view fuel excluded).trans
    (input.shortNodeWith_callback_refines target occurrence view _ after refines excluded)

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
