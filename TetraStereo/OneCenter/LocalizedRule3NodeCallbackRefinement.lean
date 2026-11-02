import TetraStereo.OneCenter.LocalizedRule3CallbackRefinement
import TetraStereo.OneCenter.LocalizedRule3ShortCircuitNode

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-- Original node success is monotone under exact successful-frame preservation. Permanent
cyclic omission is independent of the callback, so a new frame cannot overturn that omission. -/
theorem originalNodeWith_callback_refines
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (refines : input.LocalizedRule3CallbackRefines before after)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    OptionSuccessRefines
      (input.localizedDescriptorBearingRule3NodeWith? target occurrence view before excluded)
      (input.localizedDescriptorBearingRule3NodeWith? target occurrence view after excluded) := by
  classical
  unfold localizedDescriptorBearingRule3NodeWith?
  by_cases edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence
  · simp only [dif_pos edge]
    cases entry : input.localizedRule3CumulatedAxisEntry? occurrence with
    | none => exact .refl _
    | some entryValue =>
        cases entryValue with
        | internal => exact .refl _
        | branched =>
            dsimp only
            intro observation computed
            cases old : input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?
                target occurrence view before with
            | none => simp [old] at computed
            | some result =>
                have next := input.ordinarySpatialWith_callback_refines
                  target occurrence view before after refines result old
                simpa [old, next] using computed
        | terminalStart =>
            dsimp only
            cases axis : input.localizedRule3CumulatedEndpointCursorFrame?
                (input.localizedRule3CumulatedTraversalFuel carrierFuel) occurrence with
            | none => exact .refl _
            | some axisValue =>
                dsimp only
                by_cases ordinary : axisValue.doubleBondCount = 1
                · simp only [dif_pos ordinary]
                  intro observation computed
                  cases old : input.localizedRule3OccurrenceDescriptorBearingSpatialUnitWith?
                      target occurrence view before with
                  | none => simp [old] at computed
                  | some result =>
                      have next := input.ordinarySpatialWith_callback_refines
                        target occurrence view before after refines result old
                      simpa [old, next] using computed
                · simp only [dif_neg ordinary]
                  by_cases planar : Odd axisValue.doubleBondCount
                  · simp only [dif_pos planar]
                    intro observation computed
                    cases old : input.localizedRule3OddCumuleneDescriptorBearingSpatialUnitWith?
                        target occurrence view before with
                    | none => simp [old] at computed
                    | some result =>
                        have next := input.oddCumuleneSpatialWith_callback_refines
                          target occurrence view before after refines result old
                        simpa [old, next] using computed
                  · simp only [dif_neg planar]
                    exact .refl _
        | ringClosure =>
            dsimp only
            intro observation computed
            cases old : input.localizedRule3RequiredMonocyclicEZWith?
                target occurrence view before with
            | some result =>
                have next := input.requiredMonocycleWith_callback_refines
                  target occurrence view before after refines result old
                simpa [old, next] using computed
            | none =>
                simp only [old] at computed
                cases route : input.localizedRule3CyclicAuthorityRoute? occurrence with
                | none => simp [route] at computed
                | some routeValue =>
                    simp only [route] at computed
                    cases routeValue with
                    | fullyCyclicCumulene => simp at computed
                    | ordinaryMonocyclicPolicyGap => simp at computed
                    | ordinaryNonmonocyclic => simp at computed
                    | ordinaryMonocyclicPolicy initial closure policy =>
                        dsimp only at computed
                        cases policyEq : policy.policy with
                        | requireEZ => simp [policyEq] at computed
                        | permanentlyOmit =>
                            have omitted := input.localizedRule3RequiredMonocyclicEZWith?_eq_none_of_omitted
                              target occurrence view after initial closure policy route policyEq
                            simpa [omitted, route, policyEq] using computed
  · simp only [dif_neg edge]
    exact .refl _

/-- The successor node likewise transports every successful observation, including structural
absence and physical-unit exclusion, through a more capable frame callback. -/
theorem shortNodeWith_callback_refines
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (refines : input.LocalizedRule3CallbackRefines before after)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    OptionSuccessRefines
      (input.localizedRule3ShortCircuitNodeWithExec? target occurrence view before excluded)
      (input.localizedRule3ShortCircuitNodeWithExec? target occurrence view after excluded) := by
  unfold localizedRule3ShortCircuitNodeWithExec?
  cases input.localizedRule3OrdinaryRouteCertificate? occurrence with
  | none =>
      simp only [localizedDescriptorBearingRule3NodeWithExec?_eq_original]
      exact input.originalNodeWith_callback_refines target occurrence view before after refines excluded
  | some certificate =>
      simp only [localizedRule3ShortCircuitSpatialUnitWithExec?_eq_localizedRule3ShortCircuitSpatialUnitWith?]
      apply OptionSuccessRefines.bind
        (input.shortSpatialWith_callback_refines target occurrence view before after refines)
      intro result
      exact .refl _

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
