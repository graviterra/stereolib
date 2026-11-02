import TetraStereo.OneCenter.LocalizedConstitutionalOriginalRule3Coherence
import TetraStereo.OneCenter.LocalizedRerootShortCircuitRule3Key

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-- The successor full-key derivation has the same constitutional projection property. -/
theorem shortCircuitRule3Key_constitutional_derived
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ fuel excluded cursor key,
      input.DeclarativeLocalizedRerootShortCircuitRule3Key
        target view fuel excluded cursor key →
      input.DeclarativeLocalizedRerootRuleMajorKey fuel cursor key.constitutional := by
  intro fuel
  induction fuel with
  | zero =>
      intro excluded cursor key meaning
      obtain ⟨children, frame, empty, _, rfl⟩ := meaning
      exact .terminal frame empty
  | succ fuel ih =>
      intro excluded cursor key meaning
      obtain ⟨children, observation, frame, _, terminal | branch⟩ := meaning
      · obtain ⟨empty, rfl⟩ := terminal
        exact .terminal frame empty
      · obtain ⟨childKeys, sorted, nonempty, derivations, ranking, descending, rfl⟩ := branch
        exact .branch frame nonempty
          (projected_rule3_constitutional_key_list input _ (ih excluded) children childKeys derivations)
          (ranking.map (·.constitutional)) (input.rule3_descending_constitutional sorted descending)

/-- Pure constitutional compilation and the original recursive stereo compilation agree on every
comparison-visible constitutional layer, even at different successful budgets. -/
theorem constitutionalKey_eq_descriptorRule3_observable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (constitutionalFuel stereoFuel : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (plain : OfficialRuleMajorKey input.Atom) (full : input.LocalizedRerootRecursiveRule3SpatialKey)
    (plainComputed : input.buildLocalizedRerootRuleMajorKey? constitutionalFuel cursor = some plain)
    (fullComputed : input.buildLocalizedRerootDescriptorBearingRule3Key?
      target view stereoFuel excluded cursor = some full) :
    constitutionalObservable plain = constitutionalObservable full.constitutional :=
  input.compiled_constitutional_observable_eq_derived constitutionalFuel stereoFuel cursor
    plain full.constitutional plainComputed
    (input.descriptorRule3Key_constitutional_derived target view stereoFuel excluded cursor full
      (input.buildLocalizedRerootDescriptorBearingRule3Key?_sound
        target view stereoFuel excluded cursor full fullComputed))

/-- The same coherence result for the demand-driven successor. -/
theorem constitutionalKey_eq_shortCircuitRule3_observable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (constitutionalFuel stereoFuel : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (plain : OfficialRuleMajorKey input.Atom) (full : input.LocalizedRerootRecursiveRule3SpatialKey)
    (plainComputed : input.buildLocalizedRerootRuleMajorKey? constitutionalFuel cursor = some plain)
    (fullComputed : input.buildLocalizedRerootShortCircuitRule3KeyExec?
      target view stereoFuel excluded cursor = some full) :
    constitutionalObservable plain = constitutionalObservable full.constitutional :=
  input.compiled_constitutional_observable_eq_derived constitutionalFuel stereoFuel cursor
    plain full.constitutional plainComputed
    (input.shortCircuitRule3Key_constitutional_derived target view stereoFuel excluded cursor full
      (input.buildLocalizedRerootShortCircuitRule3KeyExec?_sound
        target view stereoFuel excluded cursor full fullComputed))

/-- Original and successor stereo algorithms may differ in their observation metadata; whenever
both succeed they agree on all three constitutional comparison projections, at arbitrary budgets. -/
theorem descriptorRule3_shortCircuit_constitutional_agree
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (leftTarget rightTarget : input.LocalizedCIPOccurrence carrierFuel)
    (leftView : input.LocalizedDependencyView leftTarget)
    (rightView : input.LocalizedDependencyView rightTarget)
    (leftFuel rightFuel : Nat) (leftExcluded rightExcluded : List input.LocalizedRule3PhysicalUnitId)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (left right : input.LocalizedRerootRecursiveRule3SpatialKey)
    (hl : input.buildLocalizedRerootDescriptorBearingRule3Key?
      leftTarget leftView leftFuel leftExcluded cursor = some left)
    (hr : input.buildLocalizedRerootShortCircuitRule3KeyExec?
      rightTarget rightView rightFuel rightExcluded cursor = some right) :
    constitutionalObservable left.constitutional = constitutionalObservable right.constitutional :=
  input.declarative_constitutional_observable_unique leftFuel rightFuel cursor _ _
    (input.descriptorRule3Key_constitutional_derived leftTarget leftView leftFuel leftExcluded cursor left
      (input.buildLocalizedRerootDescriptorBearingRule3Key?_sound
        leftTarget leftView leftFuel leftExcluded cursor left hl))
    (input.shortCircuitRule3Key_constitutional_derived rightTarget rightView rightFuel rightExcluded cursor right
      (input.buildLocalizedRerootShortCircuitRule3KeyExec?_sound
        rightTarget rightView rightFuel rightExcluded cursor right hr))

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
