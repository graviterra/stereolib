import TetraStereo.OneCenter.LocalizedOccurrenceDescriptorBearingRule3Through5Descriptor

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-- Exact accepted descriptor-bearing evidence plus independently checked final handedness. -/
def CanonicalLocalizedOccurrenceDescriptorBearingRule3Through5Descriptor
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (descriptor : LocalizedAuxiliaryLabel) : Prop :=
  ∃ evidence raw,
    input.localizedOccurrenceDescriptorBearingRule3Through5SpatialEvidence?
        target view = some evidence ∧
    RationalTetrahedralDescriptor evidence.points raw ∧
    descriptor = classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons

/-- Positive computation is exactly the operational descriptor-bearing canonical relation. -/
theorem localizedOccurrenceDescriptorBearingRule3Through5Descriptor?_eq_some_iff_canonical
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (descriptor : LocalizedAuxiliaryLabel) :
    input.localizedOccurrenceDescriptorBearingRule3Through5Descriptor?
        target view = some descriptor ↔
      input.CanonicalLocalizedOccurrenceDescriptorBearingRule3Through5Descriptor
        target view descriptor := by
  constructor
  · intro computed
    unfold localizedOccurrenceDescriptorBearingRule3Through5Descriptor? at computed
    cases evidenceComputed :
        input.localizedOccurrenceDescriptorBearingRule3Through5SpatialEvidence?
          target view with
    | none => simp [evidenceComputed] at computed
    | some evidence =>
        cases rawComputed : descriptorOfPriorityOrderedPoints? evidence.points with
        | none => simp [evidenceComputed, rawComputed] at computed
        | some raw =>
            simp [evidenceComputed, rawComputed] at computed
            subst descriptor
            exact ⟨evidence, raw, evidenceComputed,
              (descriptorOfPriorityOrderedPoints?_eq_some_iff
                evidence.points raw).mp rawComputed,
              rfl⟩
  · rintro ⟨evidence, raw, evidenceComputed, handedness, rfl⟩
    unfold localizedOccurrenceDescriptorBearingRule3Through5Descriptor?
    rw [evidenceComputed]
    change (do
      let observed ← descriptorOfPriorityOrderedPoints? evidence.points
      some (classifyTetrahedralRSPseudo observed
        evidence.tracked.pseudoComparisons)) =
      some (classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons)
    rw [(descriptorOfPriorityOrderedPoints?_eq_some_iff
      evidence.points raw).mpr handedness]
    rfl

/-- Refusal is exactly absence of an operational canonical descriptor-bearing result. -/
theorem localizedOccurrenceDescriptorBearingRule3Through5Descriptor?_eq_none_iff_no_canonical
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    input.localizedOccurrenceDescriptorBearingRule3Through5Descriptor?
        target view = none ↔
      ¬ ∃ descriptor,
        input.CanonicalLocalizedOccurrenceDescriptorBearingRule3Through5Descriptor
          target view descriptor := by
  constructor
  · intro refused ⟨descriptor, canonical⟩
    have accepted :=
      (input.localizedOccurrenceDescriptorBearingRule3Through5Descriptor?_eq_some_iff_canonical
        target view descriptor).mpr canonical
    rw [refused] at accepted
    contradiction
  · intro absent
    cases computed : input.localizedOccurrenceDescriptorBearingRule3Through5Descriptor?
        target view with
    | none => rfl
    | some descriptor =>
        exact (absent ⟨descriptor,
          (input.localizedOccurrenceDescriptorBearingRule3Through5Descriptor?_eq_some_iff_canonical
            target view descriptor).mp computed⟩).elim

/-- Operational canonical success implies the independent molecule-backed descriptor relation. -/
theorem CanonicalLocalizedOccurrenceDescriptorBearingRule3Through5Descriptor.implies_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (descriptor : LocalizedAuxiliaryLabel)
    (canonical :
      input.CanonicalLocalizedOccurrenceDescriptorBearingRule3Through5Descriptor
        target view descriptor) :
    input.DeclarativeLocalizedOccurrenceDescriptorBearingRule3Through5Descriptor
      target view descriptor := by
  rcases canonical with ⟨evidence, raw, evidenceComputed, handedness, descriptorEq⟩
  exact ⟨evidence, raw,
    input.localizedOccurrenceDescriptorBearingRule3Through5SpatialEvidence?_sound
      target view evidence evidenceComputed,
    handedness, descriptorEq⟩

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
