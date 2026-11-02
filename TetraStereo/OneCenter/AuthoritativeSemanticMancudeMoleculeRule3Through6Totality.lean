import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3Through6Totality
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeMoleculeRule3Through6Analysis

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Exact totality boundary for the molecule-level Rules 1a--6 endpoint

This lifts the one-shot scheduler's exact success/refusal theorem across canonical ligand-frame
construction and exact rational-coordinate parity.
-/

/-- Exact executable meaning of one molecule-level descriptor, with every optional boundary made
explicit and all chemical decisions below the initial partition stated declaratively. -/
def AromaticCanonicalScheduledRule3Through6ExecutableDescriptorJudgment
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter)
    (descriptor : RS) : Prop :=
  let target := source.aromaticCanonicalFinalOccurrence carrierFuel center
  let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
  ∃ roots parity,
    source.aromaticCanonicalOccurrenceLigandFrame? target = some roots ∧
      source.aromaticCanonicalRerootFrameParity? roots = some parity ∧
      source.AromaticCanonicalRule3Through6ExecutableDescriptorJudgment center.1 target
        (source.aromaticCanonicalDependencyView state target)
        ruleFuel roots parity descriptor

/-- The molecule endpoint emits exactly the descriptors admitted by its explicit frame,
coordinate-parity, partition, topology, and branch judgments. -/
theorem aromaticCanonicalScheduledRule3Through6Descriptor?_eq_some_iff_executableJudgment
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter)
    (descriptor : RS) :
    source.aromaticCanonicalScheduledRule3Through6Descriptor?
        semantics ruleFuel center = some descriptor ↔
      source.AromaticCanonicalScheduledRule3Through6ExecutableDescriptorJudgment
        semantics ruleFuel center descriptor := by
  unfold aromaticCanonicalScheduledRule3Through6Descriptor?
    AromaticCanonicalScheduledRule3Through6ExecutableDescriptorJudgment
  let target := source.aromaticCanonicalFinalOccurrence carrierFuel center
  let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
  constructor
  · intro computed
    cases rootsComputed : source.aromaticCanonicalOccurrenceLigandFrame? target with
    | none => simp [target, rootsComputed] at computed
    | some roots =>
        cases parityComputed : source.aromaticCanonicalRerootFrameParity? roots with
        | none => simp [target, rootsComputed, parityComputed] at computed
        | some parity =>
            have finalComputed :
                source.aromaticCanonicalRule3Through6Descriptor? center.1 target
                    (source.aromaticCanonicalDependencyView state target)
                    ruleFuel roots parity = some descriptor := by
              simpa [target, rootsComputed, parityComputed, state] using computed
            exact ⟨roots, parity, rootsComputed, parityComputed,
              (source.aromaticCanonicalRule3Through6Descriptor?_eq_some_iff_executableJudgment
                center.1 target (source.aromaticCanonicalDependencyView state target)
                ruleFuel roots parity descriptor).mp finalComputed⟩
  · rintro ⟨roots, parity, rootsComputed, parityComputed, finalJudgment⟩
    have finalComputed :
        source.aromaticCanonicalRule3Through6Descriptor? center.1 target
            (source.aromaticCanonicalDependencyView state target)
            ruleFuel roots parity = some descriptor :=
      (source.aromaticCanonicalRule3Through6Descriptor?_eq_some_iff_executableJudgment
        center.1 target (source.aromaticCanonicalDependencyView state target)
        ruleFuel roots parity descriptor).mpr finalJudgment
    simpa [target, rootsComputed, parityComputed, state] using finalComputed

/-- Descriptor-independent readiness of the complete molecule endpoint. -/
def AromaticCanonicalScheduledRule3Through6Ready
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter) : Prop :=
  ∃ descriptor,
    source.AromaticCanonicalScheduledRule3Through6ExecutableDescriptorJudgment
      semantics ruleFuel center descriptor

/-- Molecule readiness is exactly existence of a successful final descriptor. -/
theorem aromaticCanonicalScheduledRule3Through6Ready_iff_exists_descriptor
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter) :
    source.AromaticCanonicalScheduledRule3Through6Ready semantics ruleFuel center ↔
      ∃ descriptor,
        source.aromaticCanonicalScheduledRule3Through6Descriptor?
          semantics ruleFuel center = some descriptor := by
  unfold AromaticCanonicalScheduledRule3Through6Ready
  constructor <;> rintro ⟨descriptor, witnessed⟩
  · exact ⟨descriptor,
      (source.aromaticCanonicalScheduledRule3Through6Descriptor?_eq_some_iff_executableJudgment
        semantics ruleFuel center descriptor).mpr witnessed⟩
  · exact ⟨descriptor,
      (source.aromaticCanonicalScheduledRule3Through6Descriptor?_eq_some_iff_executableJudgment
        semantics ruleFuel center descriptor).mp witnessed⟩

/-- The molecule endpoint returns `none` exactly when complete readiness is false. -/
theorem aromaticCanonicalScheduledRule3Through6Descriptor?_eq_none_iff_not_ready
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter) :
    source.aromaticCanonicalScheduledRule3Through6Descriptor?
        semantics ruleFuel center = none ↔
      ¬ source.AromaticCanonicalScheduledRule3Through6Ready
        semantics ruleFuel center := by
  rw [source.aromaticCanonicalScheduledRule3Through6Ready_iff_exists_descriptor]
  cases computed : source.aromaticCanonicalScheduledRule3Through6Descriptor?
      semantics ruleFuel center <;> simp

/-- The exact executable molecule judgment entails the earlier independent complete molecule
judgment. -/
theorem AromaticCanonicalScheduledRule3Through6ExecutableDescriptorJudgment.complete
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter)
    (descriptor : RS)
    (judged : source.AromaticCanonicalScheduledRule3Through6ExecutableDescriptorJudgment
      semantics ruleFuel center descriptor) :
    source.AromaticCanonicalScheduledRule3Through6DescriptorJudgment
      semantics ruleFuel center descriptor := by
  let target := source.aromaticCanonicalFinalOccurrence carrierFuel center
  let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
  rcases judged with
    ⟨roots, parity, rootsComputed, parityComputed, finalJudgment⟩
  exact ⟨roots, parity,
    source.aromaticCanonicalOccurrenceLigandFrame?_sound target roots rootsComputed,
    source.aromaticCanonicalRerootFrameParity?_sound roots parity parityComputed,
    finalJudgment.complete⟩

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
