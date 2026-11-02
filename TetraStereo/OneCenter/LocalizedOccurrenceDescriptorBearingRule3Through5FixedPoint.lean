import TetraStereo.OneCenter.LocalizedOccurrenceDescriptorBearingRule3Through5Exact

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-- Complete optional outcome relation for the descriptor-bearing Rules-1a--5 evaluator. -/
def DeclarativeLocalizedOccurrenceDescriptorBearingRule3Through5Outcome
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (state : input.LocalizedAuxiliaryState fuel)
    (target : input.LocalizedCIPOccurrence fuel)
    (outcome : Option LocalizedAuxiliaryLabel) : Prop :=
  match outcome with
  | none =>
      ¬ ∃ descriptor,
        input.CanonicalLocalizedOccurrenceDescriptorBearingRule3Through5Descriptor
          target (input.localizedDependencyView state target) descriptor
  | some descriptor =>
      input.CanonicalLocalizedOccurrenceDescriptorBearingRule3Through5Descriptor
        target (input.localizedDependencyView state target) descriptor

/-- The complete outcome relation agrees exactly with execution. -/
theorem declarativeLocalizedOccurrenceDescriptorBearingRule3Through5Outcome_iff
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (state : input.LocalizedAuxiliaryState fuel)
    (target : input.LocalizedCIPOccurrence fuel)
    (outcome : Option LocalizedAuxiliaryLabel) :
    input.DeclarativeLocalizedOccurrenceDescriptorBearingRule3Through5Outcome
        state target outcome ↔
      input.localizedOccurrenceDescriptorBearingRule3Through5Descriptor?
        target (input.localizedDependencyView state target) = outcome := by
  cases outcome with
  | none =>
      exact
        (input.localizedOccurrenceDescriptorBearingRule3Through5Descriptor?_eq_none_iff_no_canonical
          target (input.localizedDependencyView state target)).symm
  | some descriptor =>
      exact
        (input.localizedOccurrenceDescriptorBearingRule3Through5Descriptor?_eq_some_iff_canonical
          target (input.localizedDependencyView state target) descriptor).symm

/-- Concrete dependency-restricted semantics using descriptor-bearing Rule 3. -/
noncomputable def localizedOccurrenceDescriptorBearingRule3Through5AuxiliarySemantics
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    input.LocalizedAuxiliaryRuleSemantics fuel where
  DeclarativeDerivation :=
    input.DeclarativeLocalizedOccurrenceDescriptorBearingRule3Through5Outcome
  executableRule := input.localizedOccurrenceDescriptorBearingRule3Through5Descriptor?
  derivation_executable_iff := by
    intro state target outcome
    exact input.declarativeLocalizedOccurrenceDescriptorBearingRule3Through5Outcome_iff
      state target outcome

/-- Descriptor-bearing Rules-1a--5 have exactly one complete auxiliary state. -/
theorem existsUnique_localizedOccurrenceDescriptorBearingRule3Through5Model
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    ∃! state,
      (input.localizedAuxiliaryOccurrenceSystem
        (input.localizedOccurrenceDescriptorBearingRule3Through5AuxiliarySemantics fuel)).CIPModel
          state :=
  input.existsUnique_localizedAuxiliaryCIPModel
    (input.localizedOccurrenceDescriptorBearingRule3Through5AuxiliarySemantics fuel)

/-- The causal scheduler decodes to the descriptor-bearing cumulative model. -/
theorem localizedOccurrenceDescriptorBearingRule3Through5SchedulerClosure_cipModel
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    (input.localizedAuxiliaryOccurrenceSystem
      (input.localizedOccurrenceDescriptorBearingRule3Through5AuxiliarySemantics fuel)).CIPModel
        (DeclarativeCIP.OccurrenceScheduler.decode
          (input.localizedAuxiliaryOccurrenceSystem
            (input.localizedOccurrenceDescriptorBearingRule3Through5AuxiliarySemantics fuel))
          (@input.LocalizedDepthDependency fuel)
          (DeclarativeCIP.OccurrenceScheduler.closure
            (input.localizedAuxiliaryOccurrenceSystem
              (input.localizedOccurrenceDescriptorBearingRule3Through5AuxiliarySemantics fuel))
            (@input.LocalizedDepthDependency fuel))) :=
  input.localizedAuxiliarySchedulerClosure_cipModel
    (input.localizedOccurrenceDescriptorBearingRule3Through5AuxiliarySemantics fuel)

/-- Every emitted label in any model is an operational canonical descriptor-bearing result. -/
theorem localizedOccurrenceDescriptorBearingRule3Through5Model_eq_some_iff_canonical
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (state : input.LocalizedAuxiliaryState fuel)
    (model : (input.localizedAuxiliaryOccurrenceSystem
      (input.localizedOccurrenceDescriptorBearingRule3Through5AuxiliarySemantics fuel)).CIPModel
        state)
    (target : input.LocalizedCIPOccurrence fuel)
    (descriptor : LocalizedAuxiliaryLabel) :
    state target = some descriptor ↔
      input.CanonicalLocalizedOccurrenceDescriptorBearingRule3Through5Descriptor
        target (input.localizedDependencyView state target) descriptor := by
  have fixed :=
    (input.localizedAuxiliaryOccurrenceSystem
      (input.localizedOccurrenceDescriptorBearingRule3Through5AuxiliarySemantics fuel)).cipModel_iff_executableStateStep_fixed
      (input.localizedAuxiliaryDerivationStepCorrespondence
        (input.localizedOccurrenceDescriptorBearingRule3Through5AuxiliarySemantics fuel))
      state |>.mp model
  have atTarget := congrFun fixed target
  rw [← atTarget]
  exact input.localizedOccurrenceDescriptorBearingRule3Through5Descriptor?_eq_some_iff_canonical
    target (input.localizedDependencyView state target) descriptor

/-- Consequently every model-emitted label has the independent molecule-backed meaning. -/
theorem localizedOccurrenceDescriptorBearingRule3Through5Model_eq_some_implies_declarative
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (state : input.LocalizedAuxiliaryState fuel)
    (model : (input.localizedAuxiliaryOccurrenceSystem
      (input.localizedOccurrenceDescriptorBearingRule3Through5AuxiliarySemantics fuel)).CIPModel
        state)
    (target : input.LocalizedCIPOccurrence fuel)
    (descriptor : LocalizedAuxiliaryLabel)
    (emitted : state target = some descriptor) :
    input.DeclarativeLocalizedOccurrenceDescriptorBearingRule3Through5Descriptor
      target (input.localizedDependencyView state target) descriptor := by
  exact
    CanonicalLocalizedOccurrenceDescriptorBearingRule3Through5Descriptor.implies_declarative
      input target (input.localizedDependencyView state target) descriptor
      ((input.localizedOccurrenceDescriptorBearingRule3Through5Model_eq_some_iff_canonical
        state model target descriptor).mp emitted)

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
