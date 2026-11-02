import TetraStereo.OneCenter.LocalizedOccurrenceRule3Through5Exact

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Recursive occurrence fixed point through Rule 5, including Rule 3

The exact operational positive/refusal relation instantiates the already proved finite,
strict-depth occurrence scheduler.  This replaces the previous Rules-4a--5-only recursive model
with a model whose evaluator runs the physical-unit-aware Rule-3 stage first.  Every emitted label
in the unique model is also proved to satisfy the broader molecule-backed positive relation.
-/

namespace CertifiedLocalizedCIPInput

/-- Complete optional outcome relation for the current cumulative Rules-1a--5 evaluator. -/
def DeclarativeLocalizedOccurrenceRule3Through5Outcome
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (state : input.LocalizedAuxiliaryState fuel)
    (target : input.LocalizedCIPOccurrence fuel)
    (outcome : Option LocalizedAuxiliaryLabel) : Prop :=
  match outcome with
  | none =>
      ¬ ∃ descriptor,
        input.CanonicalLocalizedOccurrenceRule3Through5Descriptor target
          (input.localizedDependencyView state target) descriptor
  | some descriptor =>
      input.CanonicalLocalizedOccurrenceRule3Through5Descriptor target
        (input.localizedDependencyView state target) descriptor

/-- The complete outcome relation is equivalent to the executable evaluator at every state. -/
theorem declarativeLocalizedOccurrenceRule3Through5Outcome_iff
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (state : input.LocalizedAuxiliaryState fuel)
    (target : input.LocalizedCIPOccurrence fuel)
    (outcome : Option LocalizedAuxiliaryLabel) :
    input.DeclarativeLocalizedOccurrenceRule3Through5Outcome state target outcome ↔
      input.localizedOccurrenceRule3Through5Descriptor? target
        (input.localizedDependencyView state target) = outcome := by
  cases outcome with
  | none =>
      exact (input.localizedOccurrenceRule3Through5Descriptor?_eq_none_iff_no_canonical
        target (input.localizedDependencyView state target)).symm
  | some descriptor =>
      exact (input.localizedOccurrenceRule3Through5Descriptor?_eq_some_iff_canonical
        target (input.localizedDependencyView state target) descriptor).symm

/-- Concrete dependency-restricted recursive semantics through Rule 5, now including Rule 3. -/
noncomputable def localizedOccurrenceRule3Through5AuxiliarySemantics
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    input.LocalizedAuxiliaryRuleSemantics fuel where
  DeclarativeDerivation := input.DeclarativeLocalizedOccurrenceRule3Through5Outcome
  executableRule := input.localizedOccurrenceRule3Through5Descriptor?
  derivation_executable_iff := by
    intro state target outcome
    exact input.declarativeLocalizedOccurrenceRule3Through5Outcome_iff
      state target outcome

/-- The cumulative recursive occurrence semantics has exactly one complete auxiliary state. -/
theorem existsUnique_localizedOccurrenceRule3Through5Model
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    ∃! state,
      (input.localizedAuxiliaryOccurrenceSystem
        (input.localizedOccurrenceRule3Through5AuxiliarySemantics fuel)).CIPModel state :=
  input.existsUnique_localizedAuxiliaryCIPModel
    (input.localizedOccurrenceRule3Through5AuxiliarySemantics fuel)

/-- The dependency-ready causal scheduler decodes to the cumulative Rules-1a--5 model. -/
theorem localizedOccurrenceRule3Through5SchedulerClosure_cipModel
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    (input.localizedAuxiliaryOccurrenceSystem
      (input.localizedOccurrenceRule3Through5AuxiliarySemantics fuel)).CIPModel
        (DeclarativeCIP.OccurrenceScheduler.decode
          (input.localizedAuxiliaryOccurrenceSystem
            (input.localizedOccurrenceRule3Through5AuxiliarySemantics fuel))
          (@input.LocalizedDepthDependency fuel)
          (DeclarativeCIP.OccurrenceScheduler.closure
            (input.localizedAuxiliaryOccurrenceSystem
              (input.localizedOccurrenceRule3Through5AuxiliarySemantics fuel))
            (@input.LocalizedDepthDependency fuel))) :=
  input.localizedAuxiliarySchedulerClosure_cipModel
    (input.localizedOccurrenceRule3Through5AuxiliarySemantics fuel)

/-- Every label in any model is exactly an operational canonical cumulative descriptor. -/
theorem localizedOccurrenceRule3Through5Model_eq_some_iff_canonical
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (state : input.LocalizedAuxiliaryState fuel)
    (model : (input.localizedAuxiliaryOccurrenceSystem
      (input.localizedOccurrenceRule3Through5AuxiliarySemantics fuel)).CIPModel state)
    (target : input.LocalizedCIPOccurrence fuel)
    (descriptor : LocalizedAuxiliaryLabel) :
    state target = some descriptor ↔
      input.CanonicalLocalizedOccurrenceRule3Through5Descriptor target
        (input.localizedDependencyView state target) descriptor := by
  have fixed :=
    (input.localizedAuxiliaryOccurrenceSystem
      (input.localizedOccurrenceRule3Through5AuxiliarySemantics fuel)).cipModel_iff_executableStateStep_fixed
      (input.localizedAuxiliaryDerivationStepCorrespondence
        (input.localizedOccurrenceRule3Through5AuxiliarySemantics fuel)) state |>.mp model
  have atTarget := congrFun fixed target
  rw [← atTarget]
  exact input.localizedOccurrenceRule3Through5Descriptor?_eq_some_iff_canonical
    target (input.localizedDependencyView state target) descriptor

/-- Consequently every model-emitted label has the broader independent molecule-backed meaning. -/
theorem localizedOccurrenceRule3Through5Model_eq_some_implies_declarative
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (state : input.LocalizedAuxiliaryState fuel)
    (model : (input.localizedAuxiliaryOccurrenceSystem
      (input.localizedOccurrenceRule3Through5AuxiliarySemantics fuel)).CIPModel state)
    (target : input.LocalizedCIPOccurrence fuel)
    (descriptor : LocalizedAuxiliaryLabel)
    (emitted : state target = some descriptor) :
    input.DeclarativeLocalizedOccurrenceRule3Through5Descriptor target
      (input.localizedDependencyView state target) descriptor := by
  exact CanonicalLocalizedOccurrenceRule3Through5Descriptor.implies_declarative
    input target (input.localizedDependencyView state target) descriptor
    ((input.localizedOccurrenceRule3Through5Model_eq_some_iff_canonical
      state model target descriptor).mp emitted)

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
