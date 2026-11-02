import TetraStereo.OneCenter.LocalizedOccurrenceRule45Exact

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Concrete recursive occurrence fixed point through Rule 5

The canonical exact descriptor relation is independent of executable equality and has complete
positive/refusal correspondence.  It therefore instantiates `LocalizedAuxiliaryRuleSemantics`.
The generic strict-depth theorem then supplies a unique complete occurrence state and a causal
scheduler model for the current Rules-4a--5 evaluator.

This is not yet the final IUPAC auxiliary fixed point: Rule 3, Rule 6, and non-tetrahedral source
families remain to be integrated.  It is the first concrete recursive model that can emit both
uppercase and lowercase tetrahedral labels from molecule-backed reroot comparisons.
-/

namespace CertifiedLocalizedCIPInput

/-- Independent complete optional outcome relation for the recursive occurrence descriptor. -/
def DeclarativeLocalizedOccurrenceRule45Outcome
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (state : input.LocalizedAuxiliaryState fuel)
    (target : input.LocalizedCIPOccurrence fuel)
    (outcome : Option LocalizedAuxiliaryLabel) : Prop :=
  match outcome with
  | none =>
      ¬ ∃ descriptor,
        input.CanonicalLocalizedOccurrenceRule45Descriptor target
          (input.localizedDependencyView state target) descriptor
  | some descriptor =>
      input.CanonicalLocalizedOccurrenceRule45Descriptor target
        (input.localizedDependencyView state target) descriptor

/-- The independent complete outcome relation is equivalent to the executable evaluator for
every state, target, and optional result. -/
theorem declarativeLocalizedOccurrenceRule45Outcome_iff
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (state : input.LocalizedAuxiliaryState fuel)
    (target : input.LocalizedCIPOccurrence fuel)
    (outcome : Option LocalizedAuxiliaryLabel) :
    input.DeclarativeLocalizedOccurrenceRule45Outcome state target outcome ↔
      input.localizedOccurrenceRule45Descriptor? target
        (input.localizedDependencyView state target) = outcome := by
  cases outcome with
  | none =>
      exact (input.localizedOccurrenceRule45Descriptor?_eq_none_iff_no_canonical
        target (input.localizedDependencyView state target)).symm
  | some descriptor =>
      exact (input.localizedOccurrenceRule45Descriptor?_eq_some_iff_canonical
        target (input.localizedDependencyView state target) descriptor).symm

/-- Concrete dependency-restricted recursive semantics through Rule 5. -/
noncomputable def localizedOccurrenceRule45AuxiliarySemantics
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    input.LocalizedAuxiliaryRuleSemantics fuel where
  DeclarativeDerivation := input.DeclarativeLocalizedOccurrenceRule45Outcome
  executableRule := input.localizedOccurrenceRule45Descriptor?
  derivation_executable_iff := by
    intro state target outcome
    exact input.declarativeLocalizedOccurrenceRule45Outcome_iff state target outcome

/-- The recursive Rules-4a--5 occurrence semantics has exactly one complete auxiliary state. -/
theorem existsUnique_localizedOccurrenceRule45Model
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    ∃! state,
      (input.localizedAuxiliaryOccurrenceSystem
        (input.localizedOccurrenceRule45AuxiliarySemantics fuel)).CIPModel state :=
  input.existsUnique_localizedAuxiliaryCIPModel
    (input.localizedOccurrenceRule45AuxiliarySemantics fuel)

/-- The dependency-ready causal scheduler decodes to a model of the concrete recursive
Rules-4a--5 semantics. -/
theorem localizedOccurrenceRule45SchedulerClosure_cipModel
    (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    (input.localizedAuxiliaryOccurrenceSystem
      (input.localizedOccurrenceRule45AuxiliarySemantics fuel)).CIPModel
        (DeclarativeCIP.OccurrenceScheduler.decode
          (input.localizedAuxiliaryOccurrenceSystem
            (input.localizedOccurrenceRule45AuxiliarySemantics fuel))
          (@input.LocalizedDepthDependency fuel)
          (DeclarativeCIP.OccurrenceScheduler.closure
            (input.localizedAuxiliaryOccurrenceSystem
              (input.localizedOccurrenceRule45AuxiliarySemantics fuel))
            (@input.LocalizedDepthDependency fuel))) :=
  input.localizedAuxiliarySchedulerClosure_cipModel
    (input.localizedOccurrenceRule45AuxiliarySemantics fuel)

/-- Every label in any model is exactly a canonical molecule-backed descriptor derivation under
that model's strict-dependency view. -/
theorem localizedOccurrenceRule45Model_eq_some_iff_canonical
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (state : input.LocalizedAuxiliaryState fuel)
    (model : (input.localizedAuxiliaryOccurrenceSystem
      (input.localizedOccurrenceRule45AuxiliarySemantics fuel)).CIPModel state)
    (target : input.LocalizedCIPOccurrence fuel)
    (descriptor : LocalizedAuxiliaryLabel) :
    state target = some descriptor ↔
      input.CanonicalLocalizedOccurrenceRule45Descriptor target
        (input.localizedDependencyView state target) descriptor := by
  have fixed :=
    (input.localizedAuxiliaryOccurrenceSystem
      (input.localizedOccurrenceRule45AuxiliarySemantics fuel)).cipModel_iff_executableStateStep_fixed
      (input.localizedAuxiliaryDerivationStepCorrespondence
        (input.localizedOccurrenceRule45AuxiliarySemantics fuel)) state |>.mp model
  have atTarget := congrFun fixed target
  rw [← atTarget]
  exact input.localizedOccurrenceRule45Descriptor?_eq_some_iff_canonical
    target (input.localizedDependencyView state target) descriptor

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
