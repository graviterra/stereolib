import TetraStereo.OneCenter.LocalizedReferenceInput
import TetraStereo.OneCenter.LocalizedDescriptorExecutable
import TetraStereo.OneCenter.LocalizedDependencyCertificate
import TetraStereo.OneCenter.LocalizedRankedIteration
import TetraStereo.OneCenter.LocalizedOccurrenceDescriptorBearingRule3Through5FixedPoint

set_option autoImplicit false
namespace TetraStereo.OneCenter.LocalizedReference
open CertifiedLocalizedCIPInput Certificate.Dependency

/-! Runnable reference evaluation for every certified localized input, including order-two bonds.
The ranked producer constructs dependency references and evaluates each occurrence in order.
The resulting state agrees with the original semantics and its bounded fixed-point iteration.
Optional refusals are retained; these theorems do not turn operational refusal into chemical
nonexistence or establish independent chemical completeness. -/

def carrierFuel (input : Input) : Nat := input.molecule.atomCount + 1
def iterationRounds (input : Input) : Nat := carrierFuel input + 2

def evaluator (input : Input) (fuel : Nat) : input.certified.LocalizedRestrictedEvaluator fuel :=
  input.certified.localizedDescriptorExec?

theorem evaluator_eq_original (input : Input) (fuel : Nat) :
    evaluator input fuel =
      input.certified.localizedOccurrenceDescriptorBearingRule3Through5Descriptor? := by
  funext target view
  exact input.certified.localizedDescriptorExec?_eq_original target view

def runtimeSemantics (input : Input) (fuel : Nat) :
    input.certified.LocalizedAuxiliaryRuleSemantics fuel where
  DeclarativeDerivation :=
    input.certified.DeclarativeLocalizedOccurrenceDescriptorBearingRule3Through5Outcome
  executableRule := evaluator input fuel
  derivation_executable_iff := by
    intro state target outcome
    rw [evaluator_eq_original]
    exact input.certified.declarativeLocalizedOccurrenceDescriptorBearingRule3Through5Outcome_iff
      state target outcome

abbrev Occurrence (input : Input) := input.certified.LocalizedCIPOccurrence (carrierFuel input)
abbrev Facts (input : Input) := List (Fact (Occurrence input) LocalizedAuxiliaryLabel)
abbrev Nodes (input : Input) := List (Node (Occurrence input) LocalizedAuxiliaryLabel)
abbrev Report := List (Nat × Option LocalizedAuxiliaryLabel)

def runtimeSystem (input : Input) :=
  input.certified.localizedCertificateSystem (carrierFuel input)
    (runtimeSemantics input (carrierFuel input))

def dependencies (input : Input) :=
  input.certified.localizedCertificateDependencies (carrierFuel input)

def referenceNodes (input : Input) : Nodes input :=
  input.certified.localizedCertificateNodes (carrierFuel input)
    (runtimeSemantics input (carrierFuel input))

def referenceFacts (input : Input) : Facts input :=
  input.certified.localizedCertificateFacts (carrierFuel input)
    (runtimeSemantics input (carrierFuel input))

def referenceState (input : Input) : input.certified.LocalizedAuxiliaryState (carrierFuel input) :=
  lookup (referenceFacts input)

def report (input : Input) (facts : Facts input) : Report :=
  input.certified.canonicalTetrahedralCenters.map fun center =>
    (center.val.val, lookup facts
      (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center))

def analyze (input : Input) : Report := report input (referenceFacts input)

theorem reference_check (input : Input) :
    check (runtimeSystem input) (dependencies input) (referenceNodes input) =
      some (referenceFacts input) :=
  input.certified.localizedCertificate_check (carrierFuel input)
    (runtimeSemantics input (carrierFuel input))

theorem reference_targets (input : Input) :
    (referenceFacts input).map Prod.fst =
      input.certified.localizedCertificateOrder (carrierFuel input) :=
  input.certified.localizedCertificateFacts_targets (carrierFuel input)
    (runtimeSemantics input (carrierFuel input))

theorem reference_model (input : Input) :
    (runtimeSystem input).CIPModel (referenceState input) :=
  input.certified.localizedCertificateFacts_cipModel (carrierFuel input)
    (runtimeSemantics input (carrierFuel input))

theorem reference_eq_boundedIteration (input : Input) :
    referenceState input = input.certified.evaluateLocalizedOccurrences (carrierFuel input)
      (evaluator input (carrierFuel input)) := by
  have model := reference_model input
  unfold runtimeSystem localizedCertificateSystem at model
  rw [input.certified.localizedAuxiliaryOccurrenceSystemExecutableRoot_eq_old] at model
  exact (input.certified.evaluateLocalizedOccurrences_eq_model (carrierFuel input)
    (runtimeSemantics input (carrierFuel input)) model).symm

/-- The explicit iteration budget suffices for the reference state's original occurrence semantics.
This is a bound for solving the bounded occurrence equations, not a new completeness theorem about
the original nested Rule-3 fuel. -/
theorem reference_eq_originalIteration (input : Input) :
    referenceState input = input.certified.evaluateLocalizedOccurrences (carrierFuel input)
      input.certified.localizedOccurrenceDescriptorBearingRule3Through5Descriptor? := by
  rw [reference_eq_boundedIteration, evaluator_eq_original]

theorem reference_eq_originalModel (input : Input)
    {state : input.certified.LocalizedAuxiliaryState (carrierFuel input)}
    (model : (input.certified.localizedAuxiliaryOccurrenceSystem
      (input.certified.localizedOccurrenceDescriptorBearingRule3Through5AuxiliarySemantics
        (carrierFuel input))).CIPModel state) :
    referenceState input = state := by
  rw [reference_eq_originalIteration]
  exact input.certified.evaluateLocalizedOccurrences_eq_model (carrierFuel input)
    (input.certified.localizedOccurrenceDescriptorBearingRule3Through5AuxiliarySemantics
      (carrierFuel input)) model

theorem reference_iff_declarative (input : Input) (target : Occurrence input)
    (outcome : Option LocalizedAuxiliaryLabel) :
    referenceState input target = outcome ↔
      input.certified.DeclarativeLocalizedOccurrenceDescriptorBearingRule3Through5Outcome
        (referenceState input) target outcome := by
  have current :=
    (input.certified.declarativeLocalizedOccurrenceDescriptorBearingRule3Through5Outcome_iff
      (referenceState input) target (referenceState input target)).mp
        (reference_model input target)
  rw [input.certified.declarativeLocalizedOccurrenceDescriptorBearingRule3Through5Outcome_iff]
  exact ⟨fun equal => current.trans equal, fun equal => current.symm.trans equal⟩

theorem report_centers (input : Input) (facts : Facts input) :
    (report input facts).map Prod.fst =
      input.certified.canonicalTetrahedralCenters.map (fun center => center.val.val) := by
  simp only [report, List.map_map, Function.comp_def]

end TetraStereo.OneCenter.LocalizedReference
