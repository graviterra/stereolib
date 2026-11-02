import TetraStereo.OneCenter.LocalizedReferenceInput
import TetraStereo.OneCenter.LocalizedShortCircuitDescriptor
import TetraStereo.OneCenter.LocalizedDependencyCertificate
import TetraStereo.OneCenter.LocalizedRankedIteration
import TetraStereo.OneCenter.LocalizedReferencePipeline

set_option autoImplicit false
namespace TetraStereo.OneCenter.LocalizedShortCircuit
open CertifiedLocalizedCIPInput Certificate.Dependency

/-! Certificate-producing evaluation of the independently sound short-circuit successor.
The certificate proves the unique solution of bounded operational equations. Every positive label
has independent rule evidence. A missing label is an operational refusal; independent completeness
and equality to the original recursive evaluator are separate obligations. -/

abbrev Input := LocalizedReference.Input
abbrev admitSource? := LocalizedReference.admitSource?
abbrev admitSmilesSpatial? (text : String) (spatial : SpatialConfiguration)
    (cycles : List AromaticCycle := []) :=
  LocalizedReference.admitSmilesSpatial? text spatial cycles

def carrierFuel (input : Input) : Nat := input.molecule.atomCount + 1
def iterationRounds (input : Input) : Nat := carrierFuel input + 2

def evaluator (input : Input) (fuel : Nat) : input.certified.LocalizedRestrictedEvaluator fuel :=
  input.certified.localizedOccurrenceShortCircuitRule3Through5Descriptor?

/-- Exact operational outcome, including bounded refusal. This relation is deliberately distinct
from the independent positive descriptor relation. -/
def OperationalOutcome (input : Input) (fuel : Nat)
    (state : input.certified.LocalizedAuxiliaryState fuel)
    (target : input.certified.LocalizedCIPOccurrence fuel)
    (outcome : Option LocalizedAuxiliaryLabel) : Prop :=
  evaluator input fuel target (input.certified.localizedDependencyView state target) = outcome

/-- Adapter to reuse the ranked equation/certificate infrastructure. Its derivation relation is
operational; independent chemical soundness is exported separately below. -/
def runtimeSemantics (input : Input) (fuel : Nat) :
    input.certified.LocalizedAuxiliaryRuleSemantics fuel where
  DeclarativeDerivation := OperationalOutcome input fuel
  executableRule := evaluator input fuel
  derivation_executable_iff := by intros; rfl

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

/-- The generated state satisfies every local operational equation. -/
theorem reference_equation (input : Input) (target : Occurrence input) :
    evaluator input (carrierFuel input) target
      (input.certified.localizedDependencyView (referenceState input) target) =
        referenceState input target :=
  reference_model input target

/-- Positive reference outcomes carry independent recursive rule and exact-geometry evidence. -/
theorem reference_positive_sound (input : Input) (target : Occurrence input)
    (descriptor : LocalizedAuxiliaryLabel)
    (computed : referenceState input target = some descriptor) :
    input.certified.DeclarativeLocalizedOccurrenceShortCircuitRule3Through5Descriptor
      target (input.certified.localizedDependencyView (referenceState input) target) descriptor :=
  input.certified.localizedOccurrenceShortCircuitRule3Through5Descriptor?_sound
    target _ descriptor ((reference_equation input target).trans computed)

/-- Explicitly expose positive soundness at each final tetrahedral center. -/
theorem reference_center_positive_sound (input : Input)
    (center : input.certified.TetrahedralCenter) (descriptor : LocalizedAuxiliaryLabel)
    (computed : referenceState input
      (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center) =
        some descriptor) :
    input.certified.DeclarativeLocalizedOccurrenceShortCircuitRule3Through5Descriptor
      (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center)
      (input.certified.localizedDependencyView (referenceState input)
        (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center)) descriptor :=
  reference_positive_sound input _ descriptor computed

theorem report_centers (input : Input) (facts : Facts input) :
    (report input facts).map Prod.fst =
      input.certified.canonicalTetrahedralCenters.map (fun center => center.val.val) := by
  simp only [report, List.map_map, Function.comp_def]

end TetraStereo.OneCenter.LocalizedShortCircuit
