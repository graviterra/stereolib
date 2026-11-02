import TetraStereo.OneCenter.LocalizedRuleMajorCompoundBuilder
import TetraStereo.OneCenter.LocalizedOrderedReferencePipeline
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Callable descriptor and whole-molecule pipeline for the rule-major cumulative builder.
The executable callback uses actual frames, actual compound keys, the checked tracked order
and actual coordinates. The generated state is its own finite ranked fixed point.
The fixed-point theorems here are operational facts, not a chemical correctness claim. -/

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

noncomputable def compareRuleMajorOccurrenceAt? (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame fuel) (left right : Fin 4) :
    Option ConstitutionalDescriptorHierarchyComparison := do
  let budget := localizedOccurrenceRerootEvaluationFuel fuel
  let leftKey ← input.buildActualRuleMajorCompoundRule45Key? target view budget (frame.cursorAt left)
  let rightKey ← input.buildActualRuleMajorCompoundRule45Key? target view budget (frame.cursorAt right)
  some (localizedOccurrenceRule45ComparisonRecord
    (input.compareLocalizedRerootCompoundThroughRule5 leftKey rightKey))

def compareRuleMajorOccurrenceExecAt? (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame fuel) (left right : Fin 4) :
    Option ConstitutionalDescriptorHierarchyComparison := do
  let budget := localizedOccurrenceRerootEvaluationFuel fuel
  let leftKey ← input.buildActualRuleMajorCompoundRule45KeyExec? target view budget (frame.cursorAt left)
  let rightKey ← input.buildActualRuleMajorCompoundRule45KeyExec? target view budget (frame.cursorAt right)
  some (localizedOccurrenceRule45ComparisonRecord
    (input.compareLocalizedRerootCompoundThroughRule5 leftKey rightKey))

theorem compareRuleMajorOccurrenceExecAt?_eq (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame fuel) (left right : Fin 4) :
    input.compareRuleMajorOccurrenceExecAt? target view frame left right =
      input.compareRuleMajorOccurrenceAt? target view frame left right := by
  unfold compareRuleMajorOccurrenceExecAt? compareRuleMajorOccurrenceAt?
  simp only [input.buildActualRuleMajorCompoundRule45KeyExec?_eq]

noncomputable def ruleMajorSpatialEvidence? (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target) :
    Option (input.LocalizedOccurrenceRule45SpatialEvidence fuel) := do
  let center ← input.localizedOccurrenceDescriptorCenter? target
  let frame ← input.localizedOccurrenceFourLigandFrame? target
  let tracked ← safeTrackedOrderOf (input.compareRuleMajorOccurrenceAt? target view frame)
  let points ← tracked.highestFirst.mapM fun index =>
    input.localizedRerootCursorSpatialPoint? (frame.cursorAt index)
  some { center := center, frame := frame, tracked := tracked, points := points }

def ruleMajorSpatialEvidenceExec? (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target) :
    Option (input.LocalizedOccurrenceRule45SpatialEvidence fuel) := do
  let center ← input.localizedOccurrenceDescriptorCenter? target
  let frame ← input.localizedNoDoubleFourLigandFrameExec? target
  let tracked ← safeTrackedOrderOrderedExecOf (input.compareRuleMajorOccurrenceExecAt? target view frame)
  let points ← tracked.highestFirst.mapM fun index =>
    input.localizedRerootCursorSpatialPoint? (frame.cursorAt index)
  some { center := center, frame := frame, tracked := tracked, points := points }

theorem ruleMajorSpatialEvidenceExec?_eq (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target) :
    input.ruleMajorSpatialEvidenceExec? target view = input.ruleMajorSpatialEvidence? target view := by
  unfold ruleMajorSpatialEvidenceExec? ruleMajorSpatialEvidence?
  rw [input.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?]
  have same : ∀ frame : input.LocalizedOccurrenceFourLigandFrame fuel,
      safeTrackedOrderOrderedExecOf (input.compareRuleMajorOccurrenceExecAt? target view frame) =
        safeTrackedOrderOf (input.compareRuleMajorOccurrenceAt? target view frame) := by
    intro frame
    rw [safeTrackedOrderOrderedExecOf_eq]
    congr 1
    funext left right
    exact input.compareRuleMajorOccurrenceExecAt?_eq target view frame left right
  simp_rw [same]

noncomputable def ruleMajorDescriptor? (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target) :
    Option LocalizedAuxiliaryLabel := do
  let evidence ← input.ruleMajorSpatialEvidence? target view
  let raw ← descriptorOfPriorityOrderedPoints? evidence.points
  some (classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons)

def ruleMajorDescriptorExec? (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target) :
    Option LocalizedAuxiliaryLabel := do
  let evidence ← input.ruleMajorSpatialEvidenceExec? target view
  let raw ← descriptorOfPriorityOrderedPoints? evidence.points
  some (classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons)

theorem ruleMajorDescriptorExec?_eq (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target) :
    input.ruleMajorDescriptorExec? target view = input.ruleMajorDescriptor? target view := by
  unfold ruleMajorDescriptorExec? ruleMajorDescriptor?
  rw [input.ruleMajorSpatialEvidenceExec?_eq]

theorem ruleMajorDescriptor?_eq_none_of_no_center
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (absent : input.localizedOccurrenceDescriptorCenter? target = none) :
    input.ruleMajorDescriptor? target view = none := by
  simp [ruleMajorDescriptor?, ruleMajorSpatialEvidence?, absent]

end CertifiedLocalizedCIPInput

namespace LocalizedRuleMajorReference
open CertifiedLocalizedCIPInput TetraStereo.Certificate.Dependency

abbrev Input := LocalizedUniversalReference.Input
abbrev carrierFuel (input : Input) := LocalizedUniversalReference.carrierFuel input
abbrev Occurrence (input : Input) := input.certified.LocalizedCIPOccurrence (carrierFuel input)
abbrev Facts (input : Input) := List (Fact (Occurrence input) LocalizedAuxiliaryLabel)
abbrev Nodes (input : Input) := List (Node (Occurrence input) LocalizedAuxiliaryLabel)
abbrev Report := List (Nat × Option LocalizedAuxiliaryLabel)

/-- Operational equations for the revised callback, separate from the independent chemical spec. -/
def runtimeSemantics (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    input.LocalizedAuxiliaryRuleSemantics fuel where
  DeclarativeDerivation state target outcome :=
    input.ruleMajorDescriptorExec? target (input.localizedDependencyView state target) = outcome
  executableRule := fun target view => input.ruleMajorDescriptorExec? target view
  derivation_executable_iff := fun _ _ _ => Iff.rfl

def runtimeSystem (input : Input) :=
  input.certified.localizedCertificateSystem (carrierFuel input)
    (runtimeSemantics input.certified (carrierFuel input))

def dependencies (input : Input) :=
  input.certified.localizedCertificateDependencies (carrierFuel input)

def referenceNodes (input : Input) : Nodes input :=
  input.certified.localizedCertificateNodes (carrierFuel input)
    (runtimeSemantics input.certified (carrierFuel input))

def referenceFacts (input : Input) : Facts input :=
  input.certified.localizedCertificateFacts (carrierFuel input)
    (runtimeSemantics input.certified (carrierFuel input))

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
    (runtimeSemantics input.certified (carrierFuel input))

theorem reference_model (input : Input) :
    (runtimeSystem input).CIPModel (referenceState input) :=
  input.certified.localizedCertificateFacts_cipModel (carrierFuel input)
    (runtimeSemantics input.certified (carrierFuel input))

theorem reference_eq_boundedIteration (input : Input) :
    referenceState input = input.certified.evaluateLocalizedOccurrences (carrierFuel input)
      (runtimeSemantics input.certified (carrierFuel input)).executableRule := by
  have model := reference_model input
  unfold runtimeSystem localizedCertificateSystem at model
  rw [input.certified.localizedAuxiliaryOccurrenceSystemExecutableRoot_eq_old] at model
  exact (input.certified.evaluateLocalizedOccurrences_eq_model (carrierFuel input)
    (runtimeSemantics input.certified (carrierFuel input)) model).symm

theorem reference_fixed (input : Input) (target : Occurrence input) :
    input.certified.ruleMajorDescriptor? target
        (input.certified.localizedDependencyView (referenceState input) target) =
      referenceState input target := by
  rw [← input.certified.ruleMajorDescriptorExec?_eq, reference_eq_boundedIteration]
  exact input.certified.cipModel_evaluateLocalizedOccurrences (carrierFuel input)
    (runtimeSemantics input.certified (carrierFuel input)) target

theorem report_centers (input : Input) (facts : Facts input) :
    (report input facts).map Prod.fst =
      input.certified.canonicalTetrahedralCenters.map (fun center => center.val.val) := by
  simp only [report, List.map_map, Function.comp_def]

theorem analyze_eq_referenceReport (input : Input) :
    analyze input = input.certified.canonicalTetrahedralCenters.map fun center =>
      (center.val.val, referenceState input
        (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center)) := rfl

end LocalizedRuleMajorReference
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareRuleMajorOccurrenceExecAt?_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajorSpatialEvidenceExec?_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajorDescriptorExec?_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajorDescriptor?_eq_none_of_no_center
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.reference_check
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.reference_model
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.reference_eq_boundedIteration
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.reference_fixed
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.report_centers
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.analyze_eq_referenceReport
