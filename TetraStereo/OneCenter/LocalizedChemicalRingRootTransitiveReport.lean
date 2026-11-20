import TetraStereo.OneCenter.LocalizedChemicalRingRootTransitiveClassification
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceModelExistence
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedReport
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Exact report and independent-source-model outcomes at physically transitive roots.
No frame, auxiliary state or descriptor is supplied. The native physical criterion interprets
this evaluator's single promotion; it does not assert unrestricted chemical completeness. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingRootTransitiveReport

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingRootTransitiveClassification (PhysicalTransitive)
open LocalizedChemicalRingRootFallbackPhysicalObstruction (FreeAt)
open LocalizedChemicalRingJointPreparedRefusalCharacterization (OddBoundarySymmetry)
open LocalizedChemicalRingJointPreparedRootInput (root_data root_reached)
open LocalizedChemicalRingJointPreparedSourceModel
open LocalizedChemicalRingJointPreparedSourceModelExistence (assignCenter_eq_sourceModel finalQuery)
open LocalizedChemicalRingJointPreparedReport (analyze mem_analyze_at_center_iff)
open LocalizedChemicalRingPreparedContextRecursion (preparedAssignCenter?)
open LocalizedChemicalRingJointMarkerOperations (jointOperations)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

/-- Independent final-root admission to a successful single-promotion reading. -/
def TransitiveSuccess (input : CertifiedLocalizedCIPInput)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (center : input.detectedMultiCenterMolecule.Center) : Prop :=
  ¬ OddBoundarySymmetry input cfg center [] [] ∧
    ∃ ligand : Fin 4, FreeAt input cfg center []
      (input.detectedMultiCenterMolecule.ligandAtomAt center ligand)

private theorem option_none_iff_no_success {α : Type} (value : Option α) :
    value = none ↔ ¬ ∃ result, value = some result := by
  cases value <;> simp

noncomputable section

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
    ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)

include agreement admissible supported single charge calibrated in
private theorem assignment_success_iff
    (center : input.detectedMultiCenterMolecule.Center)
    (transitive : PhysicalTransitive input cfg center []) :
    (∃ label, preparedAssignCenter? mol (jointOperations input mol) (inputGeometry input)
      center.1.val = some label) ↔ TransitiveSuccess input cfg center := by
  obtain ⟨data, rootAddress⟩ := root_data input mol agreement admissible supported single center
  have actual := LocalizedChemicalRingRootTransitiveClassification.descriptor_success_iff_transitive_freePoint
    input mol agreement admissible supported single charge cfg calibrated center
    (canonicalCenterRoot center.1.val) data (root_reached input mol agreement center)
    rfl rootAddress [] transitive
  exact actual

include agreement admissible supported single charge calibrated in
/-- Every physically transitive detected root has a successful actual report entry exactly
on the independent physical criterion; its refusal entry is exactly the complementary case. -/
theorem detected_report_success_refusal_iff
    (center : input.detectedMultiCenterMolecule.Center)
    (transitive : PhysicalTransitive input cfg center []) :
    ((∃ label, (center.1.val, some label) ∈ analyze input mol) ↔
      TransitiveSuccess input cfg center) ∧
    ((center.1.val, none) ∈ analyze input mol ↔ ¬ TransitiveSuccess input cfg center) := by
  have assigned := assignment_success_iff input mol agreement admissible supported single charge cfg
    calibrated center transitive
  constructor
  · simpa only [mem_analyze_at_center_iff] using assigned
  · rw [mem_analyze_at_center_iff, option_none_iff_no_success, assigned]

include agreement admissible supported single charge calibrated in
/-- The same physical criterion decides success and refusal of the unique independent source
model's final-query value. The model is constrained by its independent equations, not a label. -/
theorem sourceModel_success_refusal_iff {candidate : Profile input mol}
    (model : SourceModel input mol single candidate)
    (center : input.detectedMultiCenterMolecule.Center)
    (transitive : PhysicalTransitive input cfg center []) :
    ((∃ label, candidate (inputGeometry input) [] (finalQuery input mol agreement center) =
      some label) ↔ TransitiveSuccess input cfg center) ∧
    (candidate (inputGeometry input) [] (finalQuery input mol agreement center) = none ↔
      ¬ TransitiveSuccess input cfg center) := by
  have assigned := assignment_success_iff input mol agreement admissible supported single charge cfg
    calibrated center transitive
  rw [assignCenter_eq_sourceModel input mol agreement admissible supported single model] at assigned
  refine ⟨assigned, ?_⟩
  rw [option_none_iff_no_success, assigned]

end
end TetraStereo.OneCenter.LocalizedChemicalRingRootTransitiveReport

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRootTransitiveReport.TransitiveSuccess
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRootTransitiveReport.detected_report_success_refusal_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRootTransitiveReport.sourceModel_success_refusal_iff
