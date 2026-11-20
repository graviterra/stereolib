import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactLeftDescriptor
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRightFlip
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootOrder
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootState
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootFacts
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceModelExistence
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Exact DoubleC3 root letter from generated local descriptors and actual root priorities.
The two auxiliary facts are derived from execution, not supplied. The previously proved physical
lowercase result determines casing; the actual original-side readback determines its letter. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootFinal

open LocalizedChemicalRingDoubleC3Input
open LocalizedChemicalRingJointPreparedDoubleC3ExactCarrier (input)
open LocalizedChemicalRingJointPreparedDoubleC3ExactLeftDescriptor (left_descriptor)
open LocalizedChemicalRingJointPreparedDoubleC3ExactRightFlip (right_descriptor_flip)
open LocalizedChemicalRingJointPreparedDoubleC3ExactRootOrder (context_order_twoFacts)
open LocalizedChemicalRingJointPreparedDoubleC3ExactRootOrderPin (twoFacts)
open LocalizedChemicalRingJointPreparedDoubleC3ExactRootState (root_prepared_children_eq_local)
open LocalizedChemicalRingJointPreparedDoubleC3ExactGeometry (root_left_before_right_reading)
open LocalizedChemicalRingJointPreparedDoubleC3Pseudo (root_pseudo)
open LocalizedChemicalRingDoubleC3Domain (detectedRoot)
open LocalizedChemicalRingPreparedContextRecursion
open LocalizedChemicalRingJointMarkerOperations (jointOperations)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedChemicalRingOrientationReadback (flipDescriptorBy flipDescriptor)
open LocalizedGenericMarkedRecalculation
  (Geometry structuralDepth readback? mirror caseFromMirror? appendFacts? factOf)
open LocalizedChemicalRingJointPreparedReport (analyze mem_analyze_at_center_iff)
open LocalizedChemicalRingJointPreparedSourceModel (Profile SourceModel)
open LocalizedChemicalRingJointPreparedSourceModelExistence
  (finalQuery assignCenter_eq_sourceModel existsUnique_sourceModel)

noncomputable section

theorem right_descriptor (depth : Nat) :
    preparedDescriptor? mol (jointOperations input mol) depth (inputGeometry input) [] [] rightCenter =
      some (.chiral .S) :=
  LocalizedChemicalRingJointPreparedDoubleC3ExactRootFacts.right_descriptor depth

abbrev rootUnder (geom : Geometry) :=
  childrenUnder mol (preparedFacts mol (jointOperations input mol) (structuralDepth mol root))
    geom [] root

/-- The literal two-fact state is the actual generated state at the final root. -/
theorem actual_root_facts : rootUnder (inputGeometry input) [] = twoFacts :=
  LocalizedChemicalRingJointPreparedDoubleC3ExactRootFacts.actual_root_facts

/-- Exact original-side root readback under its own generated evidence. -/
theorem root_original_step :
    rawStepPrepared? (jointOperations input mol) mol (inputGeometry input) [] [] root
      (rootUnder (inputGeometry input)) = some .S := by
  have appended : appendFacts? [] (rootUnder (inputGeometry input) []) = some twoFacts := by
    rw [actual_root_facts]
    decide +kernel
  have actual := rawStepPrepared?_strict_uses_prepared (jointOperations input mol) mol
    (inputGeometry input) [] [] root (rootUnder (inputGeometry input))
    [1, 2, 4, 15] [1, 2, 3, 0] [some .gt, some .gt, some .gt] twoFacts
    raw_frames.1 appended context_order_twoFacts (by decide) (by decide) (by decide)
  change rawStepPrepared? (jointOperations input mol) mol (inputGeometry input) [] [] root
      (rootUnder (inputGeometry input)) =
    readback? (inputGeometry input) [2, 4, 15, 1] at actual
  exact actual.trans root_left_before_right_reading

private theorem pseudo_of_first_S (second : Option RS)
    (pseudo : ∃ value, caseFromMirror? (some .S) second = some (.pseudoasymmetric value)) :
    caseFromMirror? (some .S) second = some (.pseudoasymmetric .s) := by
  cases second with
  | none => obtain ⟨value, impossible⟩ := pseudo; cases impossible
  | some second =>
    cases second with
    | R => obtain ⟨value, impossible⟩ := pseudo; cases impossible
    | S => rfl

/-- Exact lowercase s at the actual final root; no auxiliary label or output is assumed. -/
theorem root_exact_s :
    preparedAssignCenter? mol (jointOperations input mol) (inputGeometry input) 0 =
      some (.pseudoasymmetric .s) := by
  have physical := root_pseudo
  change ∃ value, caseFromMirror?
      (rawStepPrepared? (jointOperations input mol) mol (inputGeometry input) [] [] root
        (rootUnder (inputGeometry input)))
      (rawStepPrepared? (jointOperations input mol) mol (mirror (inputGeometry input)) [] [] root
        (rootUnder (mirror (inputGeometry input)))) = some (.pseudoasymmetric value) at physical
  rw [root_original_step] at physical
  change caseFromMirror?
      (rawStepPrepared? (jointOperations input mol) mol (inputGeometry input) [] [] root
        (rootUnder (inputGeometry input)))
      (rawStepPrepared? (jointOperations input mol) mol (mirror (inputGeometry input)) [] [] root
        (rootUnder (mirror (inputGeometry input)))) = some (.pseudoasymmetric .s)
  rw [root_original_step]
  exact pseudo_of_first_S _ physical

theorem actual_report_root_s : (0, some (.pseudoasymmetric .s)) ∈ analyze input mol :=
  (mem_analyze_at_center_iff input mol detectedRoot _).mpr root_exact_s

/-- Every independent source model has the same exact final root value. -/
theorem source_root_s {candidate : Profile input mol}
    (model : SourceModel input mol single_bonded candidate) :
    candidate (inputGeometry input) [] (finalQuery input mol (structure_agreement true) detectedRoot) =
      some (.pseudoasymmetric .s) := by
  rw [← assignCenter_eq_sourceModel input mol (structure_agreement true) admissible supported
    single_bonded model]
  exact root_exact_s

/-- Inhabited unique independent source profile, with its exact root s value. -/
theorem existsUnique_source_root_s :
    ∃! candidate : Profile input mol,
      SourceModel input mol single_bonded candidate ∧
      candidate (inputGeometry input) []
        (finalQuery input mol (structure_agreement true) detectedRoot) =
          some (.pseudoasymmetric .s) := by
  obtain ⟨candidate, model, unique⟩ := existsUnique_sourceModel input mol
    (structure_agreement true) admissible supported single_bonded
  exact ⟨candidate, ⟨model, source_root_s model⟩, fun other satisfied => unique other satisfied.1⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootFinal

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootFinal.right_descriptor
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootFinal.actual_root_facts
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootFinal.root_original_step
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootFinal.root_exact_s
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootFinal.actual_report_root_s
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootFinal.source_root_s
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactRootFinal.existsUnique_source_root_s
