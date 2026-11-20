import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactC3Covariance
import TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Actual full-key ties cannot erase the oxygen/boron first-sphere distinction.
The key's constitutional head is recovered from the accepted actual staged builds. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactC3Separation

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedChemicalRingDoubleC3Input LocalizedChemicalRingDoubleC3Physical
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData referenceAt)
open LocalizedChemicalRingJointMarkerFrameExecution (slotKeys)
open LocalizedChemicalRingJointSelectedTieWitness (joint_refined_tie_constitutional)
open LocalizedChemicalRingProperRotationConsensus (slot_current referenceAt_injective)
open LocalizedMarkedRetainedPromotedRanking (frames)
open LocalizedMarkedRetainedMolecularSelection (retainedCarrierFuel)
open LocalizedChemicalRingJointPreparedDoubleC3ExactC3Covariance
open LocalizedChemicalRingJointPreparedExecution (keys)
open LocalizedGenericMarkedRecalculation (Geometry)
open LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels

noncomputable section

/-- Actual B-arm keys are equal along the threefold cycle. The hypotheses identify frame
slots by their atoms, rather than supplying comparisons or labels. -/
theorem left_boron_keys_equal
    (c : (certified true).detectedMultiCenterMolecule.Center)
    (data : OccurrenceData (certified true) mol c leftCenter)
    (depth : Nat) (geom : Geometry) (i5 i6 i7 : Fin 4)
    (at5 : referenceAt (certified true) mol c leftCenter data i5 = (5 : Fin 25))
    (at6 : referenceAt (certified true) mol c leftCenter data i6 = (6 : Fin 25))
    (at7 : referenceAt (certified true) mol c leftCenter data i7 = (7 : Fin 25)) :
    keys (certified true) mol single_bonded c leftCenter data depth geom [] i5 =
      keys (certified true) mol single_bonded c leftCenter data depth geom [] i6 ∧
    keys (certified true) mol single_bonded c leftCenter data depth geom [] i6 =
      keys (certified true) mol single_bonded c leftCenter data depth geom [] i7 := by
  obtain ⟨p, action, invariant⟩ := left_actual_keys_rotation c data depth geom
  have p5 : p i5 = i6 := by
    apply referenceAt_injective (certified true) mol c leftCenter data
    rw [action, at5, at6]
    rfl
  have p6 : p i6 = i7 := by
    apply referenceAt_injective (certified true) mol c leftCenter data
    rw [action, at6, at7]
    rfl
  constructor
  · have h := invariant i5
    rw [p5] at h
    exact h.symm
  · have h := invariant i6
    rw [p6] at h
    exact h.symm


/-- Unequal immediate atomic numbers separate actual full keys, independently of every
inherited reference and every supplied/generated auxiliary state. -/
theorem left_actual_keys_ne_of_atomic_number_ne
    (c : (certified true).detectedMultiCenterMolecule.Center)
    (data : OccurrenceData (certified true) mol c leftCenter)
    (state : OccurrenceAuxState) (references : List (certified true).Atom) (i j : Fin 4)
    (different : graph.atomZ (referenceAt (certified true) mol c leftCenter data i) ≠
      graph.atomZ (referenceAt (certified true) mol c leftCenter data j)) :
    slotKeys (certified true) mol single_bonded c leftCenter data state references i ≠
      slotKeys (certified true) mol single_bonded c leftCenter data state references j := by
  intro tie
  let input := certified true
  let unit : DetectedOccurrence input.moleculeGraph :=
    ⟨input.molecularFrameUnit data.target.1, data.detected⟩
  let execution := frames input single_bonded state data.target data.real unit rfl
  have constitutional := joint_refined_tie_constitutional input single_bonded state data.target
    data.real unit rfl references (retainedCarrierFuel input)
    (2 * (retainedCarrierFuel input + 1)) i j tie
  have columns := (officialRuleMajorKey_compare_eq_iff _ _).mp constitutional
  have z := actual_rule1a_tie_rootAtomicNumber_eq input
    (execution.stages i).a.built (execution.stages j).a.built
    ((compareSparseLayers_compareNat_eq_iff _ _).mpr columns.1)
  rw [cursorRootAtomicNumber_eq_atomZ_of_current input _
    (slot_current input mol single_bonded c leftCenter data state i),
    cursorRootAtomicNumber_eq_atomZ_of_current input _
    (slot_current input mol single_bonded c leftCenter data state j)] at z
  exact different z

/-- The actual oxygen slot is separated from every actual boron slot. -/
theorem left_oxygen_boron_keys_ne
    (c : (certified true).detectedMultiCenterMolecule.Center)
    (data : OccurrenceData (certified true) mol c leftCenter)
    (state : OccurrenceAuxState) (references : List (certified true).Atom) (iO iB : Fin 4)
    (atO : referenceAt (certified true) mol c leftCenter data iO = (4 : Fin 25))
    (atB : referenceAt (certified true) mol c leftCenter data iB = (5 : Fin 25) ∨
      referenceAt (certified true) mol c leftCenter data iB = (6 : Fin 25) ∨
      referenceAt (certified true) mol c leftCenter data iB = (7 : Fin 25)) :
    slotKeys (certified true) mol single_bonded c leftCenter data state references iO ≠
      slotKeys (certified true) mol single_bonded c leftCenter data state references iB := by
  apply left_actual_keys_ne_of_atomic_number_ne c data state references iO iB
  rw [atO]
  rcases atB with h | h | h <;> rw [h] <;> decide

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactC3Separation

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactC3Separation.left_boron_keys_equal

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactC3Separation.left_actual_keys_ne_of_atomic_number_ne
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactC3Separation.left_oxygen_boron_keys_ne
