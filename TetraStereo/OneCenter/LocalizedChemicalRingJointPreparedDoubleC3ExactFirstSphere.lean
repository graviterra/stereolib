import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactC3Separation
import TetraStereo.OneCenter.LocalizedRuleMajorSeparatedArmLocality
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactFirstSphere

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedChemicalRingDoubleC3Input
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData referenceAt)
open LocalizedChemicalRingJointMarkerFrameExecution (slotKeys)
open LocalizedChemicalRingProperRotationConsensus (slot_current)
open LocalizedMarkedRetainedPromotedRanking (frames)
open LocalizedMarkedRetainedOrdinaryRanking (rawStateKeys)
open LocalizedMarkedRetainedStateReader (rawStateDescriptorMap rawStateDescriptorMap_tetrahedral)
open LocalizedMarkedRetainedPromotedKey (ordinaryKey?)
open LocalizedChemicalRingPromotedConstitutionReadback (subtree_constitution_eq_ordinary)
open LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels
open LocalizedChemicalRingJointMarkerRanking (refinedKey)

noncomputable section

/-- Immediate atomic-number order decides the actual full key before all descriptor and
joint-marker columns, for arbitrary auxiliary state and inherited references. -/
theorem left_actual_key_lt_of_atomic_number_lt
    (c : (certified true).detectedMultiCenterMolecule.Center)
    (data : OccurrenceData (certified true) mol c leftCenter)
    (state : OccurrenceAuxState) (references : List (certified true).Atom) (i j : Fin 4)
    (lower : graph.atomZ (referenceAt (certified true) mol c leftCenter data i) <
      graph.atomZ (referenceAt (certified true) mol c leftCenter data j)) :
    slotKeys (certified true) mol single_bonded c leftCenter data state references i <
      slotKeys (certified true) mol single_bonded c leftCenter data state references j := by
  let input := certified true
  let unit : DetectedOccurrence input.moleculeGraph :=
    ⟨input.molecularFrameUnit data.target.1, data.detected⟩
  let execution := frames input single_bonded state data.target data.real unit rfl
  have ordinaryBuilt (slot : Fin 4) : ordinaryKey? input data.target
      (input.molecularView (rawStateDescriptorMap input state) data.target)
      (execution.stages slot).a.tree.source = some (execution.compounds slot) := by
    rw [(execution.stages slot).a.sourceEq]
    exact execution.compoundBuilt slot
  have head (slot : Fin 4) :
      (execution.compounds slot).prior.rule4aKey.constitutional.rule1a.head? =
        some [([], graph.atomZ (referenceAt input mol c leftCenter data slot))] := by
    have same := subtree_constitution_eq_ordinary (execution.stages slot).a.trace data.target
      (input.molecularView (rawStateDescriptorMap input state) data.target)
      (execution.compounds slot) (ordinaryBuilt slot)
    have rule1a := congrArg LocalizedConstitutionalObservable.rule1a same
    change (execution.stages slot).a.key.constitutional.rule1a =
      (execution.compounds slot).prior.rule4aKey.constitutional.rule1a at rule1a
    rw [← rule1a, actual_rule1a_head input (execution.stages slot).a.built,
      cursorRootAtomicNumber_eq_atomZ_of_current input _
        (slot_current input mol single_bonded c leftCenter data state slot)]
    rfl
  have rule1a := MoleculeGraph.officialRuleMajorKey_compare_rule1a_lt_of_heads_lt (head i) (head j) lower
  have decisive : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (execution.compounds i).prior.rule4aKey.constitutional.rule1a
      (execution.compounds j).prior.rule4aKey.constitutional.rule1a ≠ Ordering.eq := by
    rw [rule1a]
    decide
  have compared := input.compareLocalizedRerootCompoundThroughRule5_eq_rule1a_of_decisive
    (execution.compounds i) (execution.compounds j) decisive
  have full := execution.fullOrdering (rawStateDescriptorMap_tetrahedral input state)
    single_bonded unit rfl i j
  rw [compared] at full
  simp only at full
  rw [rule1a] at full
  have prior : rawStateKeys input single_bonded state data.target data.real unit rfl i <
      rawStateKeys input single_bonded state data.target data.real unit rfl j :=
    (completeLigandRule5Key_compare_lt_iff _ _).mp full.symm
  change Prod.Lex (· < ·) (· < ·) _ _
  exact Prod.Lex.left _ _ prior

/-- Oxygen 4 outranks each boron arm in the actual full key. -/
theorem left_boron_lt_oxygen
    (c : (certified true).detectedMultiCenterMolecule.Center)
    (data : OccurrenceData (certified true) mol c leftCenter)
    (state : OccurrenceAuxState) (references : List (certified true).Atom) (iO iB : Fin 4)
    (atO : referenceAt (certified true) mol c leftCenter data iO = (4 : Fin 25))
    (atB : referenceAt (certified true) mol c leftCenter data iB = (5 : Fin 25) ∨
      referenceAt (certified true) mol c leftCenter data iB = (6 : Fin 25) ∨
      referenceAt (certified true) mol c leftCenter data iB = (7 : Fin 25)) :
    slotKeys (certified true) mol single_bonded c leftCenter data state references iB <
      slotKeys (certified true) mol single_bonded c leftCenter data state references iO := by
  apply left_actual_key_lt_of_atomic_number_lt c data state references iB iO
  rw [atO]
  rcases atB with h | h | h <;> rw [h] <;> decide

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactFirstSphere

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactFirstSphere.left_actual_key_lt_of_atomic_number_lt
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDoubleC3ExactFirstSphere.left_boron_lt_oxygen
