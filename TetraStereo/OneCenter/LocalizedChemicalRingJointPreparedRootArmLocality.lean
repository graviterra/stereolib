import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootBranchSelector
import TetraStereo.OneCenter.LocalizedRuleMajorDependencyLocality
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1800000

/-! Actual original-root arm locality for the concrete two-state splice. Cursor metadata,
outward reachability, occurrence-path separation and full compound-build preservation are
derived. No equality between the arbitrary layout bounds of separate retained compilations
is asserted. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootArmLocality

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedMarkedRetainedStateReader LocalizedMarkedRetainedMolecularSelection
open LocalizedMarkedRetainedOrdinaryRanking
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData referenceAt)
open LocalizedChemicalRingJointPreparedRootWitness (root_slot_data)
open LocalizedChemicalRingJointPreparedRootBranchSelector
open LocalizedChemicalRingJointPreparedCrossGeometryWitness
open LocalizedChemicalRingJointMarkerRanking (frames)
open LocalizedChemicalRingProperRotationConsensus (slot_current referenceAt_injective)
open LocalizedActualBoundaryObservationReadback
open LocalizedActualOutwardRule1bEquivalence
open LocalizedActualBoundaryPathRealization

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (single : input.moleculeGraph.SimpleBonded)
  (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
  (data : OccurrenceData input mol c node)

abbrev rootFrame (state : OccurrenceAuxState) :=
  frames input single state data.target data.real
    ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl

theorem rootFrame_eq (state : OccurrenceAuxState) :
    (rootFrame input mol single c node data state).frame = data.frame := by
  have computed := (rootFrame input mol single c node data state).frameComputed
  rw [data.frameExec] at computed
  exact (Option.some.inj computed).symm

theorem root_slot_outward (rootAddress : data.target.1.address = [])
    (state : OccurrenceAuxState) (slot : Fin 4) :
    OutwardRerootCursor input data.target
      ((rootFrame input mol single c node data state).frame.cursorAt slot) := by
  have computed := (rootFrame input mol single c node data state).frameComputed
  rw [input.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?] at computed
  exact (input.localizedOccurrenceFourLigandFrame_root_all_outward data.target
    (rootFrame input mol single c node data state).frame computed rootAddress slot).1

theorem root_slot_path (rootAddress : data.target.1.address = [])
    (state : OccurrenceAuxState) (slot : Fin 4) :
    branchPathOf input ((rootFrame input mol single c node data state).frame.cursorAt slot).occurrence =
      [referenceAt input mol c node data slot] := by
  let frame := rootFrame input mol single c node data state
  have current := slot_current input mol single c node data state slot
  obtain ⟨_, rootEq, childSlot, addressEq⟩ := root_slot_data input single _ data.target frame
    rootAddress slot _ current
  have rootNode : data.target.1.node = OfficialCIPNode.root data.target.1.root := by
    have equality := input.declarativeLocalizedOccurrence_eq_root_of_address_nil
      ((input.mem_localizedOccurrences_iff _ _).mp data.target.2) rootAddress
    exact congrArg (fun occurrence => occurrence.node) equality
  have rootCurrent : data.target.1.node.current? = some data.target.1.root := by rw [rootNode]; rfl
  have child := outwardChild_node_mem input
    (⟨data.target, none⟩ : input.LocalizedRerootCursor (retainedCarrierFuel input))
    (frame.frame.cursorAt slot) rootEq childSlot addressEq
  obtain ⟨next, nodeEq, _, _⟩ :=
    (mem_executableOfficialCIPChildren_iff input single _ rootCurrent data.real _).mp child
  have nextEq : next = referenceAt input mol c node data slot := by
    rw [nodeEq] at current
    exact Option.some.inj current
  subst next
  have history : (frame.frame.cursorAt slot).occurrence.1.node.history =
      [referenceAt input mol c node data slot, data.target.1.root] := by
    rw [nodeEq]
    change referenceAt input mol c node data slot :: data.target.1.node.history = _
    rw [rootNode]
    rfl
  change (input.molecularFrameUnit (frame.frame.cursorAt slot).occurrence.1).path = _
  simp [molecularFrameUnit, history]

theorem rootSplice_consult_left (rootAddress : data.target.1.address = [])
    (leftState rightState cursorState : OccurrenceAuxState) (left : Fin 4)
    (unit : DetectedOccurrence input.moleculeGraph)
    (consulted : input.ReachableArmDescriptorConsult data.target
      ((rootFrame input mol single c node data cursorState).frame.cursorAt left) unit) :
    rawStateDescriptorMap input
        (rootSplice input (referenceAt input mol c node data left) leftState rightState) unit =
      rawStateDescriptorMap input leftState unit := by
  rw [rootSplice_descriptorMap]
  have result := branchMosaicMap_eq_left_of_consult input
    (root_slot_outward input mol single c node data rootAddress cursorState left)
    (rawStateDescriptorMap input leftState) (rawStateDescriptorMap input rightState) unit consulted
  simpa only [root_slot_path input mol single c node data rootAddress cursorState left] using result

theorem rootSplice_consult_right (rootAddress : data.target.1.address = [])
    (leftState rightState cursorState : OccurrenceAuxState) (left right : Fin 4)
    (distinct : left ≠ right) (unit : DetectedOccurrence input.moleculeGraph)
    (consulted : input.ReachableArmDescriptorConsult data.target
      ((rootFrame input mol single c node data cursorState).frame.cursorAt right) unit) :
    rawStateDescriptorMap input
        (rootSplice input (referenceAt input mol c node data left) leftState rightState) unit =
      rawStateDescriptorMap input rightState unit := by
  rw [rootSplice_descriptorMap]
  have disjoint : ∀ path : List input.Atom,
      branchPathOf input ((rootFrame input mol single c node data cursorState).frame.cursorAt left).occurrence <+: path →
        ¬ (branchPathOf input ((rootFrame input mol single c node data cursorState).frame.cursorAt right).occurrence <+: path) := by
    rw [root_slot_path input mol single c node data rootAddress cursorState left,
      root_slot_path input mol single c node data rootAddress cursorState right]
    exact singleton_prefix_not_of_ne
      (fun equal => distinct (referenceAt_injective input mol c node data equal))
  have result := branchMosaicMap_eq_right_of_consult input
    (root_slot_outward input mol single c node data rootAddress cursorState right) disjoint
    (rawStateDescriptorMap input leftState) (rawStateDescriptorMap input rightState) unit consulted
  simpa only [root_slot_path input mol single c node data rootAddress cursorState left] using result

include single in
theorem rootSplice_compound_left (rootAddress : data.target.1.address = [])
    (leftState rightState : OccurrenceAuxState) (left : Fin 4) (fuel : Nat) :
    input.buildActualRuleMajorCompoundRule45KeyExec? data.target
        (input.molecularView (rawStateDescriptorMap input
          (rootSplice input (referenceAt input mol c node data left) leftState rightState)) data.target)
        fuel (data.frame.cursorAt left) =
      input.buildActualRuleMajorCompoundRule45KeyExec? data.target
        (input.molecularView (rawStateDescriptorMap input leftState) data.target)
        fuel (data.frame.cursorAt left) := by
  apply input.buildActualRuleMajorCompoundRule45KeyExec?_eq_of_molecularConsult
    data.target _ _ (data.frame.cursorAt left) ?_ fuel _ Relation.ReflTransGen.refl
  intro unit consulted
  apply rootSplice_consult_left input mol single c node data rootAddress
    leftState rightState leftState left unit
  simpa only [rootFrame_eq] using consulted

include single in
theorem rootSplice_compound_right (rootAddress : data.target.1.address = [])
    (leftState rightState : OccurrenceAuxState) (left right : Fin 4)
    (distinct : left ≠ right) (fuel : Nat) :
    input.buildActualRuleMajorCompoundRule45KeyExec? data.target
        (input.molecularView (rawStateDescriptorMap input
          (rootSplice input (referenceAt input mol c node data left) leftState rightState)) data.target)
        fuel (data.frame.cursorAt right) =
      input.buildActualRuleMajorCompoundRule45KeyExec? data.target
        (input.molecularView (rawStateDescriptorMap input rightState) data.target)
        fuel (data.frame.cursorAt right) := by
  apply input.buildActualRuleMajorCompoundRule45KeyExec?_eq_of_molecularConsult
    data.target _ _ (data.frame.cursorAt right) ?_ fuel _ Relation.ReflTransGen.refl
  intro unit consulted
  apply rootSplice_consult_right input mol single c node data rootAddress
    leftState rightState rightState left right distinct unit
  simpa only [rootFrame_eq] using consulted

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootArmLocality

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootArmLocality.rootFrame_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootArmLocality.root_slot_outward
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootArmLocality.root_slot_path
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootArmLocality.rootSplice_consult_left
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootArmLocality.rootSplice_consult_right
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootArmLocality.rootSplice_compound_left
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootArmLocality.rootSplice_compound_right
