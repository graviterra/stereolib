import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedActualTiePhysical
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2400000

/-! Original-root slots supply the outward source metadata required by the all-reference
ranked reconstruction. Every frame slot is an actual fresh real child; no non-root branch
hypothesis is imposed on the root. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootWitness

open CertifiedLocalizedCIPInput DeclarativeCIP RetainedCoherentSymmetry
open LocalizedMarkedRetainedCanonicalFrame LocalizedMarkedRetainedMolecularSelection
open LocalizedMarkedRetainedOrdinaryRanking (RetainedExecutionFrame)
open LocalizedMarkedRetainedStateReader LocalizedChemicalRingJointMarkerRanking
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData referenceAt)
open LocalizedChemicalRingProperRotationConsensus (slot_current referenceAt_injective)
open LocalizedChemicalRingJointSelectedTieWitness (JointMatchedSymmetry)
open LocalizedChemicalRingJointMarkerFrameExecution (slotKeys)
open LocalizedChemicalRingJointMarkerReconstructionExecution

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput)

/-- Original-root frame slots are real outward children with their exact root and address. -/
theorem root_slot_data (single : input.moleculeGraph.SimpleBonded)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (frame : RetainedExecutionFrame descriptorMap target)
    (rootAddress : target.1.address = []) (slot : Fin 4) (atom : input.Atom)
    (current : (frame.frame.cursorAt slot).occurrence.1.node.current? = some atom) :
    (frame.frame.cursorAt slot).occurrence.1.node.provenance = .realAtom ∧
    (frame.frame.cursorAt slot).occurrence.1.root = target.1.root ∧
    ∃ childSlot, (frame.frame.cursorAt slot).occurrence.1.address = target.1.address ++ [childSlot] := by
  have computed : input.localizedOccurrenceFourLigandFrame? target = some frame.frame := by
    rw [← input.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame? target]
    exact frame.frameComputed
  have present : frame.frame.cursorAt slot ∈ frame.frame.cursors :=
    List.get_mem frame.frame.cursors (Fin.cast frame.frame.length_eq.symm slot)
  have outward := input.localizedOccurrenceFourLigandFrame_cursor_mem_neighborFrames
    target frame.frame computed _ present
  rw [input.localizedRerootNeighborFrames_eq_outwardChildFrames_of_address_nil target rootAddress]
    at outward
  have targetNode : target.1.node = OfficialCIPNode.root target.1.root := by
    have equality := input.declarativeLocalizedOccurrence_eq_root_of_address_nil
      ((input.mem_localizedOccurrences_iff _ _).mp target.2) rootAddress
    have nodes := congrArg (fun occurrence => occurrence.node) equality
    simpa using nodes
  have targetCurrent : target.1.node.current? = some target.1.root := by
    rw [targetNode]
    rfl
  have targetReal : target.1.node.provenance = .realAtom := by rw [targetNode]; rfl
  obtain ⟨neighbor, childSlot, nodeEq, neighborCurrent, rootEq, addressEq, _, _, adjacent⟩ :=
    input.simpleBond_outwardFrame_extend_zero single target targetCurrent targetReal _ outward
  have neighborEq : neighbor = atom := Option.some.inj (neighborCurrent.symm.trans current)
  subst neighbor
  have fresh : atom ∉ target.1.node.history := by
    rw [targetNode]
    change atom ∉ [target.1.root]
    intro member
    have equality := List.mem_singleton.mp member
    subst atom
    simp [MoleculeGraph.Adj, input.moleculeGraph.bond_self] at adjacent
  have childReal : (frame.frame.cursorAt slot).occurrence.1.node.provenance = .realAtom := by
    rw [nodeEq, OfficialCIPNode.extend_provenance,
      OfficialCIPNode.childProvenance_real _ _ fresh]
  exact ⟨childReal, rootEq, childSlot, addressEq⟩

/-- An actual original-root joint-key tie gives the same ranked, label-matched reconstruction
used by the recursive correction proof. The runtime layout bounds and real-child data are derived. -/
theorem root_matched_of_tie (mol : RawMolecule) (single : input.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData input mol c node) (rootAddress : data.target.1.address = [])
    (state : OccurrenceAuxState) (references : List input.Atom)
    (left right : Fin 4)
    (tie : slotKeys input mol single c node data state references left =
      slotKeys input mol single c node data state references right) :
    Nonempty (JointMatchedSymmetry input single state data.target data.real
      ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl references left right
      (referenceAt input mol c node data left) (referenceAt input mol c node data right)) := by
  let frame := frames input single state data.target data.real
    ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl
  have currentL := slot_current input mol single c node data state left
  have currentR := slot_current input mol single c node data state right
  obtain ⟨realL, rootL, slotL, addressL⟩ := root_slot_data input single
    (rawStateDescriptorMap input state) data.target frame rootAddress left
    (referenceAt input mol c node data left) currentL
  obtain ⟨realR, rootR, slotR, addressR⟩ := root_slot_data input single
    (rawStateDescriptorMap input state) data.target frame rootAddress right
    (referenceAt input mol c node data right) currentR
  obtain ⟨e, rank, fixed, entry, refs, support, matched⟩ :=
    actual_outward_default_joint_tie_witness input single state data.target data.real
      ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl references left right
      (referenceAt input mol c node data left) (referenceAt input mol c node data right)
      currentL currentR realL realR rootL rootR slotL slotR addressL addressR tie charge
  exact ⟨⟨currentL, currentR, realL, realR, e, rank, fixed, entry, refs, support, matched⟩⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootWitness

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootWitness.root_slot_data
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootWitness.root_matched_of_tie
