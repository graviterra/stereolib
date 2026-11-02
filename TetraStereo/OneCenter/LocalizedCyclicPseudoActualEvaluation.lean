import TetraStereo.OneCenter.LocalizedCyclicPseudoRootLetter
import TetraStereo.OneCenter.LocalizedCyclicPseudoRootComponentEvaluation
import TetraStereo.OneCenter.LocalizedRootwardSeparatedArmBridge
import TetraStereo.OneCenter.LocalizedCyclicContextFrameCompilation
import TetraStereo.OneCenter.LocalizedRetainedContextAllOccurrences
import TetraStereo.OneCenter.LocalizedRuleMajorReferencePipeline
import TetraStereo.OneCenter.LocalizedSimpleBondFourLigandFrames
import TetraStereo.OneCenter.LocalizedOutwardDecoratedSourceFaithfulness
import TetraStereo.OneCenter.LocalizedTrackedSortSourcePairFidelity
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 8192

/-!
Actual rule-major evaluation of the frozen nine-atom cyclic pseudo candidate.

One-step official keys are not used as adequate-fuel stage keys. Each real
carrier path under root 0 is compiled by `cyclicContextFrameCompilation`, and
its label is the fixed point of `ruleMajorDescriptor?`.
-/

namespace TetraStereo.OneCenter.LocalizedCyclicPseudoActualEvaluation

open TetraStereo.OneCenter
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.OneCenter.LocalizedRuleMajorReference
open TetraStereo.OneCenter.DeclarativeCIP
open TetraStereo.OneCenter.LocalizedCyclicPseudoInputWitness
open TetraStereo.OneCenter.LocalizedCyclicPseudoSpatialWitness
open TetraStereo.OneCenter.LocalizedCyclicPseudoGeneratedLabels
open TetraStereo.OneCenter.LocalizedCyclicPseudoRootLetter
open TetraStereo.OneCenter.MoleculeGraph
open TetraStereo.OneCenter.OfficialCIPNode
open TetraStereo.OneCenter.CartesianPoint3

noncomputable section
open scoped Classical

def pseudoReference : LocalizedRuleMajorReference.Input where
  certified := pseudoSpatialCertified

theorem carrierFuel_eq :
    carrierFuel pseudoReference =
      pseudoSpatialCertified.certified.input.molecule.atomCount + 1 := rfl

private theorem spatial_atomCount :
    pseudoSpatialCertified.certified.input.molecule.atomCount = 9 := by
  have moleculeEq : pseudoSpatialCertified.certified.input.molecule = pseudoSource.molecule := by
    rw [show pseudoSpatialCertified.certified.input = pseudoSpatialSource from rfl, spatial_molecule]
  rw [moleculeEq]
  exact atomCount_eq

private def SA (i : Fin 9) : pseudoSpatialCertified.Atom :=
  ⟨i.val, by rw [spatial_atomCount]; exact i.isLt⟩

private theorem SA_val (i : Fin 9) : (SA i).val = i.val := rfl

private theorem SA_eq (i : Fin 9) : SA i = i := by
  apply Fin.ext
  simp [SA_val]

private theorem spatial_z (i : Fin 9) :
    pseudoSpatialCertified.moleculeGraph.atomZ (SA i) = graph.atomZ i := by
  rw [SA_eq]
  simp [CertifiedLocalizedCIPInput.moleculeGraph, pseudoSpatialCertified,
    pseudoSpatialCertifiedAuthority, spatial_molecule, graph, pseudoCertified,
    pseudoCertifiedAuthority]

private theorem spatial_adj (i j : Fin 9) :
    pseudoSpatialCertified.moleculeGraph.Adj (SA i) (SA j) ↔ graph.Adj i j := by
  rw [SA_eq, SA_eq]
  simp [MoleculeGraph.Adj, CertifiedLocalizedCIPInput.moleculeGraph, pseudoSpatialCertified,
    pseudoSpatialCertifiedAuthority, spatial_molecule, graph, pseudoCertified,
    pseudoCertifiedAuthority]

theorem spatial_simpleBonded : pseudoSpatialCertified.moleculeGraph.SimpleBonded := by
  intro left right adjacent
  have leftEq : left = SA ⟨left.val, by rw [← spatial_atomCount]; exact left.isLt⟩ := Fin.ext rfl
  have rightEq : right = SA ⟨right.val, by rw [← spatial_atomCount]; exact right.isLt⟩ :=
    Fin.ext rfl
  rw [leftEq, rightEq, spatial_adj] at adjacent
  exact simple_bonded _ _ adjacent

private theorem detected_card (i : Fin 9)
    (degree : (graph.neighborFinset i).card = 4) :
    (pseudoSpatialCertified.moleculeGraph.neighborFinset (SA i)).card = 4 := by
  rw [SA_eq]
  simp [MoleculeGraph.neighborFinset, CertifiedLocalizedCIPInput.moleculeGraph,
    pseudoSpatialCertified, pseudoSpatialCertifiedAuthority, spatial_molecule]
  exact degree

private theorem center_membership (i : Fin 9) (member : i ∈ graph.tetrahedralCenterSet) :
    SA i ∈ pseudoSpatialCertified.tetrahedralCenterSet := by
  rw [SA_eq]
  simpa [CertifiedLocalizedCIPInput.tetrahedralCenterSet, pseudoSpatialCertified,
    pseudoSpatialCertifiedAuthority, spatial_molecule] using member

def rootTetra : pseudoSpatialCertified.TetrahedralCenter :=
  ⟨SA ⟨0, by decide⟩, center_membership ⟨0, by decide⟩ ((degree_four_iff 0).mpr (Or.inl rfl))⟩

def armTetra : pseudoSpatialCertified.TetrahedralCenter :=
  ⟨SA ⟨2, by decide⟩,
    center_membership ⟨2, by decide⟩ ((degree_four_iff 2).mpr (Or.inr (Or.inl rfl)))⟩

def closingTetra : pseudoSpatialCertified.TetrahedralCenter :=
  ⟨SA ⟨4, by decide⟩,
    center_membership ⟨4, by decide⟩ ((degree_four_iff 4).mpr (Or.inr (Or.inr rfl)))⟩

abbrev rootTarget : Occurrence pseudoReference :=
  pseudoSpatialCertified.localizedFinalOccurrenceExecutable
    (carrierFuel pseudoReference) rootTetra

theorem root_provenance_real :
    rootTarget.1.node.provenance = OfficialCIPNodeProvenance.realAtom :=
  finalOccurrence_provenance_real pseudoReference rootTetra

abbrev rootFrames : ContextFrameCompilation pseudoReference rootTarget
    (finalCenterUnit pseudoReference rootTetra)
    (finalOccurrence_molecularFrameUnit pseudoReference rootTetra) :=
  cyclicContextFrameCompilation pseudoReference spatial_simpleBonded rootTarget
    root_provenance_real (finalCenterUnit pseudoReference rootTetra)
    (finalOccurrence_molecularFrameUnit pseudoReference rootTetra)

private theorem root_center : rootFrames.center.1 =
    LocalizedCyclicPseudoRootComponentEvaluation.SA ⟨0, by decide⟩ := by
  rw [rootFrames.centerEq]
  simp [finalCenterUnit, OccurrenceUnit.atom, rootTetra,
    LocalizedCyclicPseudoRootComponentEvaluation.SA, SA]

private theorem root_slot (index : Fin 9)
    (adjacent : graph.Adj ⟨0, by decide⟩ index) :
    ∃ slot : Fin 4, rootFrames.actualLigandAtoms slot = SA index := by
  have adjacentCenter : pseudoSpatialCertified.moleculeGraph.Adj rootFrames.center.1
      (SA index) := by
    rw [root_center]
    exact (spatial_adj ⟨0, by decide⟩ index).mpr adjacent
  obtain ⟨i, atomEq⟩ :=
    pseudoSpatialCertified.detectedMultiCenterMolecule.ligandAtomAt_surjective
      rootFrames.center (SA index) adjacentCenter
  refine ⟨rootFrames.detectedLigandPermutation.symm i, ?_⟩
  unfold pseudoReference
  simp [ContextFrameCompilation.actualLigandAtoms, Equiv.apply_symm_apply, atomEq]

private theorem root_frame_computed :
    pseudoSpatialCertified.localizedOccurrenceFourLigandFrame? rootTarget =
      some rootFrames.frame := by
  unfold pseudoReference
  rw [← pseudoSpatialCertified.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?
    rootTarget]
  exact rootFrames.frameComputed

private theorem fuel_enough :
    pseudoSpatialCertified.certified.input.molecule.atomCount ≤ carrierFuel pseudoReference := by
  rw [carrierFuel_eq]
  exact Nat.le_succ _

private theorem root_node : rootTarget.1.node = OfficialCIPNode.root rootTetra.1 := by
  simp [rootTarget, localizedFinalOccurrenceExecutable, localizedFinalRootFrame]

private theorem root_current : rootTarget.1.node.current? = some rootTetra.1 := by
  simp [OfficialCIPNode.root]

private theorem root_history : rootTarget.1.node.history = [rootTetra.1] := by
  simp [OfficialCIPNode.root]

private theorem root_address : rootTarget.1.address = [] := by
  simp [rootTarget, localizedFinalOccurrenceExecutable, localizedFinalRootFrame]

private theorem rootFrame_eq_component_root :
    rootTarget.1 = LocalizedCyclicPseudoRootComponentEvaluation.rootF := by
  apply LocalizedCIPOccurrenceFrame.ext
  · simp [rootTarget, localizedFinalOccurrenceExecutable, localizedFinalRootFrame,
      rootTetra, LocalizedCyclicPseudoRootComponentEvaluation.rootF,
      LocalizedCyclicPseudoRootComponentEvaluation.SA, SA]
  · exact root_address
  · rw [root_node]
    rfl
  · have grade := pseudoSpatialCertified.localizedCIPOccurrence_depthGrade
      (fuel := carrierFuel pseudoReference) rootTarget
    rw [root_address] at grade
    simp [LocalizedCyclicPseudoRootComponentEvaluation.rootF,
      LocalizedCyclicPseudoRootComponentEvaluation.Fuel,
      LocalizedCyclicPseudoRootComponentEvaluation.fuel_eq,
      carrierFuel_eq, spatial_atomCount] at grade ⊢


private theorem root_cursor_present (slot : Fin 4) :
    rootFrames.frame.cursorAt slot ∈ rootFrames.frame.cursors := by
  rw [LocalizedOccurrenceFourLigandFrame.cursorAt]
  exact List.get_mem rootFrames.frame.cursors
    (Fin.cast rootFrames.frame.length_eq.symm slot)

private theorem root_cursor_mem_component_neighbors (slot : Fin 4) :
    (rootFrames.frame.cursorAt slot).occurrence.1 ∈
      [LocalizedCyclicPseudoRootComponentEvaluation.rootFluorineF,
        LocalizedCyclicPseudoRootComponentEvaluation.armF,
        LocalizedCyclicPseudoRootComponentEvaluation.closeF,
        LocalizedCyclicPseudoRootComponentEvaluation.rootHydrogenF] := by
  have mapped := pseudoSpatialCertified.localizedOccurrenceFourLigandFrame_cursors_map_eq_neighborFrames
    rootTarget rootFrames.frame root_frame_computed
  have member : (rootFrames.frame.cursorAt slot).occurrence.1 ∈
      pseudoSpatialCertified.localizedRerootNeighborFrames
        (fuel := carrierFuel pseudoReference) rootTarget.1 := by
    rw [← mapped]
    exact List.mem_map.mpr ⟨rootFrames.frame.cursorAt slot,
      root_cursor_present slot, rfl⟩
  have rootZero : rootTarget.1.root =
      LocalizedCyclicPseudoRootComponentEvaluation.SA 0 := by
    have roots := congrArg
      (fun f : pseudoSpatialCertified.LocalizedCIPOccurrenceFrame => f.root)
      rootFrame_eq_component_root
    simpa [LocalizedCyclicPseudoRootComponentEvaluation.rootF,
      LocalizedCyclicPseudoRootComponentEvaluation.SA, SA] using roots
  rw [LocalizedCyclicPseudoRootComponentEvaluation.neighborFrames_eq0
      rootTarget.1 rootZero] at member
  rw [rootFrame_eq_component_root,
    LocalizedCyclicPseudoRootComponentEvaluation.rootNeighborFrames_eq] at member
  exact member

theorem root_cursor_eq_component
    (slot : Fin 4)
    (candidate : LocalizedCyclicPseudoRootComponentEvaluation.Frame)
    (sameCurrent : (rootFrames.frame.cursorAt slot).occurrence.1.node.current? =
      candidate.node.current?)
    (candidateMem : candidate ∈
      [LocalizedCyclicPseudoRootComponentEvaluation.rootFluorineF,
        LocalizedCyclicPseudoRootComponentEvaluation.armF,
        LocalizedCyclicPseudoRootComponentEvaluation.closeF,
        LocalizedCyclicPseudoRootComponentEvaluation.rootHydrogenF]) :
    (rootFrames.frame.cursorAt slot).occurrence.1 = candidate := by
  have nodup :
      ([LocalizedCyclicPseudoRootComponentEvaluation.rootFluorineF,
        LocalizedCyclicPseudoRootComponentEvaluation.armF,
        LocalizedCyclicPseudoRootComponentEvaluation.closeF,
        LocalizedCyclicPseudoRootComponentEvaluation.rootHydrogenF].map
        (fun f => f.node.current?)).Nodup := by
    decide
  exact List.inj_on_of_nodup_map nodup
    (root_cursor_mem_component_neighbors slot) candidateMem sameCurrent


noncomputable def rootFluorineSlot : Fin 4 :=
  Classical.choose (root_slot ⟨1, by decide⟩ ((adj_root 1).mpr (by simp)))
theorem rootFluorineSlot_atom :
    rootFrames.actualLigandAtoms rootFluorineSlot = SA ⟨1, by decide⟩ :=
  Classical.choose_spec (root_slot ⟨1, by decide⟩ ((adj_root 1).mpr (by simp)))

noncomputable def rootArmSlot : Fin 4 :=
  Classical.choose (root_slot ⟨2, by decide⟩ ((adj_root 2).mpr (by simp)))
theorem rootArmSlot_atom :
    rootFrames.actualLigandAtoms rootArmSlot = SA ⟨2, by decide⟩ :=
  Classical.choose_spec (root_slot ⟨2, by decide⟩ ((adj_root 2).mpr (by simp)))

noncomputable def rootClosingSlot : Fin 4 :=
  Classical.choose (root_slot ⟨4, by decide⟩ ((adj_root 4).mpr (by simp)))
theorem rootClosingSlot_atom :
    rootFrames.actualLigandAtoms rootClosingSlot = SA ⟨4, by decide⟩ :=
  Classical.choose_spec (root_slot ⟨4, by decide⟩ ((adj_root 4).mpr (by simp)))

noncomputable def rootHydrogenSlot : Fin 4 :=
  Classical.choose (root_slot ⟨5, by decide⟩ ((adj_root 5).mpr (by simp)))
theorem rootHydrogenSlot_atom :
    rootFrames.actualLigandAtoms rootHydrogenSlot = SA ⟨5, by decide⟩ :=
  Classical.choose_spec (root_slot ⟨5, by decide⟩ ((adj_root 5).mpr (by simp)))

private theorem root_parent_none : rootTarget.1.node.parent? = none := by
  simp [OfficialCIPNode.root, OfficialCIPNode.parent?]

private theorem fresh_on_root (i : Fin 9) (neZero : i ≠ 0) :
    SA i ∉ rootTarget.1.node.history := by
  simp [OfficialCIPNode.root, rootTetra]
  intro eq
  exact neZero (Fin.ext (by simpa [SA_val] using congrArg Fin.val eq))

private theorem graph_card_four (i : Fin 9) (member : i ∈ graph.tetrahedralCenterSet) :
    (graph.neighborFinset i).card = 4 := by
  rw [mem_tetrahedralCenterSet, isTetrahedralCenter_iff_neighborFinset_card] at member
  exact member

private theorem detected_atom (i : Fin 9) (member : i ∈ graph.tetrahedralCenterSet) :
    IsDetectedCenter pseudoSpatialCertified.moleculeGraph (SA i) := by
  rw [IsDetectedCenter]
  exact detected_card i (graph_card_four i member)

/-- One outward real child of a real carrier occurrence, packaged with its frame equations. -/
private structure OutwardChild
    (target : Occurrence pseudoReference) (atom : pseudoSpatialCertified.Atom) where
  frame : pseudoSpatialCertified.LocalizedCIPOccurrenceFrame
  slot : Nat
  addressEq : frame.address = target.1.address ++ [slot]
  sameRoot : frame.root = target.1.root
  currentEq : frame.node.current? = some atom
  nodeEq : frame.node = target.1.node.extend atom 0
  present : frame ∈ pseudoSpatialCertified.localizedOccurrences (carrierFuel pseudoReference)
  outward : frame ∈ pseudoSpatialCertified.localizedCarrierOutwardChildFrames
    (fuel := carrierFuel pseudoReference) target.1

private noncomputable def outwardChild
    (target : Occurrence pseudoReference) (center child : Fin 9)
    (current : target.1.node.current? = some (SA center))
    (adjacent : graph.Adj center child)
    (notParent : target.1.node.parent? ≠ some (SA child))
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom) : OutwardChild target (SA child) := by
  let found := pseudoSpatialCertified.realCenter_outwardChildFrame_of_notParent fuel_enough target
    current ((spatial_adj center child).mpr adjacent) notParent real
  let frame := Classical.choose found
  have spec := Classical.choose_spec found
  let slot := Classical.choose spec
  have rest := Classical.choose_spec spec
  exact ⟨frame, slot, rest.1, rest.2.1, rest.2.2.1, rest.2.2.2.1, rest.2.2.2.2.1, rest.2.2.2.2.2⟩

private theorem outward_real
    {target : Occurrence pseudoReference} {atom : pseudoSpatialCertified.Atom}
    (child : OutwardChild target atom)
    (fresh : atom ∉ target.1.node.history) :
    child.frame.node.provenance = OfficialCIPNodeProvenance.realAtom := by
  rw [child.nodeEq, OfficialCIPNode.extend, OfficialCIPNode.childProvenance]
  simp [fresh]

private theorem outward_unit
    {target : Occurrence pseudoReference} {atom : pseudoSpatialCertified.Atom}
    (child : OutwardChild target atom)
    (history : target.1.node.history = [target.1.root]) :
    pseudoSpatialCertified.molecularFrameUnit child.frame =
      ⟨target.1.root, [atom]⟩ := by
  unfold molecularFrameUnit
  rw [child.nodeEq, child.sameRoot, OfficialCIPNode.extend, history]
  simp

private noncomputable def directArmChild : OutwardChild rootTarget (SA ⟨2, by decide⟩) :=
  outwardChild rootTarget ⟨0, by decide⟩ ⟨2, by decide⟩ root_current
    ((adj_root 2).mpr (by simp)) (by simp [OfficialCIPNode.root, OfficialCIPNode.parent?])
    root_provenance_real

private noncomputable def directClosingChild : OutwardChild rootTarget (SA ⟨4, by decide⟩) :=
  outwardChild rootTarget ⟨0, by decide⟩ ⟨4, by decide⟩ root_current
    ((adj_root 4).mpr (by simp)) (by simp [OfficialCIPNode.root, OfficialCIPNode.parent?])
    root_provenance_real

private theorem directArm_real :
    directArmChild.frame.node.provenance = OfficialCIPNodeProvenance.realAtom :=
  outward_real directArmChild (fresh_on_root ⟨2, by decide⟩ (by decide))

private theorem directClosing_real :
    directClosingChild.frame.node.provenance = OfficialCIPNodeProvenance.realAtom :=
  outward_real directClosingChild (fresh_on_root ⟨4, by decide⟩ (by decide))

private theorem directArm_frameUnit :
    pseudoSpatialCertified.molecularFrameUnit directArmChild.frame =
      ⟨rootTarget.1.root, [SA ⟨2, by decide⟩]⟩ :=
  outward_unit directArmChild root_history

private theorem directClosing_frameUnit :
    pseudoSpatialCertified.molecularFrameUnit directClosingChild.frame =
      ⟨rootTarget.1.root, [SA ⟨4, by decide⟩]⟩ :=
  outward_unit directClosingChild root_history

def directArmUnit : DetectedOccurrence pseudoSpatialCertified.moleculeGraph :=
  ⟨⟨rootTetra.1, [armTetra.1]⟩,
    by
      simpa [OccurrenceUnit.atom, rootTetra, armTetra] using
        detected_atom ⟨2, by decide⟩ ((degree_four_iff 2).mpr (Or.inr (Or.inl rfl)))⟩

def directClosingUnit : DetectedOccurrence pseudoSpatialCertified.moleculeGraph :=
  ⟨⟨rootTetra.1, [closingTetra.1]⟩,
    by
      simpa [OccurrenceUnit.atom, rootTetra, closingTetra] using
        detected_atom ⟨4, by decide⟩ ((degree_four_iff 4).mpr (Or.inr (Or.inr rfl)))⟩

private theorem directArm_targetRoot : rootTarget.1.root = rootTetra.1 := by
  simp [rootTarget, localizedFinalOccurrenceExecutable, localizedFinalRootFrame]

private theorem directArm_unitEq :
    pseudoSpatialCertified.molecularFrameUnit directArmChild.frame = directArmUnit.1 := by
  rw [directArm_frameUnit, directArm_targetRoot]
  rfl

private theorem directClosing_unitEq :
    pseudoSpatialCertified.molecularFrameUnit directClosingChild.frame = directClosingUnit.1 := by
  rw [directClosing_frameUnit, directArm_targetRoot]
  rfl

private theorem component_root_children :
    LocalizedCyclicPseudoRootComponentEvaluation.Input.executableOfficialCIPChildren
      LocalizedCyclicPseudoRootComponentEvaluation.rootNode =
      [LocalizedCyclicPseudoRootComponentEvaluation.rootNode.extend (SA 1) 0,
       LocalizedCyclicPseudoRootComponentEvaluation.rootNode.extend (SA 2) 0,
       LocalizedCyclicPseudoRootComponentEvaluation.rootNode.extend (SA 4) 0,
       LocalizedCyclicPseudoRootComponentEvaluation.rootNode.extend (SA 5) 0] := by
  rw [LocalizedCyclicPseudoRootComponentEvaluation.children_eq]
  decide

private theorem component_arm_children :
    LocalizedCyclicPseudoRootComponentEvaluation.Input.executableOfficialCIPChildren
      LocalizedCyclicPseudoRootComponentEvaluation.node2 =
      [LocalizedCyclicPseudoRootComponentEvaluation.node2.extend (SA 3) 0,
       LocalizedCyclicPseudoRootComponentEvaluation.node2.extend (SA 4) 0,
       LocalizedCyclicPseudoRootComponentEvaluation.node2.extend (SA 6) 0] := by
  rw [LocalizedCyclicPseudoRootComponentEvaluation.children_eq]
  decide

private theorem component_close_children :
    LocalizedCyclicPseudoRootComponentEvaluation.Input.executableOfficialCIPChildren
      LocalizedCyclicPseudoRootComponentEvaluation.node4 =
      [LocalizedCyclicPseudoRootComponentEvaluation.node4.extend (SA 2) 0,
       LocalizedCyclicPseudoRootComponentEvaluation.node4.extend (SA 7) 0,
       LocalizedCyclicPseudoRootComponentEvaluation.node4.extend (SA 8) 0] := by
  rw [LocalizedCyclicPseudoRootComponentEvaluation.children_eq]
  decide

private theorem directArmChild_slot : directArmChild.slot = 1 := by
  obtain ⟨w, childSlot, nodeEq, _current, _root, _address, zipMem, _notParent, _adj⟩ :=
    pseudoSpatialCertified.simpleBond_outwardFrame_extend_zero spatial_simpleBonded
      rootTarget root_current root_provenance_real directArmChild.frame directArmChild.outward
  have wEq : w = SA ⟨2, by decide⟩ := by
    have same := directArmChild.nodeEq.symm.trans nodeEq
    injection same with atomEq
    exact Option.some.inj atomEq.symm
  subst w
  have parentNodeEq : rootTarget.1.node =
      LocalizedCyclicPseudoRootComponentEvaluation.rootNode := by
    simp [rootTarget, LocalizedCyclicPseudoRootComponentEvaluation.rootNode,
      rootTetra, SA, LocalizedCyclicPseudoRootComponentEvaluation.SA]
  have childNodeEq : rootTarget.1.node.extend (SA ⟨2, by decide⟩) 0 =
      LocalizedCyclicPseudoRootComponentEvaluation.rootNode.extend (SA 2) 0 := by
    rw [parentNodeEq]
    congr 1
  rw [parentNodeEq, component_root_children] at zipMem
  have atList :
      (LocalizedCyclicPseudoRootComponentEvaluation.rootNode.extend (SA 2) 0, childSlot) ∈
        ([LocalizedCyclicPseudoRootComponentEvaluation.rootNode.extend (SA 1) 0,
          LocalizedCyclicPseudoRootComponentEvaluation.rootNode.extend (SA 2) 0,
          LocalizedCyclicPseudoRootComponentEvaluation.rootNode.extend (SA 4) 0,
          LocalizedCyclicPseudoRootComponentEvaluation.rootNode.extend (SA 5) 0] :
          List (OfficialCIPNode pseudoSpatialCertified.Atom)).zipIdx := by
    simpa using zipMem
  have childSlotEq : childSlot = 1 := by
    simpa [SA, LocalizedCyclicPseudoRootComponentEvaluation.SA,
      OfficialCIPNode.extend, OfficialCIPNode.childProvenance] using atList
  have addressEq := directArmChild.addressEq.symm.trans _address
  rw [root_address] at addressEq
  have directSlotEq : directArmChild.slot = childSlot := by
    injection addressEq with slotEq
  exact directSlotEq.trans childSlotEq

abbrev directArmTarget : Occurrence pseudoReference :=
  ⟨directArmChild.frame, directArmChild.present⟩

private theorem directArmFrame_eq_component_armF :
    directArmTarget.1 = LocalizedCyclicPseudoRootComponentEvaluation.armF := by
  apply LocalizedCIPOccurrenceFrame.ext
  · simp [directArmChild.sameRoot, rootTarget, rootTetra,
      LocalizedCyclicPseudoRootComponentEvaluation.armF,
      LocalizedCyclicPseudoRootComponentEvaluation.SA, SA]
  · rw [directArmTarget, directArmChild.addressEq, root_address, directArmChild_slot]
    rfl
  · rw [directArmTarget, directArmChild.nodeEq, root_node]
    rfl
  · have grade := pseudoSpatialCertified.localizedCIPOccurrence_depthGrade
      (fuel := carrierFuel pseudoReference) directArmTarget
    rw [directArmTarget, directArmChild.addressEq, root_address, directArmChild_slot] at grade
    have remainingEq : directArmTarget.1.remaining = directArmChild.frame.remaining := rfl
    rw [remainingEq] at grade
    have fuelNum : carrierFuel pseudoReference = 10 := by
      rw [carrierFuel_eq, spatial_atomCount]
    simp [LocalizedCyclicPseudoRootComponentEvaluation.armF,
      LocalizedCyclicPseudoRootComponentEvaluation.Fuel,
      LocalizedCyclicPseudoRootComponentEvaluation.fuel_eq] at ⊢
    have grade' : 1 + directArmChild.frame.remaining = 11 := by
      simpa [fuelNum] using grade
    omega

abbrev directClosingTarget : Occurrence pseudoReference :=
  ⟨directClosingChild.frame, directClosingChild.present⟩

private theorem directClosingChild_slot : directClosingChild.slot = 2 := by
  obtain ⟨w, childSlot, nodeEq, _current, _root, _address, zipMem, _notParent, _adj⟩ :=
    pseudoSpatialCertified.simpleBond_outwardFrame_extend_zero spatial_simpleBonded
      rootTarget root_current root_provenance_real directClosingChild.frame
      directClosingChild.outward
  have same := directClosingChild.nodeEq.symm.trans nodeEq
  have wEq : w = SA ⟨4, by decide⟩ := by
    injection same with atomEq
    exact Option.some.inj atomEq.symm
  subst w
  have parentNodeEq : rootTarget.1.node =
      LocalizedCyclicPseudoRootComponentEvaluation.rootNode := by
    simp [rootTarget, LocalizedCyclicPseudoRootComponentEvaluation.rootNode,
      rootTetra, SA, LocalizedCyclicPseudoRootComponentEvaluation.SA]
  rw [parentNodeEq, component_root_children] at zipMem
  have atList :
      (LocalizedCyclicPseudoRootComponentEvaluation.rootNode.extend (SA 4) 0, childSlot) ∈
        ([LocalizedCyclicPseudoRootComponentEvaluation.rootNode.extend (SA 1) 0,
          LocalizedCyclicPseudoRootComponentEvaluation.rootNode.extend (SA 2) 0,
          LocalizedCyclicPseudoRootComponentEvaluation.rootNode.extend (SA 4) 0,
          LocalizedCyclicPseudoRootComponentEvaluation.rootNode.extend (SA 5) 0] :
          List (OfficialCIPNode pseudoSpatialCertified.Atom)).zipIdx := by
    simpa using zipMem
  have childSlotEq : childSlot = 2 := by
    simpa [SA, LocalizedCyclicPseudoRootComponentEvaluation.SA,
      OfficialCIPNode.extend, OfficialCIPNode.childProvenance] using atList
  have addressEq := directClosingChild.addressEq.symm.trans _address
  rw [root_address] at addressEq
  have directSlotEq : directClosingChild.slot = childSlot := by
    injection addressEq with slotEq
  exact directSlotEq.trans childSlotEq

private theorem directClosingFrame_eq_component_closeF :
    directClosingTarget.1 = LocalizedCyclicPseudoRootComponentEvaluation.closeF := by
  apply LocalizedCIPOccurrenceFrame.ext
  · simp [directClosingChild.sameRoot, rootTarget, rootTetra,
      LocalizedCyclicPseudoRootComponentEvaluation.closeF,
      LocalizedCyclicPseudoRootComponentEvaluation.SA, SA]
  · rw [directClosingTarget, directClosingChild.addressEq, root_address,
      directClosingChild_slot]
    rfl
  · rw [directClosingTarget, directClosingChild.nodeEq, root_node]
    rfl
  · have grade := pseudoSpatialCertified.localizedCIPOccurrence_depthGrade
      (fuel := carrierFuel pseudoReference) directClosingTarget
    rw [directClosingTarget, directClosingChild.addressEq, root_address,
      directClosingChild_slot] at grade
    have remainingEq : directClosingTarget.1.remaining = directClosingChild.frame.remaining := rfl
    rw [remainingEq] at grade
    have fuelNum : carrierFuel pseudoReference = 10 := by
      rw [carrierFuel_eq, spatial_atomCount]
    simp [LocalizedCyclicPseudoRootComponentEvaluation.closeF,
      LocalizedCyclicPseudoRootComponentEvaluation.Fuel,
      LocalizedCyclicPseudoRootComponentEvaluation.fuel_eq] at ⊢
    have grade' : 1 + directClosingChild.frame.remaining = 11 := by
      simpa [fuelNum] using grade
    omega

abbrev directArmFrames : ContextFrameCompilation pseudoReference directArmTarget directArmUnit
    directArm_unitEq :=
  cyclicContextFrameCompilation pseudoReference spatial_simpleBonded directArmTarget
    directArm_real directArmUnit directArm_unitEq

abbrev directClosingFrames : ContextFrameCompilation pseudoReference directClosingTarget
    directClosingUnit directClosing_unitEq :=
  cyclicContextFrameCompilation pseudoReference spatial_simpleBonded directClosingTarget
    directClosing_real directClosingUnit directClosing_unitEq

/-! ## Actual stage keys: the first sphere is the ligand atomic number -/

private theorem node_z
    (node : OfficialCIPNode pseudoSpatialCertified.Atom) (atom : pseudoSpatialCertified.Atom)
    (current : node.current? = some atom) :
    (ofLex (pseudoSpatialCertified.moleculeGraph.officialNodeAtomLabel node)).1 =
      pseudoSpatialCertified.moleculeGraph.atomZ atom := by
  cases provenance : node.provenance <;>
    simp [officialNodeAtomLabel, current, provenance, rawCIPAtomLabel, ofLex_toLex]

private theorem declarative_head {fuel : Nat}
    {cursor : pseudoSpatialCertified.LocalizedRerootCursor (carrierFuel pseudoReference)}
    {key : OfficialRuleMajorKey pseudoSpatialCertified.Atom}
    (derived : pseudoSpatialCertified.DeclarativeLocalizedRerootRuleMajorKey fuel cursor key) :
    key.rule1a.head? = some [([], (ofLex
      (pseudoSpatialCertified.moleculeGraph.officialNodeAtomLabel cursor.occurrence.1.node)).1)] := by
  cases derived with
  | terminal _ _ => simp [officialRuleMajorRootKey]
  | branch _ _ _ _ _ => simp [OfficialRuleMajorKey.assemble, officialRuleMajorRootKey]

private theorem directArm_center : directArmFrames.center.1 = SA ⟨2, by decide⟩ := by
  rw [directArmFrames.centerEq]
  simp [directArmUnit, OccurrenceUnit.atom, armTetra]

private theorem directClosing_center : directClosingFrames.center.1 = SA ⟨4, by decide⟩ := by
  rw [directClosingFrames.centerEq]
  simp [directClosingUnit, OccurrenceUnit.atom, closingTetra]

private theorem stage_derived
    {target : Occurrence pseudoReference}
    {unit : DetectedOccurrence pseudoSpatialCertified.moleculeGraph}
    {targetUnit : pseudoSpatialCertified.molecularFrameUnit target.1 = unit.1}
    (frames : ContextFrameCompilation pseudoReference target unit targetUnit) (slot : Fin 4) :
    pseudoSpatialCertified.DeclarativeLocalizedRerootRuleMajorKey
      (2 * (carrierFuel pseudoReference + 1)) (frames.frame.cursorAt slot)
      (frames.stages slot).a.key.constitutional := by
  have built := (frames.stages slot).a.built
  unfold pseudoReference at built
  rw [pseudoSpatialCertified.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized] at built
  exact pseudoSpatialCertified.buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_declarative
    .rule4a (contextOccurrenceRead pseudoReference target)
    (2 * (carrierFuel pseudoReference + 1)) (frames.frame.cursorAt slot)
    (frames.stages slot).a.key built

private theorem slot_head
    {target : Occurrence pseudoReference}
    {unit : DetectedOccurrence pseudoSpatialCertified.moleculeGraph}
    {targetUnit : pseudoSpatialCertified.molecularFrameUnit target.1 = unit.1}
    (frames : ContextFrameCompilation pseudoReference target unit targetUnit) (slot : Fin 4) :
    (frames.stages slot).a.key.constitutional.rule1a.head? =
      some [([], pseudoSpatialCertified.moleculeGraph.atomZ (frames.actualLigandAtoms slot))] := by
  have derived := stage_derived frames slot
  have head := declarative_head derived
  have current := frames.ligandAt slot
  rw [node_z _ _ current] at head
  simpa [ContextFrameCompilation.actualLigandAtoms] using head

private theorem direct_slot (index : Fin 9) (adjacent : graph.Adj ⟨2, by decide⟩ index) :
    ∃ slot : Fin 4, directArmFrames.actualLigandAtoms slot = SA index := by
  have adjacentCenter : pseudoSpatialCertified.moleculeGraph.Adj directArmFrames.center.1
      (SA index) := by
    rw [directArm_center]
    exact (spatial_adj ⟨2, by decide⟩ index).mpr adjacent
  obtain ⟨i, atomEq⟩ :=
    pseudoSpatialCertified.detectedMultiCenterMolecule.ligandAtomAt_surjective
      directArmFrames.center (SA index) adjacentCenter
  refine ⟨directArmFrames.detectedLigandPermutation.symm i, ?_⟩
  unfold pseudoReference
  simp [ContextFrameCompilation.actualLigandAtoms, Equiv.apply_symm_apply, atomEq]

private theorem closing_slot (index : Fin 9)
    (adjacent : graph.Adj ⟨4, by decide⟩ index) :
    ∃ slot : Fin 4, directClosingFrames.actualLigandAtoms slot = SA index := by
  have adjacentCenter : pseudoSpatialCertified.moleculeGraph.Adj directClosingFrames.center.1
      (SA index) := by
    rw [directClosing_center]
    exact (spatial_adj ⟨4, by decide⟩ index).mpr adjacent
  obtain ⟨i, atomEq⟩ :=
    pseudoSpatialCertified.detectedMultiCenterMolecule.ligandAtomAt_surjective
      directClosingFrames.center (SA index) adjacentCenter
  refine ⟨directClosingFrames.detectedLigandPermutation.symm i, ?_⟩
  unfold pseudoReference
  simp [ContextFrameCompilation.actualLigandAtoms, Equiv.apply_symm_apply, atomEq]

private noncomputable def closingCarbonSlot : Fin 4 :=
  Classical.choose (closing_slot ⟨2, by decide⟩ ((adj_closing 2).mpr (by simp)))

private theorem closingCarbonSlot_atom :
    directClosingFrames.actualLigandAtoms closingCarbonSlot = SA ⟨2, by decide⟩ :=
  Classical.choose_spec (closing_slot ⟨2, by decide⟩ ((adj_closing 2).mpr (by simp)))

private theorem spatialZ (i : Fin 9) (z : ℕ) (fact : graph.atomZ i = z) :
    pseudoSpatialCertified.moleculeGraph.atomZ (SA i) = z := by
  rw [spatial_z, fact]

theorem direct_arm_first_spheres :
    ∃ slotParent slotChlorine slotCarbon slotHydrogen : Fin 4,
      directArmFrames.actualLigandAtoms slotParent = SA ⟨0, by decide⟩ ∧
      directArmFrames.actualLigandAtoms slotChlorine = SA ⟨3, by decide⟩ ∧
      directArmFrames.actualLigandAtoms slotCarbon = SA ⟨4, by decide⟩ ∧
      directArmFrames.actualLigandAtoms slotHydrogen = SA ⟨6, by decide⟩ ∧
      (directArmFrames.stages slotParent).a.key.constitutional.rule1a.head? = some [([], 6)] ∧
      (directArmFrames.stages slotChlorine).a.key.constitutional.rule1a.head? = some [([], 17)] ∧
      (directArmFrames.stages slotCarbon).a.key.constitutional.rule1a.head? = some [([], 6)] ∧
      (directArmFrames.stages slotHydrogen).a.key.constitutional.rule1a.head? = some [([], 1)] := by
  obtain ⟨slotParent, parentAtom⟩ := direct_slot ⟨0, by decide⟩ ((adj_arm 0).mpr (by simp))
  obtain ⟨slotChlorine, chlorineAtom⟩ := direct_slot ⟨3, by decide⟩ ((adj_arm 3).mpr (by simp))
  obtain ⟨slotCarbon, carbonAtom⟩ := direct_slot ⟨4, by decide⟩ ((adj_arm 4).mpr (by simp))
  obtain ⟨slotHydrogen, hydrogenAtom⟩ := direct_slot ⟨6, by decide⟩ ((adj_arm 6).mpr (by simp))
  refine ⟨slotParent, slotChlorine, slotCarbon, slotHydrogen, parentAtom, chlorineAtom, carbonAtom,
    hydrogenAtom, ?_, ?_, ?_, ?_⟩
  · simpa [parentAtom, spatialZ ⟨0, by decide⟩ 6 ((z_carbon 0).mpr (Or.inl rfl))] using
      slot_head directArmFrames slotParent
  · simpa [chlorineAtom, spatialZ ⟨3, by decide⟩ 17 ((z_chlorine 3).mpr (Or.inl rfl))] using
      slot_head directArmFrames slotChlorine
  · simpa [carbonAtom, spatialZ ⟨4, by decide⟩ 6 ((z_carbon 4).mpr (Or.inr (Or.inr rfl)))] using
      slot_head directArmFrames slotCarbon
  · simpa [hydrogenAtom, spatialZ ⟨6, by decide⟩ 1 ((z_hydrogen 6).mpr (Or.inr (Or.inl rfl)))] using
      slot_head directArmFrames slotHydrogen

private theorem compare_gt_of_heads
    {left right : OfficialRuleMajorKey pseudoSpatialCertified.Atom} {leftZ rightZ : ℕ}
    (leftHead : left.rule1a.head? = some [([], leftZ)])
    (rightHead : right.rule1a.head? = some [([], rightZ)])
    (higher : rightZ < leftZ) :
    OfficialRuleMajorKey.compare left right = Ordering.gt := by
  have layers := officialRuleMajorKey_compare_rule1a_gt_of_heads_gt leftHead rightHead higher
  rw [OfficialRuleMajorKey.compare_eq_rule1a_of_decisive (by rw [layers]; decide), layers]

private noncomputable def directSlot (index : Fin 9)
    (adjacent : graph.Adj ⟨2, by decide⟩ index) : Fin 4 :=
  Classical.choose (direct_slot index adjacent)

private theorem directSlot_atom (index : Fin 9)
    (adjacent : graph.Adj ⟨2, by decide⟩ index) :
    directArmFrames.actualLigandAtoms (directSlot index adjacent) = SA index :=
  Classical.choose_spec (direct_slot index adjacent)

private theorem direct_head (index : Fin 9) (z : ℕ)
    (adjacent : graph.Adj ⟨2, by decide⟩ index) (atomic : graph.atomZ index = z) :
    (directArmFrames.stages (directSlot index adjacent)).a.key.constitutional.rule1a.head? =
      some [([], z)] := by
  simpa [directSlot_atom index adjacent, spatialZ index z atomic] using
    slot_head directArmFrames (directSlot index adjacent)

private theorem direct_gt (left right : Fin 9) (leftZ rightZ : ℕ)
    (leftAdj : graph.Adj ⟨2, by decide⟩ left) (rightAdj : graph.Adj ⟨2, by decide⟩ right)
    (leftAtomic : graph.atomZ left = leftZ) (rightAtomic : graph.atomZ right = rightZ)
    (higher : rightZ < leftZ) :
    OfficialRuleMajorKey.compare
      (directArmFrames.stages (directSlot left leftAdj)).a.key.constitutional
      (directArmFrames.stages (directSlot right rightAdj)).a.key.constitutional = Ordering.gt :=
  compare_gt_of_heads (direct_head left leftZ leftAdj leftAtomic)
    (direct_head right rightZ rightAdj rightAtomic) higher

theorem direct_arm_first_sphere_separation :
    OfficialRuleMajorKey.compare
        (directArmFrames.stages (directSlot ⟨3, by decide⟩ ((adj_arm 3).mpr (by simp)))).a.key.constitutional
        (directArmFrames.stages (directSlot ⟨0, by decide⟩ ((adj_arm 0).mpr (by simp)))).a.key.constitutional =
      Ordering.gt ∧
    OfficialRuleMajorKey.compare
        (directArmFrames.stages (directSlot ⟨3, by decide⟩ ((adj_arm 3).mpr (by simp)))).a.key.constitutional
        (directArmFrames.stages (directSlot ⟨4, by decide⟩ ((adj_arm 4).mpr (by simp)))).a.key.constitutional =
      Ordering.gt ∧
    OfficialRuleMajorKey.compare
        (directArmFrames.stages (directSlot ⟨3, by decide⟩ ((adj_arm 3).mpr (by simp)))).a.key.constitutional
        (directArmFrames.stages (directSlot ⟨6, by decide⟩ ((adj_arm 6).mpr (by simp)))).a.key.constitutional =
      Ordering.gt ∧
    OfficialRuleMajorKey.compare
        (directArmFrames.stages (directSlot ⟨0, by decide⟩ ((adj_arm 0).mpr (by simp)))).a.key.constitutional
        (directArmFrames.stages (directSlot ⟨6, by decide⟩ ((adj_arm 6).mpr (by simp)))).a.key.constitutional =
      Ordering.gt ∧
    OfficialRuleMajorKey.compare
        (directArmFrames.stages (directSlot ⟨4, by decide⟩ ((adj_arm 4).mpr (by simp)))).a.key.constitutional
        (directArmFrames.stages (directSlot ⟨6, by decide⟩ ((adj_arm 6).mpr (by simp)))).a.key.constitutional =
      Ordering.gt := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact direct_gt ⟨3, by decide⟩ ⟨0, by decide⟩ 17 6 ((adj_arm 3).mpr (by simp))
      ((adj_arm 0).mpr (by simp)) ((z_chlorine 3).mpr (Or.inl rfl)) ((z_carbon 0).mpr (Or.inl rfl))
      (by decide)
  · exact direct_gt ⟨3, by decide⟩ ⟨4, by decide⟩ 17 6 ((adj_arm 3).mpr (by simp))
      ((adj_arm 4).mpr (by simp)) ((z_chlorine 3).mpr (Or.inl rfl))
      ((z_carbon 4).mpr (Or.inr (Or.inr rfl))) (by decide)
  · exact direct_gt ⟨3, by decide⟩ ⟨6, by decide⟩ 17 1 ((adj_arm 3).mpr (by simp))
      ((adj_arm 6).mpr (by simp)) ((z_chlorine 3).mpr (Or.inl rfl))
      ((z_hydrogen 6).mpr (Or.inr (Or.inl rfl))) (by decide)
  · exact direct_gt ⟨0, by decide⟩ ⟨6, by decide⟩ 6 1 ((adj_arm 0).mpr (by simp))
      ((adj_arm 6).mpr (by simp)) ((z_carbon 0).mpr (Or.inl rfl))
      ((z_hydrogen 6).mpr (Or.inr (Or.inl rfl))) (by decide)
  · exact direct_gt ⟨4, by decide⟩ ⟨6, by decide⟩ 6 1 ((adj_arm 4).mpr (by simp))
      ((adj_arm 6).mpr (by simp)) ((z_carbon 4).mpr (Or.inr (Or.inr rfl)))
      ((z_hydrogen 6).mpr (Or.inr (Or.inl rfl))) (by decide)

private theorem direct_frame :
    pseudoSpatialCertified.localizedOccurrenceFourLigandFrame? directArmTarget =
      some directArmFrames.frame := by
  unfold pseudoReference
  rw [← pseudoSpatialCertified.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?
    directArmTarget]
  exact directArmFrames.frameComputed

private theorem component_arm_neighbors :
    LocalizedCyclicPseudoRootComponentEvaluation.neighborFrames0
        LocalizedCyclicPseudoRootComponentEvaluation.armF =
      [LocalizedCyclicPseudoRootComponentEvaluation.rootF,
        LocalizedCyclicPseudoRootComponentEvaluation.armClF,
        LocalizedCyclicPseudoRootComponentEvaluation.via24F,
        LocalizedCyclicPseudoRootComponentEvaluation.armHF] := by
  decide +kernel

private theorem closing_frame :
    pseudoSpatialCertified.localizedOccurrenceFourLigandFrame? directClosingTarget =
      some directClosingFrames.frame := by
  rw [← pseudoSpatialCertified.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?
    directClosingTarget]
  exact directClosingFrames.frameComputed

private def carbonSlot : Fin 4 :=
  directSlot ⟨4, by decide⟩ ((adj_arm 4).mpr (by simp))

private theorem carbonSlot_atom :
    directArmFrames.actualLigandAtoms carbonSlot = SA ⟨4, by decide⟩ :=
  directSlot_atom ⟨4, by decide⟩ ((adj_arm 4).mpr (by simp))

private theorem direct_cursor_present (slot : Fin 4) :
    directArmFrames.frame.cursorAt slot ∈ directArmFrames.frame.cursors := by
  rw [LocalizedOccurrenceFourLigandFrame.cursorAt]
  exact List.get_mem (directArmFrames.frame.cursors)
    (Fin.cast directArmFrames.frame.length_eq.symm slot)

private theorem direct_cursor_mem_component_neighbors (slot : Fin 4) :
    (directArmFrames.frame.cursorAt slot).occurrence.1 ∈
      [LocalizedCyclicPseudoRootComponentEvaluation.rootF,
        LocalizedCyclicPseudoRootComponentEvaluation.armClF,
        LocalizedCyclicPseudoRootComponentEvaluation.via24F,
        LocalizedCyclicPseudoRootComponentEvaluation.armHF] := by
  have computed :
      pseudoSpatialCertified.localizedOccurrenceFourLigandFrame? directArmTarget =
        some directArmFrames.frame := direct_frame
  have mapped := pseudoSpatialCertified.localizedOccurrenceFourLigandFrame_cursors_map_eq_neighborFrames
    directArmTarget directArmFrames.frame computed
  have member :
      (directArmFrames.frame.cursorAt slot).occurrence.1 ∈
        pseudoSpatialCertified.localizedRerootNeighborFrames
          (fuel := carrierFuel pseudoReference) directArmTarget.1 := by
    rw [← mapped]
    exact List.mem_map.mpr ⟨directArmFrames.frame.cursorAt slot,
      direct_cursor_present slot, rfl⟩
  have rootZero : directArmTarget.1.root =
      LocalizedCyclicPseudoRootComponentEvaluation.SA 0 := by
    have roots := congrArg
      (fun f : pseudoSpatialCertified.LocalizedCIPOccurrenceFrame => f.root)
      directArmFrame_eq_component_armF
    rw [LocalizedCyclicPseudoRootComponentEvaluation.armF] at roots
    exact roots
  rw [LocalizedCyclicPseudoRootComponentEvaluation.neighborFrames_eq0
      directArmTarget.1 rootZero] at member
  rw [directArmFrame_eq_component_armF, component_arm_neighbors] at member
  exact member

private theorem direct_cursor_eq_component
    (slot : Fin 4)
    (candidate : LocalizedCyclicPseudoRootComponentEvaluation.Frame)
    (sameCurrent : (directArmFrames.frame.cursorAt slot).occurrence.1.node.current? =
      candidate.node.current?)
    (candidateMem : candidate ∈
      [LocalizedCyclicPseudoRootComponentEvaluation.rootF,
        LocalizedCyclicPseudoRootComponentEvaluation.armClF,
        LocalizedCyclicPseudoRootComponentEvaluation.via24F,
        LocalizedCyclicPseudoRootComponentEvaluation.armHF]) :
    (directArmFrames.frame.cursorAt slot).occurrence.1 = candidate := by
  have nodup :
      ([LocalizedCyclicPseudoRootComponentEvaluation.rootF,
        LocalizedCyclicPseudoRootComponentEvaluation.armClF,
        LocalizedCyclicPseudoRootComponentEvaluation.via24F,
        LocalizedCyclicPseudoRootComponentEvaluation.armHF].map
        (fun f => f.node.current?)).Nodup := by
    decide
  exact List.inj_on_of_nodup_map nodup
    (direct_cursor_mem_component_neighbors slot) candidateMem sameCurrent

private theorem closing_cursor_present (slot : Fin 4) :
    directClosingFrames.frame.cursorAt slot ∈ directClosingFrames.frame.cursors := by
  rw [LocalizedOccurrenceFourLigandFrame.cursorAt]
  exact List.get_mem directClosingFrames.frame.cursors
    (Fin.cast directClosingFrames.frame.length_eq.symm slot)

private noncomputable def shallowClosingRootSlot : Fin 4 :=
  Classical.choose (closing_slot ⟨0, by decide⟩ ((adj_closing 0).mpr (by simp)))
private noncomputable def shallowClosingClSlot : Fin 4 :=
  Classical.choose (closing_slot ⟨8, by decide⟩ ((adj_closing 8).mpr (by simp)))
private noncomputable def shallowClosingCarbonSlot : Fin 4 :=
  Classical.choose (closing_slot ⟨2, by decide⟩ ((adj_closing 2).mpr (by simp)))
private noncomputable def shallowClosingHSlot : Fin 4 :=
  Classical.choose (closing_slot ⟨7, by decide⟩ ((adj_closing 7).mpr (by simp)))

private theorem shallowClosingRootSlot_atom :
    directClosingFrames.actualLigandAtoms shallowClosingRootSlot = SA ⟨0, by decide⟩ :=
  Classical.choose_spec (closing_slot ⟨0, by decide⟩ ((adj_closing 0).mpr (by simp)))
private theorem shallowClosingClSlot_atom :
    directClosingFrames.actualLigandAtoms shallowClosingClSlot = SA ⟨8, by decide⟩ :=
  Classical.choose_spec (closing_slot ⟨8, by decide⟩ ((adj_closing 8).mpr (by simp)))
private theorem shallowClosingCarbonSlot_atom :
    directClosingFrames.actualLigandAtoms shallowClosingCarbonSlot = SA ⟨2, by decide⟩ :=
  Classical.choose_spec (closing_slot ⟨2, by decide⟩ ((adj_closing 2).mpr (by simp)))
private theorem shallowClosingHSlot_atom :
    directClosingFrames.actualLigandAtoms shallowClosingHSlot = SA ⟨7, by decide⟩ :=
  Classical.choose_spec (closing_slot ⟨7, by decide⟩ ((adj_closing 7).mpr (by simp)))

private theorem component_close_neighbors :
    LocalizedCyclicPseudoRootComponentEvaluation.neighborFrames0
        LocalizedCyclicPseudoRootComponentEvaluation.closeF =
      [LocalizedCyclicPseudoRootComponentEvaluation.rootF,
        LocalizedCyclicPseudoRootComponentEvaluation.via42F,
        LocalizedCyclicPseudoRootComponentEvaluation.closeHF,
        LocalizedCyclicPseudoRootComponentEvaluation.closeClF] := by
  decide +kernel

private theorem closing_cursor_mem_component_neighbors (slot : Fin 4) :
    (directClosingFrames.frame.cursorAt slot).occurrence.1 ∈
      [LocalizedCyclicPseudoRootComponentEvaluation.rootF,
        LocalizedCyclicPseudoRootComponentEvaluation.via42F,
        LocalizedCyclicPseudoRootComponentEvaluation.closeHF,
        LocalizedCyclicPseudoRootComponentEvaluation.closeClF] := by
  have computed :
      pseudoSpatialCertified.localizedOccurrenceFourLigandFrame? directClosingTarget =
        some directClosingFrames.frame := closing_frame
  have mapped := pseudoSpatialCertified.localizedOccurrenceFourLigandFrame_cursors_map_eq_neighborFrames
    directClosingTarget directClosingFrames.frame computed
  have member :
      (directClosingFrames.frame.cursorAt slot).occurrence.1 ∈
        pseudoSpatialCertified.localizedRerootNeighborFrames
          (fuel := carrierFuel pseudoReference) directClosingTarget.1 := by
    rw [← mapped]
    exact List.mem_map.mpr ⟨directClosingFrames.frame.cursorAt slot,
      closing_cursor_present slot, rfl⟩
  have rootZero : directClosingTarget.1.root =
      LocalizedCyclicPseudoRootComponentEvaluation.SA 0 := by
    have roots := congrArg
      (fun f : pseudoSpatialCertified.LocalizedCIPOccurrenceFrame => f.root)
      directClosingFrame_eq_component_closeF
    rw [LocalizedCyclicPseudoRootComponentEvaluation.closeF] at roots
    exact roots
  rw [LocalizedCyclicPseudoRootComponentEvaluation.neighborFrames_eq0
      directClosingTarget.1 rootZero] at member
  rw [directClosingFrame_eq_component_closeF, component_close_neighbors] at member
  exact member

private theorem closing_cursor_eq_component
    (slot : Fin 4)
    (candidate : LocalizedCyclicPseudoRootComponentEvaluation.Frame)
    (sameCurrent : (directClosingFrames.frame.cursorAt slot).occurrence.1.node.current? =
      candidate.node.current?)
    (candidateMem : candidate ∈
      [LocalizedCyclicPseudoRootComponentEvaluation.rootF,
        LocalizedCyclicPseudoRootComponentEvaluation.via42F,
        LocalizedCyclicPseudoRootComponentEvaluation.closeHF,
        LocalizedCyclicPseudoRootComponentEvaluation.closeClF]) :
    (directClosingFrames.frame.cursorAt slot).occurrence.1 = candidate := by
  have nodup :
      ([LocalizedCyclicPseudoRootComponentEvaluation.rootF,
        LocalizedCyclicPseudoRootComponentEvaluation.via42F,
        LocalizedCyclicPseudoRootComponentEvaluation.closeHF,
        LocalizedCyclicPseudoRootComponentEvaluation.closeClF].map
        (fun f => f.node.current?)).Nodup := by
    decide
  exact List.inj_on_of_nodup_map nodup
    (closing_cursor_mem_component_neighbors slot) candidateMem sameCurrent

private theorem direct_address_nonempty : directArmTarget.1.address ≠ [] := by
  rw [directArmChild.addressEq, root_address]
  exact List.cons_ne_nil _ _

private theorem closing_address_nonempty : directClosingTarget.1.address ≠ [] := by
  rw [directClosingChild.addressEq, root_address]
  exact List.cons_ne_nil _ _

private theorem closing_cursor_outward :
    (directClosingFrames.frame.cursorAt closingCarbonSlot).occurrence.1 ∈
      pseudoSpatialCertified.localizedCarrierOutwardChildFrames
        (fuel := carrierFuel pseudoReference) directClosingTarget.1 := by
  have neighbor :=
    pseudoSpatialCertified.localizedOccurrenceFourLigandFrame_cursor_mem_neighborFrames
      directClosingTarget directClosingFrames.frame closing_frame _
      (closing_cursor_present closingCarbonSlot)
  rw [localizedRerootNeighborFrames, List.mem_append] at neighbor
  rcases neighbor with parent | outward
  · exfalso
    obtain ⟨certificate, parentAtom, parentCurrent, parentObserved, _visited, _adjacent,
      _active, _member⟩ :=
      pseudoSpatialCertified.realCenter_parent_current directClosingTarget
        directClosingChild.currentEq closing_address_nonempty
    have singleton := certificate.carrierParentFrames_eq_singleton pseudoSpatialCertified
    have frameEq : (directClosingFrames.frame.cursorAt closingCarbonSlot).occurrence.1 =
        certificate.parent.1 := by
      have member : (directClosingFrames.frame.cursorAt closingCarbonSlot).occurrence.1 ∈
          [certificate.parent.1] := by
        simpa [singleton] using parent
      simpa using member
    have onParent : certificate.parent.1.node.current? = some (SA ⟨2, by decide⟩) := by
      have current := directClosingFrames.ligandAt closingCarbonSlot
      unfold pseudoReference at current
      rw [frameEq] at current
      have atomEq : pseudoSpatialCertified.detectedMultiCenterMolecule.ligandAtomAt
          directClosingFrames.center
          (directClosingFrames.detectedLigandPermutation closingCarbonSlot) =
          SA ⟨2, by decide⟩ := by
        have defined : directClosingFrames.actualLigandAtoms closingCarbonSlot =
            pseudoSpatialCertified.detectedMultiCenterMolecule.ligandAtomAt
              directClosingFrames.center
              (directClosingFrames.detectedLigandPermutation closingCarbonSlot) := by
          unfold pseudoReference
          rfl
        rw [← defined]
        exact closingCarbonSlot_atom
      rw [atomEq] at current
      exact current
    have parentIsRoot : parentAtom = SA ⟨0, by decide⟩ := by
      have observed : directClosingTarget.1.node.parent? = some parentAtom := parentObserved
      have nodeParent : directClosingTarget.1.node.parent? = some (SA ⟨0, by decide⟩) := by
        rw [directClosingChild.nodeEq, root_node, OfficialCIPNode.extend,
          OfficialCIPNode.root, OfficialCIPNode.parent?]
        rfl
      exact Option.some.inj (observed.symm.trans nodeParent)
    have wrong : parentAtom = SA ⟨2, by decide⟩ :=
      Option.some.inj (parentCurrent.symm.trans onParent)
    have vals := congrArg Fin.val (parentIsRoot.symm.trans wrong)
    simp [SA_val] at vals
  · exact outward

private theorem closingCarbon_extend :
    (directClosingFrames.frame.cursorAt closingCarbonSlot).occurrence.1.node =
      directClosingTarget.1.node.extend (SA ⟨2, by decide⟩) 0 := by
  obtain ⟨w, _slot, nodeEq, current, _root, _address, _zip, _notParent, _adj⟩ :=
    pseudoSpatialCertified.simpleBond_outwardFrame_extend_zero spatial_simpleBonded
      directClosingTarget directClosingChild.currentEq directClosing_real _
      closing_cursor_outward
  have wEq : w = SA ⟨2, by decide⟩ := by
    apply Option.some.inj
    rw [← current]
    have ligandCurrent := directClosingFrames.ligandAt closingCarbonSlot
    unfold pseudoReference at ligandCurrent
    have atomEq : pseudoSpatialCertified.detectedMultiCenterMolecule.ligandAtomAt
        directClosingFrames.center
        (directClosingFrames.detectedLigandPermutation closingCarbonSlot) =
        SA ⟨2, by decide⟩ := by
      have defined : directClosingFrames.actualLigandAtoms closingCarbonSlot =
          pseudoSpatialCertified.detectedMultiCenterMolecule.ligandAtomAt
            directClosingFrames.center
            (directClosingFrames.detectedLigandPermutation closingCarbonSlot) := by
        unfold pseudoReference
        rfl
      rw [← defined]
      exact closingCarbonSlot_atom
    rw [atomEq] at ligandCurrent
    exact ligandCurrent
  rw [wEq] at nodeEq
  exact nodeEq

private theorem closingCarbonCursor_eq_via42F :
    (directClosingFrames.frame.cursorAt closingCarbonSlot).occurrence.1 =
      LocalizedCyclicPseudoRootComponentEvaluation.via42F := by
  obtain ⟨w, childSlot, _nodeEq, _current, _root, addressEq, zipMem, _notParent, _adj⟩ :=
    pseudoSpatialCertified.simpleBond_outwardFrame_extend_zero spatial_simpleBonded
      directClosingTarget directClosingChild.currentEq directClosing_real _
      closing_cursor_outward
  have wEq : w = SA ⟨2, by decide⟩ := by
    have same := closingCarbon_extend.symm.trans _nodeEq
    injection same with atomEq
    exact Option.some.inj atomEq.symm
  subst w
  have parentNodeEq : directClosingTarget.1.node =
      LocalizedCyclicPseudoRootComponentEvaluation.node4 := by
    have := congrArg (fun f : pseudoSpatialCertified.LocalizedCIPOccurrenceFrame => f.node)
      directClosingFrame_eq_component_closeF
    simpa [LocalizedCyclicPseudoRootComponentEvaluation.closeF] using this
  rw [parentNodeEq, component_close_children] at zipMem
  have atList :
      (LocalizedCyclicPseudoRootComponentEvaluation.node4.extend (SA 2) 0, childSlot) ∈
        ([LocalizedCyclicPseudoRootComponentEvaluation.node4.extend (SA 2) 0,
          LocalizedCyclicPseudoRootComponentEvaluation.node4.extend (SA 7) 0,
          LocalizedCyclicPseudoRootComponentEvaluation.node4.extend (SA 8) 0] :
          List (OfficialCIPNode pseudoSpatialCertified.Atom)).zipIdx := by
    simpa using zipMem
  have childSlotEq : childSlot = 0 := by
    simpa [SA, LocalizedCyclicPseudoRootComponentEvaluation.SA,
      OfficialCIPNode.extend, OfficialCIPNode.childProvenance] using atList
  have exactAddress :
      (directClosingFrames.frame.cursorAt closingCarbonSlot).occurrence.1.address = [2, 0] := by
    rw [addressEq, directClosingFrame_eq_component_closeF, childSlotEq,
      LocalizedCyclicPseudoRootComponentEvaluation.closeF]
    rfl
  apply LocalizedCIPOccurrenceFrame.ext
  · have rootEq := congrArg
      (fun f : pseudoSpatialCertified.LocalizedCIPOccurrenceFrame => f.root)
      directClosingFrame_eq_component_closeF
    change directClosingTarget.1.root =
      LocalizedCyclicPseudoRootComponentEvaluation.closeF.root at rootEq
    rw [LocalizedCyclicPseudoRootComponentEvaluation.via42F]
    exact (pseudoSpatialCertified.localizedOccurrenceFourLigandFrame_cursor_root
      directClosingTarget directClosingFrames.frame closing_frame _
      (closing_cursor_present closingCarbonSlot)).trans rootEq
  · exact exactAddress
  · have parentNodeEq := congrArg
      (fun f : pseudoSpatialCertified.LocalizedCIPOccurrenceFrame => f.node)
      directClosingFrame_eq_component_closeF
    change directClosingTarget.1.node =
      LocalizedCyclicPseudoRootComponentEvaluation.closeF.node at parentNodeEq
    rw [closingCarbon_extend, parentNodeEq,
      LocalizedCyclicPseudoRootComponentEvaluation.via42F,
      LocalizedCyclicPseudoRootComponentEvaluation.node42,
      LocalizedCyclicPseudoRootComponentEvaluation.node4,
      LocalizedCyclicPseudoRootComponentEvaluation.rootNode]
    simp [OfficialCIPNode.extend, OfficialCIPNode.root,
      LocalizedCyclicPseudoRootComponentEvaluation.SA, SA,
      LocalizedCyclicPseudoRootComponentEvaluation.closeF,
      LocalizedCyclicPseudoRootComponentEvaluation.node4,
      LocalizedCyclicPseudoRootComponentEvaluation.rootNode]
  · have grade := pseudoSpatialCertified.localizedCIPOccurrence_depthGrade
      (fuel := carrierFuel pseudoReference)
      (directClosingFrames.frame.cursorAt closingCarbonSlot).occurrence
    rw [exactAddress] at grade
    have fuelNum : carrierFuel pseudoReference = 10 := by
      rw [carrierFuel_eq, spatial_atomCount]
    have grade' : 2 +
        (directClosingFrames.frame.cursorAt closingCarbonSlot).occurrence.1.remaining = 11 := by
      simpa [fuelNum] using grade
    simp [LocalizedCyclicPseudoRootComponentEvaluation.via42F,
      LocalizedCyclicPseudoRootComponentEvaluation.Fuel,
      LocalizedCyclicPseudoRootComponentEvaluation.fuel_eq]
    omega

abbrev via42Target : Occurrence pseudoReference :=
  (directClosingFrames.frame.cursorAt closingCarbonSlot).occurrence

private theorem via42_current :
    via42Target.1.node.current? = some (SA ⟨2, by decide⟩) := by
  change (directClosingFrames.frame.cursorAt closingCarbonSlot).occurrence.1.node.current? =
    some (SA ⟨2, by decide⟩)
  rw [closingCarbon_extend]
  simp [OfficialCIPNode.extend]

private theorem via42_real :
    via42Target.1.node.provenance = OfficialCIPNodeProvenance.realAtom := by
  change (directClosingFrames.frame.cursorAt closingCarbonSlot).occurrence.1.node.provenance =
    OfficialCIPNodeProvenance.realAtom
  rw [closingCarbon_extend, OfficialCIPNode.extend, OfficialCIPNode.childProvenance]
  have fresh : SA ⟨2, by decide⟩ ∉ directClosingTarget.1.node.history := by
    rw [directClosingChild.nodeEq, root_node]
    simp [OfficialCIPNode.extend_history, OfficialCIPNode.root, rootTetra, SA]
  exact if_neg fresh

private theorem via42_unit_eq :
    pseudoSpatialCertified.molecularFrameUnit via42Target.1 =
      ⟨SA ⟨0, by decide⟩, [SA ⟨4, by decide⟩, SA ⟨2, by decide⟩]⟩ := by
  unfold molecularFrameUnit
  rw [closingCarbonCursor_eq_via42F,
    LocalizedCyclicPseudoRootComponentEvaluation.via42F]
  rfl

private theorem via42_unit_root :
    (pseudoSpatialCertified.molecularFrameUnit via42Target.1).root = rootTetra.1 := by
  change via42Target.1.root = SA ⟨0, by decide⟩
  have rootEq := congrArg
    (fun f : pseudoSpatialCertified.LocalizedCIPOccurrenceFrame => f.root)
    closingCarbonCursor_eq_via42F
  rw [LocalizedCyclicPseudoRootComponentEvaluation.via42F] at rootEq
  exact rootEq

private theorem via42_unit_atom :
    (pseudoSpatialCertified.molecularFrameUnit via42Target.1).atom = armTetra.1 := by
  rw [via42_unit_eq]
  rfl

private theorem via42_detected :
    IsDetectedCenter pseudoSpatialCertified.moleculeGraph
      (pseudoSpatialCertified.molecularFrameUnit via42Target.1).atom := by
  rw [via42_unit_atom]
  exact detected_atom ⟨2, by decide⟩
    ((degree_four_iff 2).mpr (Or.inr (Or.inl rfl)))

private def via42Unit : DetectedOccurrence pseudoSpatialCertified.moleculeGraph :=
  ⟨pseudoSpatialCertified.molecularFrameUnit via42Target.1, via42_detected⟩

private theorem via42_unit_target :
    pseudoSpatialCertified.molecularFrameUnit via42Target.1 = via42Unit.1 := rfl

private abbrev via42Frames :
    ContextFrameCompilation pseudoReference via42Target via42Unit via42_unit_target :=
  cyclicContextFrameCompilation pseudoReference spatial_simpleBonded via42Target
    via42_real via42Unit via42_unit_target

private theorem component_via42_children :
    pseudoSpatialCertified.executableOfficialCIPChildren
        LocalizedCyclicPseudoRootComponentEvaluation.node42 =
      [LocalizedCyclicPseudoRootComponentEvaluation.node42.extend
          (SA ⟨0, by decide⟩) 0,
        LocalizedCyclicPseudoRootComponentEvaluation.node42.extend
          (SA ⟨3, by decide⟩) 0,
        LocalizedCyclicPseudoRootComponentEvaluation.node42.extend
          (SA ⟨6, by decide⟩) 0] := by
  rw [LocalizedCyclicPseudoRootComponentEvaluation.children_eq]
  decide

private theorem component_via42_neighbors :
    LocalizedCyclicPseudoRootComponentEvaluation.neighborFrames0
        LocalizedCyclicPseudoRootComponentEvaluation.via42F =
      [LocalizedCyclicPseudoRootComponentEvaluation.closeF,
        LocalizedCyclicPseudoRootComponentEvaluation.via42DupF,
        LocalizedCyclicPseudoRootComponentEvaluation.via42ClF,
        LocalizedCyclicPseudoRootComponentEvaluation.via42HF] := by
  decide

/-- A successful actual frame stage and the constant-none root-component twin have the same
Rule-1a table. This transfers only the constitutional table from the actual reader. -/
theorem actualRule1a_eq_rootComponent
    (cursor : pseudoSpatialCertified.LocalizedRerootCursor (carrierFuel pseudoReference))
    (valid : pseudoSpatialCertified.LocalizedRerootCursorValid cursor)
    (read : pseudoSpatialCertified.LocalizedRerootCursor (carrierFuel pseudoReference) →
      Option LocalizedAuxiliaryLabel)
    {fuel : Nat} (key : pseudoSpatialCertified.LocalizedRerootCumulativeRule45Key)
    (built : pseudoSpatialCertified.buildLocalizedRerootCumulativeRule45KeyWithRead?
      .rule4a read fuel cursor = some key)
    (rootZero : cursor.occurrence.1.root =
      LocalizedCyclicPseudoRootComponentEvaluation.SA 0) :
    ∃ twinKey,
      LocalizedCyclicPseudoRootComponentEvaluation.buildF .rule4a
        LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
        cursor.occurrence.1 (cursor.previous?.map Subtype.val) = some twinKey ∧
      twinKey.constitutional.rule1a = key.constitutional.rule1a := by
  let input := pseudoSpatialCertified
  have fuelEq : carrierFuel pseudoReference =
      LocalizedRootwardConstitutionalSeparation.carrierFuel input := by
    rw [carrierFuel_eq]
  have evalEq : LocalizedCyclicPseudoRootComponentEvaluation.evalFuel =
      CertifiedLocalizedCIPInput.evaluationFuel input := by
    norm_num [LocalizedCyclicPseudoRootComponentEvaluation.evalFuel,
      LocalizedCyclicPseudoRootComponentEvaluation.fuel_eq,
      CertifiedLocalizedCIPInput.evaluationFuel,
      LocalizedRootwardConstitutionalSeparation.carrierFuel,
      localizedOccurrenceRerootEvaluationFuel]
    change 22 = 2 * (pseudoSpatialCertified.certified.input.molecule.atomCount + 1 + 1)
    rw [spatial_atomCount]
  obtain ⟨noneKey, noneBuilt, tableEq⟩ :=
    CertifiedLocalizedCIPInput.constNone_rule4a_rule1a_eq
      input cursor valid read (fuel := fuel) key built
  refine ⟨noneKey, ?_, tableEq⟩
  have productionEq :=
    LocalizedCyclicPseudoRootComponentEvaluation.build_eq .rule4a
      (CertifiedLocalizedCIPInput.evaluationFuel input)
      cursor rootZero
  rw [← evalEq] at productionEq
  have noneReadEq :
      input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
        (CertifiedLocalizedCIPInput.constNoneRead input)
        LocalizedCyclicPseudoRootComponentEvaluation.evalFuel cursor =
      input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
        LocalizedCyclicPseudoRootComponentEvaluation.readT
        LocalizedCyclicPseudoRootComponentEvaluation.evalFuel cursor := by
    rfl
  rw [← evalEq] at noneBuilt
  rw [noneReadEq] at noneBuilt
  exact productionEq.symm.trans noneBuilt

private theorem actual_direct_cursor_const_rule1a
    (slot : Fin 4)
    (candidate : LocalizedCyclicPseudoRootComponentEvaluation.Frame)
    (sameCurrent : (directArmFrames.frame.cursorAt slot).occurrence.1.node.current? =
      candidate.node.current?)
    (candidateMem : candidate ∈
      [LocalizedCyclicPseudoRootComponentEvaluation.rootF,
        LocalizedCyclicPseudoRootComponentEvaluation.armClF,
        LocalizedCyclicPseudoRootComponentEvaluation.via24F,
        LocalizedCyclicPseudoRootComponentEvaluation.armHF]) :
    ∃ key,
      LocalizedCyclicPseudoRootComponentEvaluation.buildF .rule4a
        LocalizedCyclicPseudoRootComponentEvaluation.evalFuel candidate
        (some LocalizedCyclicPseudoRootComponentEvaluation.armF) = some key ∧
      key.constitutional.rule1a =
        (directArmFrames.stages slot).a.key.constitutional.rule1a := by
  let cursor := directArmFrames.frame.cursorAt slot
  let parent : pseudoSpatialCertified.LocalizedRerootCursor
      (carrierFuel pseudoReference) := ⟨directArmTarget, none⟩
  have valid := pseudoSpatialCertified.localizedRerootChild_valid parent cursor
    (pseudoSpatialCertified.executableLocalizedRerootChildren parent)
    (pseudoSpatialCertified.executableLocalizedRerootChildren_declarative parent)
    (directArmFrames.childAt slot)
  have computed :
      pseudoSpatialCertified.localizedOccurrenceFourLigandFrame? directArmTarget =
        some directArmFrames.frame := direct_frame
  have rootZero : cursor.occurrence.1.root =
      LocalizedCyclicPseudoRootComponentEvaluation.SA 0 := by
    have cursorRoot := pseudoSpatialCertified.localizedOccurrenceFourLigandFrame_cursor_root
      directArmTarget directArmFrames.frame computed cursor (direct_cursor_present slot)
    have targetRoot := congrArg
      (fun f : pseudoSpatialCertified.LocalizedCIPOccurrenceFrame => f.root)
      directArmFrame_eq_component_armF
    rw [LocalizedCyclicPseudoRootComponentEvaluation.armF] at targetRoot
    exact cursorRoot.trans targetRoot
  have built := (directArmFrames.stages slot).a.built
  unfold pseudoReference at built
  rw [pseudoSpatialCertified.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized] at built
  obtain ⟨twinKey, builtTwin, tableEq⟩ := actualRule1a_eq_rootComponent cursor valid
    (contextOccurrenceRead pseudoReference directArmTarget)
    (fuel := 2 * (carrierFuel pseudoReference + 1))
    (directArmFrames.stages slot).a.key built rootZero
  have occurrenceEq : cursor.occurrence.1 = candidate :=
    direct_cursor_eq_component slot candidate sameCurrent candidateMem
  have previousEq :
      cursor.previous?.map Subtype.val =
        some LocalizedCyclicPseudoRootComponentEvaluation.armF := by
    change (directArmFrames.frame.cursorAt slot).previous?.map Subtype.val =
      some LocalizedCyclicPseudoRootComponentEvaluation.armF
    rw [pseudoSpatialCertified.localizedOccurrenceFourLigandFrame_cursor_previous
        directArmTarget directArmFrames.frame computed cursor (direct_cursor_present slot)]
    exact congrArg some directArmFrame_eq_component_armF
  have inputEq :
      ((cursor.occurrence.1, cursor.previous?.map Subtype.val) :
        LocalizedCyclicPseudoRootComponentEvaluation.Frame ×
          Option LocalizedCyclicPseudoRootComponentEvaluation.Frame) =
        (candidate, some LocalizedCyclicPseudoRootComponentEvaluation.armF) :=
    Prod.ext occurrenceEq previousEq
  have callEq := congrArg
    (fun pair : LocalizedCyclicPseudoRootComponentEvaluation.Frame ×
        Option LocalizedCyclicPseudoRootComponentEvaluation.Frame =>
      LocalizedCyclicPseudoRootComponentEvaluation.buildF .rule4a
        LocalizedCyclicPseudoRootComponentEvaluation.evalFuel pair.1 pair.2) inputEq
  exact ⟨twinKey, callEq.symm.trans builtTwin, tableEq⟩

private theorem direct_slot_current (index : Fin 9)
    (adjacent : graph.Adj ⟨2, by decide⟩ index) :
    (directArmFrames.frame.cursorAt (directSlot index adjacent)).occurrence.1.node.current? =
      some (SA index) := by
  have current := directArmFrames.ligandAt (directSlot index adjacent)
  unfold pseudoReference at current
  have defined : directArmFrames.actualLigandAtoms (directSlot index adjacent) =
      pseudoSpatialCertified.detectedMultiCenterMolecule.ligandAtomAt
        directArmFrames.center
        (directArmFrames.detectedLigandPermutation (directSlot index adjacent)) := by
    unfold pseudoReference
    rfl
  rw [← defined, directSlot_atom index adjacent] at current
  exact current

private theorem direct_arm_parent_rule1a_key :
    ∃ key,
      LocalizedCyclicPseudoRootComponentEvaluation.buildF .rule4a
        LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
        LocalizedCyclicPseudoRootComponentEvaluation.rootF
        (some LocalizedCyclicPseudoRootComponentEvaluation.armF) = some key ∧
      key.constitutional.rule1a =
        (directArmFrames.stages (directSlot ⟨0, by decide⟩
          ((adj_arm 0).mpr (by simp)))).a.key.constitutional.rule1a := by
  apply actual_direct_cursor_const_rule1a _
    LocalizedCyclicPseudoRootComponentEvaluation.rootF
  · have current := direct_slot_current ⟨0, by decide⟩ ((adj_arm 0).mpr (by simp))
    rw [current]
    change some (SA ⟨0, by decide⟩) = some (SA ⟨0, by decide⟩)
    rfl
  · simp

private theorem direct_arm_cl_rule1a_key :
    ∃ key,
      LocalizedCyclicPseudoRootComponentEvaluation.buildF .rule4a
        LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
        LocalizedCyclicPseudoRootComponentEvaluation.armClF
        (some LocalizedCyclicPseudoRootComponentEvaluation.armF) = some key ∧
      key.constitutional.rule1a =
        (directArmFrames.stages (directSlot ⟨3, by decide⟩
          ((adj_arm 3).mpr (by simp)))).a.key.constitutional.rule1a := by
  apply actual_direct_cursor_const_rule1a _
    LocalizedCyclicPseudoRootComponentEvaluation.armClF
  · have current := direct_slot_current ⟨3, by decide⟩ ((adj_arm 3).mpr (by simp))
    rw [current]
    simp [LocalizedCyclicPseudoRootComponentEvaluation.armClF,
      LocalizedCyclicPseudoRootComponentEvaluation.node2,
      LocalizedCyclicPseudoRootComponentEvaluation.rootNode,
      LocalizedCyclicPseudoRootComponentEvaluation.SA, SA]
  · simp

private theorem direct_arm_carbon_rule1a_key :
    ∃ key,
      LocalizedCyclicPseudoRootComponentEvaluation.buildF .rule4a
        LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
        LocalizedCyclicPseudoRootComponentEvaluation.via24F
        (some LocalizedCyclicPseudoRootComponentEvaluation.armF) = some key ∧
      key.constitutional.rule1a =
        (directArmFrames.stages (directSlot ⟨4, by decide⟩
          ((adj_arm 4).mpr (by simp)))).a.key.constitutional.rule1a := by
  apply actual_direct_cursor_const_rule1a _
    LocalizedCyclicPseudoRootComponentEvaluation.via24F
  · have current := direct_slot_current ⟨4, by decide⟩ ((adj_arm 4).mpr (by simp))
    rw [current]
    simp [LocalizedCyclicPseudoRootComponentEvaluation.via24F,
      LocalizedCyclicPseudoRootComponentEvaluation.node24,
      LocalizedCyclicPseudoRootComponentEvaluation.node2,
      LocalizedCyclicPseudoRootComponentEvaluation.rootNode,
      LocalizedCyclicPseudoRootComponentEvaluation.SA, SA]
  · simp

private theorem direct_arm_h_rule1a_key :
    ∃ key,
      LocalizedCyclicPseudoRootComponentEvaluation.buildF .rule4a
        LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
        LocalizedCyclicPseudoRootComponentEvaluation.armHF
        (some LocalizedCyclicPseudoRootComponentEvaluation.armF) = some key ∧
      key.constitutional.rule1a =
        (directArmFrames.stages (directSlot ⟨6, by decide⟩
          ((adj_arm 6).mpr (by simp)))).a.key.constitutional.rule1a := by
  apply actual_direct_cursor_const_rule1a _
    LocalizedCyclicPseudoRootComponentEvaluation.armHF
  · have current := direct_slot_current ⟨6, by decide⟩ ((adj_arm 6).mpr (by simp))
    rw [current]
    simp [LocalizedCyclicPseudoRootComponentEvaluation.armHF,
      LocalizedCyclicPseudoRootComponentEvaluation.node2,
      LocalizedCyclicPseudoRootComponentEvaluation.rootNode,
      LocalizedCyclicPseudoRootComponentEvaluation.SA, SA]
  · simp

private def directComponentKey
    (frame : LocalizedCyclicPseudoRootComponentEvaluation.Frame) :
    OfficialRuleMajorKey LocalizedCyclicPseudoRootComponentEvaluation.Atom :=
  match LocalizedCyclicPseudoRootComponentEvaluation.buildF .rule4a
      LocalizedCyclicPseudoRootComponentEvaluation.evalFuel frame
      (some LocalizedCyclicPseudoRootComponentEvaluation.armF) with
  | some key => key.constitutional
  | none => { rule1a := [], rule1b := [], rule2 := [], sourceNodes := [], complete := false }

private theorem direct_component_sparse_order :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (directComponentKey LocalizedCyclicPseudoRootComponentEvaluation.armClF).rule1a
        (directComponentKey LocalizedCyclicPseudoRootComponentEvaluation.rootF).rule1a = Ordering.gt ∧
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (directComponentKey LocalizedCyclicPseudoRootComponentEvaluation.armClF).rule1a
        (directComponentKey LocalizedCyclicPseudoRootComponentEvaluation.via24F).rule1a = Ordering.gt ∧
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (directComponentKey LocalizedCyclicPseudoRootComponentEvaluation.armClF).rule1a
        (directComponentKey LocalizedCyclicPseudoRootComponentEvaluation.armHF).rule1a = Ordering.gt ∧
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (directComponentKey LocalizedCyclicPseudoRootComponentEvaluation.via24F).rule1a
        (directComponentKey LocalizedCyclicPseudoRootComponentEvaluation.rootF).rule1a = Ordering.gt ∧
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (directComponentKey LocalizedCyclicPseudoRootComponentEvaluation.via24F).rule1a
        (directComponentKey LocalizedCyclicPseudoRootComponentEvaluation.armHF).rule1a = Ordering.gt ∧
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (directComponentKey LocalizedCyclicPseudoRootComponentEvaluation.rootF).rule1a
        (directComponentKey LocalizedCyclicPseudoRootComponentEvaluation.armHF).rule1a = Ordering.gt := by
  decide +kernel

private theorem direct_actual_sparse_order :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (directArmFrames.stages (directSlot ⟨3, by decide⟩ ((adj_arm 3).mpr (by simp)))).a.key.constitutional.rule1a
        (directArmFrames.stages (directSlot ⟨0, by decide⟩ ((adj_arm 0).mpr (by simp)))).a.key.constitutional.rule1a = Ordering.gt ∧
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (directArmFrames.stages (directSlot ⟨3, by decide⟩ ((adj_arm 3).mpr (by simp)))).a.key.constitutional.rule1a
        (directArmFrames.stages (directSlot ⟨4, by decide⟩ ((adj_arm 4).mpr (by simp)))).a.key.constitutional.rule1a = Ordering.gt ∧
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (directArmFrames.stages (directSlot ⟨3, by decide⟩ ((adj_arm 3).mpr (by simp)))).a.key.constitutional.rule1a
        (directArmFrames.stages (directSlot ⟨6, by decide⟩ ((adj_arm 6).mpr (by simp)))).a.key.constitutional.rule1a = Ordering.gt ∧
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (directArmFrames.stages (directSlot ⟨4, by decide⟩ ((adj_arm 4).mpr (by simp)))).a.key.constitutional.rule1a
        (directArmFrames.stages (directSlot ⟨0, by decide⟩ ((adj_arm 0).mpr (by simp)))).a.key.constitutional.rule1a = Ordering.gt ∧
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (directArmFrames.stages (directSlot ⟨4, by decide⟩ ((adj_arm 4).mpr (by simp)))).a.key.constitutional.rule1a
        (directArmFrames.stages (directSlot ⟨6, by decide⟩ ((adj_arm 6).mpr (by simp)))).a.key.constitutional.rule1a = Ordering.gt ∧
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (directArmFrames.stages (directSlot ⟨0, by decide⟩ ((adj_arm 0).mpr (by simp)))).a.key.constitutional.rule1a
        (directArmFrames.stages (directSlot ⟨6, by decide⟩ ((adj_arm 6).mpr (by simp)))).a.key.constitutional.rule1a = Ordering.gt := by
  obtain ⟨pk, pb, pt⟩ := direct_arm_parent_rule1a_key
  obtain ⟨ck, cb, ct⟩ := direct_arm_cl_rule1a_key
  obtain ⟨xk, xb, xt⟩ := direct_arm_carbon_rule1a_key
  obtain ⟨hk, hb, ht⟩ := direct_arm_h_rule1a_key
  have pEq : directComponentKey LocalizedCyclicPseudoRootComponentEvaluation.rootF = pk.constitutional := by
    simp [directComponentKey, pb]
  have cEq : directComponentKey LocalizedCyclicPseudoRootComponentEvaluation.armClF = ck.constitutional := by
    simp [directComponentKey, cb]
  have xEq : directComponentKey LocalizedCyclicPseudoRootComponentEvaluation.via24F = xk.constitutional := by
    simp [directComponentKey, xb]
  have hEq : directComponentKey LocalizedCyclicPseudoRootComponentEvaluation.armHF = hk.constitutional := by
    simp [directComponentKey, hb]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← ct, ← pt, ← cEq, ← pEq]
    exact direct_component_sparse_order.1
  · rw [← ct, ← xt, ← cEq, ← xEq]
    exact direct_component_sparse_order.2.1
  · rw [← ct, ← ht, ← cEq, ← hEq]
    exact direct_component_sparse_order.2.2.1
  · rw [← xt, ← pt, ← xEq, ← pEq]
    exact direct_component_sparse_order.2.2.2.1
  · rw [← xt, ← ht, ← xEq, ← hEq]
    exact direct_component_sparse_order.2.2.2.2.1
  · rw [← pt, ← ht, ← pEq, ← hEq]
    exact direct_component_sparse_order.2.2.2.2.2

private theorem direct_compare_rule1a_of_sparse
    {left right : OfficialRuleMajorKey pseudoSpatialCertified.Atom}
    (strict : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      left.rule1a right.rule1a = Ordering.gt) :
    OfficialRuleMajorKey.compare left right = Ordering.gt := by
  rw [OfficialRuleMajorKey.compare_eq_rule1a_of_decisive
    (by rw [strict]; decide), strict]

private theorem direct_actual_order :
    OfficialRuleMajorKey.compare
        (directArmFrames.stages (directSlot ⟨3, by decide⟩ ((adj_arm 3).mpr (by simp)))).a.key.constitutional
        (directArmFrames.stages (directSlot ⟨0, by decide⟩ ((adj_arm 0).mpr (by simp)))).a.key.constitutional = Ordering.gt ∧
    OfficialRuleMajorKey.compare
        (directArmFrames.stages (directSlot ⟨3, by decide⟩ ((adj_arm 3).mpr (by simp)))).a.key.constitutional
        (directArmFrames.stages (directSlot ⟨4, by decide⟩ ((adj_arm 4).mpr (by simp)))).a.key.constitutional = Ordering.gt ∧
    OfficialRuleMajorKey.compare
        (directArmFrames.stages (directSlot ⟨3, by decide⟩ ((adj_arm 3).mpr (by simp)))).a.key.constitutional
        (directArmFrames.stages (directSlot ⟨6, by decide⟩ ((adj_arm 6).mpr (by simp)))).a.key.constitutional = Ordering.gt ∧
    OfficialRuleMajorKey.compare
        (directArmFrames.stages (directSlot ⟨4, by decide⟩ ((adj_arm 4).mpr (by simp)))).a.key.constitutional
        (directArmFrames.stages (directSlot ⟨0, by decide⟩ ((adj_arm 0).mpr (by simp)))).a.key.constitutional = Ordering.gt ∧
    OfficialRuleMajorKey.compare
        (directArmFrames.stages (directSlot ⟨4, by decide⟩ ((adj_arm 4).mpr (by simp)))).a.key.constitutional
        (directArmFrames.stages (directSlot ⟨6, by decide⟩ ((adj_arm 6).mpr (by simp)))).a.key.constitutional = Ordering.gt ∧
    OfficialRuleMajorKey.compare
        (directArmFrames.stages (directSlot ⟨0, by decide⟩ ((adj_arm 0).mpr (by simp)))).a.key.constitutional
        (directArmFrames.stages (directSlot ⟨6, by decide⟩ ((adj_arm 6).mpr (by simp)))).a.key.constitutional = Ordering.gt := by
  rcases direct_actual_sparse_order with ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩
  exact ⟨direct_compare_rule1a_of_sparse h₁, direct_compare_rule1a_of_sparse h₂,
    direct_compare_rule1a_of_sparse h₃, direct_compare_rule1a_of_sparse h₄,
    direct_compare_rule1a_of_sparse h₅, direct_compare_rule1a_of_sparse h₆⟩

private def shallowArmRootSlot : Fin 4 :=
  directSlot ⟨0, by decide⟩ ((adj_arm 0).mpr (by simp))

private def shallowArmClSlot : Fin 4 :=
  directSlot ⟨3, by decide⟩ ((adj_arm 3).mpr (by simp))

private def shallowArmCarbonSlot : Fin 4 :=
  directSlot ⟨4, by decide⟩ ((adj_arm 4).mpr (by simp))

private def shallowArmHSlot : Fin 4 :=
  directSlot ⟨6, by decide⟩ ((adj_arm 6).mpr (by simp))

private theorem shallowArmRootSlot_atom :
    directArmFrames.actualLigandAtoms shallowArmRootSlot = SA ⟨0, by decide⟩ :=
  directSlot_atom _ _

private theorem shallowArmClSlot_atom :
    directArmFrames.actualLigandAtoms shallowArmClSlot = SA ⟨3, by decide⟩ :=
  directSlot_atom _ _

private theorem shallowArmCarbonSlot_atom :
    directArmFrames.actualLigandAtoms shallowArmCarbonSlot = SA ⟨4, by decide⟩ :=
  directSlot_atom _ _

private theorem shallowArmHSlot_atom :
    directArmFrames.actualLigandAtoms shallowArmHSlot = SA ⟨6, by decide⟩ :=
  directSlot_atom _ _

private theorem shallowArm_slots_pairwise_distinct :
    shallowArmClSlot ≠ shallowArmCarbonSlot ∧
    shallowArmClSlot ≠ shallowArmRootSlot ∧
    shallowArmClSlot ≠ shallowArmHSlot ∧
    shallowArmCarbonSlot ≠ shallowArmRootSlot ∧
    shallowArmCarbonSlot ≠ shallowArmHSlot ∧
    shallowArmRootSlot ≠ shallowArmHSlot := by
  have h1 : shallowArmClSlot ≠ shallowArmRootSlot := by
    intro equal
    have atomEq := congrArg directArmFrames.actualLigandAtoms equal
    rw [shallowArmClSlot_atom, shallowArmRootSlot_atom] at atomEq
    have values := congrArg Fin.val atomEq
    norm_num [SA, LocalizedCyclicPseudoRootComponentEvaluation.SA] at values
  have h2 : shallowArmClSlot ≠ shallowArmCarbonSlot := by
    intro equal
    have atomEq := congrArg directArmFrames.actualLigandAtoms equal
    rw [shallowArmClSlot_atom, shallowArmCarbonSlot_atom] at atomEq
    have values := congrArg Fin.val atomEq
    norm_num [SA, LocalizedCyclicPseudoRootComponentEvaluation.SA] at values
  have h3 : shallowArmClSlot ≠ shallowArmHSlot := by
    intro equal
    have atomEq := congrArg directArmFrames.actualLigandAtoms equal
    rw [shallowArmClSlot_atom, shallowArmHSlot_atom] at atomEq
    have values := congrArg Fin.val atomEq
    norm_num [SA, LocalizedCyclicPseudoRootComponentEvaluation.SA] at values
  have h4 : shallowArmRootSlot ≠ shallowArmCarbonSlot := by
    intro equal
    have atomEq := congrArg directArmFrames.actualLigandAtoms equal
    rw [shallowArmRootSlot_atom, shallowArmCarbonSlot_atom] at atomEq
    have values := congrArg Fin.val atomEq
    norm_num [SA, LocalizedCyclicPseudoRootComponentEvaluation.SA] at values
  have h5 : shallowArmRootSlot ≠ shallowArmHSlot := by
    intro equal
    have atomEq := congrArg directArmFrames.actualLigandAtoms equal
    rw [shallowArmRootSlot_atom, shallowArmHSlot_atom] at atomEq
    have values := congrArg Fin.val atomEq
    norm_num [SA, LocalizedCyclicPseudoRootComponentEvaluation.SA] at values
  have h6 : shallowArmCarbonSlot ≠ shallowArmHSlot := by
    intro equal
    have atomEq := congrArg directArmFrames.actualLigandAtoms equal
    rw [shallowArmCarbonSlot_atom, shallowArmHSlot_atom] at atomEq
    have values := congrArg Fin.val atomEq
    norm_num [SA, LocalizedCyclicPseudoRootComponentEvaluation.SA] at values
  exact ⟨h2, h1, h3, h4.symm, h6, h5⟩

private theorem shallowArm_sparse_strict_pairs :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (directArmFrames.stages shallowArmClSlot).a.key.constitutional.rule1a
        (directArmFrames.stages shallowArmCarbonSlot).a.key.constitutional.rule1a = Ordering.gt ∧
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (directArmFrames.stages shallowArmClSlot).a.key.constitutional.rule1a
        (directArmFrames.stages shallowArmRootSlot).a.key.constitutional.rule1a = Ordering.gt ∧
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (directArmFrames.stages shallowArmClSlot).a.key.constitutional.rule1a
        (directArmFrames.stages shallowArmHSlot).a.key.constitutional.rule1a = Ordering.gt ∧
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (directArmFrames.stages shallowArmCarbonSlot).a.key.constitutional.rule1a
        (directArmFrames.stages shallowArmRootSlot).a.key.constitutional.rule1a = Ordering.gt ∧
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (directArmFrames.stages shallowArmCarbonSlot).a.key.constitutional.rule1a
        (directArmFrames.stages shallowArmHSlot).a.key.constitutional.rule1a = Ordering.gt ∧
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (directArmFrames.stages shallowArmRootSlot).a.key.constitutional.rule1a
        (directArmFrames.stages shallowArmHSlot).a.key.constitutional.rule1a = Ordering.gt := by
  rcases direct_actual_sparse_order with ⟨cr, cc, ch, xr, xh, rh⟩
  simpa [shallowArmClSlot, shallowArmRootSlot, shallowArmCarbonSlot, shallowArmHSlot] using
    ⟨cc, cr, ch, xr, xh, rh⟩

private theorem shallowArm_actual_order :
    OfficialRuleMajorKey.compare (directArmFrames.stages shallowArmClSlot).a.key.constitutional
        (directArmFrames.stages shallowArmCarbonSlot).a.key.constitutional = Ordering.gt ∧
    OfficialRuleMajorKey.compare (directArmFrames.stages shallowArmClSlot).a.key.constitutional
        (directArmFrames.stages shallowArmRootSlot).a.key.constitutional = Ordering.gt ∧
    OfficialRuleMajorKey.compare (directArmFrames.stages shallowArmClSlot).a.key.constitutional
        (directArmFrames.stages shallowArmHSlot).a.key.constitutional = Ordering.gt ∧
    OfficialRuleMajorKey.compare (directArmFrames.stages shallowArmCarbonSlot).a.key.constitutional
        (directArmFrames.stages shallowArmRootSlot).a.key.constitutional = Ordering.gt ∧
    OfficialRuleMajorKey.compare (directArmFrames.stages shallowArmCarbonSlot).a.key.constitutional
        (directArmFrames.stages shallowArmHSlot).a.key.constitutional = Ordering.gt ∧
    OfficialRuleMajorKey.compare (directArmFrames.stages shallowArmRootSlot).a.key.constitutional
        (directArmFrames.stages shallowArmHSlot).a.key.constitutional = Ordering.gt := by
  rcases direct_actual_order with ⟨cr, cc, ch, xr, xh, rh⟩
  simpa [shallowArmClSlot, shallowArmRootSlot, shallowArmCarbonSlot, shallowArmHSlot] using
    ⟨cc, cr, ch, xr, xh, rh⟩

private theorem closing_slot_current (slot : Fin 4) (index : Fin 9)
    (atomEq : directClosingFrames.actualLigandAtoms slot = SA index) :
    (directClosingFrames.frame.cursorAt slot).occurrence.1.node.current? = some (SA index) := by
  have current := directClosingFrames.ligandAt slot
  unfold pseudoReference at current
  have defined : directClosingFrames.actualLigandAtoms slot =
      pseudoSpatialCertified.detectedMultiCenterMolecule.ligandAtomAt
        directClosingFrames.center (directClosingFrames.detectedLigandPermutation slot) := by
    unfold pseudoReference
    rfl
  have actualAtom : pseudoSpatialCertified.detectedMultiCenterMolecule.ligandAtomAt
      directClosingFrames.center (directClosingFrames.detectedLigandPermutation slot) = SA index := by
    rw [← defined]
    exact atomEq
  rw [actualAtom] at current
  exact current

private theorem actual_closing_cursor_const_rule1a
    (slot : Fin 4)
    (candidate : LocalizedCyclicPseudoRootComponentEvaluation.Frame)
    (sameCurrent : (directClosingFrames.frame.cursorAt slot).occurrence.1.node.current? =
      candidate.node.current?)
    (candidateMem : candidate ∈
      [LocalizedCyclicPseudoRootComponentEvaluation.rootF,
        LocalizedCyclicPseudoRootComponentEvaluation.via42F,
        LocalizedCyclicPseudoRootComponentEvaluation.closeHF,
        LocalizedCyclicPseudoRootComponentEvaluation.closeClF]) :
    ∃ key,
      LocalizedCyclicPseudoRootComponentEvaluation.buildF .rule4a
        LocalizedCyclicPseudoRootComponentEvaluation.evalFuel candidate
        (some LocalizedCyclicPseudoRootComponentEvaluation.closeF) = some key ∧
      key.constitutional.rule1a =
        (directClosingFrames.stages slot).a.key.constitutional.rule1a := by
  let cursor := directClosingFrames.frame.cursorAt slot
  let parent : pseudoSpatialCertified.LocalizedRerootCursor
      (carrierFuel pseudoReference) := ⟨directClosingTarget, none⟩
  have valid := pseudoSpatialCertified.localizedRerootChild_valid parent cursor
    (pseudoSpatialCertified.executableLocalizedRerootChildren parent)
    (pseudoSpatialCertified.executableLocalizedRerootChildren_declarative parent)
    (directClosingFrames.childAt slot)
  have computed :
      pseudoSpatialCertified.localizedOccurrenceFourLigandFrame? directClosingTarget =
        some directClosingFrames.frame := closing_frame
  have rootZero : cursor.occurrence.1.root =
      LocalizedCyclicPseudoRootComponentEvaluation.SA 0 := by
    have cursorRoot := pseudoSpatialCertified.localizedOccurrenceFourLigandFrame_cursor_root
      directClosingTarget directClosingFrames.frame computed cursor (closing_cursor_present slot)
    have targetRoot := congrArg
      (fun f : pseudoSpatialCertified.LocalizedCIPOccurrenceFrame => f.root)
      directClosingFrame_eq_component_closeF
    rw [LocalizedCyclicPseudoRootComponentEvaluation.closeF] at targetRoot
    exact cursorRoot.trans targetRoot
  have built := (directClosingFrames.stages slot).a.built
  unfold pseudoReference at built
  rw [pseudoSpatialCertified.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized] at built
  obtain ⟨twinKey, builtTwin, tableEq⟩ := actualRule1a_eq_rootComponent cursor valid
    (contextOccurrenceRead pseudoReference directClosingTarget)
    (fuel := 2 * (carrierFuel pseudoReference + 1))
    (directClosingFrames.stages slot).a.key built rootZero
  have occurrenceEq : cursor.occurrence.1 = candidate :=
    closing_cursor_eq_component slot candidate sameCurrent candidateMem
  have previousEq : cursor.previous?.map Subtype.val =
      some LocalizedCyclicPseudoRootComponentEvaluation.closeF := by
    change (directClosingFrames.frame.cursorAt slot).previous?.map Subtype.val =
      some LocalizedCyclicPseudoRootComponentEvaluation.closeF
    rw [pseudoSpatialCertified.localizedOccurrenceFourLigandFrame_cursor_previous
      directClosingTarget directClosingFrames.frame computed cursor (closing_cursor_present slot)]
    exact congrArg some directClosingFrame_eq_component_closeF
  have inputEq :
      ((cursor.occurrence.1, cursor.previous?.map Subtype.val) :
        LocalizedCyclicPseudoRootComponentEvaluation.Frame ×
          Option LocalizedCyclicPseudoRootComponentEvaluation.Frame) =
        (candidate, some LocalizedCyclicPseudoRootComponentEvaluation.closeF) :=
    Prod.ext occurrenceEq previousEq
  have callEq := congrArg
    (fun pair : LocalizedCyclicPseudoRootComponentEvaluation.Frame ×
        Option LocalizedCyclicPseudoRootComponentEvaluation.Frame =>
      LocalizedCyclicPseudoRootComponentEvaluation.buildF .rule4a
        LocalizedCyclicPseudoRootComponentEvaluation.evalFuel pair.1 pair.2) inputEq
  exact ⟨twinKey, callEq.symm.trans builtTwin, tableEq⟩

private theorem shallowClosing_root_rule1a_key :
    ∃ key,
      LocalizedCyclicPseudoRootComponentEvaluation.buildF .rule4a
        LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
        LocalizedCyclicPseudoRootComponentEvaluation.rootF
        (some LocalizedCyclicPseudoRootComponentEvaluation.closeF) = some key ∧
      key.constitutional.rule1a =
        (directClosingFrames.stages shallowClosingRootSlot).a.key.constitutional.rule1a := by
  apply actual_closing_cursor_const_rule1a shallowClosingRootSlot
    LocalizedCyclicPseudoRootComponentEvaluation.rootF
  · have current := closing_slot_current shallowClosingRootSlot ⟨0, by decide⟩
      shallowClosingRootSlot_atom
    rw [current]
    change some (SA ⟨0, by decide⟩) = some (SA ⟨0, by decide⟩)
    rfl
  · simp

private theorem shallowClosing_cl_rule1a_key :
    ∃ key,
      LocalizedCyclicPseudoRootComponentEvaluation.buildF .rule4a
        LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
        LocalizedCyclicPseudoRootComponentEvaluation.closeClF
        (some LocalizedCyclicPseudoRootComponentEvaluation.closeF) = some key ∧
      key.constitutional.rule1a =
        (directClosingFrames.stages shallowClosingClSlot).a.key.constitutional.rule1a := by
  apply actual_closing_cursor_const_rule1a shallowClosingClSlot
    LocalizedCyclicPseudoRootComponentEvaluation.closeClF
  · exact (closing_slot_current shallowClosingClSlot ⟨8, by decide⟩
      shallowClosingClSlot_atom).trans (by simp [LocalizedCyclicPseudoRootComponentEvaluation.closeClF,
        LocalizedCyclicPseudoRootComponentEvaluation.node4,
        LocalizedCyclicPseudoRootComponentEvaluation.rootNode,
        LocalizedCyclicPseudoRootComponentEvaluation.SA, SA])
  · simp

private theorem shallowClosing_carbon_rule1a_key :
    ∃ key,
      LocalizedCyclicPseudoRootComponentEvaluation.buildF .rule4a
        LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
        LocalizedCyclicPseudoRootComponentEvaluation.via42F
        (some LocalizedCyclicPseudoRootComponentEvaluation.closeF) = some key ∧
      key.constitutional.rule1a =
        (directClosingFrames.stages shallowClosingCarbonSlot).a.key.constitutional.rule1a := by
  apply actual_closing_cursor_const_rule1a shallowClosingCarbonSlot
    LocalizedCyclicPseudoRootComponentEvaluation.via42F
  · exact (closing_slot_current shallowClosingCarbonSlot ⟨2, by decide⟩
      shallowClosingCarbonSlot_atom).trans (by simp [LocalizedCyclicPseudoRootComponentEvaluation.via42F,
        LocalizedCyclicPseudoRootComponentEvaluation.node42,
        LocalizedCyclicPseudoRootComponentEvaluation.node4,
        LocalizedCyclicPseudoRootComponentEvaluation.rootNode,
        LocalizedCyclicPseudoRootComponentEvaluation.SA, SA])
  · simp

private theorem shallowClosing_h_rule1a_key :
    ∃ key,
      LocalizedCyclicPseudoRootComponentEvaluation.buildF .rule4a
        LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
        LocalizedCyclicPseudoRootComponentEvaluation.closeHF
        (some LocalizedCyclicPseudoRootComponentEvaluation.closeF) = some key ∧
      key.constitutional.rule1a =
        (directClosingFrames.stages shallowClosingHSlot).a.key.constitutional.rule1a := by
  apply actual_closing_cursor_const_rule1a shallowClosingHSlot
    LocalizedCyclicPseudoRootComponentEvaluation.closeHF
  · exact (closing_slot_current shallowClosingHSlot ⟨7, by decide⟩
      shallowClosingHSlot_atom).trans (by simp [LocalizedCyclicPseudoRootComponentEvaluation.closeHF,
        LocalizedCyclicPseudoRootComponentEvaluation.node4,
        LocalizedCyclicPseudoRootComponentEvaluation.rootNode,
        LocalizedCyclicPseudoRootComponentEvaluation.SA, SA])
  · simp

private def shallowClosingComponentKey
    (frame : LocalizedCyclicPseudoRootComponentEvaluation.Frame) :
    OfficialRuleMajorKey LocalizedCyclicPseudoRootComponentEvaluation.Atom :=
  match LocalizedCyclicPseudoRootComponentEvaluation.buildF .rule4a
      LocalizedCyclicPseudoRootComponentEvaluation.evalFuel frame
      (some LocalizedCyclicPseudoRootComponentEvaluation.closeF) with
  | some key => key.constitutional
  | none => { rule1a := [], rule1b := [], rule2 := [], sourceNodes := [], complete := false }

private theorem shallowClosing_component_sparse_order :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (shallowClosingComponentKey LocalizedCyclicPseudoRootComponentEvaluation.closeClF).rule1a
        (shallowClosingComponentKey LocalizedCyclicPseudoRootComponentEvaluation.via42F).rule1a = Ordering.gt ∧
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (shallowClosingComponentKey LocalizedCyclicPseudoRootComponentEvaluation.closeClF).rule1a
        (shallowClosingComponentKey LocalizedCyclicPseudoRootComponentEvaluation.rootF).rule1a = Ordering.gt ∧
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (shallowClosingComponentKey LocalizedCyclicPseudoRootComponentEvaluation.closeClF).rule1a
        (shallowClosingComponentKey LocalizedCyclicPseudoRootComponentEvaluation.closeHF).rule1a = Ordering.gt ∧
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (shallowClosingComponentKey LocalizedCyclicPseudoRootComponentEvaluation.via42F).rule1a
        (shallowClosingComponentKey LocalizedCyclicPseudoRootComponentEvaluation.rootF).rule1a = Ordering.gt ∧
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (shallowClosingComponentKey LocalizedCyclicPseudoRootComponentEvaluation.via42F).rule1a
        (shallowClosingComponentKey LocalizedCyclicPseudoRootComponentEvaluation.closeHF).rule1a = Ordering.gt ∧
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (shallowClosingComponentKey LocalizedCyclicPseudoRootComponentEvaluation.rootF).rule1a
        (shallowClosingComponentKey LocalizedCyclicPseudoRootComponentEvaluation.closeHF).rule1a = Ordering.gt := by
  decide +kernel

private theorem shallowClosing_sparse_strict_pairs :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (directClosingFrames.stages shallowClosingClSlot).a.key.constitutional.rule1a
        (directClosingFrames.stages shallowClosingCarbonSlot).a.key.constitutional.rule1a = Ordering.gt ∧
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (directClosingFrames.stages shallowClosingClSlot).a.key.constitutional.rule1a
        (directClosingFrames.stages shallowClosingRootSlot).a.key.constitutional.rule1a = Ordering.gt ∧
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (directClosingFrames.stages shallowClosingClSlot).a.key.constitutional.rule1a
        (directClosingFrames.stages shallowClosingHSlot).a.key.constitutional.rule1a = Ordering.gt ∧
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (directClosingFrames.stages shallowClosingCarbonSlot).a.key.constitutional.rule1a
        (directClosingFrames.stages shallowClosingRootSlot).a.key.constitutional.rule1a = Ordering.gt ∧
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (directClosingFrames.stages shallowClosingCarbonSlot).a.key.constitutional.rule1a
        (directClosingFrames.stages shallowClosingHSlot).a.key.constitutional.rule1a = Ordering.gt ∧
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (directClosingFrames.stages shallowClosingRootSlot).a.key.constitutional.rule1a
        (directClosingFrames.stages shallowClosingHSlot).a.key.constitutional.rule1a = Ordering.gt := by
  obtain ⟨rk, rb, rt⟩ := shallowClosing_root_rule1a_key
  obtain ⟨ck, cb, ct⟩ := shallowClosing_cl_rule1a_key
  obtain ⟨xk, xb, xt⟩ := shallowClosing_carbon_rule1a_key
  obtain ⟨hk, hb, ht⟩ := shallowClosing_h_rule1a_key
  have rEq : shallowClosingComponentKey LocalizedCyclicPseudoRootComponentEvaluation.rootF = rk.constitutional := by
    simp [shallowClosingComponentKey, rb]
  have cEq : shallowClosingComponentKey LocalizedCyclicPseudoRootComponentEvaluation.closeClF = ck.constitutional := by
    simp [shallowClosingComponentKey, cb]
  have xEq : shallowClosingComponentKey LocalizedCyclicPseudoRootComponentEvaluation.via42F = xk.constitutional := by
    simp [shallowClosingComponentKey, xb]
  have hEq : shallowClosingComponentKey LocalizedCyclicPseudoRootComponentEvaluation.closeHF = hk.constitutional := by
    simp [shallowClosingComponentKey, hb]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← ct, ← xt, ← cEq, ← xEq]
    exact shallowClosing_component_sparse_order.1
  · rw [← ct, ← rt, ← cEq, ← rEq]
    exact shallowClosing_component_sparse_order.2.1
  · rw [← ct, ← ht, ← cEq, ← hEq]
    exact shallowClosing_component_sparse_order.2.2.1
  · rw [← xt, ← rt, ← xEq, ← rEq]
    exact shallowClosing_component_sparse_order.2.2.2.1
  · rw [← xt, ← ht, ← xEq, ← hEq]
    exact shallowClosing_component_sparse_order.2.2.2.2.1
  · rw [← rt, ← ht, ← rEq, ← hEq]
    exact shallowClosing_component_sparse_order.2.2.2.2.2

private theorem shallowClosing_actual_order :
    OfficialRuleMajorKey.compare (directClosingFrames.stages shallowClosingClSlot).a.key.constitutional
        (directClosingFrames.stages shallowClosingCarbonSlot).a.key.constitutional = Ordering.gt ∧
    OfficialRuleMajorKey.compare (directClosingFrames.stages shallowClosingClSlot).a.key.constitutional
        (directClosingFrames.stages shallowClosingRootSlot).a.key.constitutional = Ordering.gt ∧
    OfficialRuleMajorKey.compare (directClosingFrames.stages shallowClosingClSlot).a.key.constitutional
        (directClosingFrames.stages shallowClosingHSlot).a.key.constitutional = Ordering.gt ∧
    OfficialRuleMajorKey.compare (directClosingFrames.stages shallowClosingCarbonSlot).a.key.constitutional
        (directClosingFrames.stages shallowClosingRootSlot).a.key.constitutional = Ordering.gt ∧
    OfficialRuleMajorKey.compare (directClosingFrames.stages shallowClosingCarbonSlot).a.key.constitutional
        (directClosingFrames.stages shallowClosingHSlot).a.key.constitutional = Ordering.gt ∧
    OfficialRuleMajorKey.compare (directClosingFrames.stages shallowClosingRootSlot).a.key.constitutional
        (directClosingFrames.stages shallowClosingHSlot).a.key.constitutional = Ordering.gt := by
  rcases shallowClosing_sparse_strict_pairs with ⟨a,b,c,d,e,f⟩
  exact ⟨direct_compare_rule1a_of_sparse a, direct_compare_rule1a_of_sparse b,
    direct_compare_rule1a_of_sparse c, direct_compare_rule1a_of_sparse d,
    direct_compare_rule1a_of_sparse e, direct_compare_rule1a_of_sparse f⟩

private theorem shallowClosing_slots_pairwise_distinct :
    shallowClosingClSlot ≠ shallowClosingCarbonSlot ∧
    shallowClosingClSlot ≠ shallowClosingRootSlot ∧
    shallowClosingClSlot ≠ shallowClosingHSlot ∧
    shallowClosingCarbonSlot ≠ shallowClosingRootSlot ∧
    shallowClosingCarbonSlot ≠ shallowClosingHSlot ∧
    shallowClosingRootSlot ≠ shallowClosingHSlot := by
  have h1 : shallowClosingClSlot ≠ shallowClosingCarbonSlot := by
    intro e; have h := congrArg directClosingFrames.actualLigandAtoms e
    rw [shallowClosingClSlot_atom, shallowClosingCarbonSlot_atom] at h
    have v := congrArg Fin.val h
    norm_num [SA, LocalizedCyclicPseudoRootComponentEvaluation.SA] at v
  have h2 : shallowClosingClSlot ≠ shallowClosingRootSlot := by
    intro e; have h := congrArg directClosingFrames.actualLigandAtoms e
    rw [shallowClosingClSlot_atom, shallowClosingRootSlot_atom] at h
    have v := congrArg Fin.val h
    norm_num [SA, LocalizedCyclicPseudoRootComponentEvaluation.SA] at v
  have h3 : shallowClosingClSlot ≠ shallowClosingHSlot := by
    intro e; have h := congrArg directClosingFrames.actualLigandAtoms e
    rw [shallowClosingClSlot_atom, shallowClosingHSlot_atom] at h
    have v := congrArg Fin.val h
    norm_num [SA, LocalizedCyclicPseudoRootComponentEvaluation.SA] at v
  have h4 : shallowClosingCarbonSlot ≠ shallowClosingRootSlot := by
    intro e; have h := congrArg directClosingFrames.actualLigandAtoms e
    rw [shallowClosingCarbonSlot_atom, shallowClosingRootSlot_atom] at h
    have v := congrArg Fin.val h
    norm_num [SA, LocalizedCyclicPseudoRootComponentEvaluation.SA] at v
  have h5 : shallowClosingCarbonSlot ≠ shallowClosingHSlot := by
    intro e; have h := congrArg directClosingFrames.actualLigandAtoms e
    rw [shallowClosingCarbonSlot_atom, shallowClosingHSlot_atom] at h
    have v := congrArg Fin.val h
    norm_num [SA, LocalizedCyclicPseudoRootComponentEvaluation.SA] at v
  have h6 : shallowClosingRootSlot ≠ shallowClosingHSlot := by
    intro e; have h := congrArg directClosingFrames.actualLigandAtoms e
    rw [shallowClosingRootSlot_atom, shallowClosingHSlot_atom] at h
    have v := congrArg Fin.val h
    norm_num [SA, LocalizedCyclicPseudoRootComponentEvaluation.SA] at v
  exact ⟨h1,h2,h3,h4,h5,h6⟩

private theorem shallowArm_retained_compare_of_rule1a
    (left right : Fin 4)
    (decisive : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (directArmFrames.stages left).a.key.constitutional.rule1a
      (directArmFrames.stages right).a.key.constitutional.rule1a ≠ Ordering.eq) :
    compare (directArmFrames.retainedKeys left) (directArmFrames.retainedKeys right) =
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (directArmFrames.stages left).a.key.constitutional.rule1a
        (directArmFrames.stages right).a.key.constitutional.rule1a := by
  have compoundReadback (index : Fin 4) :
      (directArmFrames.compounds index).prior.rule4aKey = (directArmFrames.stages index).a.key := by
    let view := contextOccurrenceView pseudoReference directArmTarget
    let read := fun source => pseudoSpatialCertified.localizedDependencyLabel directArmTarget view source
    have uniformBuilt :
        pseudoSpatialCertified.buildRuleMajorCompoundRule45KeyWith?
          (fun stage position => pseudoSpatialCertified.buildRuleMajorCumulativeWithRead?
            stage read (2 * (carrierFuel pseudoReference + 1)) position)
          (directArmFrames.frame.cursorAt index) = some (directArmFrames.compounds index) := by
      rw [← pseudoSpatialCertified.buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor]
      rw [← pseudoSpatialCertified.buildActualRuleMajorCompoundRule45KeyExec?_eq]
      exact directArmFrames.compoundBuilt index
    exact (pseudoSpatialCertified.contextStages_compound_readback
      (directArmFrames.stages index) uniformBuilt).1
  have full := directArmFrames.retainedActual_fullOrdering spatial_simpleBonded left right
  have comparison := CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundThroughRule5_eq_rule1a_of_decisive
    pseudoSpatialCertified (directArmFrames.compounds left) (directArmFrames.compounds right) (by
      rw [compoundReadback left, compoundReadback right]
      exact decisive)
  calc
    compare (directArmFrames.retainedKeys left) (directArmFrames.retainedKeys right) =
        (pseudoSpatialCertified.compareLocalizedRerootCompoundThroughRule5
          (directArmFrames.compounds left) (directArmFrames.compounds right)).ordering := full.symm
    _ = OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (directArmFrames.stages left).a.key.constitutional.rule1a
        (directArmFrames.stages right).a.key.constitutional.rule1a := by
      rw [comparison, compoundReadback left, compoundReadback right]

private theorem shallowArm_retained_lt
    (higher lower : Fin 4)
    (sparse : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (directArmFrames.stages higher).a.key.constitutional.rule1a
      (directArmFrames.stages lower).a.key.constitutional.rule1a = Ordering.gt) :
    directArmFrames.retainedKeys lower < directArmFrames.retainedKeys higher := by
  have decisive : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (directArmFrames.stages higher).a.key.constitutional.rule1a
      (directArmFrames.stages lower).a.key.constitutional.rule1a ≠ Ordering.eq := by
    rw [sparse]
    decide
  have comparison := shallowArm_retained_compare_of_rule1a higher lower decisive
  rw [sparse] at comparison
  exact (completeLigandRule5Key_compare_gt_iff
    (directArmFrames.retainedKeys higher) (directArmFrames.retainedKeys lower)).mp comparison

private theorem shallowArm_retained_order :
    [shallowArmClSlot, shallowArmCarbonSlot, shallowArmRootSlot, shallowArmHSlot].Pairwise
      (fun left right => directArmFrames.retainedKeys right < directArmFrames.retainedKeys left) := by
  rcases shallowArm_sparse_strict_pairs with ⟨clParent, clDup, clH, parentDup, parentH, dupH⟩
  apply List.Pairwise.cons
  · intro slot member
    simp only [List.mem_cons] at member
    rcases member with equal | equal | equal | empty
    · subst slot
      exact shallowArm_retained_lt shallowArmClSlot shallowArmCarbonSlot clParent
    · subst slot
      exact shallowArm_retained_lt shallowArmClSlot shallowArmRootSlot clDup
    · subst slot
      exact shallowArm_retained_lt shallowArmClSlot shallowArmHSlot clH
    · simp at empty
  · apply List.Pairwise.cons
    · intro slot member
      simp only [List.mem_cons] at member
      rcases member with equal | equal | empty
      · subst slot
        exact shallowArm_retained_lt shallowArmCarbonSlot shallowArmRootSlot parentDup
      · subst slot
        exact shallowArm_retained_lt shallowArmCarbonSlot shallowArmHSlot parentH
      · simp at empty
    · apply List.Pairwise.cons
      · intro slot member
        simp only [List.mem_cons] at member
        rcases member with equal | empty
        · subst slot
          exact shallowArm_retained_lt shallowArmRootSlot shallowArmHSlot dupH
        · simp at empty
      · apply List.Pairwise.cons
        · intro slot member
          simp at member
        · exact List.Pairwise.nil

private theorem shallowArm_fin4_four_distinct_perm {a b c d : Fin 4}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    [a, b, c, d].Perm (List.finRange 4) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp_all <;> decide

private theorem shallowArm_order_perm :
    [shallowArmClSlot, shallowArmCarbonSlot, shallowArmRootSlot, shallowArmHSlot].Perm (List.finRange 4) := by
  rcases shallowArm_slots_pairwise_distinct with ⟨hab, hac, had, hbc, hbd, hcd⟩
  exact shallowArm_fin4_four_distinct_perm hab hac had hbc hbd hcd

private theorem shallowArm_retained_prior_compare_of_rule1a
    (left right : Fin 4)
    (decisive : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (directArmFrames.stages left).a.key.constitutional.rule1a
      (directArmFrames.stages right).a.key.constitutional.rule1a ≠ Ordering.eq) :
    compare (ofLex (directArmFrames.retainedKeys left)).1
        (ofLex (directArmFrames.retainedKeys right)).1 =
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (directArmFrames.stages left).a.key.constitutional.rule1a
        (directArmFrames.stages right).a.key.constitutional.rule1a := by
  have compoundReadback (index : Fin 4) :
      (directArmFrames.compounds index).prior.rule4aKey = (directArmFrames.stages index).a.key := by
    let view := contextOccurrenceView pseudoReference directArmTarget
    let read := fun source => pseudoSpatialCertified.localizedDependencyLabel directArmTarget view source
    have uniformBuilt :
        pseudoSpatialCertified.buildRuleMajorCompoundRule45KeyWith?
          (fun stage position => pseudoSpatialCertified.buildRuleMajorCumulativeWithRead?
            stage read (2 * (carrierFuel pseudoReference + 1)) position)
          (directArmFrames.frame.cursorAt index) = some (directArmFrames.compounds index) := by
      rw [← pseudoSpatialCertified.buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor]
      rw [← pseudoSpatialCertified.buildActualRuleMajorCompoundRule45KeyExec?_eq]
      exact directArmFrames.compoundBuilt index
    exact (pseudoSpatialCertified.contextStages_compound_readback
      (directArmFrames.stages index) uniformBuilt).1
  have priorAgreement := directArmFrames.retainedActual_priorComparison spatial_simpleBonded left right
  have constEq := OfficialRuleMajorKey.compare_eq_rule1a_of_decisive
    (left := (directArmFrames.compounds left).prior.rule4aKey.constitutional)
    (right := (directArmFrames.compounds right).prior.rule4aKey.constitutional) (by
      rw [compoundReadback left, compoundReadback right]
      exact decisive)
  have constNe : OfficialRuleMajorKey.compare
      (directArmFrames.compounds left).prior.rule4aKey.constitutional
      (directArmFrames.compounds right).prior.rule4aKey.constitutional ≠ Ordering.eq := by
    rw [constEq, compoundReadback left, compoundReadback right]
    exact decisive
  have cumulativeEq : pseudoSpatialCertified.compareLocalizedRerootCumulativeRule45Keys
      (directArmFrames.compounds left).prior.rule4aKey
      (directArmFrames.compounds right).prior.rule4aKey =
      OfficialRuleMajorKey.compare
        (directArmFrames.compounds left).prior.rule4aKey.constitutional
        (directArmFrames.compounds right).prior.rule4aKey.constitutional := by
    unfold CertifiedLocalizedCIPInput.compareLocalizedRerootCumulativeRule45Keys
    refine ConstitutionalLexAlgebra.compareLex_eq_left_of_left_ne_eq _ _ _ _ ?_
    simpa [Ordering.byKey] using constNe
  have cumulativeNe : pseudoSpatialCertified.compareLocalizedRerootCumulativeRule45Keys
      (directArmFrames.compounds left).prior.rule4aKey
      (directArmFrames.compounds right).prior.rule4aKey ≠ Ordering.eq := by
    rw [cumulativeEq]
    exact constNe
  have compoundComparison :=
    CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundRule4bcKeys_eq_rule4a_of_ne
      pseudoSpatialCertified (directArmFrames.compounds left).prior
      (directArmFrames.compounds right).prior cumulativeNe
  calc
    compare (ofLex (directArmFrames.retainedKeys left)).1
        (ofLex (directArmFrames.retainedKeys right)).1 =
      pseudoSpatialCertified.compareLocalizedRerootCompoundRule4bcKeys
        (directArmFrames.compounds left).prior (directArmFrames.compounds right).prior :=
      priorAgreement.symm
    _ = pseudoSpatialCertified.compareLocalizedRerootCumulativeRule45Keys
        (directArmFrames.compounds left).prior.rule4aKey
        (directArmFrames.compounds right).prior.rule4aKey := compoundComparison
    _ = OfficialRuleMajorKey.compare
        (directArmFrames.compounds left).prior.rule4aKey.constitutional
        (directArmFrames.compounds right).prior.rule4aKey.constitutional := cumulativeEq
    _ = OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (directArmFrames.stages left).a.key.constitutional.rule1a
        (directArmFrames.stages right).a.key.constitutional.rule1a := by
      rw [OfficialRuleMajorKey.compare_eq_rule1a_of_decisive (by
        rw [compoundReadback left, compoundReadback right]
        exact decisive), compoundReadback left, compoundReadback right]

private theorem shallowArm_retained_prior_lt
    (higher lower : Fin 4)
    (sparse : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (directArmFrames.stages higher).a.key.constitutional.rule1a
      (directArmFrames.stages lower).a.key.constitutional.rule1a = Ordering.gt) :
    (ofLex (directArmFrames.retainedKeys lower)).1 <
      (ofLex (directArmFrames.retainedKeys higher)).1 := by
  have decisive : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (directArmFrames.stages higher).a.key.constitutional.rule1a
      (directArmFrames.stages lower).a.key.constitutional.rule1a ≠ Ordering.eq := by
    rw [sparse]
    decide
  have comparison := shallowArm_retained_prior_compare_of_rule1a higher lower decisive
  rw [sparse] at comparison
  exact (completeLigandPriorKey_compare_gt_iff
    (ofLex (directArmFrames.retainedKeys higher)).1
    (ofLex (directArmFrames.retainedKeys lower)).1).mp comparison

private theorem shallowArm_retained_prior_order :
    [shallowArmClSlot, shallowArmCarbonSlot, shallowArmRootSlot, shallowArmHSlot].Pairwise
      (fun left right => (ofLex (directArmFrames.retainedKeys right)).1 <
        (ofLex (directArmFrames.retainedKeys left)).1) := by
  rcases shallowArm_sparse_strict_pairs with ⟨clParent, clDup, clH, parentDup, parentH, dupH⟩
  apply List.Pairwise.cons
  · intro slot member
    simp only [List.mem_cons] at member
    rcases member with equal | equal | equal | empty
    · subst slot
      exact shallowArm_retained_prior_lt shallowArmClSlot shallowArmCarbonSlot clParent
    · subst slot
      exact shallowArm_retained_prior_lt shallowArmClSlot shallowArmRootSlot clDup
    · subst slot
      exact shallowArm_retained_prior_lt shallowArmClSlot shallowArmHSlot clH
    · simp at empty
  · apply List.Pairwise.cons
    · intro slot member
      simp only [List.mem_cons] at member
      rcases member with equal | equal | empty
      · subst slot
        exact shallowArm_retained_prior_lt shallowArmCarbonSlot shallowArmRootSlot parentDup
      · subst slot
        exact shallowArm_retained_prior_lt shallowArmCarbonSlot shallowArmHSlot parentH
      · simp at empty
    · apply List.Pairwise.cons
      · intro slot member
        simp only [List.mem_cons] at member
        rcases member with equal | empty
        · subst slot
          exact shallowArm_retained_prior_lt shallowArmRootSlot shallowArmHSlot dupH
        · simp at empty
      · apply List.Pairwise.cons
        · intro slot member
          simp at member
        · exact List.Pairwise.nil

private theorem shallowArm_retainedPrior_pairwise_injective
    {α : Type} [LinearOrder α] {xs : List (Fin 4)} {key : Fin 4 → α}
    (perm : xs.Perm (List.finRange 4))
    (sorted : xs.Pairwise (fun i j => key j < key i)) :
    Function.Injective key := by
  intro i j equal
  by_contra different
  have hi : i ∈ xs := perm.mem_iff.mpr (List.mem_finRange i)
  have hj : j ∈ xs := perm.mem_iff.mpr (List.mem_finRange j)
  have either := (List.Pairwise.forall (fun _ _ h => h.symm)
    (sorted.imp fun h => Or.inr h)) hi hj different
  rw [equal] at either
  exact either.elim (lt_irrefl _) (lt_irrefl _)

private theorem shallowArm_prior_injective :
    Function.Injective (fun slot => (ofLex (directArmFrames.retainedKeys slot)).1) :=
  shallowArm_retainedPrior_pairwise_injective shallowArm_order_perm shallowArm_retained_prior_order

private theorem shallowArm_not_prior_pair (left right : Fin 4) (different : left ≠ right) :
    ¬ CompletePriorPair directArmFrames.retainedKeys left right := by
  intro pair
  exact different (shallowArm_prior_injective pair.2)

private theorem shallowArm_completeRule5PairCount_zero :
    completeRule5PairCount directArmFrames.retainedKeys = 0 := by
  have h01 : ¬ CompletePriorPair directArmFrames.retainedKeys 0 1 :=
    shallowArm_not_prior_pair 0 1 (by decide)
  have h02 : ¬ CompletePriorPair directArmFrames.retainedKeys 0 2 :=
    shallowArm_not_prior_pair 0 2 (by decide)
  have h12 : ¬ CompletePriorPair directArmFrames.retainedKeys 1 2 :=
    shallowArm_not_prior_pair 1 2 (by decide)
  have h03 : ¬ CompletePriorPair directArmFrames.retainedKeys 0 3 :=
    shallowArm_not_prior_pair 0 3 (by decide)
  have h13 : ¬ CompletePriorPair directArmFrames.retainedKeys 1 3 :=
    shallowArm_not_prior_pair 1 3 (by decide)
  have h23 : ¬ CompletePriorPair directArmFrames.retainedKeys 2 3 :=
    shallowArm_not_prior_pair 2 3 (by decide)
  rw [completeRule5PairCount, sourceEnantiomorphicPairCount_eq_filter_length]
  simp [sourceUnorderedPairList, h01, h02, h12, h03, h13, h23]




private theorem shallowClosing_retained_compare_of_rule1a
    (left right : Fin 4)
    (decisive : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (directClosingFrames.stages left).a.key.constitutional.rule1a
      (directClosingFrames.stages right).a.key.constitutional.rule1a ≠ Ordering.eq) :
    compare (directClosingFrames.retainedKeys left) (directClosingFrames.retainedKeys right) =
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (directClosingFrames.stages left).a.key.constitutional.rule1a
        (directClosingFrames.stages right).a.key.constitutional.rule1a := by
  have compoundReadback (index : Fin 4) :
      (directClosingFrames.compounds index).prior.rule4aKey = (directClosingFrames.stages index).a.key := by
    let view := contextOccurrenceView pseudoReference directClosingTarget
    let read := fun source => pseudoSpatialCertified.localizedDependencyLabel directClosingTarget view source
    have uniformBuilt :
        pseudoSpatialCertified.buildRuleMajorCompoundRule45KeyWith?
          (fun stage position => pseudoSpatialCertified.buildRuleMajorCumulativeWithRead?
            stage read (2 * (carrierFuel pseudoReference + 1)) position)
          (directClosingFrames.frame.cursorAt index) = some (directClosingFrames.compounds index) := by
      rw [← pseudoSpatialCertified.buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor]
      rw [← pseudoSpatialCertified.buildActualRuleMajorCompoundRule45KeyExec?_eq]
      exact directClosingFrames.compoundBuilt index
    exact (pseudoSpatialCertified.contextStages_compound_readback
      (directClosingFrames.stages index) uniformBuilt).1
  have full := directClosingFrames.retainedActual_fullOrdering spatial_simpleBonded left right
  have comparison := CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundThroughRule5_eq_rule1a_of_decisive
    pseudoSpatialCertified (directClosingFrames.compounds left) (directClosingFrames.compounds right) (by
      rw [compoundReadback left, compoundReadback right]
      exact decisive)
  calc
    compare (directClosingFrames.retainedKeys left) (directClosingFrames.retainedKeys right) =
        (pseudoSpatialCertified.compareLocalizedRerootCompoundThroughRule5
          (directClosingFrames.compounds left) (directClosingFrames.compounds right)).ordering := full.symm
    _ = OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (directClosingFrames.stages left).a.key.constitutional.rule1a
        (directClosingFrames.stages right).a.key.constitutional.rule1a := by
      rw [comparison, compoundReadback left, compoundReadback right]

private theorem shallowClosing_retained_lt
    (higher lower : Fin 4)
    (sparse : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (directClosingFrames.stages higher).a.key.constitutional.rule1a
      (directClosingFrames.stages lower).a.key.constitutional.rule1a = Ordering.gt) :
    directClosingFrames.retainedKeys lower < directClosingFrames.retainedKeys higher := by
  have decisive : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (directClosingFrames.stages higher).a.key.constitutional.rule1a
      (directClosingFrames.stages lower).a.key.constitutional.rule1a ≠ Ordering.eq := by
    rw [sparse]
    decide
  have comparison := shallowClosing_retained_compare_of_rule1a higher lower decisive
  rw [sparse] at comparison
  exact (completeLigandRule5Key_compare_gt_iff
    (directClosingFrames.retainedKeys higher) (directClosingFrames.retainedKeys lower)).mp comparison

private theorem shallowClosing_retained_order :
    [shallowClosingClSlot, shallowClosingCarbonSlot, shallowClosingRootSlot, shallowClosingHSlot].Pairwise
      (fun left right => directClosingFrames.retainedKeys right < directClosingFrames.retainedKeys left) := by
  rcases shallowClosing_sparse_strict_pairs with ⟨clParent, clDup, clH, parentDup, parentH, dupH⟩
  apply List.Pairwise.cons
  · intro slot member
    simp only [List.mem_cons] at member
    rcases member with equal | equal | equal | empty
    · subst slot
      exact shallowClosing_retained_lt shallowClosingClSlot shallowClosingCarbonSlot clParent
    · subst slot
      exact shallowClosing_retained_lt shallowClosingClSlot shallowClosingRootSlot clDup
    · subst slot
      exact shallowClosing_retained_lt shallowClosingClSlot shallowClosingHSlot clH
    · simp at empty
  · apply List.Pairwise.cons
    · intro slot member
      simp only [List.mem_cons] at member
      rcases member with equal | equal | empty
      · subst slot
        exact shallowClosing_retained_lt shallowClosingCarbonSlot shallowClosingRootSlot parentDup
      · subst slot
        exact shallowClosing_retained_lt shallowClosingCarbonSlot shallowClosingHSlot parentH
      · simp at empty
    · apply List.Pairwise.cons
      · intro slot member
        simp only [List.mem_cons] at member
        rcases member with equal | empty
        · subst slot
          exact shallowClosing_retained_lt shallowClosingRootSlot shallowClosingHSlot dupH
        · simp at empty
      · apply List.Pairwise.cons
        · intro slot member
          simp at member
        · exact List.Pairwise.nil

private theorem shallowClosing_fin4_four_distinct_perm {a b c d : Fin 4}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    [a,b,c,d].Perm (List.finRange 4) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp_all <;> decide

private theorem shallowClosing_order_perm :
    [shallowClosingClSlot, shallowClosingCarbonSlot, shallowClosingRootSlot, shallowClosingHSlot].Perm (List.finRange 4) := by
  rcases shallowClosing_slots_pairwise_distinct with ⟨hab, hac, had, hbc, hbd, hcd⟩
  exact shallowClosing_fin4_four_distinct_perm hab hac had hbc hbd hcd

private theorem shallowClosing_retained_prior_compare_of_rule1a
    (left right : Fin 4)
    (decisive : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (directClosingFrames.stages left).a.key.constitutional.rule1a
      (directClosingFrames.stages right).a.key.constitutional.rule1a ≠ Ordering.eq) :
    compare (ofLex (directClosingFrames.retainedKeys left)).1
        (ofLex (directClosingFrames.retainedKeys right)).1 =
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (directClosingFrames.stages left).a.key.constitutional.rule1a
        (directClosingFrames.stages right).a.key.constitutional.rule1a := by
  have compoundReadback (index : Fin 4) :
      (directClosingFrames.compounds index).prior.rule4aKey = (directClosingFrames.stages index).a.key := by
    let view := contextOccurrenceView pseudoReference directClosingTarget
    let read := fun source => pseudoSpatialCertified.localizedDependencyLabel directClosingTarget view source
    have uniformBuilt :
        pseudoSpatialCertified.buildRuleMajorCompoundRule45KeyWith?
          (fun stage position => pseudoSpatialCertified.buildRuleMajorCumulativeWithRead?
            stage read (2 * (carrierFuel pseudoReference + 1)) position)
          (directClosingFrames.frame.cursorAt index) = some (directClosingFrames.compounds index) := by
      rw [← pseudoSpatialCertified.buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor]
      rw [← pseudoSpatialCertified.buildActualRuleMajorCompoundRule45KeyExec?_eq]
      exact directClosingFrames.compoundBuilt index
    exact (pseudoSpatialCertified.contextStages_compound_readback
      (directClosingFrames.stages index) uniformBuilt).1
  have priorAgreement := directClosingFrames.retainedActual_priorComparison spatial_simpleBonded left right
  have constEq := OfficialRuleMajorKey.compare_eq_rule1a_of_decisive
    (left := (directClosingFrames.compounds left).prior.rule4aKey.constitutional)
    (right := (directClosingFrames.compounds right).prior.rule4aKey.constitutional) (by
      rw [compoundReadback left, compoundReadback right]
      exact decisive)
  have constNe : OfficialRuleMajorKey.compare
      (directClosingFrames.compounds left).prior.rule4aKey.constitutional
      (directClosingFrames.compounds right).prior.rule4aKey.constitutional ≠ Ordering.eq := by
    rw [constEq, compoundReadback left, compoundReadback right]
    exact decisive
  have cumulativeEq : pseudoSpatialCertified.compareLocalizedRerootCumulativeRule45Keys
      (directClosingFrames.compounds left).prior.rule4aKey
      (directClosingFrames.compounds right).prior.rule4aKey =
      OfficialRuleMajorKey.compare
        (directClosingFrames.compounds left).prior.rule4aKey.constitutional
        (directClosingFrames.compounds right).prior.rule4aKey.constitutional := by
    unfold CertifiedLocalizedCIPInput.compareLocalizedRerootCumulativeRule45Keys
    refine ConstitutionalLexAlgebra.compareLex_eq_left_of_left_ne_eq _ _ _ _ ?_
    simpa [Ordering.byKey] using constNe
  have cumulativeNe : pseudoSpatialCertified.compareLocalizedRerootCumulativeRule45Keys
      (directClosingFrames.compounds left).prior.rule4aKey
      (directClosingFrames.compounds right).prior.rule4aKey ≠ Ordering.eq := by
    rw [cumulativeEq]
    exact constNe
  have compoundComparison :=
    CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundRule4bcKeys_eq_rule4a_of_ne
      pseudoSpatialCertified (directClosingFrames.compounds left).prior
      (directClosingFrames.compounds right).prior cumulativeNe
  calc
    compare (ofLex (directClosingFrames.retainedKeys left)).1
        (ofLex (directClosingFrames.retainedKeys right)).1 =
      pseudoSpatialCertified.compareLocalizedRerootCompoundRule4bcKeys
        (directClosingFrames.compounds left).prior (directClosingFrames.compounds right).prior :=
      priorAgreement.symm
    _ = pseudoSpatialCertified.compareLocalizedRerootCumulativeRule45Keys
        (directClosingFrames.compounds left).prior.rule4aKey
        (directClosingFrames.compounds right).prior.rule4aKey := compoundComparison
    _ = OfficialRuleMajorKey.compare
        (directClosingFrames.compounds left).prior.rule4aKey.constitutional
        (directClosingFrames.compounds right).prior.rule4aKey.constitutional := cumulativeEq
    _ = OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (directClosingFrames.stages left).a.key.constitutional.rule1a
        (directClosingFrames.stages right).a.key.constitutional.rule1a := by
      rw [OfficialRuleMajorKey.compare_eq_rule1a_of_decisive (by
        rw [compoundReadback left, compoundReadback right]
        exact decisive), compoundReadback left, compoundReadback right]

private theorem shallowClosing_retained_prior_lt
    (higher lower : Fin 4)
    (sparse : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (directClosingFrames.stages higher).a.key.constitutional.rule1a
      (directClosingFrames.stages lower).a.key.constitutional.rule1a = Ordering.gt) :
    (ofLex (directClosingFrames.retainedKeys lower)).1 <
      (ofLex (directClosingFrames.retainedKeys higher)).1 := by
  have decisive : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (directClosingFrames.stages higher).a.key.constitutional.rule1a
      (directClosingFrames.stages lower).a.key.constitutional.rule1a ≠ Ordering.eq := by
    rw [sparse]
    decide
  have comparison := shallowClosing_retained_prior_compare_of_rule1a higher lower decisive
  rw [sparse] at comparison
  exact (completeLigandPriorKey_compare_gt_iff
    (ofLex (directClosingFrames.retainedKeys higher)).1
    (ofLex (directClosingFrames.retainedKeys lower)).1).mp comparison

private theorem shallowClosing_retained_prior_order :
    [shallowClosingClSlot, shallowClosingCarbonSlot, shallowClosingRootSlot, shallowClosingHSlot].Pairwise
      (fun left right => (ofLex (directClosingFrames.retainedKeys right)).1 <
        (ofLex (directClosingFrames.retainedKeys left)).1) := by
  rcases shallowClosing_sparse_strict_pairs with ⟨clParent, clDup, clH, parentDup, parentH, dupH⟩
  apply List.Pairwise.cons
  · intro slot member
    simp only [List.mem_cons] at member
    rcases member with equal | equal | equal | empty
    · subst slot
      exact shallowClosing_retained_prior_lt shallowClosingClSlot shallowClosingCarbonSlot clParent
    · subst slot
      exact shallowClosing_retained_prior_lt shallowClosingClSlot shallowClosingRootSlot clDup
    · subst slot
      exact shallowClosing_retained_prior_lt shallowClosingClSlot shallowClosingHSlot clH
    · simp at empty
  · apply List.Pairwise.cons
    · intro slot member
      simp only [List.mem_cons] at member
      rcases member with equal | equal | empty
      · subst slot
        exact shallowClosing_retained_prior_lt shallowClosingCarbonSlot shallowClosingRootSlot parentDup
      · subst slot
        exact shallowClosing_retained_prior_lt shallowClosingCarbonSlot shallowClosingHSlot parentH
      · simp at empty
    · apply List.Pairwise.cons
      · intro slot member
        simp only [List.mem_cons] at member
        rcases member with equal | empty
        · subst slot
          exact shallowClosing_retained_prior_lt shallowClosingRootSlot shallowClosingHSlot dupH
        · simp at empty
      · apply List.Pairwise.cons
        · intro slot member
          simp at member
        · exact List.Pairwise.nil

private theorem shallowClosing_retainedPrior_pairwise_injective
    {α : Type} [LinearOrder α] {xs : List (Fin 4)} {key : Fin 4 → α}
    (perm : xs.Perm (List.finRange 4))
    (sorted : xs.Pairwise (fun i j => key j < key i)) :
    Function.Injective key := by
  intro i j equal
  by_contra different
  have hi : i ∈ xs := perm.mem_iff.mpr (List.mem_finRange i)
  have hj : j ∈ xs := perm.mem_iff.mpr (List.mem_finRange j)
  have either := (List.Pairwise.forall (fun _ _ h => h.symm)
    (sorted.imp fun h => Or.inr h)) hi hj different
  rw [equal] at either
  exact either.elim (lt_irrefl _) (lt_irrefl _)

private theorem shallowClosing_prior_injective :
    Function.Injective (fun slot => (ofLex (directClosingFrames.retainedKeys slot)).1) :=
  shallowClosing_retainedPrior_pairwise_injective shallowClosing_order_perm shallowClosing_retained_prior_order

private theorem shallowClosing_not_prior_pair (left right : Fin 4) (different : left ≠ right) :
    ¬ CompletePriorPair directClosingFrames.retainedKeys left right := by
  intro pair
  exact different (shallowClosing_prior_injective pair.2)

private theorem shallowClosing_completeRule5PairCount_zero :
    completeRule5PairCount directClosingFrames.retainedKeys = 0 := by
  have h01 : ¬ CompletePriorPair directClosingFrames.retainedKeys 0 1 :=
    shallowClosing_not_prior_pair 0 1 (by decide)
  have h02 : ¬ CompletePriorPair directClosingFrames.retainedKeys 0 2 :=
    shallowClosing_not_prior_pair 0 2 (by decide)
  have h12 : ¬ CompletePriorPair directClosingFrames.retainedKeys 1 2 :=
    shallowClosing_not_prior_pair 1 2 (by decide)
  have h03 : ¬ CompletePriorPair directClosingFrames.retainedKeys 0 3 :=
    shallowClosing_not_prior_pair 0 3 (by decide)
  have h13 : ¬ CompletePriorPair directClosingFrames.retainedKeys 1 3 :=
    shallowClosing_not_prior_pair 1 3 (by decide)
  have h23 : ¬ CompletePriorPair directClosingFrames.retainedKeys 2 3 :=
    shallowClosing_not_prior_pair 2 3 (by decide)
  rw [completeRule5PairCount, sourceEnantiomorphicPairCount_eq_filter_length]
  simp [sourceUnorderedPairList, h01, h02, h12, h03, h13, h23]


private theorem via42_slot (index : Fin 9)
    (adjacent : graph.Adj ⟨2, by decide⟩ index) :
    ∃ slot : Fin 4, via42Frames.actualLigandAtoms slot = SA index := by
  have centerEq : via42Frames.center.1 = SA ⟨2, by decide⟩ := by
    rw [via42Frames.centerEq]
    simp [via42Unit, OccurrenceUnit.atom, via42_unit_eq]
  have adjacentCenter : pseudoSpatialCertified.moleculeGraph.Adj via42Frames.center.1
      (SA index) := by
    rw [centerEq]
    exact (spatial_adj ⟨2, by decide⟩ index).mpr adjacent
  obtain ⟨i, atomEq⟩ :=
    pseudoSpatialCertified.detectedMultiCenterMolecule.ligandAtomAt_surjective
      via42Frames.center (SA index) adjacentCenter
  refine ⟨via42Frames.detectedLigandPermutation.symm i, ?_⟩
  unfold pseudoReference
  simp [ContextFrameCompilation.actualLigandAtoms, Equiv.apply_symm_apply, atomEq]

private theorem via42_cursor_mem_component_neighbors (slot : Fin 4) :
    (via42Frames.frame.cursorAt slot).occurrence.1 ∈
      [LocalizedCyclicPseudoRootComponentEvaluation.closeF,
        LocalizedCyclicPseudoRootComponentEvaluation.via42DupF,
        LocalizedCyclicPseudoRootComponentEvaluation.via42ClF,
        LocalizedCyclicPseudoRootComponentEvaluation.via42HF] := by
  have present : via42Frames.frame.cursorAt slot ∈ via42Frames.frame.cursors :=
    List.get_mem via42Frames.frame.cursors (Fin.cast via42Frames.frame.length_eq.symm slot)
  have computed :
      pseudoSpatialCertified.localizedOccurrenceFourLigandFrame? via42Target =
        some via42Frames.frame := by
    rw [← pseudoSpatialCertified.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?]
    exact via42Frames.frameComputed
  have mapped := pseudoSpatialCertified.localizedOccurrenceFourLigandFrame_cursors_map_eq_neighborFrames
    via42Target via42Frames.frame computed
  have member :
      (via42Frames.frame.cursorAt slot).occurrence.1 ∈
        pseudoSpatialCertified.localizedRerootNeighborFrames
          (fuel := carrierFuel pseudoReference) via42Target.1 := by
    rw [← mapped]
    exact List.mem_map.mpr ⟨via42Frames.frame.cursorAt slot, present, rfl⟩
  have rootZero : via42Target.1.root =
      LocalizedCyclicPseudoRootComponentEvaluation.SA 0 := by
    have roots := congrArg
      (fun f : pseudoSpatialCertified.LocalizedCIPOccurrenceFrame => f.root)
      closingCarbonCursor_eq_via42F
    rw [LocalizedCyclicPseudoRootComponentEvaluation.via42F] at roots
    exact roots
  rw [LocalizedCyclicPseudoRootComponentEvaluation.neighborFrames_eq0
    via42Target.1 rootZero] at member
  rw [closingCarbonCursor_eq_via42F,
    component_via42_neighbors] at member
  exact member

private theorem via42_cursor_eq_component
    (slot : Fin 4)
    (candidate : LocalizedCyclicPseudoRootComponentEvaluation.Frame)
    (sameCurrent :
      (via42Frames.frame.cursorAt slot).occurrence.1.node.current? =
        candidate.node.current?)
    (candidateMem : candidate ∈
      [LocalizedCyclicPseudoRootComponentEvaluation.closeF,
        LocalizedCyclicPseudoRootComponentEvaluation.via42DupF,
        LocalizedCyclicPseudoRootComponentEvaluation.via42ClF,
        LocalizedCyclicPseudoRootComponentEvaluation.via42HF]) :
    (via42Frames.frame.cursorAt slot).occurrence.1 = candidate := by
  have actualMem := via42_cursor_mem_component_neighbors slot
  have nodup :
      ([LocalizedCyclicPseudoRootComponentEvaluation.closeF,
        LocalizedCyclicPseudoRootComponentEvaluation.via42DupF,
        LocalizedCyclicPseudoRootComponentEvaluation.via42ClF,
        LocalizedCyclicPseudoRootComponentEvaluation.via42HF].map
        (fun f => f.node.current?)).Nodup := by
    decide
  exact List.inj_on_of_nodup_map nodup actualMem candidateMem sameCurrent

private theorem actual_via42_cursor_const_rule1a
    (slot : Fin 4)
    (candidate : LocalizedCyclicPseudoRootComponentEvaluation.Frame)
    (sameCurrent :
      (via42Frames.frame.cursorAt slot).occurrence.1.node.current? =
        candidate.node.current?)
    (candidateMem : candidate ∈
      [LocalizedCyclicPseudoRootComponentEvaluation.closeF,
        LocalizedCyclicPseudoRootComponentEvaluation.via42DupF,
        LocalizedCyclicPseudoRootComponentEvaluation.via42ClF,
        LocalizedCyclicPseudoRootComponentEvaluation.via42HF]) :
    ∃ key,
      LocalizedCyclicPseudoRootComponentEvaluation.buildF .rule4a
        LocalizedCyclicPseudoRootComponentEvaluation.evalFuel candidate
        (some LocalizedCyclicPseudoRootComponentEvaluation.via42F) = some key ∧
      key.constitutional.rule1a =
        (via42Frames.stages slot).a.key.constitutional.rule1a := by
  let cursor := via42Frames.frame.cursorAt slot
  let parent : pseudoSpatialCertified.LocalizedRerootCursor
      (carrierFuel pseudoReference) := ⟨via42Target, none⟩
  have valid := pseudoSpatialCertified.localizedRerootChild_valid parent cursor
    (pseudoSpatialCertified.executableLocalizedRerootChildren parent)
    (pseudoSpatialCertified.executableLocalizedRerootChildren_declarative parent)
    (via42Frames.childAt slot)
  have rootZero : cursor.occurrence.1.root =
      LocalizedCyclicPseudoRootComponentEvaluation.SA 0 := by
    have cursorRoot :=
      pseudoSpatialCertified.localizedOccurrenceFourLigandFrame_cursor_root
        via42Target via42Frames.frame
        (by
          rw [← pseudoSpatialCertified.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?]
          exact via42Frames.frameComputed)
        cursor (by
          exact List.get_mem via42Frames.frame.cursors
            (Fin.cast via42Frames.frame.length_eq.symm slot))
    have targetRoot := congrArg
      (fun f : pseudoSpatialCertified.LocalizedCIPOccurrenceFrame => f.root)
      closingCarbonCursor_eq_via42F
    rw [LocalizedCyclicPseudoRootComponentEvaluation.via42F] at targetRoot
    exact cursorRoot.trans targetRoot
  have built := (via42Frames.stages slot).a.built
  unfold pseudoReference at built
  rw [pseudoSpatialCertified.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized] at built
  obtain ⟨twinKey, builtTwin, tableEq⟩ := actualRule1a_eq_rootComponent cursor valid
    (contextOccurrenceRead pseudoReference via42Target)
    (fuel := 2 * (carrierFuel pseudoReference + 1))
    (via42Frames.stages slot).a.key built rootZero
  have occurrenceEq :
      cursor.occurrence.1 = candidate :=
    via42_cursor_eq_component slot candidate sameCurrent candidateMem
  have previousEq :
      cursor.previous?.map Subtype.val =
        some LocalizedCyclicPseudoRootComponentEvaluation.via42F := by
    change (via42Frames.frame.cursorAt slot).previous?.map Subtype.val =
      some LocalizedCyclicPseudoRootComponentEvaluation.via42F
    rw [pseudoSpatialCertified.localizedOccurrenceFourLigandFrame_cursor_previous
        via42Target via42Frames.frame
        (by
          rw [← pseudoSpatialCertified.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?]
          exact via42Frames.frameComputed)
        (via42Frames.frame.cursorAt slot)
        (List.get_mem via42Frames.frame.cursors
          (Fin.cast via42Frames.frame.length_eq.symm slot))]
    exact congrArg some closingCarbonCursor_eq_via42F
  have previousEq' :
      (cursor.previous?.map Subtype.val :
        Option LocalizedCyclicPseudoRootComponentEvaluation.Frame) =
        some LocalizedCyclicPseudoRootComponentEvaluation.via42F := by
    exact previousEq
  have inputEq :
      ((cursor.occurrence.1, cursor.previous?.map Subtype.val) :
        LocalizedCyclicPseudoRootComponentEvaluation.Frame ×
          Option LocalizedCyclicPseudoRootComponentEvaluation.Frame) =
        (candidate, some LocalizedCyclicPseudoRootComponentEvaluation.via42F) := by
    exact Prod.ext occurrenceEq previousEq'
  have callEq := congrArg
    (fun pair : LocalizedCyclicPseudoRootComponentEvaluation.Frame ×
        Option LocalizedCyclicPseudoRootComponentEvaluation.Frame =>
      LocalizedCyclicPseudoRootComponentEvaluation.buildF .rule4a
        LocalizedCyclicPseudoRootComponentEvaluation.evalFuel pair.1 pair.2)
    inputEq
  refine ⟨twinKey, ?_, tableEq⟩
  exact callEq.symm.trans builtTwin

private noncomputable def via42ClSlot : Fin 4 :=
  Classical.choose (via42_slot ⟨3, by decide⟩ ((adj_arm 3).mpr (by simp)))

private theorem via42ClSlot_atom :
    via42Frames.actualLigandAtoms via42ClSlot = SA ⟨3, by decide⟩ :=
  Classical.choose_spec (via42_slot ⟨3, by decide⟩ ((adj_arm 3).mpr (by simp)))

private noncomputable def via42ParentSlot : Fin 4 :=
  Classical.choose (via42_slot ⟨4, by decide⟩ ((adj_arm 4).mpr (by simp)))

private theorem via42ParentSlot_atom :
    via42Frames.actualLigandAtoms via42ParentSlot = SA ⟨4, by decide⟩ :=
  Classical.choose_spec (via42_slot ⟨4, by decide⟩ ((adj_arm 4).mpr (by simp)))

private noncomputable def via42DupSlot : Fin 4 :=
  Classical.choose (via42_slot ⟨0, by decide⟩ ((adj_arm 0).mpr (by simp)))

private theorem via42DupSlot_atom :
    via42Frames.actualLigandAtoms via42DupSlot = SA ⟨0, by decide⟩ :=
  Classical.choose_spec (via42_slot ⟨0, by decide⟩ ((adj_arm 0).mpr (by simp)))

private noncomputable def via42HSlot : Fin 4 :=
  Classical.choose (via42_slot ⟨6, by decide⟩ ((adj_arm 6).mpr (by simp)))

private theorem via42HSlot_atom :
    via42Frames.actualLigandAtoms via42HSlot = SA ⟨6, by decide⟩ :=
  Classical.choose_spec (via42_slot ⟨6, by decide⟩ ((adj_arm 6).mpr (by simp)))

private theorem via42_slot_current (slot : Fin 4) (index : Fin 9)
    (atomEq : via42Frames.actualLigandAtoms slot = SA index) :
    (via42Frames.frame.cursorAt slot).occurrence.1.node.current? = some (SA index) := by
  have current := via42Frames.ligandAt slot
  unfold pseudoReference at current
  have defined : via42Frames.actualLigandAtoms slot =
      pseudoSpatialCertified.detectedMultiCenterMolecule.ligandAtomAt
        via42Frames.center (via42Frames.detectedLigandPermutation slot) := by
    unfold pseudoReference
    rfl
  have actualAtom :
      pseudoSpatialCertified.detectedMultiCenterMolecule.ligandAtomAt
        via42Frames.center (via42Frames.detectedLigandPermutation slot) = SA index := by
    rw [← defined]
    exact atomEq
  rw [actualAtom] at current
  exact current

private theorem via42_cl_key :
    ∃ key,
      LocalizedCyclicPseudoRootComponentEvaluation.buildF .rule4a
        LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
        LocalizedCyclicPseudoRootComponentEvaluation.via42ClF
        (some LocalizedCyclicPseudoRootComponentEvaluation.via42F) = some key ∧
      key.constitutional.rule1a =
        (via42Frames.stages via42ClSlot).a.key.constitutional.rule1a := by
  apply actual_via42_cursor_const_rule1a via42ClSlot
      LocalizedCyclicPseudoRootComponentEvaluation.via42ClF
  · exact (via42_slot_current via42ClSlot ⟨3, by decide⟩ via42ClSlot_atom).trans
      (by simp [LocalizedCyclicPseudoRootComponentEvaluation.via42ClF,
        LocalizedCyclicPseudoRootComponentEvaluation.node42,
        LocalizedCyclicPseudoRootComponentEvaluation.node4,
        LocalizedCyclicPseudoRootComponentEvaluation.rootNode,
        OfficialCIPNode.root, OfficialCIPNode.extend, SA,
        LocalizedCyclicPseudoRootComponentEvaluation.SA])
  · simp

private theorem via42_parent_key :
    ∃ key,
      LocalizedCyclicPseudoRootComponentEvaluation.buildF .rule4a
        LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
        LocalizedCyclicPseudoRootComponentEvaluation.closeF
        (some LocalizedCyclicPseudoRootComponentEvaluation.via42F) = some key ∧
      key.constitutional.rule1a =
        (via42Frames.stages via42ParentSlot).a.key.constitutional.rule1a := by
  apply actual_via42_cursor_const_rule1a via42ParentSlot
      LocalizedCyclicPseudoRootComponentEvaluation.closeF
  · exact (via42_slot_current via42ParentSlot ⟨4, by decide⟩ via42ParentSlot_atom).trans
      (by simp [LocalizedCyclicPseudoRootComponentEvaluation.closeF,
        LocalizedCyclicPseudoRootComponentEvaluation.node4,
        LocalizedCyclicPseudoRootComponentEvaluation.rootNode,
        OfficialCIPNode.root, OfficialCIPNode.extend, SA,
        LocalizedCyclicPseudoRootComponentEvaluation.SA])
  · simp

private theorem via42_dup_key :
    ∃ key,
      LocalizedCyclicPseudoRootComponentEvaluation.buildF .rule4a
        LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
        LocalizedCyclicPseudoRootComponentEvaluation.via42DupF
        (some LocalizedCyclicPseudoRootComponentEvaluation.via42F) = some key ∧
      key.constitutional.rule1a =
        (via42Frames.stages via42DupSlot).a.key.constitutional.rule1a := by
  apply actual_via42_cursor_const_rule1a via42DupSlot
      LocalizedCyclicPseudoRootComponentEvaluation.via42DupF
  · exact (via42_slot_current via42DupSlot ⟨0, by decide⟩ via42DupSlot_atom).trans
      (by simp [LocalizedCyclicPseudoRootComponentEvaluation.via42DupF,
        LocalizedCyclicPseudoRootComponentEvaluation.node42,
        LocalizedCyclicPseudoRootComponentEvaluation.node4,
        LocalizedCyclicPseudoRootComponentEvaluation.rootNode,
        OfficialCIPNode.root, OfficialCIPNode.extend, SA,
        LocalizedCyclicPseudoRootComponentEvaluation.SA])
  · simp

private theorem via42_h_key :
    ∃ key,
      LocalizedCyclicPseudoRootComponentEvaluation.buildF .rule4a
        LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
        LocalizedCyclicPseudoRootComponentEvaluation.via42HF
        (some LocalizedCyclicPseudoRootComponentEvaluation.via42F) = some key ∧
      key.constitutional.rule1a =
        (via42Frames.stages via42HSlot).a.key.constitutional.rule1a := by
  apply actual_via42_cursor_const_rule1a via42HSlot
      LocalizedCyclicPseudoRootComponentEvaluation.via42HF
  · exact (via42_slot_current via42HSlot ⟨6, by decide⟩ via42HSlot_atom).trans
      (by simp [LocalizedCyclicPseudoRootComponentEvaluation.via42HF,
        LocalizedCyclicPseudoRootComponentEvaluation.node42,
        LocalizedCyclicPseudoRootComponentEvaluation.node4,
        LocalizedCyclicPseudoRootComponentEvaluation.rootNode,
        OfficialCIPNode.root, OfficialCIPNode.extend, SA,
        LocalizedCyclicPseudoRootComponentEvaluation.SA])
  · simp

private def via42FiniteKey
    (frame : LocalizedCyclicPseudoRootComponentEvaluation.Frame) :
    OfficialRuleMajorKey LocalizedCyclicPseudoRootComponentEvaluation.Atom :=
  match LocalizedCyclicPseudoRootComponentEvaluation.buildF .rule4a
      LocalizedCyclicPseudoRootComponentEvaluation.evalFuel frame
      (some LocalizedCyclicPseudoRootComponentEvaluation.via42F) with
  | some key => key.constitutional
  | none =>
      { rule1a := [], rule1b := [], rule2 := [], sourceNodes := [], complete := false }

private theorem via42_component_cl_rule1a_gt_parent :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (via42FiniteKey LocalizedCyclicPseudoRootComponentEvaluation.via42ClF).rule1a
        (via42FiniteKey LocalizedCyclicPseudoRootComponentEvaluation.closeF).rule1a =
      Ordering.gt := by
  decide

private theorem via42_actual_cl_rule1a_gt_parent :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (via42Frames.stages via42ClSlot).a.key.constitutional.rule1a
        (via42Frames.stages via42ParentSlot).a.key.constitutional.rule1a =
      Ordering.gt := by
  obtain ⟨clKey, clBuilt, clTable⟩ := via42_cl_key
  obtain ⟨parentKey, parentBuilt, parentTable⟩ := via42_parent_key
  have clEq :
      via42FiniteKey LocalizedCyclicPseudoRootComponentEvaluation.via42ClF =
        clKey.constitutional := by
    simp [via42FiniteKey, clBuilt]
  have parentEq :
      via42FiniteKey LocalizedCyclicPseudoRootComponentEvaluation.closeF =
        parentKey.constitutional := by
    simp [via42FiniteKey, parentBuilt]
  rw [← clTable, ← parentTable, ← clEq, ← parentEq]
  exact via42_component_cl_rule1a_gt_parent

private theorem via42_component_parent_rule1a_gt_dup :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (via42FiniteKey LocalizedCyclicPseudoRootComponentEvaluation.closeF).rule1a
        (via42FiniteKey LocalizedCyclicPseudoRootComponentEvaluation.via42DupF).rule1a =
      Ordering.gt := by
  decide +kernel

private theorem via42_actual_parent_rule1a_gt_dup :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (via42Frames.stages via42ParentSlot).a.key.constitutional.rule1a
        (via42Frames.stages via42DupSlot).a.key.constitutional.rule1a =
      Ordering.gt := by
  obtain ⟨parentKey, parentBuilt, parentTable⟩ := via42_parent_key
  obtain ⟨dupKey, dupBuilt, dupTable⟩ := via42_dup_key
  have parentEq :
      via42FiniteKey LocalizedCyclicPseudoRootComponentEvaluation.closeF =
        parentKey.constitutional := by
    simp [via42FiniteKey, parentBuilt]
  have dupEq :
      via42FiniteKey LocalizedCyclicPseudoRootComponentEvaluation.via42DupF =
        dupKey.constitutional := by
    simp [via42FiniteKey, dupBuilt]
  rw [← parentTable, ← dupTable, ← parentEq, ← dupEq]
  exact via42_component_parent_rule1a_gt_dup

private theorem via42_cl_head :
    (via42Frames.stages via42ClSlot).a.key.constitutional.rule1a.head? =
      some [([], 17)] := by
  have head := slot_head via42Frames via42ClSlot
  rw [via42ClSlot_atom] at head
  simpa [spatial_z, (z_chlorine ⟨3, by decide⟩).mpr (Or.inl rfl)] using head

private theorem via42_parent_head :
    (via42Frames.stages via42ParentSlot).a.key.constitutional.rule1a.head? =
      some [([], 6)] := by
  have head := slot_head via42Frames via42ParentSlot
  rw [via42ParentSlot_atom] at head
  simpa [spatial_z, (z_carbon ⟨4, by decide⟩).mpr (Or.inr (Or.inr rfl))] using head

private theorem via42_dup_head :
    (via42Frames.stages via42DupSlot).a.key.constitutional.rule1a.head? =
      some [([], 6)] := by
  have head := slot_head via42Frames via42DupSlot
  rw [via42DupSlot_atom] at head
  simpa [spatial_z, (z_carbon ⟨0, by decide⟩).mpr (Or.inl rfl)] using head

private theorem via42_h_head :
    (via42Frames.stages via42HSlot).a.key.constitutional.rule1a.head? =
      some [([], 1)] := by
  have head := slot_head via42Frames via42HSlot
  rw [via42HSlot_atom] at head
  simpa [spatial_z, (z_hydrogen ⟨6, by decide⟩).mpr (Or.inr (Or.inl rfl))] using head

private theorem via42_actual_order :
    OfficialRuleMajorKey.compare
        (via42Frames.stages via42ClSlot).a.key.constitutional
        (via42Frames.stages via42ParentSlot).a.key.constitutional = Ordering.gt ∧
    OfficialRuleMajorKey.compare
        (via42Frames.stages via42ClSlot).a.key.constitutional
        (via42Frames.stages via42DupSlot).a.key.constitutional = Ordering.gt ∧
    OfficialRuleMajorKey.compare
        (via42Frames.stages via42ClSlot).a.key.constitutional
        (via42Frames.stages via42HSlot).a.key.constitutional = Ordering.gt ∧
    OfficialRuleMajorKey.compare
        (via42Frames.stages via42ParentSlot).a.key.constitutional
        (via42Frames.stages via42DupSlot).a.key.constitutional = Ordering.gt ∧
    OfficialRuleMajorKey.compare
        (via42Frames.stages via42ParentSlot).a.key.constitutional
        (via42Frames.stages via42HSlot).a.key.constitutional = Ordering.gt ∧
    OfficialRuleMajorKey.compare
        (via42Frames.stages via42DupSlot).a.key.constitutional
        (via42Frames.stages via42HSlot).a.key.constitutional = Ordering.gt := by
  refine ⟨compare_gt_of_heads via42_cl_head via42_parent_head (by decide),
    compare_gt_of_heads via42_cl_head via42_dup_head (by decide),
    compare_gt_of_heads via42_cl_head via42_h_head (by decide), ?_,
    compare_gt_of_heads via42_parent_head via42_h_head (by decide),
    compare_gt_of_heads via42_dup_head via42_h_head (by decide)⟩
  have decisive := via42_actual_parent_rule1a_gt_dup
  rw [OfficialRuleMajorKey.compare_eq_rule1a_of_decisive
      (by rw [decisive]; decide), decisive]

private theorem via42_retained_compare_of_rule1a
    (left right : Fin 4)
    (decisive : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (via42Frames.stages left).a.key.constitutional.rule1a
      (via42Frames.stages right).a.key.constitutional.rule1a ≠ Ordering.eq) :
    compare (via42Frames.retainedKeys left) (via42Frames.retainedKeys right) =
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (via42Frames.stages left).a.key.constitutional.rule1a
        (via42Frames.stages right).a.key.constitutional.rule1a := by
  have compoundReadback (index : Fin 4) :
      (via42Frames.compounds index).prior.rule4aKey = (via42Frames.stages index).a.key := by
    let view := contextOccurrenceView pseudoReference via42Target
    let read := fun source => pseudoSpatialCertified.localizedDependencyLabel via42Target view source
    have uniformBuilt :
        pseudoSpatialCertified.buildRuleMajorCompoundRule45KeyWith?
          (fun stage position => pseudoSpatialCertified.buildRuleMajorCumulativeWithRead?
            stage read (2 * (carrierFuel pseudoReference + 1)) position)
          (via42Frames.frame.cursorAt index) = some (via42Frames.compounds index) := by
      rw [← pseudoSpatialCertified.buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor]
      rw [← pseudoSpatialCertified.buildActualRuleMajorCompoundRule45KeyExec?_eq]
      exact via42Frames.compoundBuilt index
    exact (pseudoSpatialCertified.contextStages_compound_readback
      (via42Frames.stages index) uniformBuilt).1
  have full := via42Frames.retainedActual_fullOrdering spatial_simpleBonded left right
  have comparison := CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundThroughRule5_eq_rule1a_of_decisive
    pseudoSpatialCertified (via42Frames.compounds left) (via42Frames.compounds right) (by
      rw [compoundReadback left, compoundReadback right]
      exact decisive)
  calc
    compare (via42Frames.retainedKeys left) (via42Frames.retainedKeys right) =
        (pseudoSpatialCertified.compareLocalizedRerootCompoundThroughRule5
          (via42Frames.compounds left) (via42Frames.compounds right)).ordering := full.symm
    _ = OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (via42Frames.stages left).a.key.constitutional.rule1a
        (via42Frames.stages right).a.key.constitutional.rule1a := by
      rw [comparison, compoundReadback left, compoundReadback right]

private theorem fin4_four_distinct_perm {a b c d : Fin 4}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    [a, b, c, d].Perm (List.finRange 4) := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp_all <;> decide

private theorem via42_actualLigandAtoms_injective :
    Function.Injective via42Frames.actualLigandAtoms := by
  intro left right equal
  have atomEqual :
      pseudoSpatialCertified.detectedMultiCenterMolecule.ligandAtomAt via42Frames.center
          (via42Frames.detectedLigandPermutation left) =
        pseudoSpatialCertified.detectedMultiCenterMolecule.ligandAtomAt via42Frames.center
          (via42Frames.detectedLigandPermutation right) := equal
  have indexEqual := pseudoSpatialCertified.detectedMultiCenterMolecule.ligandAtomAt_injective
    via42Frames.center atomEqual
  exact via42Frames.detectedLigandPermutation.injective indexEqual

private theorem via42_slots_pairwise_distinct :
    via42ClSlot ≠ via42ParentSlot ∧ via42ClSlot ≠ via42DupSlot ∧
    via42ClSlot ≠ via42HSlot ∧ via42ParentSlot ≠ via42DupSlot ∧
    via42ParentSlot ≠ via42HSlot ∧ via42DupSlot ≠ via42HSlot := by
  have h₁ : via42ClSlot ≠ via42ParentSlot := by
    intro equal
    have atoms := congrArg via42Frames.actualLigandAtoms equal
    rw [via42ClSlot_atom, via42ParentSlot_atom] at atoms
    have vals := congrArg Fin.val atoms
    norm_num [SA, LocalizedCyclicPseudoRootComponentEvaluation.SA] at vals
  have h₂ : via42ClSlot ≠ via42DupSlot := by
    intro equal
    have atoms := congrArg via42Frames.actualLigandAtoms equal
    rw [via42ClSlot_atom, via42DupSlot_atom] at atoms
    have vals := congrArg Fin.val atoms
    norm_num [SA, LocalizedCyclicPseudoRootComponentEvaluation.SA] at vals
  have h₃ : via42ClSlot ≠ via42HSlot := by
    intro equal
    have atoms := congrArg via42Frames.actualLigandAtoms equal
    rw [via42ClSlot_atom, via42HSlot_atom] at atoms
    have vals := congrArg Fin.val atoms
    norm_num [SA, LocalizedCyclicPseudoRootComponentEvaluation.SA] at vals
  have h₄ : via42ParentSlot ≠ via42DupSlot := by
    intro equal
    have atoms := congrArg via42Frames.actualLigandAtoms equal
    rw [via42ParentSlot_atom, via42DupSlot_atom] at atoms
    have vals := congrArg Fin.val atoms
    norm_num [SA, LocalizedCyclicPseudoRootComponentEvaluation.SA] at vals
  have h₅ : via42ParentSlot ≠ via42HSlot := by
    intro equal
    have atoms := congrArg via42Frames.actualLigandAtoms equal
    rw [via42ParentSlot_atom, via42HSlot_atom] at atoms
    have vals := congrArg Fin.val atoms
    norm_num [SA, LocalizedCyclicPseudoRootComponentEvaluation.SA] at vals
  have h₆ : via42DupSlot ≠ via42HSlot := by
    intro equal
    have atoms := congrArg via42Frames.actualLigandAtoms equal
    rw [via42DupSlot_atom, via42HSlot_atom] at atoms
    have vals := congrArg Fin.val atoms
    norm_num [SA, LocalizedCyclicPseudoRootComponentEvaluation.SA] at vals
  exact ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩

private theorem via42_sparse_strict_pairs :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (via42Frames.stages via42ClSlot).a.key.constitutional.rule1a
        (via42Frames.stages via42ParentSlot).a.key.constitutional.rule1a = Ordering.gt ∧
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (via42Frames.stages via42ClSlot).a.key.constitutional.rule1a
        (via42Frames.stages via42DupSlot).a.key.constitutional.rule1a = Ordering.gt ∧
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (via42Frames.stages via42ClSlot).a.key.constitutional.rule1a
        (via42Frames.stages via42HSlot).a.key.constitutional.rule1a = Ordering.gt ∧
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (via42Frames.stages via42ParentSlot).a.key.constitutional.rule1a
        (via42Frames.stages via42DupSlot).a.key.constitutional.rule1a = Ordering.gt ∧
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (via42Frames.stages via42ParentSlot).a.key.constitutional.rule1a
        (via42Frames.stages via42HSlot).a.key.constitutional.rule1a = Ordering.gt ∧
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (via42Frames.stages via42DupSlot).a.key.constitutional.rule1a
        (via42Frames.stages via42HSlot).a.key.constitutional.rule1a = Ordering.gt := by
  refine ⟨officialRuleMajorKey_compare_rule1a_gt_of_heads_gt via42_cl_head via42_parent_head (by decide),
    officialRuleMajorKey_compare_rule1a_gt_of_heads_gt via42_cl_head via42_dup_head (by decide),
    officialRuleMajorKey_compare_rule1a_gt_of_heads_gt via42_cl_head via42_h_head (by decide),
    via42_actual_parent_rule1a_gt_dup,
    officialRuleMajorKey_compare_rule1a_gt_of_heads_gt via42_parent_head via42_h_head (by decide),
    officialRuleMajorKey_compare_rule1a_gt_of_heads_gt via42_dup_head via42_h_head (by decide)⟩

private theorem via42_retained_lt
    (higher lower : Fin 4)
    (sparse : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (via42Frames.stages higher).a.key.constitutional.rule1a
      (via42Frames.stages lower).a.key.constitutional.rule1a = Ordering.gt) :
    via42Frames.retainedKeys lower < via42Frames.retainedKeys higher := by
  have decisive : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (via42Frames.stages higher).a.key.constitutional.rule1a
      (via42Frames.stages lower).a.key.constitutional.rule1a ≠ Ordering.eq := by
    rw [sparse]
    decide
  have comparison := via42_retained_compare_of_rule1a higher lower decisive
  rw [sparse] at comparison
  exact (completeLigandRule5Key_compare_gt_iff
    (via42Frames.retainedKeys higher) (via42Frames.retainedKeys lower)).mp comparison

private theorem via42_retained_order :
    [via42ClSlot, via42ParentSlot, via42DupSlot, via42HSlot].Pairwise
      (fun left right => via42Frames.retainedKeys right < via42Frames.retainedKeys left) := by
  rcases via42_sparse_strict_pairs with ⟨clParent, clDup, clH, parentDup, parentH, dupH⟩
  apply List.Pairwise.cons
  · intro slot member
    simp only [List.mem_cons] at member
    rcases member with equal | equal | equal | empty
    · subst slot
      exact via42_retained_lt via42ClSlot via42ParentSlot clParent
    · subst slot
      exact via42_retained_lt via42ClSlot via42DupSlot clDup
    · subst slot
      exact via42_retained_lt via42ClSlot via42HSlot clH
    · simp at empty
  · apply List.Pairwise.cons
    · intro slot member
      simp only [List.mem_cons] at member
      rcases member with equal | equal | empty
      · subst slot
        exact via42_retained_lt via42ParentSlot via42DupSlot parentDup
      · subst slot
        exact via42_retained_lt via42ParentSlot via42HSlot parentH
      · simp at empty
    · apply List.Pairwise.cons
      · intro slot member
        simp only [List.mem_cons] at member
        rcases member with equal | empty
        · subst slot
          exact via42_retained_lt via42DupSlot via42HSlot dupH
        · simp at empty
      · apply List.Pairwise.cons
        · intro slot member
          simp at member
        · exact List.Pairwise.nil

private theorem via42_order_perm :
    [via42ClSlot, via42ParentSlot, via42DupSlot, via42HSlot].Perm (List.finRange 4) := by
  rcases via42_slots_pairwise_distinct with ⟨hab, hac, had, hbc, hbd, hcd⟩
  exact fin4_four_distinct_perm hab hac had hbc hbd hcd

private theorem via42_retained_prior_compare_of_rule1a
    (left right : Fin 4)
    (decisive : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (via42Frames.stages left).a.key.constitutional.rule1a
      (via42Frames.stages right).a.key.constitutional.rule1a ≠ Ordering.eq) :
    compare (ofLex (via42Frames.retainedKeys left)).1
        (ofLex (via42Frames.retainedKeys right)).1 =
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (via42Frames.stages left).a.key.constitutional.rule1a
        (via42Frames.stages right).a.key.constitutional.rule1a := by
  have compoundReadback (index : Fin 4) :
      (via42Frames.compounds index).prior.rule4aKey = (via42Frames.stages index).a.key := by
    let view := contextOccurrenceView pseudoReference via42Target
    let read := fun source => pseudoSpatialCertified.localizedDependencyLabel via42Target view source
    have uniformBuilt :
        pseudoSpatialCertified.buildRuleMajorCompoundRule45KeyWith?
          (fun stage position => pseudoSpatialCertified.buildRuleMajorCumulativeWithRead?
            stage read (2 * (carrierFuel pseudoReference + 1)) position)
          (via42Frames.frame.cursorAt index) = some (via42Frames.compounds index) := by
      rw [← pseudoSpatialCertified.buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor]
      rw [← pseudoSpatialCertified.buildActualRuleMajorCompoundRule45KeyExec?_eq]
      exact via42Frames.compoundBuilt index
    exact (pseudoSpatialCertified.contextStages_compound_readback
      (via42Frames.stages index) uniformBuilt).1
  have priorAgreement := via42Frames.retainedActual_priorComparison spatial_simpleBonded left right
  have constEq := OfficialRuleMajorKey.compare_eq_rule1a_of_decisive
    (left := (via42Frames.compounds left).prior.rule4aKey.constitutional)
    (right := (via42Frames.compounds right).prior.rule4aKey.constitutional) (by
      rw [compoundReadback left, compoundReadback right]
      exact decisive)
  have constNe : OfficialRuleMajorKey.compare
      (via42Frames.compounds left).prior.rule4aKey.constitutional
      (via42Frames.compounds right).prior.rule4aKey.constitutional ≠ Ordering.eq := by
    rw [constEq, compoundReadback left, compoundReadback right]
    exact decisive
  have cumulativeEq : pseudoSpatialCertified.compareLocalizedRerootCumulativeRule45Keys
      (via42Frames.compounds left).prior.rule4aKey
      (via42Frames.compounds right).prior.rule4aKey =
      OfficialRuleMajorKey.compare
        (via42Frames.compounds left).prior.rule4aKey.constitutional
        (via42Frames.compounds right).prior.rule4aKey.constitutional := by
    unfold CertifiedLocalizedCIPInput.compareLocalizedRerootCumulativeRule45Keys
    refine ConstitutionalLexAlgebra.compareLex_eq_left_of_left_ne_eq _ _ _ _ ?_
    simpa [Ordering.byKey] using constNe
  have cumulativeNe : pseudoSpatialCertified.compareLocalizedRerootCumulativeRule45Keys
      (via42Frames.compounds left).prior.rule4aKey
      (via42Frames.compounds right).prior.rule4aKey ≠ Ordering.eq := by
    rw [cumulativeEq]
    exact constNe
  have compoundComparison :=
    CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundRule4bcKeys_eq_rule4a_of_ne
      pseudoSpatialCertified (via42Frames.compounds left).prior
      (via42Frames.compounds right).prior cumulativeNe
  calc
    compare (ofLex (via42Frames.retainedKeys left)).1
        (ofLex (via42Frames.retainedKeys right)).1 =
      pseudoSpatialCertified.compareLocalizedRerootCompoundRule4bcKeys
        (via42Frames.compounds left).prior (via42Frames.compounds right).prior :=
      priorAgreement.symm
    _ = pseudoSpatialCertified.compareLocalizedRerootCumulativeRule45Keys
        (via42Frames.compounds left).prior.rule4aKey
        (via42Frames.compounds right).prior.rule4aKey := compoundComparison
    _ = OfficialRuleMajorKey.compare
        (via42Frames.compounds left).prior.rule4aKey.constitutional
        (via42Frames.compounds right).prior.rule4aKey.constitutional := cumulativeEq
    _ = OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (via42Frames.stages left).a.key.constitutional.rule1a
        (via42Frames.stages right).a.key.constitutional.rule1a := by
      rw [OfficialRuleMajorKey.compare_eq_rule1a_of_decisive (by
        rw [compoundReadback left, compoundReadback right]
        exact decisive), compoundReadback left, compoundReadback right]

private theorem via42_retained_prior_lt
    (higher lower : Fin 4)
    (sparse : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (via42Frames.stages higher).a.key.constitutional.rule1a
      (via42Frames.stages lower).a.key.constitutional.rule1a = Ordering.gt) :
    (ofLex (via42Frames.retainedKeys lower)).1 <
      (ofLex (via42Frames.retainedKeys higher)).1 := by
  have decisive : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (via42Frames.stages higher).a.key.constitutional.rule1a
      (via42Frames.stages lower).a.key.constitutional.rule1a ≠ Ordering.eq := by
    rw [sparse]
    decide
  have comparison := via42_retained_prior_compare_of_rule1a higher lower decisive
  rw [sparse] at comparison
  exact (completeLigandPriorKey_compare_gt_iff
    (ofLex (via42Frames.retainedKeys higher)).1
    (ofLex (via42Frames.retainedKeys lower)).1).mp comparison

private theorem via42_retained_prior_order :
    [via42ClSlot, via42ParentSlot, via42DupSlot, via42HSlot].Pairwise
      (fun left right => (ofLex (via42Frames.retainedKeys right)).1 <
        (ofLex (via42Frames.retainedKeys left)).1) := by
  rcases via42_sparse_strict_pairs with ⟨clParent, clDup, clH, parentDup, parentH, dupH⟩
  apply List.Pairwise.cons
  · intro slot member
    simp only [List.mem_cons] at member
    rcases member with equal | equal | equal | empty
    · subst slot
      exact via42_retained_prior_lt via42ClSlot via42ParentSlot clParent
    · subst slot
      exact via42_retained_prior_lt via42ClSlot via42DupSlot clDup
    · subst slot
      exact via42_retained_prior_lt via42ClSlot via42HSlot clH
    · simp at empty
  · apply List.Pairwise.cons
    · intro slot member
      simp only [List.mem_cons] at member
      rcases member with equal | equal | empty
      · subst slot
        exact via42_retained_prior_lt via42ParentSlot via42DupSlot parentDup
      · subst slot
        exact via42_retained_prior_lt via42ParentSlot via42HSlot parentH
      · simp at empty
    · apply List.Pairwise.cons
      · intro slot member
        simp only [List.mem_cons] at member
        rcases member with equal | empty
        · subst slot
          exact via42_retained_prior_lt via42DupSlot via42HSlot dupH
        · simp at empty
      · apply List.Pairwise.cons
        · intro slot member
          simp at member
        · exact List.Pairwise.nil

private theorem retainedPrior_pairwise_injective
    {α : Type} [LinearOrder α] {xs : List (Fin 4)} {key : Fin 4 → α}
    (perm : xs.Perm (List.finRange 4))
    (sorted : xs.Pairwise (fun i j => key j < key i)) :
    Function.Injective key := by
  intro i j equal
  by_contra different
  have hi : i ∈ xs := perm.mem_iff.mpr (List.mem_finRange i)
  have hj : j ∈ xs := perm.mem_iff.mpr (List.mem_finRange j)
  have either := (List.Pairwise.forall (fun _ _ h => h.symm)
    (sorted.imp fun h => Or.inr h)) hi hj different
  rw [equal] at either
  exact either.elim (lt_irrefl _) (lt_irrefl _)

private theorem via42_prior_injective :
    Function.Injective (fun slot => (ofLex (via42Frames.retainedKeys slot)).1) :=
  retainedPrior_pairwise_injective via42_order_perm via42_retained_prior_order

private theorem via42_not_prior_pair (left right : Fin 4) (different : left ≠ right) :
    ¬ CompletePriorPair via42Frames.retainedKeys left right := by
  intro pair
  exact different (via42_prior_injective pair.2)

private theorem via42_completeRule5PairCount_zero :
    completeRule5PairCount via42Frames.retainedKeys = 0 := by
  have h01 : ¬ CompletePriorPair via42Frames.retainedKeys 0 1 :=
    via42_not_prior_pair 0 1 (by decide)
  have h02 : ¬ CompletePriorPair via42Frames.retainedKeys 0 2 :=
    via42_not_prior_pair 0 2 (by decide)
  have h12 : ¬ CompletePriorPair via42Frames.retainedKeys 1 2 :=
    via42_not_prior_pair 1 2 (by decide)
  have h03 : ¬ CompletePriorPair via42Frames.retainedKeys 0 3 :=
    via42_not_prior_pair 0 3 (by decide)
  have h13 : ¬ CompletePriorPair via42Frames.retainedKeys 1 3 :=
    via42_not_prior_pair 1 3 (by decide)
  have h23 : ¬ CompletePriorPair via42Frames.retainedKeys 2 3 :=
    via42_not_prior_pair 2 3 (by decide)
  rw [completeRule5PairCount, sourceEnantiomorphicPairCount_eq_filter_length]
  simp [sourceUnorderedPairList, h01, h02, h12, h03, h13, h23]

private theorem spatialPoint_exists (atom : pseudoSpatialCertified.Atom) :
    ∃ point, pseudoSpatialCertified.spatialPointAt? atom = some point := by
  rcases LocalizedCyclicPseudoGeneratedLabels.spatial_readback with
    ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩
  fin_cases atom
  · exact ⟨P0, h0⟩
  · exact ⟨P1, h1⟩
  · exact ⟨P2, h2⟩
  · exact ⟨P3, h3⟩
  · exact ⟨P4, h4⟩
  · exact ⟨P5, h5⟩
  · exact ⟨P6, h6⟩
  · exact ⟨P7, h7⟩
  · exact ⟨P8, h8⟩

private noncomputable def via42Points (slot : Fin 4) : CartesianPoint3 :=
  Classical.choose (spatialPoint_exists (via42Frames.actualLigandAtoms slot))

private theorem via42Points_read (slot : Fin 4) :
    pseudoSpatialCertified.spatialPointAt? (via42Frames.actualLigandAtoms slot) =
      some (via42Points slot) :=
  Classical.choose_spec (spatialPoint_exists (via42Frames.actualLigandAtoms slot))

private theorem via42_point_values :
    via42Points via42ClSlot = P3 ∧ via42Points via42ParentSlot = P4 ∧
    via42Points via42DupSlot = P0 ∧ via42Points via42HSlot = P6 := by
  rcases LocalizedCyclicPseudoGeneratedLabels.spatial_readback with
    ⟨h0, _, _, h3, h4, _, h6, _, _⟩
  have p3 : pseudoSpatialCertified.spatialPointAt? (SA 3) = some P3 := by
    change pseudoSpatialCertified.spatialPointAt? (SA 3) = some P3 at h3
    exact h3
  have p4 : pseudoSpatialCertified.spatialPointAt? (SA 4) = some P4 := by
    change pseudoSpatialCertified.spatialPointAt? (SA 4) = some P4 at h4
    exact h4
  have p0 : pseudoSpatialCertified.spatialPointAt? (SA 0) = some P0 := by
    change pseudoSpatialCertified.spatialPointAt? (SA 0) = some P0 at h0
    exact h0
  have p6 : pseudoSpatialCertified.spatialPointAt? (SA 6) = some P6 := by
    change pseudoSpatialCertified.spatialPointAt? (SA 6) = some P6 at h6
    exact h6
  constructor
  · apply Option.some.inj
    exact (via42Points_read via42ClSlot).symm.trans (by rw [via42ClSlot_atom]; exact p3)
  constructor
  · apply Option.some.inj
    exact (via42Points_read via42ParentSlot).symm.trans (by rw [via42ParentSlot_atom]; exact p4)
  constructor
  · apply Option.some.inj
    exact (via42Points_read via42DupSlot).symm.trans (by rw [via42DupSlot_atom]; exact p0)
  · apply Option.some.inj
    exact (via42Points_read via42HSlot).symm.trans (by rw [via42HSlot_atom]; exact p6)

private theorem via42_order_points :
    [via42ClSlot, via42ParentSlot, via42DupSlot, via42HSlot].map via42Points =
      [P3, P4, P0, P6] := by
  rcases via42_point_values with ⟨h3, h4, h0, h6⟩
  simp [h3, h4, h0, h6]

private theorem via42_geometric_judgment :
    RetainedContextualDescriptorJudgmentAt pseudoSpatialCertified.moleculeGraph
      (descriptorMap pseudoReference) via42Unit via42Frames.actualArmGraphs
      via42Frames.W via42Frames.D via42Frames.actualCoordinates (.chiral RS.R) := by
  let points := via42Points
  refine ⟨points, ?_, ?_⟩
  · intro slot
    change pseudoSpatialCertified.spatialPointAt?
        (via42Frames.actualLigandAtoms slot) = some (points slot)
    exact via42Points_read slot
  · refine ⟨[via42ClSlot, via42ParentSlot, via42DupSlot, via42HSlot], RS.R,
      via42_order_perm, via42_retained_order, ?_, ?_⟩
    · change RationalTetrahedralDescriptor
        ([via42ClSlot, via42ParentSlot, via42DupSlot, via42HSlot].map via42Points) RS.R
      rw [via42_order_points]
      have sign : CartesianPoint3.orientedVolume P3 P4 P0 P6 < 0 :=
        (descriptorOfOrientedVolume?_eq_some_R_iff _).mp arm_descriptor.2
      exact ⟨P3, P4, P0, P6, rfl, sign⟩
    · change (LocalizedTetrahedralRSPseudoDescriptor.chiral RS.R) =
        classifyTetrahedralRSPseudo RS.R
          (completeRule5PairCount via42Frames.retainedKeys)
      rw [via42_completeRule5PairCount_zero]
      simp

private theorem via42_referenceState_R :
    referenceState pseudoReference via42Target = some (.chiral RS.R) :=
  (via42Frames.referenceState_some_iff_retainedJudgment spatial_simpleBonded (.chiral RS.R)).2
    via42_geometric_judgment

private noncomputable def shallowArmPoints (slot : Fin 4) : CartesianPoint3 :=
  Classical.choose (spatialPoint_exists (directArmFrames.actualLigandAtoms slot))

private theorem shallowArmPoints_read (slot : Fin 4) :
    pseudoSpatialCertified.spatialPointAt? (directArmFrames.actualLigandAtoms slot) =
      some (shallowArmPoints slot) :=
  Classical.choose_spec (spatialPoint_exists (directArmFrames.actualLigandAtoms slot))

private theorem shallowArm_point_values :
    shallowArmPoints shallowArmClSlot = P3 ∧ shallowArmPoints shallowArmCarbonSlot = P4 ∧
    shallowArmPoints shallowArmRootSlot = P0 ∧ shallowArmPoints shallowArmHSlot = P6 := by
  rcases LocalizedCyclicPseudoGeneratedLabels.spatial_readback with
    ⟨h0, _, _, h3, h4, _, h6, _, _⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Option.some.inj
    exact (shallowArmPoints_read shallowArmClSlot).symm.trans
      (by rw [shallowArmClSlot_atom]; exact h3)
  · apply Option.some.inj
    exact (shallowArmPoints_read shallowArmCarbonSlot).symm.trans
      (by rw [shallowArmCarbonSlot_atom]; exact h4)
  · apply Option.some.inj
    exact (shallowArmPoints_read shallowArmRootSlot).symm.trans
      (by rw [shallowArmRootSlot_atom]; exact h0)
  · apply Option.some.inj
    exact (shallowArmPoints_read shallowArmHSlot).symm.trans
      (by rw [shallowArmHSlot_atom]; exact h6)

private theorem shallowArm_order_points :
    [shallowArmClSlot, shallowArmCarbonSlot, shallowArmRootSlot, shallowArmHSlot].map
        shallowArmPoints = [P3, P4, P0, P6] := by
  rcases shallowArm_point_values with ⟨h3, h4, h0, h6⟩
  simp [h3, h4, h0, h6]

private theorem shallowArm_geometric_judgment :
    RetainedContextualDescriptorJudgmentAt pseudoSpatialCertified.moleculeGraph
      (descriptorMap pseudoReference) directArmUnit directArmFrames.actualArmGraphs
      directArmFrames.W directArmFrames.D directArmFrames.actualCoordinates (.chiral RS.R) := by
  let points := shallowArmPoints
  refine ⟨points, ?_, ?_⟩
  · intro slot
    change pseudoSpatialCertified.spatialPointAt?
      (directArmFrames.actualLigandAtoms slot) = some (points slot)
    exact shallowArmPoints_read slot
  · refine ⟨[shallowArmClSlot, shallowArmCarbonSlot, shallowArmRootSlot, shallowArmHSlot],
      RS.R, shallowArm_order_perm, shallowArm_retained_order, ?_, ?_⟩
    · change RationalTetrahedralDescriptor
        ([shallowArmClSlot, shallowArmCarbonSlot, shallowArmRootSlot, shallowArmHSlot].map
          shallowArmPoints) RS.R
      rw [shallowArm_order_points]
      have sign : CartesianPoint3.orientedVolume P3 P4 P0 P6 < 0 :=
        (descriptorOfOrientedVolume?_eq_some_R_iff _).mp arm_descriptor.2
      exact ⟨P3, P4, P0, P6, rfl, sign⟩
    · change LocalizedTetrahedralRSPseudoDescriptor.chiral RS.R =
        classifyTetrahedralRSPseudo RS.R
          (completeRule5PairCount directArmFrames.retainedKeys)
      rw [shallowArm_completeRule5PairCount_zero]
      simp

private theorem shallowArm_referenceState_R :
    referenceState pseudoReference directArmTarget = some (.chiral RS.R) :=
  (directArmFrames.referenceState_some_iff_retainedJudgment spatial_simpleBonded (.chiral RS.R)).2
    shallowArm_geometric_judgment

private theorem carbon_cursor_outward :
    (directArmFrames.frame.cursorAt carbonSlot).occurrence.1 ∈
      pseudoSpatialCertified.localizedCarrierOutwardChildFrames
        (fuel := carrierFuel pseudoReference) directArmTarget.1 := by
  have neighbor :=
    pseudoSpatialCertified.localizedOccurrenceFourLigandFrame_cursor_mem_neighborFrames
      directArmTarget directArmFrames.frame direct_frame _
      (direct_cursor_present carbonSlot)
  rw [localizedRerootNeighborFrames, List.mem_append] at neighbor
  rcases neighbor with parent | outward
  · exfalso
    obtain ⟨certificate, parentAtom, parentCurrent, parentObserved, _visited, _adjacent, _active,
        _member⟩ :=
      pseudoSpatialCertified.realCenter_parent_current directArmTarget directArmChild.currentEq
        direct_address_nonempty
    have singleton := certificate.carrierParentFrames_eq_singleton pseudoSpatialCertified
    have frameEq : (directArmFrames.frame.cursorAt carbonSlot).occurrence.1 =
        certificate.parent.1 := by
      have member : (directArmFrames.frame.cursorAt carbonSlot).occurrence.1 ∈
          [certificate.parent.1] := by
        simpa [singleton] using parent
      simpa using member
    have onParent : certificate.parent.1.node.current? = some (SA ⟨4, by decide⟩) := by
      have current := directArmFrames.ligandAt carbonSlot
      unfold pseudoReference at current
      rw [frameEq] at current
      have atomEq : pseudoSpatialCertified.detectedMultiCenterMolecule.ligandAtomAt
          directArmFrames.center (directArmFrames.detectedLigandPermutation carbonSlot) =
          SA ⟨4, by decide⟩ := by
        have defined : directArmFrames.actualLigandAtoms carbonSlot =
            pseudoSpatialCertified.detectedMultiCenterMolecule.ligandAtomAt
              directArmFrames.center (directArmFrames.detectedLigandPermutation carbonSlot) := by
          unfold pseudoReference
          rfl
        rw [← defined]
        exact carbonSlot_atom
      rw [atomEq] at current
      exact current
    have parentIsRoot : parentAtom = SA ⟨0, by decide⟩ := by
      have observed : directArmTarget.1.node.parent? = some parentAtom := parentObserved
      have nodeParent : directArmTarget.1.node.parent? = some (SA ⟨0, by decide⟩) := by
        rw [directArmChild.nodeEq, root_node, OfficialCIPNode.extend, OfficialCIPNode.root,
          OfficialCIPNode.parent?]
        rfl
      exact Option.some.inj (observed.symm.trans nodeParent)
    have wrong : parentAtom = SA ⟨4, by decide⟩ :=
      Option.some.inj (parentCurrent.symm.trans onParent)
    have vals := congrArg Fin.val (parentIsRoot.symm.trans wrong)
    simp [SA_val] at vals
  · exact outward

private theorem carbon_extend :
    (directArmFrames.frame.cursorAt carbonSlot).occurrence.1.node =
      directArmTarget.1.node.extend (SA ⟨4, by decide⟩) 0 := by
  obtain ⟨w, _slot, nodeEq, current, _rootEq, _addressEq, _zip, _notParent, _adj⟩ :=
    pseudoSpatialCertified.simpleBond_outwardFrame_extend_zero spatial_simpleBonded
      directArmTarget directArmChild.currentEq directArm_real _
      carbon_cursor_outward
  have ligandCurrent := directArmFrames.ligandAt carbonSlot
  unfold pseudoReference at ligandCurrent
  have wEq : w = SA ⟨4, by decide⟩ := by
    apply Option.some.inj
    rw [← current]
    have atomEq : pseudoSpatialCertified.detectedMultiCenterMolecule.ligandAtomAt
        directArmFrames.center (directArmFrames.detectedLigandPermutation carbonSlot) =
        SA ⟨4, by decide⟩ := by
      have defined : directArmFrames.actualLigandAtoms carbonSlot =
          pseudoSpatialCertified.detectedMultiCenterMolecule.ligandAtomAt
            directArmFrames.center (directArmFrames.detectedLigandPermutation carbonSlot) := by
        unfold pseudoReference
        rfl
      rw [← defined]
      exact carbonSlot_atom
    rw [atomEq] at ligandCurrent
    exact ligandCurrent
  simpa [wEq] using nodeEq

private theorem carbon_parent :
    (directArmFrames.frame.cursorAt carbonSlot).occurrence.1.node.parent? =
      some (SA ⟨2, by decide⟩) := by
  rw [carbon_extend, directArmChild.nodeEq, root_node]
  simp [OfficialCIPNode.extend, OfficialCIPNode.root, OfficialCIPNode.parent?]

private theorem carbon_fresh {a : pseudoSpatialCertified.Atom} (ha : a.val = 4) :
    a ∉ directArmTarget.1.node.history := by
  intro member
  rw [directArmChild.nodeEq] at member
  simp only [OfficialCIPNode.extend_history, root_history, List.mem_cons] at member
  rcases member with eq | eq
  · have vals := congrArg Fin.val eq
    simp [SA_val, ha] at vals
  · rcases eq with eq | eq
    · have vals := congrArg Fin.val eq
      simp [SA_val, rootTetra, ha] at vals
    · cases eq

private theorem carbon_real :
    (directArmFrames.frame.cursorAt carbonSlot).occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom := by
  rw [carbon_extend, OfficialCIPNode.extend, OfficialCIPNode.childProvenance]
  exact if_neg (carbon_fresh (a := SA ⟨4, by decide⟩) (by simp [SA_val]))

private theorem carbon_previous :
    (directArmFrames.frame.cursorAt carbonSlot).previous? = some directArmTarget :=
  pseudoSpatialCertified.localizedOccurrenceFourLigandFrame_cursor_previous
    directArmTarget directArmFrames.frame direct_frame _
    (direct_cursor_present carbonSlot)

private theorem carbon_duplicateFree :
    (directArmFrames.frame.cursorAt carbonSlot).occurrence.1.node.isDuplicateLeaf = false :=
  pseudoSpatialCertified.isDuplicateLeaf_eq_false_of_provenance_real _ carbon_real

private theorem carbon_sameRoot :
    directArmTarget.1.root =
      (directArmFrames.frame.cursorAt carbonSlot).occurrence.1.root :=
  (pseudoSpatialCertified.localizedOccurrenceFourLigandFrame_cursor_root
    directArmTarget directArmFrames.frame direct_frame _
    (direct_cursor_present carbonSlot)).symm

private theorem carbon_addressDrop :
    directArmTarget.1.address =
      (directArmFrames.frame.cursorAt carbonSlot).occurrence.1.address.dropLast := by
  obtain ⟨_w, _slot, _nodeEq, _current, _rootEq, addressEq, _zip, _notParent, _adj⟩ :=
    pseudoSpatialCertified.simpleBond_outwardFrame_extend_zero spatial_simpleBonded
      directArmTarget directArmChild.currentEq directArm_real
      (directArmFrames.frame.cursorAt carbonSlot).occurrence.1 carbon_cursor_outward
  simp [addressEq]

private theorem carbon_addressStep :
    directArmTarget.1.address.length + 1 =
      (directArmFrames.frame.cursorAt carbonSlot).occurrence.1.address.length := by
  obtain ⟨_w, _slot, _nodeEq, _current, _rootEq, addressEq, _zip, _notParent, _adj⟩ :=
    pseudoSpatialCertified.simpleBond_outwardFrame_extend_zero spatial_simpleBonded
      directArmTarget directArmChild.currentEq directArm_real
      (directArmFrames.frame.cursorAt carbonSlot).occurrence.1 carbon_cursor_outward
  simp [addressEq]

private theorem carbon_current :
    (directArmFrames.frame.cursorAt carbonSlot).occurrence.1.node.current? =
      some (SA ⟨4, by decide⟩) := by
  rw [carbon_extend]
  simp [OfficialCIPNode.extend_current?]

private theorem carbonCursor_slot :
    (directArmFrames.frame.cursorAt carbonSlot).occurrence.1.address = [1, 1] := by
  obtain ⟨w, childSlot, nodeEq, _current, _root, addressEq, zipMem, _notParent, _adj⟩ :=
    pseudoSpatialCertified.simpleBond_outwardFrame_extend_zero spatial_simpleBonded
      directArmTarget directArmChild.currentEq directArm_real _ carbon_cursor_outward
  have sameNode := carbon_extend.symm.trans nodeEq
  have wEq : w = SA ⟨4, by decide⟩ := by
    injection sameNode with atomEq
    exact Option.some.inj atomEq.symm
  subst w
  have parentNodeEq : directArmTarget.1.node =
      LocalizedCyclicPseudoRootComponentEvaluation.node2 := by
    have := congrArg (fun f : pseudoSpatialCertified.LocalizedCIPOccurrenceFrame => f.node)
      directArmFrame_eq_component_armF
    simpa [LocalizedCyclicPseudoRootComponentEvaluation.armF] using this
  rw [parentNodeEq, component_arm_children] at zipMem
  have atList :
      (LocalizedCyclicPseudoRootComponentEvaluation.node2.extend (SA 4) 0, childSlot) ∈
        ([LocalizedCyclicPseudoRootComponentEvaluation.node2.extend (SA 3) 0,
          LocalizedCyclicPseudoRootComponentEvaluation.node2.extend (SA 4) 0,
          LocalizedCyclicPseudoRootComponentEvaluation.node2.extend (SA 6) 0] :
          List (OfficialCIPNode pseudoSpatialCertified.Atom)).zipIdx := by
    simpa using zipMem
  have childSlotEq : childSlot = 1 := by
    simpa [SA, LocalizedCyclicPseudoRootComponentEvaluation.SA,
      OfficialCIPNode.extend, OfficialCIPNode.childProvenance] using atList
  rw [addressEq, directArmFrame_eq_component_armF, childSlotEq,
    LocalizedCyclicPseudoRootComponentEvaluation.armF]
  rfl

private theorem carbonCursor_eq_via24F :
    (directArmFrames.frame.cursorAt carbonSlot).occurrence.1 =
      LocalizedCyclicPseudoRootComponentEvaluation.via24F := by
  apply LocalizedCIPOccurrenceFrame.ext
  · rw [LocalizedCyclicPseudoRootComponentEvaluation.via24F]
    have rootEq := congrArg
      (fun f : pseudoSpatialCertified.LocalizedCIPOccurrenceFrame => f.root)
      directArmFrame_eq_component_armF
    exact carbon_sameRoot.symm.trans rootEq
  · exact carbonCursor_slot
  · have parentNodeEq := congrArg
      (fun f : pseudoSpatialCertified.LocalizedCIPOccurrenceFrame => f.node)
      directArmFrame_eq_component_armF
    change directArmTarget.1.node =
      LocalizedCyclicPseudoRootComponentEvaluation.armF.node at parentNodeEq
    rw [carbon_extend, parentNodeEq,
      LocalizedCyclicPseudoRootComponentEvaluation.via24F,
      LocalizedCyclicPseudoRootComponentEvaluation.node24,
      LocalizedCyclicPseudoRootComponentEvaluation.node2,
      LocalizedCyclicPseudoRootComponentEvaluation.rootNode]
    simp [OfficialCIPNode.extend, OfficialCIPNode.root,
      LocalizedCyclicPseudoRootComponentEvaluation.SA, SA,
      LocalizedCyclicPseudoRootComponentEvaluation.armF,
      LocalizedCyclicPseudoRootComponentEvaluation.node2,
      LocalizedCyclicPseudoRootComponentEvaluation.rootNode]
  · have grade := pseudoSpatialCertified.localizedCIPOccurrence_depthGrade
      (fuel := carrierFuel pseudoReference) (directArmFrames.frame.cursorAt carbonSlot).occurrence
    rw [carbonCursor_slot] at grade
    have fuelNum : carrierFuel pseudoReference = 10 := by
      rw [carrierFuel_eq, spatial_atomCount]
    have grade' : 2 + (directArmFrames.frame.cursorAt carbonSlot).occurrence.1.remaining = 11 := by
      simpa [fuelNum] using grade
    simp [LocalizedCyclicPseudoRootComponentEvaluation.via24F,
      LocalizedCyclicPseudoRootComponentEvaluation.Fuel,
      LocalizedCyclicPseudoRootComponentEvaluation.fuel_eq]
    omega

abbrev via24Target : Occurrence pseudoReference :=
  (directArmFrames.frame.cursorAt carbonSlot).occurrence

private theorem via24_unit_eq :
    pseudoSpatialCertified.molecularFrameUnit via24Target.1 =
      ⟨SA ⟨0, by decide⟩, [SA ⟨2, by decide⟩, SA ⟨4, by decide⟩]⟩ := by
  have eq := congrArg pseudoSpatialCertified.molecularFrameUnit
    carbonCursor_eq_via24F
  rw [LocalizedCyclicPseudoRootComponentEvaluation.via24F] at eq
  simpa [molecularFrameUnit, LocalizedCyclicPseudoRootComponentEvaluation.node24,
    LocalizedCyclicPseudoRootComponentEvaluation.node2,
    LocalizedCyclicPseudoRootComponentEvaluation.rootNode,
    OfficialCIPNode.extend, OfficialCIPNode.root, SA,
    LocalizedCyclicPseudoRootComponentEvaluation.SA] using eq

private theorem via24_detected :
    IsDetectedCenter pseudoSpatialCertified.moleculeGraph
      (pseudoSpatialCertified.molecularFrameUnit via24Target.1).atom := by
  rw [via24_unit_eq]
  exact detected_atom ⟨4, by decide⟩
    ((degree_four_iff 4).mpr (Or.inr (Or.inr rfl)))

private def via24Unit : DetectedOccurrence pseudoSpatialCertified.moleculeGraph :=
  ⟨pseudoSpatialCertified.molecularFrameUnit via24Target.1, via24_detected⟩

private theorem via24_unit_target :
    pseudoSpatialCertified.molecularFrameUnit via24Target.1 = via24Unit.1 := rfl

private abbrev via24Frames :
    ContextFrameCompilation pseudoReference via24Target via24Unit via24_unit_target :=
  cyclicContextFrameCompilation pseudoReference spatial_simpleBonded via24Target
    carbon_real via24Unit via24_unit_target

private theorem component_via24_neighbors :
    LocalizedCyclicPseudoRootComponentEvaluation.neighborFrames0
        LocalizedCyclicPseudoRootComponentEvaluation.via24F =
      [LocalizedCyclicPseudoRootComponentEvaluation.armF,
        LocalizedCyclicPseudoRootComponentEvaluation.via24DupF,
        LocalizedCyclicPseudoRootComponentEvaluation.via24HF,
        LocalizedCyclicPseudoRootComponentEvaluation.via24ClF] := by
  decide +kernel

private theorem via24_slot (index : Fin 9)
    (adjacent : graph.Adj ⟨4, by decide⟩ index) :
    ∃ slot : Fin 4, via24Frames.actualLigandAtoms slot = SA index := by
  have centerEq : via24Frames.center.1 = SA ⟨4, by decide⟩ := by
    rw [via24Frames.centerEq]
    simp [via24Unit, OccurrenceUnit.atom, via24_unit_eq, SA]
  have adjacentCenter : pseudoSpatialCertified.moleculeGraph.Adj via24Frames.center.1
      (SA index) := by
    rw [centerEq]
    exact (spatial_adj ⟨4, by decide⟩ index).mpr adjacent
  obtain ⟨i, atomEq⟩ :=
    pseudoSpatialCertified.detectedMultiCenterMolecule.ligandAtomAt_surjective
      via24Frames.center (SA index) adjacentCenter
  refine ⟨via24Frames.detectedLigandPermutation.symm i, ?_⟩
  unfold pseudoReference
  simp [ContextFrameCompilation.actualLigandAtoms, Equiv.apply_symm_apply, atomEq]

private theorem via24_cursor_mem_component_neighbors (slot : Fin 4) :
    (via24Frames.frame.cursorAt slot).occurrence.1 ∈
      [LocalizedCyclicPseudoRootComponentEvaluation.armF,
        LocalizedCyclicPseudoRootComponentEvaluation.via24DupF,
        LocalizedCyclicPseudoRootComponentEvaluation.via24HF,
        LocalizedCyclicPseudoRootComponentEvaluation.via24ClF] := by
  have present : via24Frames.frame.cursorAt slot ∈ via24Frames.frame.cursors :=
    List.get_mem via24Frames.frame.cursors (Fin.cast via24Frames.frame.length_eq.symm slot)
  have computed :
      pseudoSpatialCertified.localizedOccurrenceFourLigandFrame? via24Target =
        some via24Frames.frame := by
    rw [← pseudoSpatialCertified.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?]
    exact via24Frames.frameComputed
  have mapped := pseudoSpatialCertified.localizedOccurrenceFourLigandFrame_cursors_map_eq_neighborFrames
    via24Target via24Frames.frame computed
  have member :
      (via24Frames.frame.cursorAt slot).occurrence.1 ∈
        pseudoSpatialCertified.localizedRerootNeighborFrames
          (fuel := carrierFuel pseudoReference) via24Target.1 := by
    rw [← mapped]
    exact List.mem_map.mpr ⟨via24Frames.frame.cursorAt slot, present, rfl⟩
  have rootZero : via24Target.1.root =
      LocalizedCyclicPseudoRootComponentEvaluation.SA 0 := by
    have roots := congrArg
      (fun f : pseudoSpatialCertified.LocalizedCIPOccurrenceFrame => f.root)
      carbonCursor_eq_via24F
    rw [LocalizedCyclicPseudoRootComponentEvaluation.via24F] at roots
    exact roots
  rw [LocalizedCyclicPseudoRootComponentEvaluation.neighborFrames_eq0
    via24Target.1 rootZero] at member
  rw [carbonCursor_eq_via24F, component_via24_neighbors] at member
  exact member

private noncomputable def via24ClSlot : Fin 4 :=
  Classical.choose (via24_slot ⟨8, by decide⟩ ((adj_closing 8).mpr (by simp)))

private theorem via24ClSlot_atom :
    via24Frames.actualLigandAtoms via24ClSlot = SA ⟨8, by decide⟩ :=
  Classical.choose_spec (via24_slot ⟨8, by decide⟩ ((adj_closing 8).mpr (by simp)))

private noncomputable def via24ParentSlot : Fin 4 :=
  Classical.choose (via24_slot ⟨2, by decide⟩ ((adj_closing 2).mpr (by simp)))

private theorem via24ParentSlot_atom :
    via24Frames.actualLigandAtoms via24ParentSlot = SA ⟨2, by decide⟩ :=
  Classical.choose_spec (via24_slot ⟨2, by decide⟩ ((adj_closing 2).mpr (by simp)))

private noncomputable def via24DupSlot : Fin 4 :=
  Classical.choose (via24_slot ⟨0, by decide⟩ ((adj_closing 0).mpr (by simp)))

private theorem via24DupSlot_atom :
    via24Frames.actualLigandAtoms via24DupSlot = SA ⟨0, by decide⟩ :=
  Classical.choose_spec (via24_slot ⟨0, by decide⟩ ((adj_closing 0).mpr (by simp)))

private noncomputable def via24HSlot : Fin 4 :=
  Classical.choose (via24_slot ⟨7, by decide⟩ ((adj_closing 7).mpr (by simp)))

private theorem via24HSlot_atom :
    via24Frames.actualLigandAtoms via24HSlot = SA ⟨7, by decide⟩ :=
  Classical.choose_spec (via24_slot ⟨7, by decide⟩ ((adj_closing 7).mpr (by simp)))

private theorem via24_slot_current (slot : Fin 4) (index : Fin 9)
    (atomEq : via24Frames.actualLigandAtoms slot = SA index) :
    (via24Frames.frame.cursorAt slot).occurrence.1.node.current? = some (SA index) := by
  have current := via24Frames.ligandAt slot
  unfold pseudoReference at current
  have defined : via24Frames.actualLigandAtoms slot =
      pseudoSpatialCertified.detectedMultiCenterMolecule.ligandAtomAt
        via24Frames.center (via24Frames.detectedLigandPermutation slot) := by
    unfold pseudoReference
    rfl
  have actualAtom :
      pseudoSpatialCertified.detectedMultiCenterMolecule.ligandAtomAt
        via24Frames.center (via24Frames.detectedLigandPermutation slot) = SA index := by
    rw [← defined]
    exact atomEq
  rw [actualAtom] at current
  exact current

private theorem via24_cursor_eq_component
    (slot : Fin 4)
    (candidate : LocalizedCyclicPseudoRootComponentEvaluation.Frame)
    (sameCurrent :
      (via24Frames.frame.cursorAt slot).occurrence.1.node.current? =
        candidate.node.current?)
    (candidateMem : candidate ∈
      [LocalizedCyclicPseudoRootComponentEvaluation.armF,
        LocalizedCyclicPseudoRootComponentEvaluation.via24DupF,
        LocalizedCyclicPseudoRootComponentEvaluation.via24HF,
        LocalizedCyclicPseudoRootComponentEvaluation.via24ClF]) :
    (via24Frames.frame.cursorAt slot).occurrence.1 = candidate := by
  have actualMem := via24_cursor_mem_component_neighbors slot
  have nodup :
      ([LocalizedCyclicPseudoRootComponentEvaluation.armF,
        LocalizedCyclicPseudoRootComponentEvaluation.via24DupF,
        LocalizedCyclicPseudoRootComponentEvaluation.via24HF,
        LocalizedCyclicPseudoRootComponentEvaluation.via24ClF].map
        (fun f => f.node.current?)).Nodup := by
    decide
  exact List.inj_on_of_nodup_map nodup actualMem candidateMem sameCurrent

private theorem actual_via24_cursor_const_rule1a
    (slot : Fin 4)
    (candidate : LocalizedCyclicPseudoRootComponentEvaluation.Frame)
    (sameCurrent :
      (via24Frames.frame.cursorAt slot).occurrence.1.node.current? =
        candidate.node.current?)
    (candidateMem : candidate ∈
      [LocalizedCyclicPseudoRootComponentEvaluation.armF,
        LocalizedCyclicPseudoRootComponentEvaluation.via24DupF,
        LocalizedCyclicPseudoRootComponentEvaluation.via24HF,
        LocalizedCyclicPseudoRootComponentEvaluation.via24ClF]) :
    ∃ key,
      LocalizedCyclicPseudoRootComponentEvaluation.buildF .rule4a
        LocalizedCyclicPseudoRootComponentEvaluation.evalFuel candidate
        (some LocalizedCyclicPseudoRootComponentEvaluation.via24F) = some key ∧
      key.constitutional.rule1a =
        (via24Frames.stages slot).a.key.constitutional.rule1a := by
  let cursor := via24Frames.frame.cursorAt slot
  let parent : pseudoSpatialCertified.LocalizedRerootCursor
      (carrierFuel pseudoReference) := ⟨via24Target, none⟩
  have valid := pseudoSpatialCertified.localizedRerootChild_valid parent cursor
    (pseudoSpatialCertified.executableLocalizedRerootChildren parent)
    (pseudoSpatialCertified.executableLocalizedRerootChildren_declarative parent)
    (via24Frames.childAt slot)
  have rootZero : cursor.occurrence.1.root =
      LocalizedCyclicPseudoRootComponentEvaluation.SA 0 := by
    have cursorRoot :=
      pseudoSpatialCertified.localizedOccurrenceFourLigandFrame_cursor_root
        via24Target via24Frames.frame
        (by
          rw [← pseudoSpatialCertified.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?]
          exact via24Frames.frameComputed)
        cursor (List.get_mem via24Frames.frame.cursors
          (Fin.cast via24Frames.frame.length_eq.symm slot))
    have targetRoot := congrArg
      (fun f : pseudoSpatialCertified.LocalizedCIPOccurrenceFrame => f.root)
      carbonCursor_eq_via24F
    rw [LocalizedCyclicPseudoRootComponentEvaluation.via24F] at targetRoot
    exact cursorRoot.trans targetRoot
  have built := (via24Frames.stages slot).a.built
  unfold pseudoReference at built
  rw [pseudoSpatialCertified.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized] at built
  obtain ⟨twinKey, builtTwin, tableEq⟩ := actualRule1a_eq_rootComponent cursor valid
    (contextOccurrenceRead pseudoReference via24Target)
    (fuel := 2 * (carrierFuel pseudoReference + 1))
    (via24Frames.stages slot).a.key built rootZero
  have occurrenceEq : cursor.occurrence.1 = candidate :=
    via24_cursor_eq_component slot candidate sameCurrent candidateMem
  have previousEq :
      cursor.previous?.map Subtype.val =
        some LocalizedCyclicPseudoRootComponentEvaluation.via24F := by
    change (via24Frames.frame.cursorAt slot).previous?.map Subtype.val =
      some LocalizedCyclicPseudoRootComponentEvaluation.via24F
    rw [pseudoSpatialCertified.localizedOccurrenceFourLigandFrame_cursor_previous
        via24Target via24Frames.frame
        (by
          rw [← pseudoSpatialCertified.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?]
          exact via24Frames.frameComputed)
        (via24Frames.frame.cursorAt slot)
        (List.get_mem via24Frames.frame.cursors
          (Fin.cast via24Frames.frame.length_eq.symm slot))]
    exact congrArg some carbonCursor_eq_via24F
  have previousEq' :
      (cursor.previous?.map Subtype.val :
        Option LocalizedCyclicPseudoRootComponentEvaluation.Frame) =
        some LocalizedCyclicPseudoRootComponentEvaluation.via24F := by
    exact previousEq
  have inputEq :
      ((cursor.occurrence.1, cursor.previous?.map Subtype.val) :
        LocalizedCyclicPseudoRootComponentEvaluation.Frame ×
          Option LocalizedCyclicPseudoRootComponentEvaluation.Frame) =
        (candidate, some LocalizedCyclicPseudoRootComponentEvaluation.via24F) := by
    exact Prod.ext occurrenceEq previousEq'
  have callEq := congrArg
    (fun pair : LocalizedCyclicPseudoRootComponentEvaluation.Frame ×
        Option LocalizedCyclicPseudoRootComponentEvaluation.Frame =>
      LocalizedCyclicPseudoRootComponentEvaluation.buildF .rule4a
        LocalizedCyclicPseudoRootComponentEvaluation.evalFuel pair.1 pair.2)
    inputEq
  refine ⟨twinKey, ?_, tableEq⟩
  exact callEq.symm.trans builtTwin

private theorem via24_cl_key :
    ∃ key,
      LocalizedCyclicPseudoRootComponentEvaluation.buildF .rule4a
        LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
        LocalizedCyclicPseudoRootComponentEvaluation.via24ClF
        (some LocalizedCyclicPseudoRootComponentEvaluation.via24F) = some key ∧
      key.constitutional.rule1a =
        (via24Frames.stages via24ClSlot).a.key.constitutional.rule1a := by
  apply actual_via24_cursor_const_rule1a via24ClSlot
      LocalizedCyclicPseudoRootComponentEvaluation.via24ClF
  · exact (via24_slot_current via24ClSlot ⟨8, by decide⟩ via24ClSlot_atom).trans
      (by simp [LocalizedCyclicPseudoRootComponentEvaluation.via24ClF,
        LocalizedCyclicPseudoRootComponentEvaluation.node24,
        LocalizedCyclicPseudoRootComponentEvaluation.node2,
        LocalizedCyclicPseudoRootComponentEvaluation.rootNode,
        OfficialCIPNode.root, OfficialCIPNode.extend, SA,
        LocalizedCyclicPseudoRootComponentEvaluation.SA])
  · simp

private theorem via24_parent_key :
    ∃ key,
      LocalizedCyclicPseudoRootComponentEvaluation.buildF .rule4a
        LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
        LocalizedCyclicPseudoRootComponentEvaluation.armF
        (some LocalizedCyclicPseudoRootComponentEvaluation.via24F) = some key ∧
      key.constitutional.rule1a =
        (via24Frames.stages via24ParentSlot).a.key.constitutional.rule1a := by
  apply actual_via24_cursor_const_rule1a via24ParentSlot
      LocalizedCyclicPseudoRootComponentEvaluation.armF
  · exact (via24_slot_current via24ParentSlot ⟨2, by decide⟩ via24ParentSlot_atom).trans
      (by simp [LocalizedCyclicPseudoRootComponentEvaluation.armF,
        LocalizedCyclicPseudoRootComponentEvaluation.node2,
        LocalizedCyclicPseudoRootComponentEvaluation.rootNode,
        OfficialCIPNode.root, OfficialCIPNode.extend, SA,
        LocalizedCyclicPseudoRootComponentEvaluation.SA])
  · simp

private theorem via24_dup_key :
    ∃ key,
      LocalizedCyclicPseudoRootComponentEvaluation.buildF .rule4a
        LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
        LocalizedCyclicPseudoRootComponentEvaluation.via24DupF
        (some LocalizedCyclicPseudoRootComponentEvaluation.via24F) = some key ∧
      key.constitutional.rule1a =
        (via24Frames.stages via24DupSlot).a.key.constitutional.rule1a := by
  apply actual_via24_cursor_const_rule1a via24DupSlot
      LocalizedCyclicPseudoRootComponentEvaluation.via24DupF
  · exact (via24_slot_current via24DupSlot ⟨0, by decide⟩ via24DupSlot_atom).trans
      (by simp [LocalizedCyclicPseudoRootComponentEvaluation.via24DupF,
        LocalizedCyclicPseudoRootComponentEvaluation.node24,
        LocalizedCyclicPseudoRootComponentEvaluation.node2,
        LocalizedCyclicPseudoRootComponentEvaluation.rootNode,
        OfficialCIPNode.root, OfficialCIPNode.extend, SA,
        LocalizedCyclicPseudoRootComponentEvaluation.SA])
  · simp

private theorem via24_h_key :
    ∃ key,
      LocalizedCyclicPseudoRootComponentEvaluation.buildF .rule4a
        LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
        LocalizedCyclicPseudoRootComponentEvaluation.via24HF
        (some LocalizedCyclicPseudoRootComponentEvaluation.via24F) = some key ∧
      key.constitutional.rule1a =
        (via24Frames.stages via24HSlot).a.key.constitutional.rule1a := by
  apply actual_via24_cursor_const_rule1a via24HSlot
      LocalizedCyclicPseudoRootComponentEvaluation.via24HF
  · exact (via24_slot_current via24HSlot ⟨7, by decide⟩ via24HSlot_atom).trans
      (by simp [LocalizedCyclicPseudoRootComponentEvaluation.via24HF,
        LocalizedCyclicPseudoRootComponentEvaluation.node24,
        LocalizedCyclicPseudoRootComponentEvaluation.node2,
        LocalizedCyclicPseudoRootComponentEvaluation.rootNode,
        OfficialCIPNode.root, OfficialCIPNode.extend, SA,
        LocalizedCyclicPseudoRootComponentEvaluation.SA])
  · simp

private def via24FiniteKey
    (frame : LocalizedCyclicPseudoRootComponentEvaluation.Frame) :
    OfficialRuleMajorKey LocalizedCyclicPseudoRootComponentEvaluation.Atom :=
  match LocalizedCyclicPseudoRootComponentEvaluation.buildF .rule4a
      LocalizedCyclicPseudoRootComponentEvaluation.evalFuel frame
      (some LocalizedCyclicPseudoRootComponentEvaluation.via24F) with
  | some key => key.constitutional
  | none =>
      { rule1a := [], rule1b := [], rule2 := [], sourceNodes := [], complete := false }

private theorem via24_component_cl_rule1a_gt_parent :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (via24FiniteKey LocalizedCyclicPseudoRootComponentEvaluation.via24ClF).rule1a
        (via24FiniteKey LocalizedCyclicPseudoRootComponentEvaluation.armF).rule1a =
      Ordering.gt := by
  decide +kernel

private theorem via24_component_parent_rule1a_gt_dup :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (via24FiniteKey LocalizedCyclicPseudoRootComponentEvaluation.armF).rule1a
        (via24FiniteKey LocalizedCyclicPseudoRootComponentEvaluation.via24DupF).rule1a =
      Ordering.gt := by
  decide +kernel

private theorem via24_actual_cl_rule1a_gt_parent :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (via24Frames.stages via24ClSlot).a.key.constitutional.rule1a
        (via24Frames.stages via24ParentSlot).a.key.constitutional.rule1a =
      Ordering.gt := by
  obtain ⟨clKey, clBuilt, clTable⟩ := via24_cl_key
  obtain ⟨parentKey, parentBuilt, parentTable⟩ := via24_parent_key
  have clEq :
      via24FiniteKey LocalizedCyclicPseudoRootComponentEvaluation.via24ClF =
        clKey.constitutional := by
    simp [via24FiniteKey, clBuilt]
  have parentEq :
      via24FiniteKey LocalizedCyclicPseudoRootComponentEvaluation.armF =
        parentKey.constitutional := by
    simp [via24FiniteKey, parentBuilt]
  rw [← clTable, ← parentTable, ← clEq, ← parentEq]
  exact via24_component_cl_rule1a_gt_parent

private theorem via24_actual_parent_rule1a_gt_dup :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (via24Frames.stages via24ParentSlot).a.key.constitutional.rule1a
        (via24Frames.stages via24DupSlot).a.key.constitutional.rule1a =
      Ordering.gt := by
  obtain ⟨parentKey, parentBuilt, parentTable⟩ := via24_parent_key
  obtain ⟨dupKey, dupBuilt, dupTable⟩ := via24_dup_key
  have parentEq :
      via24FiniteKey LocalizedCyclicPseudoRootComponentEvaluation.armF =
        parentKey.constitutional := by
    simp [via24FiniteKey, parentBuilt]
  have dupEq :
      via24FiniteKey LocalizedCyclicPseudoRootComponentEvaluation.via24DupF =
        dupKey.constitutional := by
    simp [via24FiniteKey, dupBuilt]
  rw [← parentTable, ← dupTable, ← parentEq, ← dupEq]
  exact via24_component_parent_rule1a_gt_dup

private theorem via24_cl_head :
    (via24Frames.stages via24ClSlot).a.key.constitutional.rule1a.head? =
      some [([], 17)] := by
  have head := slot_head via24Frames via24ClSlot
  rw [via24ClSlot_atom] at head
  simpa [spatial_z, (z_chlorine ⟨8, by decide⟩).mpr (Or.inr rfl)] using head

private theorem via24_parent_head :
    (via24Frames.stages via24ParentSlot).a.key.constitutional.rule1a.head? =
      some [([], 6)] := by
  have head := slot_head via24Frames via24ParentSlot
  rw [via24ParentSlot_atom] at head
  simpa [spatial_z, (z_carbon ⟨2, by decide⟩).mpr (Or.inr (Or.inl rfl))] using head

private theorem via24_dup_head :
    (via24Frames.stages via24DupSlot).a.key.constitutional.rule1a.head? =
      some [([], 6)] := by
  have head := slot_head via24Frames via24DupSlot
  rw [via24DupSlot_atom] at head
  simpa [spatial_z, (z_carbon ⟨0, by decide⟩).mpr (Or.inl rfl)] using head

private theorem via24_h_head :
    (via24Frames.stages via24HSlot).a.key.constitutional.rule1a.head? =
      some [([], 1)] := by
  have head := slot_head via24Frames via24HSlot
  rw [via24HSlot_atom] at head
  simpa [spatial_z, (z_hydrogen ⟨7, by decide⟩).mpr (Or.inr (Or.inr rfl))] using head

private theorem via24_actual_order :
    OfficialRuleMajorKey.compare
        (via24Frames.stages via24ClSlot).a.key.constitutional
        (via24Frames.stages via24ParentSlot).a.key.constitutional = Ordering.gt ∧
    OfficialRuleMajorKey.compare
        (via24Frames.stages via24ClSlot).a.key.constitutional
        (via24Frames.stages via24DupSlot).a.key.constitutional = Ordering.gt ∧
    OfficialRuleMajorKey.compare
        (via24Frames.stages via24ClSlot).a.key.constitutional
        (via24Frames.stages via24HSlot).a.key.constitutional = Ordering.gt ∧
    OfficialRuleMajorKey.compare
        (via24Frames.stages via24ParentSlot).a.key.constitutional
        (via24Frames.stages via24DupSlot).a.key.constitutional = Ordering.gt ∧
    OfficialRuleMajorKey.compare
        (via24Frames.stages via24ParentSlot).a.key.constitutional
        (via24Frames.stages via24HSlot).a.key.constitutional = Ordering.gt ∧
    OfficialRuleMajorKey.compare
        (via24Frames.stages via24DupSlot).a.key.constitutional
        (via24Frames.stages via24HSlot).a.key.constitutional = Ordering.gt := by
  refine ⟨compare_gt_of_heads via24_cl_head via24_parent_head (by decide),
    compare_gt_of_heads via24_cl_head via24_dup_head (by decide),
    compare_gt_of_heads via24_cl_head via24_h_head (by decide), ?_,
    compare_gt_of_heads via24_parent_head via24_h_head (by decide),
    compare_gt_of_heads via24_dup_head via24_h_head (by decide)⟩
  have decisive := via24_actual_parent_rule1a_gt_dup
  rw [OfficialRuleMajorKey.compare_eq_rule1a_of_decisive
      (by rw [decisive]; decide), decisive]

private theorem via24_retained_compare_of_rule1a
    (left right : Fin 4)
    (decisive : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (via24Frames.stages left).a.key.constitutional.rule1a
      (via24Frames.stages right).a.key.constitutional.rule1a ≠ Ordering.eq) :
    compare (via24Frames.retainedKeys left) (via24Frames.retainedKeys right) =
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (via24Frames.stages left).a.key.constitutional.rule1a
        (via24Frames.stages right).a.key.constitutional.rule1a := by
  have compoundReadback (index : Fin 4) :
      (via24Frames.compounds index).prior.rule4aKey = (via24Frames.stages index).a.key := by
    let view := contextOccurrenceView pseudoReference via24Target
    let read := fun source => pseudoSpatialCertified.localizedDependencyLabel via24Target view source
    have uniformBuilt :
        pseudoSpatialCertified.buildRuleMajorCompoundRule45KeyWith?
          (fun stage position => pseudoSpatialCertified.buildRuleMajorCumulativeWithRead?
            stage read (2 * (carrierFuel pseudoReference + 1)) position)
          (via24Frames.frame.cursorAt index) = some (via24Frames.compounds index) := by
      rw [← pseudoSpatialCertified.buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor]
      rw [← pseudoSpatialCertified.buildActualRuleMajorCompoundRule45KeyExec?_eq]
      exact via24Frames.compoundBuilt index
    exact (pseudoSpatialCertified.contextStages_compound_readback
      (via24Frames.stages index) uniformBuilt).1
  have full := via24Frames.retainedActual_fullOrdering spatial_simpleBonded left right
  have comparison := CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundThroughRule5_eq_rule1a_of_decisive
    pseudoSpatialCertified (via24Frames.compounds left) (via24Frames.compounds right) (by
      rw [compoundReadback left, compoundReadback right]
      exact decisive)
  calc
    compare (via24Frames.retainedKeys left) (via24Frames.retainedKeys right) =
        (pseudoSpatialCertified.compareLocalizedRerootCompoundThroughRule5
          (via24Frames.compounds left) (via24Frames.compounds right)).ordering := full.symm
    _ = OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (via24Frames.stages left).a.key.constitutional.rule1a
        (via24Frames.stages right).a.key.constitutional.rule1a := by
      rw [comparison, compoundReadback left, compoundReadback right]

private theorem via24_slots_pairwise_distinct :
    via24ClSlot ≠ via24ParentSlot ∧ via24ClSlot ≠ via24DupSlot ∧
    via24ClSlot ≠ via24HSlot ∧ via24ParentSlot ≠ via24DupSlot ∧
    via24ParentSlot ≠ via24HSlot ∧ via24DupSlot ≠ via24HSlot := by
  have h₁ : via24ClSlot ≠ via24ParentSlot := by
    intro equal
    have atoms := congrArg via24Frames.actualLigandAtoms equal
    rw [via24ClSlot_atom, via24ParentSlot_atom] at atoms
    have vals := congrArg Fin.val atoms
    norm_num [SA, LocalizedCyclicPseudoRootComponentEvaluation.SA] at vals
  have h₂ : via24ClSlot ≠ via24DupSlot := by
    intro equal
    have atoms := congrArg via24Frames.actualLigandAtoms equal
    rw [via24ClSlot_atom, via24DupSlot_atom] at atoms
    have vals := congrArg Fin.val atoms
    norm_num [SA, LocalizedCyclicPseudoRootComponentEvaluation.SA] at vals
  have h₃ : via24ClSlot ≠ via24HSlot := by
    intro equal
    have atoms := congrArg via24Frames.actualLigandAtoms equal
    rw [via24ClSlot_atom, via24HSlot_atom] at atoms
    have vals := congrArg Fin.val atoms
    norm_num [SA, LocalizedCyclicPseudoRootComponentEvaluation.SA] at vals
  have h₄ : via24ParentSlot ≠ via24DupSlot := by
    intro equal
    have atoms := congrArg via24Frames.actualLigandAtoms equal
    rw [via24ParentSlot_atom, via24DupSlot_atom] at atoms
    have vals := congrArg Fin.val atoms
    norm_num [SA, LocalizedCyclicPseudoRootComponentEvaluation.SA] at vals
  have h₅ : via24ParentSlot ≠ via24HSlot := by
    intro equal
    have atoms := congrArg via24Frames.actualLigandAtoms equal
    rw [via24ParentSlot_atom, via24HSlot_atom] at atoms
    have vals := congrArg Fin.val atoms
    norm_num [SA, LocalizedCyclicPseudoRootComponentEvaluation.SA] at vals
  have h₆ : via24DupSlot ≠ via24HSlot := by
    intro equal
    have atoms := congrArg via24Frames.actualLigandAtoms equal
    rw [via24DupSlot_atom, via24HSlot_atom] at atoms
    have vals := congrArg Fin.val atoms
    norm_num [SA, LocalizedCyclicPseudoRootComponentEvaluation.SA] at vals
  exact ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩

private theorem via24_sparse_strict_pairs :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (via24Frames.stages via24ClSlot).a.key.constitutional.rule1a
        (via24Frames.stages via24ParentSlot).a.key.constitutional.rule1a = Ordering.gt ∧
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (via24Frames.stages via24ClSlot).a.key.constitutional.rule1a
        (via24Frames.stages via24DupSlot).a.key.constitutional.rule1a = Ordering.gt ∧
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (via24Frames.stages via24ClSlot).a.key.constitutional.rule1a
        (via24Frames.stages via24HSlot).a.key.constitutional.rule1a = Ordering.gt ∧
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (via24Frames.stages via24ParentSlot).a.key.constitutional.rule1a
        (via24Frames.stages via24DupSlot).a.key.constitutional.rule1a = Ordering.gt ∧
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (via24Frames.stages via24ParentSlot).a.key.constitutional.rule1a
        (via24Frames.stages via24HSlot).a.key.constitutional.rule1a = Ordering.gt ∧
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (via24Frames.stages via24DupSlot).a.key.constitutional.rule1a
        (via24Frames.stages via24HSlot).a.key.constitutional.rule1a = Ordering.gt := by
  refine ⟨officialRuleMajorKey_compare_rule1a_gt_of_heads_gt via24_cl_head via24_parent_head (by decide),
    officialRuleMajorKey_compare_rule1a_gt_of_heads_gt via24_cl_head via24_dup_head (by decide),
    officialRuleMajorKey_compare_rule1a_gt_of_heads_gt via24_cl_head via24_h_head (by decide),
    via24_actual_parent_rule1a_gt_dup,
    officialRuleMajorKey_compare_rule1a_gt_of_heads_gt via24_parent_head via24_h_head (by decide),
    officialRuleMajorKey_compare_rule1a_gt_of_heads_gt via24_dup_head via24_h_head (by decide)⟩

private theorem via24_retained_lt
    (higher lower : Fin 4)
    (sparse : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (via24Frames.stages higher).a.key.constitutional.rule1a
      (via24Frames.stages lower).a.key.constitutional.rule1a = Ordering.gt) :
    via24Frames.retainedKeys lower < via24Frames.retainedKeys higher := by
  have decisive : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (via24Frames.stages higher).a.key.constitutional.rule1a
      (via24Frames.stages lower).a.key.constitutional.rule1a ≠ Ordering.eq := by
    rw [sparse]
    decide
  have comparison := via24_retained_compare_of_rule1a higher lower decisive
  rw [sparse] at comparison
  exact (completeLigandRule5Key_compare_gt_iff
    (via24Frames.retainedKeys higher) (via24Frames.retainedKeys lower)).mp comparison

private theorem via24_retained_order :
    [via24ClSlot, via24ParentSlot, via24DupSlot, via24HSlot].Pairwise
      (fun left right => via24Frames.retainedKeys right < via24Frames.retainedKeys left) := by
  rcases via24_sparse_strict_pairs with ⟨clParent, clDup, clH, parentDup, parentH, dupH⟩
  apply List.Pairwise.cons
  · intro slot member
    simp only [List.mem_cons] at member
    rcases member with equal | equal | equal | empty
    · subst slot
      exact via24_retained_lt via24ClSlot via24ParentSlot clParent
    · subst slot
      exact via24_retained_lt via24ClSlot via24DupSlot clDup
    · subst slot
      exact via24_retained_lt via24ClSlot via24HSlot clH
    · simp at empty
  · apply List.Pairwise.cons
    · intro slot member
      simp only [List.mem_cons] at member
      rcases member with equal | equal | empty
      · subst slot
        exact via24_retained_lt via24ParentSlot via24DupSlot parentDup
      · subst slot
        exact via24_retained_lt via24ParentSlot via24HSlot parentH
      · simp at empty
    · apply List.Pairwise.cons
      · intro slot member
        simp only [List.mem_cons] at member
        rcases member with equal | empty
        · subst slot
          exact via24_retained_lt via24DupSlot via24HSlot dupH
        · simp at empty
      · apply List.Pairwise.cons
        · intro slot member
          simp at member
        · exact List.Pairwise.nil

private theorem via24_order_perm :
    [via24ClSlot, via24ParentSlot, via24DupSlot, via24HSlot].Perm (List.finRange 4) := by
  rcases via24_slots_pairwise_distinct with ⟨hab, hac, had, hbc, hbd, hcd⟩
  exact fin4_four_distinct_perm hab hac had hbc hbd hcd

private theorem via24_retained_prior_compare_of_rule1a
    (left right : Fin 4)
    (decisive : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (via24Frames.stages left).a.key.constitutional.rule1a
      (via24Frames.stages right).a.key.constitutional.rule1a ≠ Ordering.eq) :
    compare (ofLex (via24Frames.retainedKeys left)).1
        (ofLex (via24Frames.retainedKeys right)).1 =
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (via24Frames.stages left).a.key.constitutional.rule1a
        (via24Frames.stages right).a.key.constitutional.rule1a := by
  have compoundReadback (index : Fin 4) :
      (via24Frames.compounds index).prior.rule4aKey = (via24Frames.stages index).a.key := by
    let view := contextOccurrenceView pseudoReference via24Target
    let read := fun source => pseudoSpatialCertified.localizedDependencyLabel via24Target view source
    have uniformBuilt :
        pseudoSpatialCertified.buildRuleMajorCompoundRule45KeyWith?
          (fun stage position => pseudoSpatialCertified.buildRuleMajorCumulativeWithRead?
            stage read (2 * (carrierFuel pseudoReference + 1)) position)
          (via24Frames.frame.cursorAt index) = some (via24Frames.compounds index) := by
      rw [← pseudoSpatialCertified.buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor]
      rw [← pseudoSpatialCertified.buildActualRuleMajorCompoundRule45KeyExec?_eq]
      exact via24Frames.compoundBuilt index
    exact (pseudoSpatialCertified.contextStages_compound_readback
      (via24Frames.stages index) uniformBuilt).1
  have priorAgreement := via24Frames.retainedActual_priorComparison spatial_simpleBonded left right
  have constEq := OfficialRuleMajorKey.compare_eq_rule1a_of_decisive
    (left := (via24Frames.compounds left).prior.rule4aKey.constitutional)
    (right := (via24Frames.compounds right).prior.rule4aKey.constitutional) (by
      rw [compoundReadback left, compoundReadback right]
      exact decisive)
  have constNe : OfficialRuleMajorKey.compare
      (via24Frames.compounds left).prior.rule4aKey.constitutional
      (via24Frames.compounds right).prior.rule4aKey.constitutional ≠ Ordering.eq := by
    rw [constEq, compoundReadback left, compoundReadback right]
    exact decisive
  have cumulativeEq : pseudoSpatialCertified.compareLocalizedRerootCumulativeRule45Keys
      (via24Frames.compounds left).prior.rule4aKey
      (via24Frames.compounds right).prior.rule4aKey =
      OfficialRuleMajorKey.compare
        (via24Frames.compounds left).prior.rule4aKey.constitutional
        (via24Frames.compounds right).prior.rule4aKey.constitutional := by
    unfold CertifiedLocalizedCIPInput.compareLocalizedRerootCumulativeRule45Keys
    refine ConstitutionalLexAlgebra.compareLex_eq_left_of_left_ne_eq _ _ _ _ ?_
    simpa [Ordering.byKey] using constNe
  have cumulativeNe : pseudoSpatialCertified.compareLocalizedRerootCumulativeRule45Keys
      (via24Frames.compounds left).prior.rule4aKey
      (via24Frames.compounds right).prior.rule4aKey ≠ Ordering.eq := by
    rw [cumulativeEq]
    exact constNe
  have compoundComparison :=
    CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundRule4bcKeys_eq_rule4a_of_ne
      pseudoSpatialCertified (via24Frames.compounds left).prior
      (via24Frames.compounds right).prior cumulativeNe
  calc
    compare (ofLex (via24Frames.retainedKeys left)).1
        (ofLex (via24Frames.retainedKeys right)).1 =
      pseudoSpatialCertified.compareLocalizedRerootCompoundRule4bcKeys
        (via24Frames.compounds left).prior (via24Frames.compounds right).prior :=
      priorAgreement.symm
    _ = pseudoSpatialCertified.compareLocalizedRerootCumulativeRule45Keys
        (via24Frames.compounds left).prior.rule4aKey
        (via24Frames.compounds right).prior.rule4aKey := compoundComparison
    _ = OfficialRuleMajorKey.compare
        (via24Frames.compounds left).prior.rule4aKey.constitutional
        (via24Frames.compounds right).prior.rule4aKey.constitutional := cumulativeEq
    _ = OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (via24Frames.stages left).a.key.constitutional.rule1a
        (via24Frames.stages right).a.key.constitutional.rule1a := by
      rw [OfficialRuleMajorKey.compare_eq_rule1a_of_decisive (by
        rw [compoundReadback left, compoundReadback right]
        exact decisive), compoundReadback left, compoundReadback right]

private theorem via24_retained_prior_lt
    (higher lower : Fin 4)
    (sparse : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (via24Frames.stages higher).a.key.constitutional.rule1a
      (via24Frames.stages lower).a.key.constitutional.rule1a = Ordering.gt) :
    (ofLex (via24Frames.retainedKeys lower)).1 <
      (ofLex (via24Frames.retainedKeys higher)).1 := by
  have decisive : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (via24Frames.stages higher).a.key.constitutional.rule1a
      (via24Frames.stages lower).a.key.constitutional.rule1a ≠ Ordering.eq := by
    rw [sparse]
    decide
  have comparison := via24_retained_prior_compare_of_rule1a higher lower decisive
  rw [sparse] at comparison
  exact (completeLigandPriorKey_compare_gt_iff
    (ofLex (via24Frames.retainedKeys higher)).1
    (ofLex (via24Frames.retainedKeys lower)).1).mp comparison

private theorem via24_retained_prior_order :
    [via24ClSlot, via24ParentSlot, via24DupSlot, via24HSlot].Pairwise
      (fun left right => (ofLex (via24Frames.retainedKeys right)).1 <
        (ofLex (via24Frames.retainedKeys left)).1) := by
  rcases via24_sparse_strict_pairs with ⟨clParent, clDup, clH, parentDup, parentH, dupH⟩
  apply List.Pairwise.cons
  · intro slot member
    simp only [List.mem_cons] at member
    rcases member with equal | equal | equal | empty
    · subst slot
      exact via24_retained_prior_lt via24ClSlot via24ParentSlot clParent
    · subst slot
      exact via24_retained_prior_lt via24ClSlot via24DupSlot clDup
    · subst slot
      exact via24_retained_prior_lt via24ClSlot via24HSlot clH
    · simp at empty
  · apply List.Pairwise.cons
    · intro slot member
      simp only [List.mem_cons] at member
      rcases member with equal | equal | empty
      · subst slot
        exact via24_retained_prior_lt via24ParentSlot via24DupSlot parentDup
      · subst slot
        exact via24_retained_prior_lt via24ParentSlot via24HSlot parentH
      · simp at empty
    · apply List.Pairwise.cons
      · intro slot member
        simp only [List.mem_cons] at member
        rcases member with equal | empty
        · subst slot
          exact via24_retained_prior_lt via24DupSlot via24HSlot dupH
        · simp at empty
      · apply List.Pairwise.cons
        · intro slot member
          simp at member
        · exact List.Pairwise.nil

private theorem via24_retainedPrior_pairwise_injective
    {α : Type} [LinearOrder α] {xs : List (Fin 4)} {key : Fin 4 → α}
    (perm : xs.Perm (List.finRange 4))
    (sorted : xs.Pairwise (fun i j => key j < key i)) :
    Function.Injective key := by
  intro i j equal
  by_contra different
  have hi : i ∈ xs := perm.mem_iff.mpr (List.mem_finRange i)
  have hj : j ∈ xs := perm.mem_iff.mpr (List.mem_finRange j)
  have either := (List.Pairwise.forall (fun _ _ h => h.symm)
    (sorted.imp fun h => Or.inr h)) hi hj different
  rw [equal] at either
  exact either.elim (lt_irrefl _) (lt_irrefl _)

private theorem via24_prior_injective :
    Function.Injective (fun slot => (ofLex (via24Frames.retainedKeys slot)).1) :=
  via24_retainedPrior_pairwise_injective via24_order_perm via24_retained_prior_order

private theorem via24_not_prior_pair (left right : Fin 4) (different : left ≠ right) :
    ¬ CompletePriorPair via24Frames.retainedKeys left right := by
  intro pair
  exact different (via24_prior_injective pair.2)

private theorem via24_completeRule5PairCount_zero :
    completeRule5PairCount via24Frames.retainedKeys = 0 := by
  have h01 : ¬ CompletePriorPair via24Frames.retainedKeys 0 1 :=
    via24_not_prior_pair 0 1 (by decide)
  have h02 : ¬ CompletePriorPair via24Frames.retainedKeys 0 2 :=
    via24_not_prior_pair 0 2 (by decide)
  have h12 : ¬ CompletePriorPair via24Frames.retainedKeys 1 2 :=
    via24_not_prior_pair 1 2 (by decide)
  have h03 : ¬ CompletePriorPair via24Frames.retainedKeys 0 3 :=
    via24_not_prior_pair 0 3 (by decide)
  have h13 : ¬ CompletePriorPair via24Frames.retainedKeys 1 3 :=
    via24_not_prior_pair 1 3 (by decide)
  have h23 : ¬ CompletePriorPair via24Frames.retainedKeys 2 3 :=
    via24_not_prior_pair 2 3 (by decide)
  rw [completeRule5PairCount, sourceEnantiomorphicPairCount_eq_filter_length]
  simp [sourceUnorderedPairList, h01, h02, h12, h03, h13, h23]

private noncomputable def via24Points (slot : Fin 4) : CartesianPoint3 :=
  Classical.choose (spatialPoint_exists (via24Frames.actualLigandAtoms slot))

private theorem via24Points_read (slot : Fin 4) :
    pseudoSpatialCertified.spatialPointAt? (via24Frames.actualLigandAtoms slot) =
      some (via24Points slot) :=
  Classical.choose_spec (spatialPoint_exists (via24Frames.actualLigandAtoms slot))

private theorem via24_point_values :
    via24Points via24ClSlot = P8 ∧ via24Points via24ParentSlot = P2 ∧
    via24Points via24DupSlot = P0 ∧ via24Points via24HSlot = P7 := by
  rcases LocalizedCyclicPseudoGeneratedLabels.spatial_readback with
    ⟨h0, _, h2, _, _, _, _, h7, h8⟩
  constructor
  · apply Option.some.inj
    exact (via24Points_read via24ClSlot).symm.trans (by rw [via24ClSlot_atom]; exact h8)
  constructor
  · apply Option.some.inj
    exact (via24Points_read via24ParentSlot).symm.trans (by rw [via24ParentSlot_atom]; exact h2)
  constructor
  · apply Option.some.inj
    exact (via24Points_read via24DupSlot).symm.trans (by rw [via24DupSlot_atom]; exact h0)
  · apply Option.some.inj
    exact (via24Points_read via24HSlot).symm.trans (by rw [via24HSlot_atom]; exact h7)

private theorem via24_order_points :
    [via24ClSlot, via24ParentSlot, via24DupSlot, via24HSlot].map via24Points =
      [P8, P2, P0, P7] := by
  rcases via24_point_values with ⟨h8, h2, h0, h7⟩
  simp [h8, h2, h0, h7]

private theorem via24_geometric_judgment :
    RetainedContextualDescriptorJudgmentAt pseudoSpatialCertified.moleculeGraph
      (descriptorMap pseudoReference) via24Unit via24Frames.actualArmGraphs
      via24Frames.W via24Frames.D via24Frames.actualCoordinates (.chiral RS.S) := by
  let points := via24Points
  refine ⟨points, ?_, ?_⟩
  · intro slot
    change pseudoSpatialCertified.spatialPointAt?
        (via24Frames.actualLigandAtoms slot) = some (points slot)
    exact via24Points_read slot
  · refine ⟨[via24ClSlot, via24ParentSlot, via24DupSlot, via24HSlot], RS.S,
      via24_order_perm, via24_retained_order, ?_, ?_⟩
    · change RationalTetrahedralDescriptor
        ([via24ClSlot, via24ParentSlot, via24DupSlot, via24HSlot].map via24Points) RS.S
      rw [via24_order_points]
      have sign : CartesianPoint3.orientedVolume P8 P2 P0 P7 > 0 :=
        (descriptorOfOrientedVolume?_eq_some_S_iff _).mp closing_descriptor.2
      exact ⟨P8, P2, P0, P7, rfl, sign⟩
    · change (LocalizedTetrahedralRSPseudoDescriptor.chiral RS.S) =
        classifyTetrahedralRSPseudo RS.S
          (completeRule5PairCount via24Frames.retainedKeys)
      rw [via24_completeRule5PairCount_zero]
      simp

private theorem via24_referenceState_S :
    referenceState pseudoReference via24Target = some (.chiral RS.S) :=
  (via24Frames.referenceState_some_iff_retainedJudgment spatial_simpleBonded (.chiral RS.S)).2
    via24_geometric_judgment

private noncomputable def shallowClosingPoints (slot : Fin 4) : CartesianPoint3 :=
  Classical.choose (spatialPoint_exists (directClosingFrames.actualLigandAtoms slot))

private theorem shallowClosingPoints_read (slot : Fin 4) :
    pseudoSpatialCertified.spatialPointAt? (directClosingFrames.actualLigandAtoms slot) =
      some (shallowClosingPoints slot) :=
  Classical.choose_spec (spatialPoint_exists (directClosingFrames.actualLigandAtoms slot))

private theorem shallowClosing_point_values :
    shallowClosingPoints shallowClosingClSlot = P8 ∧
    shallowClosingPoints shallowClosingCarbonSlot = P2 ∧
    shallowClosingPoints shallowClosingRootSlot = P0 ∧
    shallowClosingPoints shallowClosingHSlot = P7 := by
  rcases LocalizedCyclicPseudoGeneratedLabels.spatial_readback with
    ⟨h0, _, h2, _, _, _, _, h7, h8⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply Option.some.inj
    exact (shallowClosingPoints_read shallowClosingClSlot).symm.trans
      (by rw [shallowClosingClSlot_atom]; exact h8)
  · apply Option.some.inj
    exact (shallowClosingPoints_read shallowClosingCarbonSlot).symm.trans
      (by rw [shallowClosingCarbonSlot_atom]; exact h2)
  · apply Option.some.inj
    exact (shallowClosingPoints_read shallowClosingRootSlot).symm.trans
      (by rw [shallowClosingRootSlot_atom]; exact h0)
  · apply Option.some.inj
    exact (shallowClosingPoints_read shallowClosingHSlot).symm.trans
      (by rw [shallowClosingHSlot_atom]; exact h7)

private theorem shallowClosing_order_points :
    [shallowClosingClSlot, shallowClosingCarbonSlot, shallowClosingRootSlot,
      shallowClosingHSlot].map shallowClosingPoints = [P8, P2, P0, P7] := by
  rcases shallowClosing_point_values with ⟨h8,h2,h0,h7⟩
  simp [h8,h2,h0,h7]

private theorem shallowClosing_geometric_judgment :
    RetainedContextualDescriptorJudgmentAt pseudoSpatialCertified.moleculeGraph
      (descriptorMap pseudoReference) directClosingUnit directClosingFrames.actualArmGraphs
      directClosingFrames.W directClosingFrames.D directClosingFrames.actualCoordinates (.chiral RS.S) := by
  let points := shallowClosingPoints
  refine ⟨points, ?_, ?_⟩
  · intro slot
    change pseudoSpatialCertified.spatialPointAt?
      (directClosingFrames.actualLigandAtoms slot) = some (points slot)
    exact shallowClosingPoints_read slot
  · refine ⟨[shallowClosingClSlot, shallowClosingCarbonSlot, shallowClosingRootSlot,
      shallowClosingHSlot], RS.S, shallowClosing_order_perm,
      shallowClosing_retained_order, ?_, ?_⟩
    · change RationalTetrahedralDescriptor
        ([shallowClosingClSlot, shallowClosingCarbonSlot, shallowClosingRootSlot,
          shallowClosingHSlot].map shallowClosingPoints) RS.S
      rw [shallowClosing_order_points]
      have sign : CartesianPoint3.orientedVolume P8 P2 P0 P7 > 0 :=
        (descriptorOfOrientedVolume?_eq_some_S_iff _).mp closing_descriptor.2
      exact ⟨P8, P2, P0, P7, rfl, sign⟩
    · change LocalizedTetrahedralRSPseudoDescriptor.chiral RS.S =
        classifyTetrahedralRSPseudo RS.S
          (completeRule5PairCount directClosingFrames.retainedKeys)
      rw [shallowClosing_completeRule5PairCount_zero]
      simp

private theorem shallowClosing_referenceState_S :
    referenceState pseudoReference directClosingTarget = some (.chiral RS.S) :=
  (directClosingFrames.referenceState_some_iff_retainedJudgment spatial_simpleBonded (.chiral RS.S)).2
    shallowClosing_geometric_judgment

/-- The four actual root-component auxiliary occurrences derive their own reference labels. -/
theorem auxiliary_actual_referenceStates :
    referenceState pseudoReference directArmTarget = some (.chiral RS.R) ∧
    referenceState pseudoReference directClosingTarget = some (.chiral RS.S) ∧
    referenceState pseudoReference via42Target = some (.chiral RS.R) ∧
    referenceState pseudoReference via24Target = some (.chiral RS.S) :=
  ⟨shallowArm_referenceState_R, shallowClosing_referenceState_S,
    via42_referenceState_R, via24_referenceState_S⟩

/-- The generated map reads back exactly the four real occurrence states at their actual units. -/
theorem auxiliary_generatedMap_readback :
    (descriptorMap pseudoReference directArmUnit).bind Descriptor.toLocalizedLabel =
        referenceState pseudoReference directArmTarget ∧
    (descriptorMap pseudoReference directClosingUnit).bind Descriptor.toLocalizedLabel =
        referenceState pseudoReference directClosingTarget ∧
    (descriptorMap pseudoReference via42Unit).bind Descriptor.toLocalizedLabel =
        referenceState pseudoReference via42Target ∧
    (descriptorMap pseudoReference via24Unit).bind Descriptor.toLocalizedLabel =
        referenceState pseudoReference via24Target := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact descriptorMap_readback_of_simpleBonded pseudoReference spatial_simpleBonded
      directArmUnit directArmTarget directArm_unitEq
  · exact descriptorMap_readback_of_simpleBonded pseudoReference spatial_simpleBonded
      directClosingUnit directClosingTarget directClosing_unitEq
  · exact descriptorMap_readback_of_simpleBonded pseudoReference spatial_simpleBonded
      via42Unit via42Target via42_unit_target
  · exact descriptorMap_readback_of_simpleBonded pseudoReference spatial_simpleBonded
      via24Unit via24Target via24_unit_target

private def rootAuxUnits : List (OccurrenceUnit pseudoSpatialCertified.Atom) :=
  [⟨LocalizedCyclicPseudoRootComponentEvaluation.SA 0,
      [LocalizedCyclicPseudoRootComponentEvaluation.SA 2]⟩,
    ⟨LocalizedCyclicPseudoRootComponentEvaluation.SA 0,
      [LocalizedCyclicPseudoRootComponentEvaluation.SA 4]⟩,
    ⟨LocalizedCyclicPseudoRootComponentEvaluation.SA 0,
      [LocalizedCyclicPseudoRootComponentEvaluation.SA 2,
        LocalizedCyclicPseudoRootComponentEvaluation.SA 4]⟩,
    ⟨LocalizedCyclicPseudoRootComponentEvaluation.SA 0,
      [LocalizedCyclicPseudoRootComponentEvaluation.SA 4,
        LocalizedCyclicPseudoRootComponentEvaluation.SA 2]⟩]

private def rootComponentMapT
    (unit : OccurrenceUnit pseudoSpatialCertified.Atom) : Option Descriptor :=
  if unit = directArmUnit then some .R
  else if unit = directClosingUnit then some .S
  else if unit = via24Unit then some .S
  else if unit = via42Unit then some .R
  else none

private def rootComponentReadFrame (frame :
    LocalizedCyclicPseudoRootComponentEvaluation.Frame) : Option LocalizedAuxiliaryLabel :=
  if frame.root = LocalizedCyclicPseudoRootComponentEvaluation.SA 0 ∧
      0 < frame.address.length then
    if frame.node.provenance = .realAtom then
      if IsDetectedCenter pseudoSpatialCertified.moleculeGraph
          (pseudoSpatialCertified.molecularFrameUnit frame).atom then
        (rootComponentMapT (pseudoSpatialCertified.molecularFrameUnit frame)).bind
          Descriptor.toLocalizedLabel
      else none
    else none
  else none

private def rootComponentReadT
    (cursor : LocalizedCyclicPseudoRootComponentEvaluation.Cursor) :
      Option LocalizedAuxiliaryLabel := rootComponentReadFrame cursor.occurrence.1

/-- Every strict-depth real detected center in the finite root-zero component is one of the
four auxiliary molecular units whose actual labels were proved above. -/
private theorem rootComponent_subtree_centers :
    ∀ frame ∈ LocalizedCyclicPseudoRootComponentEvaluation.subtree0,
      0 < frame.address.length → frame.node.provenance = .realAtom →
        IsDetectedCenter pseudoSpatialCertified.moleculeGraph
          (pseudoSpatialCertified.molecularFrameUnit frame).atom →
          pseudoSpatialCertified.molecularFrameUnit frame ∈ rootAuxUnits := by
  decide +kernel

private theorem rootComponent_map_eq_mapT (unit : OccurrenceUnit pseudoSpatialCertified.Atom)
    (member : unit ∈ rootAuxUnits)
    (detected : IsDetectedCenter pseudoSpatialCertified.moleculeGraph unit.atom) :
    (descriptorMap pseudoReference
      (⟨unit, detected⟩ : DetectedOccurrence pseudoReference.certified.moleculeGraph)).bind
        Descriptor.toLocalizedLabel =
      (rootComponentMapT unit).bind Descriptor.toLocalizedLabel := by
  have reads := auxiliary_generatedMap_readback
  simp only [rootAuxUnits, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with arm | closing | via24 | via42
  · subst unit
    have unitEq : (⟨⟨LocalizedCyclicPseudoRootComponentEvaluation.SA 0,
        [LocalizedCyclicPseudoRootComponentEvaluation.SA 2]⟩, detected⟩ :
        DetectedOccurrence pseudoReference.certified.moleculeGraph) = directArmUnit := by
      apply Subtype.ext
      simp [directArmUnit, rootTetra, armTetra, SA,
        LocalizedCyclicPseudoRootComponentEvaluation.SA]
    rw [unitEq]
    have labels := auxiliary_actual_referenceStates
    simp only [rootComponentMapT, Descriptor.toLocalizedLabel]
    exact reads.1.trans labels.1
  · subst unit
    have unitEq : (⟨⟨LocalizedCyclicPseudoRootComponentEvaluation.SA 0,
        [LocalizedCyclicPseudoRootComponentEvaluation.SA 4]⟩, detected⟩ :
        DetectedOccurrence pseudoReference.certified.moleculeGraph) = directClosingUnit := by
      apply Subtype.ext
      simp [directClosingUnit, rootTetra, closingTetra, SA,
        LocalizedCyclicPseudoRootComponentEvaluation.SA]
    rw [unitEq]
    have labels := auxiliary_actual_referenceStates
    simp only [rootComponentMapT, Descriptor.toLocalizedLabel]
    exact reads.2.1.trans labels.2.1
  · subst unit
    have unitEq : (⟨⟨LocalizedCyclicPseudoRootComponentEvaluation.SA 0,
        [LocalizedCyclicPseudoRootComponentEvaluation.SA 2,
          LocalizedCyclicPseudoRootComponentEvaluation.SA 4]⟩, detected⟩ :
        DetectedOccurrence pseudoReference.certified.moleculeGraph) = via24Unit := by
      apply Subtype.ext
      exact via24_unit_eq.symm.trans via24_unit_target
    rw [unitEq]
    have labels := auxiliary_actual_referenceStates
    rw [reads.2.2.2, labels.2.2.2]
    simp [rootComponentMapT, directArmUnit, directClosingUnit, via24Unit,
      via24_unit_eq, via42Unit, via42_unit_eq, Descriptor.toLocalizedLabel,
      LocalizedCyclicPseudoRootComponentEvaluation.SA]
    all_goals decide
  · subst unit
    have unitEq : (⟨⟨LocalizedCyclicPseudoRootComponentEvaluation.SA 0,
        [LocalizedCyclicPseudoRootComponentEvaluation.SA 4,
          LocalizedCyclicPseudoRootComponentEvaluation.SA 2]⟩, detected⟩ :
        DetectedOccurrence pseudoReference.certified.moleculeGraph) = via42Unit := by
      apply Subtype.ext
      exact via42_unit_eq.symm.trans via42_unit_target
    rw [unitEq]
    have labels := auxiliary_actual_referenceStates
    rw [reads.2.2.1, labels.2.2.1]
    simp [rootComponentMapT, directArmUnit, directClosingUnit, via24Unit,
      via24_unit_eq, via42Unit, via42_unit_eq, Descriptor.toLocalizedLabel,
      LocalizedCyclicPseudoRootComponentEvaluation.SA]
    all_goals decide

private def rootComponentReadFrameActual (frame :
    LocalizedCyclicPseudoRootComponentEvaluation.Frame)
    : Option LocalizedAuxiliaryLabel :=
  if frame.root = LocalizedCyclicPseudoRootComponentEvaluation.SA 0 ∧
        0 < frame.address.length then
    if frame.node.provenance = .realAtom then
      if detected : IsDetectedCenter pseudoSpatialCertified.moleculeGraph
          (pseudoSpatialCertified.molecularFrameUnit frame).atom then
        (descriptorMap pseudoReference
          (⟨pseudoSpatialCertified.molecularFrameUnit frame, detected⟩ :
            DetectedOccurrence pseudoReference.certified.moleculeGraph)).bind
            Descriptor.toLocalizedLabel
      else none
    else none
  else none

private theorem rootComponentRead_eq_actualFrame (frame :
    LocalizedCyclicPseudoRootComponentEvaluation.Frame)
    (member : frame ∈ LocalizedCyclicPseudoRootComponentEvaluation.subtree0) :
    rootComponentReadFrameActual frame = rootComponentReadFrame frame := by
  unfold rootComponentReadFrameActual rootComponentReadFrame
  by_cases rootPositive : frame.root = LocalizedCyclicPseudoRootComponentEvaluation.SA 0 ∧
      0 < frame.address.length
  · by_cases real : frame.node.provenance = OfficialCIPNodeProvenance.realAtom
    · by_cases detected : IsDetectedCenter pseudoSpatialCertified.moleculeGraph
          (pseudoSpatialCertified.molecularFrameUnit frame).atom
      · simp only [if_pos rootPositive, if_pos real, dif_pos detected, if_pos detected]
        exact rootComponent_map_eq_mapT _
          (rootComponent_subtree_centers frame member rootPositive.2 real detected) detected
      · simp [rootPositive, real, detected]
    · simp [rootPositive, real]
  · simp [rootPositive]

private theorem rootComponentRead_eq_context (cursor :
    LocalizedCyclicPseudoRootComponentEvaluation.Cursor)
    (rootEq : cursor.occurrence.1.root = LocalizedCyclicPseudoRootComponentEvaluation.SA 0) :
    contextOccurrenceRead pseudoReference rootTarget cursor =
      rootComponentReadT cursor := by
  have generatedEq := congrFun
    (molecularReader_eq_generatedReader_of_simpleBonded pseudoReference
      spatial_simpleBonded rootTarget) cursor
  have member := LocalizedCyclicPseudoRootComponentEvaluation.mem_subtree0_of_mem_carrier
    cursor.occurrence.2 rootEq
  calc
    contextOccurrenceRead pseudoReference rootTarget cursor =
        pseudoReference.certified.molecularReader (descriptorMap pseudoReference) rootTarget cursor :=
          generatedEq.symm
    _ = rootComponentReadFrameActual cursor.occurrence.1 := by
      show pseudoReference.certified.molecularReader (descriptorMap pseudoReference)
        rootTarget cursor = rootComponentReadFrameActual cursor.occurrence.1
      unfold CertifiedLocalizedCIPInput.molecularReader
        CertifiedLocalizedCIPInput.localizedDependencyLabel rootComponentReadFrameActual
      have hdep : pseudoReference.certified.LocalizedDepthDependency cursor.occurrence
          rootTarget ↔
            (cursor.occurrence.1.root = LocalizedCyclicPseudoRootComponentEvaluation.SA 0 ∧
              0 < cursor.occurrence.1.address.length) := by
        unfold CertifiedLocalizedCIPInput.LocalizedDepthDependency
        rw [root_address]
        have rootEq' : rootTarget.1.root =
            LocalizedCyclicPseudoRootComponentEvaluation.SA 0 := by
          change SA 0 = LocalizedCyclicPseudoRootComponentEvaluation.SA 0
          rfl
        rw [rootEq']
        exact Iff.rfl
      by_cases h : cursor.occurrence.1.root =
          LocalizedCyclicPseudoRootComponentEvaluation.SA 0 ∧
            0 < cursor.occurrence.1.address.length
      · rw [dif_pos (hdep.mpr h), if_pos h]
        rfl
      · rw [dif_neg (fun d => h (hdep.mp d)), if_neg h]
    _ = rootComponentReadFrame cursor.occurrence.1 :=
      rootComponentRead_eq_actualFrame cursor.occurrence.1 member
    _ = rootComponentReadT cursor := rfl

/-- At the root, the generated descriptor map supplies the fixed-point reader values. -/
theorem root_generatedView_readback :
    pseudoSpatialCertified.molecularView (descriptorMap pseudoReference) rootTarget =
      pseudoSpatialCertified.localizedDependencyView
        (referenceState pseudoReference) rootTarget :=
  molecularView_eq_generatedView_of_simpleBonded pseudoReference spatial_simpleBonded rootTarget

/-- Transfer a successful current production cumulative stage to the finite root-component
evaluator, retaining the actual generated-map reader at every cursor in the root-zero tree. -/
private theorem actualRuleMajorStage_eq_rootComponent
    (stage : LocalizedCumulativeRule45Stage)
    (cursor : pseudoSpatialCertified.LocalizedRerootCursor (carrierFuel pseudoReference))
    (arm : pseudoSpatialCertified.RuleMajorContextArm (carrierFuel pseudoReference)
      stage (contextOccurrenceRead pseudoReference rootTarget) cursor)
    (rootZero : cursor.occurrence.1.root =
      LocalizedCyclicPseudoRootComponentEvaluation.SA 0) :
    LocalizedCyclicPseudoRootComponentEvaluation.buildRuleMajorF stage
      rootComponentReadFrame LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
      cursor.occurrence.1 (cursor.previous?.map Subtype.val) = some arm.key := by
  have evalEq : LocalizedCyclicPseudoRootComponentEvaluation.evalFuel =
      2 * (carrierFuel pseudoReference + 1) := by
    norm_num [LocalizedCyclicPseudoRootComponentEvaluation.evalFuel,
      LocalizedCyclicPseudoRootComponentEvaluation.fuel_eq, carrierFuel_eq,
      CertifiedLocalizedCIPInput.evaluationFuel, localizedOccurrenceRerootEvaluationFuel,
      spatial_atomCount]
  have same := LocalizedCyclicPseudoRootComponentEvaluation.buildRuleMajorF_eq_actual
    stage rootComponentReadFrame (contextOccurrenceRead pseudoReference rootTarget)
    (fun c hc => rootComponentRead_eq_context c hc)
    (fuel := LocalizedCyclicPseudoRootComponentEvaluation.evalFuel) cursor rootZero
  have built := arm.built
  rw [← evalEq] at built
  exact same.symm.trans built

private theorem root_slot_current (slot : Fin 4) (index : Fin 9)
    (atomEq : rootFrames.actualLigandAtoms slot = SA index) :
    (rootFrames.frame.cursorAt slot).occurrence.1.node.current? = some (SA index) := by
  have current := rootFrames.ligandAt slot
  unfold pseudoReference at current
  have defined : rootFrames.actualLigandAtoms slot =
      pseudoSpatialCertified.detectedMultiCenterMolecule.ligandAtomAt rootFrames.center
        (rootFrames.detectedLigandPermutation slot) := by
    unfold pseudoReference
    rfl
  rw [← defined, atomEq] at current
  exact current

private theorem root_arm_cursor_eq :
    (rootFrames.frame.cursorAt rootArmSlot).occurrence.1 =
      LocalizedCyclicPseudoRootComponentEvaluation.armF := by
  apply root_cursor_eq_component rootArmSlot _ _ (by decide)
  rw [root_slot_current rootArmSlot ⟨2, by decide⟩ rootArmSlot_atom]
  simp [LocalizedCyclicPseudoRootComponentEvaluation.armF,
    LocalizedCyclicPseudoRootComponentEvaluation.node2,
    LocalizedCyclicPseudoRootComponentEvaluation.rootNode,
    LocalizedCyclicPseudoRootComponentEvaluation.SA, SA]

private theorem root_closing_cursor_eq :
    (rootFrames.frame.cursorAt rootClosingSlot).occurrence.1 =
      LocalizedCyclicPseudoRootComponentEvaluation.closeF := by
  apply root_cursor_eq_component rootClosingSlot _ _ (by decide)
  rw [root_slot_current rootClosingSlot ⟨4, by decide⟩ rootClosingSlot_atom]
  simp [LocalizedCyclicPseudoRootComponentEvaluation.closeF,
    LocalizedCyclicPseudoRootComponentEvaluation.node4,
    LocalizedCyclicPseudoRootComponentEvaluation.rootNode,
    LocalizedCyclicPseudoRootComponentEvaluation.SA, SA]


theorem root_fluorine_cursor_eq :
    (rootFrames.frame.cursorAt rootFluorineSlot).occurrence.1 =
      LocalizedCyclicPseudoRootComponentEvaluation.rootFluorineF := by
  apply root_cursor_eq_component rootFluorineSlot _ _ (by decide)
  rw [root_slot_current rootFluorineSlot ⟨1, by decide⟩ rootFluorineSlot_atom]
  simp [LocalizedCyclicPseudoRootComponentEvaluation.rootFluorineF,
    LocalizedCyclicPseudoRootComponentEvaluation.rootNode,
    LocalizedCyclicPseudoRootComponentEvaluation.SA, SA]

theorem root_hydrogen_cursor_eq :
    (rootFrames.frame.cursorAt rootHydrogenSlot).occurrence.1 =
      LocalizedCyclicPseudoRootComponentEvaluation.rootHydrogenF := by
  apply root_cursor_eq_component rootHydrogenSlot _ _ (by decide)
  rw [root_slot_current rootHydrogenSlot ⟨5, by decide⟩ rootHydrogenSlot_atom]
  simp [LocalizedCyclicPseudoRootComponentEvaluation.rootHydrogenF,
    LocalizedCyclicPseudoRootComponentEvaluation.rootNode,
    LocalizedCyclicPseudoRootComponentEvaluation.SA, SA]

theorem root_actual_frame_correspondence :
    (rootFrames.actualLigandAtoms rootFluorineSlot = SA ⟨1, by decide⟩) ∧
    (rootFrames.actualLigandAtoms rootArmSlot = SA ⟨2, by decide⟩) ∧
    (rootFrames.actualLigandAtoms rootClosingSlot = SA ⟨4, by decide⟩) ∧
    (rootFrames.actualLigandAtoms rootHydrogenSlot = SA ⟨5, by decide⟩) ∧
    ((rootFrames.frame.cursorAt rootFluorineSlot).occurrence.1 =
      LocalizedCyclicPseudoRootComponentEvaluation.rootFluorineF) ∧
    ((rootFrames.frame.cursorAt rootArmSlot).occurrence.1 =
      LocalizedCyclicPseudoRootComponentEvaluation.armF) ∧
    ((rootFrames.frame.cursorAt rootClosingSlot).occurrence.1 =
      LocalizedCyclicPseudoRootComponentEvaluation.closeF) ∧
    ((rootFrames.frame.cursorAt rootHydrogenSlot).occurrence.1 =
      LocalizedCyclicPseudoRootComponentEvaluation.rootHydrogenF) :=
  ⟨rootFluorineSlot_atom, rootArmSlot_atom, rootClosingSlot_atom, rootHydrogenSlot_atom,
    root_fluorine_cursor_eq, root_arm_cursor_eq, root_closing_cursor_eq,
    root_hydrogen_cursor_eq⟩

theorem root_actual_stage_eq_component
    (slot : Fin 4)
    (candidate : LocalizedCyclicPseudoRootComponentEvaluation.Frame)
    (sameCurrent : (rootFrames.frame.cursorAt slot).occurrence.1.node.current? =
      candidate.node.current?)
    (candidateMem : candidate ∈
      [LocalizedCyclicPseudoRootComponentEvaluation.rootFluorineF,
        LocalizedCyclicPseudoRootComponentEvaluation.armF,
        LocalizedCyclicPseudoRootComponentEvaluation.closeF,
        LocalizedCyclicPseudoRootComponentEvaluation.rootHydrogenF])
    (stage : LocalizedCumulativeRule45Stage) :
    pseudoSpatialCertified.buildRuleMajorCumulativeWithRead?
        stage (contextOccurrenceRead pseudoReference rootTarget)
        (2 * (carrierFuel pseudoReference + 1))
        (rootFrames.frame.cursorAt slot) =
      LocalizedCyclicPseudoRootComponentEvaluation.buildRuleMajorF stage
        rootComponentReadFrame LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
        candidate (some LocalizedCyclicPseudoRootComponentEvaluation.rootF) := by
  let cursor := rootFrames.frame.cursorAt slot
  let parent : pseudoSpatialCertified.LocalizedRerootCursor
      (carrierFuel pseudoReference) := ⟨rootTarget, none⟩
  have valid := pseudoSpatialCertified.localizedRerootChild_valid parent cursor
    (pseudoSpatialCertified.executableLocalizedRerootChildren parent)
    (pseudoSpatialCertified.executableLocalizedRerootChildren_declarative parent)
    (rootFrames.childAt slot)
  obtain ⟨arm⟩ := pseudoSpatialCertified.exists_ruleMajorContextArm
    (carrierFuel pseudoReference) stage
    (contextOccurrenceRead pseudoReference rootTarget) cursor valid
  have computed := root_frame_computed
  have rootZero : cursor.occurrence.1.root =
      LocalizedCyclicPseudoRootComponentEvaluation.SA 0 := by
    have cursorRoot := pseudoSpatialCertified.localizedOccurrenceFourLigandFrame_cursor_root
      rootTarget rootFrames.frame computed cursor (root_cursor_present slot)
    have targetRoot := congrArg
      (fun f : pseudoSpatialCertified.LocalizedCIPOccurrenceFrame => f.root)
      rootFrame_eq_component_root
    rw [LocalizedCyclicPseudoRootComponentEvaluation.rootF] at targetRoot
    exact cursorRoot.trans targetRoot
  have actualStage := actualRuleMajorStage_eq_rootComponent stage cursor arm rootZero
  have occurrenceEq := root_cursor_eq_component slot candidate sameCurrent candidateMem
  have previousEq :
      cursor.previous?.map Subtype.val =
        some LocalizedCyclicPseudoRootComponentEvaluation.rootF := by
    change (rootFrames.frame.cursorAt slot).previous?.map Subtype.val =
      some LocalizedCyclicPseudoRootComponentEvaluation.rootF
    rw [pseudoSpatialCertified.localizedOccurrenceFourLigandFrame_cursor_previous
      rootTarget rootFrames.frame computed cursor (root_cursor_present slot)]
    exact congrArg some rootFrame_eq_component_root
  have inputEq :
      ((cursor.occurrence.1, cursor.previous?.map Subtype.val) :
        LocalizedCyclicPseudoRootComponentEvaluation.Frame ×
          Option LocalizedCyclicPseudoRootComponentEvaluation.Frame) =
        (candidate, some LocalizedCyclicPseudoRootComponentEvaluation.rootF) :=
    Prod.ext occurrenceEq previousEq
  have callEq := congrArg
    (fun pair : LocalizedCyclicPseudoRootComponentEvaluation.Frame ×
        Option LocalizedCyclicPseudoRootComponentEvaluation.Frame =>
      LocalizedCyclicPseudoRootComponentEvaluation.buildRuleMajorF stage
        rootComponentReadFrame LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
        pair.1 pair.2) inputEq
  have evalEq : LocalizedCyclicPseudoRootComponentEvaluation.evalFuel =
      2 * (carrierFuel pseudoReference + 1) := by
    norm_num [LocalizedCyclicPseudoRootComponentEvaluation.evalFuel,
      LocalizedCyclicPseudoRootComponentEvaluation.fuel_eq, carrierFuel_eq,
      CertifiedLocalizedCIPInput.evaluationFuel, localizedOccurrenceRerootEvaluationFuel,
      spatial_atomCount]
  have uniformBuilt := arm.built
  rw [← evalEq] at uniformBuilt
  exact (uniformBuilt.trans actualStage.symm).trans callEq

/-- Actual root compound execution equals the finite root-component production assembler for
any slot whose occurrence frame is identified by its real current atom. -/
theorem root_component_compound_eq_actual
    (slot : Fin 4)
    (candidate : LocalizedCyclicPseudoRootComponentEvaluation.Frame)
    (sameCurrent : (rootFrames.frame.cursorAt slot).occurrence.1.node.current? =
      candidate.node.current?)
    (candidateMem : candidate ∈
      [LocalizedCyclicPseudoRootComponentEvaluation.rootFluorineF,
        LocalizedCyclicPseudoRootComponentEvaluation.armF,
        LocalizedCyclicPseudoRootComponentEvaluation.closeF,
        LocalizedCyclicPseudoRootComponentEvaluation.rootHydrogenF]) :
    pseudoSpatialCertified.buildRuleMajorCompoundRule45KeyWith?
      (fun stage _ =>
        LocalizedCyclicPseudoRootComponentEvaluation.buildRuleMajorF stage
          rootComponentReadFrame LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
          candidate (some LocalizedCyclicPseudoRootComponentEvaluation.rootF))
      (rootFrames.frame.cursorAt slot) = some (rootFrames.compounds slot) := by
  let actualCompiler : pseudoSpatialCertified.RuleMajorCompoundStageCompiler
      (carrierFuel pseudoReference) :=
    fun stage cursor => pseudoSpatialCertified.buildRuleMajorCumulativeWithRead?
      stage (contextOccurrenceRead pseudoReference rootTarget)
      (2 * (carrierFuel pseudoReference + 1)) cursor
  let componentCompiler : pseudoSpatialCertified.RuleMajorCompoundStageCompiler
      (carrierFuel pseudoReference) :=
    fun stage _ => LocalizedCyclicPseudoRootComponentEvaluation.buildRuleMajorF stage
      rootComponentReadFrame LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
      candidate (some LocalizedCyclicPseudoRootComponentEvaluation.rootF)
  have sameStage (stage : LocalizedCumulativeRule45Stage) :
      actualCompiler stage (rootFrames.frame.cursorAt slot) =
        componentCompiler stage (rootFrames.frame.cursorAt slot) := by
    exact root_actual_stage_eq_component slot candidate sameCurrent candidateMem stage
  have assembled := pseudoSpatialCertified.buildRuleMajorCompoundRule45KeyWith?_eq
    actualCompiler componentCompiler (rootFrames.frame.cursorAt slot) sameStage
  let view := contextOccurrenceView pseudoReference rootTarget
  let read := fun source =>
    pseudoSpatialCertified.localizedDependencyLabel rootTarget view source
  have uniformBuiltExact :
      pseudoSpatialCertified.buildRuleMajorCompoundRule45KeyWith?
        (fun stage position => pseudoSpatialCertified.buildRuleMajorCumulativeWithRead?
          stage read (2 * (carrierFuel pseudoReference + 1)) position)
        (rootFrames.frame.cursorAt slot) = some (rootFrames.compounds slot) := by
    rw [← pseudoSpatialCertified.buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor]
    rw [← pseudoSpatialCertified.buildActualRuleMajorCompoundRule45KeyExec?_eq]
    exact rootFrames.compoundBuilt slot
  have uniformBuilt :
      pseudoSpatialCertified.buildRuleMajorCompoundRule45KeyWith? actualCompiler
        (rootFrames.frame.cursorAt slot) = some (rootFrames.compounds slot) := by
    simpa [actualCompiler, contextOccurrenceRead, contextOccurrenceView, view, read] using
      uniformBuiltExact
  dsimp [componentCompiler] at assembled ⊢
  exact assembled.symm.trans uniformBuilt

/-! ### The concrete reader

`rootComponentReadFrame` compares units with `via24Unit` and `via42Unit`, whose values are read
from classically compiled frames, so a kernel evaluation stops at the two deep ring frames.
`concreteReadFrame` decides only root, depth, provenance and the final unit atom. The equality
below is proved from the finite center classification and the four derived labels. Neither reader
is evaluated to obtain it. -/

private theorem rootComponentMapT_labels :
    (some (.chiral RS.R) : Option LocalizedAuxiliaryLabel) =
        (rootComponentMapT ⟨LocalizedCyclicPseudoRootComponentEvaluation.SA 0,
          [LocalizedCyclicPseudoRootComponentEvaluation.SA 2]⟩).bind
          Descriptor.toLocalizedLabel ∧
      (some (.chiral RS.S) : Option LocalizedAuxiliaryLabel) =
        (rootComponentMapT ⟨LocalizedCyclicPseudoRootComponentEvaluation.SA 0,
          [LocalizedCyclicPseudoRootComponentEvaluation.SA 4]⟩).bind
          Descriptor.toLocalizedLabel ∧
      (some (.chiral RS.S) : Option LocalizedAuxiliaryLabel) =
        (rootComponentMapT ⟨LocalizedCyclicPseudoRootComponentEvaluation.SA 0,
          [LocalizedCyclicPseudoRootComponentEvaluation.SA 2,
            LocalizedCyclicPseudoRootComponentEvaluation.SA 4]⟩).bind
          Descriptor.toLocalizedLabel ∧
      (some (.chiral RS.R) : Option LocalizedAuxiliaryLabel) =
        (rootComponentMapT ⟨LocalizedCyclicPseudoRootComponentEvaluation.SA 0,
          [LocalizedCyclicPseudoRootComponentEvaluation.SA 4,
            LocalizedCyclicPseudoRootComponentEvaluation.SA 2]⟩).bind
          Descriptor.toLocalizedLabel := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    simp [rootComponentMapT, directArmUnit, directClosingUnit, via24Unit,
      via24_unit_eq, via42Unit, via42_unit_eq, Descriptor.toLocalizedLabel,
      LocalizedCyclicPseudoRootComponentEvaluation.SA]
  all_goals decide

/-- On the finite root-zero tree the concrete reader is the generated-map reader. -/
theorem rootComponentReadFrame_eq_concrete
    (frame : LocalizedCyclicPseudoRootComponentEvaluation.Frame)
    (member : frame ∈ LocalizedCyclicPseudoRootComponentEvaluation.subtree0) :
    rootComponentReadFrame frame =
      LocalizedCyclicPseudoRootComponentEvaluation.concreteReadFrame frame := by
  unfold rootComponentReadFrame LocalizedCyclicPseudoRootComponentEvaluation.concreteReadFrame
  by_cases rootPositive : frame.root = LocalizedCyclicPseudoRootComponentEvaluation.SA 0 ∧
      0 < frame.address.length
  · rw [if_pos rootPositive, if_pos rootPositive]
    by_cases real : frame.node.provenance = OfficialCIPNodeProvenance.realAtom
    · rw [if_pos real, if_pos real]
      by_cases detected : IsDetectedCenter pseudoSpatialCertified.moleculeGraph
          (pseudoSpatialCertified.molecularFrameUnit frame).atom
      · rw [if_pos detected]
        have units := rootComponent_subtree_centers frame member rootPositive.2 real detected
        simp only [rootAuxUnits, List.mem_cons, List.not_mem_nil, or_false] at units
        obtain ⟨labelTwo, labelFour, labelTwoFour, labelFourTwo⟩ := rootComponentMapT_labels
        rcases units with unitEq | unitEq | unitEq | unitEq <;> rw [unitEq]
        · rw [← labelTwo]
          rfl
        · rw [← labelFour]
          rfl
        · rw [← labelTwoFour]
          rfl
        · rw [← labelFourTwo]
          rfl
      · rw [if_neg detected]
        have notTwo : (pseudoSpatialCertified.molecularFrameUnit frame).atom ≠
            LocalizedCyclicPseudoRootComponentEvaluation.SA 2 := by
          intro atomEq
          apply detected
          rw [atomEq]
          exact detected_atom ⟨2, by decide⟩ ((degree_four_iff 2).mpr (Or.inr (Or.inl rfl)))
        have notFour : (pseudoSpatialCertified.molecularFrameUnit frame).atom ≠
            LocalizedCyclicPseudoRootComponentEvaluation.SA 4 := by
          intro atomEq
          apply detected
          rw [atomEq]
          exact detected_atom ⟨4, by decide⟩ ((degree_four_iff 4).mpr (Or.inr (Or.inr rfl)))
        rw [if_neg notTwo, if_neg notFour]
    · rw [if_neg real, if_neg real]
  · rw [if_neg rootPositive, if_neg rootPositive]

/-- The actual root compound at a slot is the production assembly over the concrete reader. -/
theorem root_component_compound_eq_actual_concrete
    (slot : Fin 4)
    (candidate : LocalizedCyclicPseudoRootComponentEvaluation.Frame)
    (sameCurrent : (rootFrames.frame.cursorAt slot).occurrence.1.node.current? =
      candidate.node.current?)
    (candidateMem : candidate ∈
      [LocalizedCyclicPseudoRootComponentEvaluation.rootFluorineF,
        LocalizedCyclicPseudoRootComponentEvaluation.armF,
        LocalizedCyclicPseudoRootComponentEvaluation.closeF,
        LocalizedCyclicPseudoRootComponentEvaluation.rootHydrogenF]) :
    pseudoSpatialCertified.buildRuleMajorCompoundRule45KeyWith?
      (fun stage _ =>
        LocalizedCyclicPseudoRootComponentEvaluation.buildRuleMajorF stage
          LocalizedCyclicPseudoRootComponentEvaluation.concreteReadFrame
          LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
          candidate (some LocalizedCyclicPseudoRootComponentEvaluation.rootF))
      (rootFrames.frame.cursorAt slot) = some (rootFrames.compounds slot) := by
  have candidateTree : candidate ∈ LocalizedCyclicPseudoRootComponentEvaluation.subtree0 := by
    obtain ⟨fluorine, arm, closing, hydrogen⟩ :=
      LocalizedCyclicPseudoRootComponentEvaluation.rootLigandFrames_mem_subtree0
    simp only [List.mem_cons, List.not_mem_nil, or_false] at candidateMem
    rcases candidateMem with rfl | rfl | rfl | rfl
    · exact fluorine
    · exact arm
    · exact closing
    · exact hydrogen
  exact (pseudoSpatialCertified.buildRuleMajorCompoundRule45KeyWith?_eq
    (fun stage _ =>
      LocalizedCyclicPseudoRootComponentEvaluation.buildRuleMajorF stage
        LocalizedCyclicPseudoRootComponentEvaluation.concreteReadFrame
        LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
        candidate (some LocalizedCyclicPseudoRootComponentEvaluation.rootF))
    (fun stage _ =>
      LocalizedCyclicPseudoRootComponentEvaluation.buildRuleMajorF stage
        rootComponentReadFrame LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
        candidate (some LocalizedCyclicPseudoRootComponentEvaluation.rootF))
    (rootFrames.frame.cursorAt slot)
    (fun stage => LocalizedCyclicPseudoRootComponentEvaluation.buildRuleMajorF_congr stage
      LocalizedCyclicPseudoRootComponentEvaluation.concreteReadFrame rootComponentReadFrame
      (fun frame member => (rootComponentReadFrame_eq_concrete frame member).symm)
      LocalizedCyclicPseudoRootComponentEvaluation.evalFuel candidate
      (some LocalizedCyclicPseudoRootComponentEvaluation.rootF) candidateTree)).trans
    (root_component_compound_eq_actual slot candidate sameCurrent candidateMem)

/-- Finite production compound key for one of the four root ligands. The stage compiler
reads only the retained root-component tree and the four actual auxiliary labels. -/
def rootComponentCompound (candidate : LocalizedCyclicPseudoRootComponentEvaluation.Frame) :
    Option pseudoSpatialCertified.LocalizedRerootCompoundRule45Key :=
  pseudoSpatialCertified.buildRuleMajorCompoundRule45KeyWith?
    (fun stage _ =>
      LocalizedCyclicPseudoRootComponentEvaluation.buildRuleMajorF stage
        rootComponentReadFrame LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
        candidate (some LocalizedCyclicPseudoRootComponentEvaluation.rootF))
    ⟨rootTarget, none⟩

theorem root_arm_component_compound_success :
    rootComponentCompound LocalizedCyclicPseudoRootComponentEvaluation.armF =
      some (rootFrames.compounds rootArmSlot) := by
  simpa [rootComponentCompound] using root_component_compound_eq_actual rootArmSlot
    LocalizedCyclicPseudoRootComponentEvaluation.armF
    (by rw [root_arm_cursor_eq]) (by decide)

theorem root_closing_component_compound_success :
    rootComponentCompound LocalizedCyclicPseudoRootComponentEvaluation.closeF =
      some (rootFrames.compounds rootClosingSlot) := by
  simpa [rootComponentCompound] using root_component_compound_eq_actual rootClosingSlot
    LocalizedCyclicPseudoRootComponentEvaluation.closeF
    (by rw [root_closing_cursor_eq]) (by decide)

theorem root_fluorine_component_compound_success :
    rootComponentCompound LocalizedCyclicPseudoRootComponentEvaluation.rootFluorineF =
      some (rootFrames.compounds rootFluorineSlot) := by
  simpa [rootComponentCompound] using root_component_compound_eq_actual rootFluorineSlot
    LocalizedCyclicPseudoRootComponentEvaluation.rootFluorineF
    (by rw [root_fluorine_cursor_eq]) (by decide)

theorem root_hydrogen_component_compound_success :
    rootComponentCompound LocalizedCyclicPseudoRootComponentEvaluation.rootHydrogenF =
      some (rootFrames.compounds rootHydrogenSlot) := by
  simpa [rootComponentCompound] using root_component_compound_eq_actual rootHydrogenSlot
    LocalizedCyclicPseudoRootComponentEvaluation.rootHydrogenF
    (by rw [root_hydrogen_cursor_eq]) (by decide)

theorem root_arm_compound_eq_component :
    rootFrames.compounds rootArmSlot =
      (rootComponentCompound LocalizedCyclicPseudoRootComponentEvaluation.armF).getD
        (rootFrames.compounds rootArmSlot) := by
  have assembled := root_component_compound_eq_actual rootArmSlot
    LocalizedCyclicPseudoRootComponentEvaluation.armF
    (by rw [root_arm_cursor_eq]) (by decide)
  have h : rootComponentCompound LocalizedCyclicPseudoRootComponentEvaluation.armF =
      some (rootFrames.compounds rootArmSlot) := by
    simpa [rootComponentCompound] using assembled
  rw [h]
  rfl

theorem root_closing_compound_eq_component :
    rootFrames.compounds rootClosingSlot =
      (rootComponentCompound LocalizedCyclicPseudoRootComponentEvaluation.closeF).getD
        (rootFrames.compounds rootClosingSlot) := by
  have assembled := root_component_compound_eq_actual rootClosingSlot
    LocalizedCyclicPseudoRootComponentEvaluation.closeF
    (by rw [root_closing_cursor_eq]) (by decide)
  have h : rootComponentCompound LocalizedCyclicPseudoRootComponentEvaluation.closeF =
      some (rootFrames.compounds rootClosingSlot) := by
    simpa [rootComponentCompound] using assembled
  rw [h]
  rfl

theorem root_fluorine_compound_eq_component :
    rootFrames.compounds rootFluorineSlot =
      (rootComponentCompound LocalizedCyclicPseudoRootComponentEvaluation.rootFluorineF).getD
        (rootFrames.compounds rootFluorineSlot) := by
  have assembled := root_component_compound_eq_actual rootFluorineSlot
    LocalizedCyclicPseudoRootComponentEvaluation.rootFluorineF
    (by rw [root_fluorine_cursor_eq]) (by decide)
  have h : rootComponentCompound LocalizedCyclicPseudoRootComponentEvaluation.rootFluorineF =
      some (rootFrames.compounds rootFluorineSlot) := by
    simpa [rootComponentCompound] using assembled
  rw [h]
  rfl

theorem root_hydrogen_compound_eq_component :
    rootFrames.compounds rootHydrogenSlot =
      (rootComponentCompound LocalizedCyclicPseudoRootComponentEvaluation.rootHydrogenF).getD
        (rootFrames.compounds rootHydrogenSlot) := by
  have assembled := root_component_compound_eq_actual rootHydrogenSlot
    LocalizedCyclicPseudoRootComponentEvaluation.rootHydrogenF
    (by rw [root_hydrogen_cursor_eq]) (by decide)
  have h : rootComponentCompound LocalizedCyclicPseudoRootComponentEvaluation.rootHydrogenF =
      some (rootFrames.compounds rootHydrogenSlot) := by
    simpa [rootComponentCompound] using assembled
  rw [h]
  rfl

theorem root_arm_rule4a_component_computes :
    (LocalizedCyclicPseudoRootComponentEvaluation.buildRuleMajorF .rule4a
      rootComponentReadFrame LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
      LocalizedCyclicPseudoRootComponentEvaluation.armF
      (some LocalizedCyclicPseudoRootComponentEvaluation.rootF)).isSome = true := by
  decide +kernel

theorem root_arm_rule4a_component_references :
    (LocalizedCyclicPseudoRootComponentEvaluation.buildRuleMajorF .rule4a
      rootComponentReadFrame LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
      LocalizedCyclicPseudoRootComponentEvaluation.armF
      (some LocalizedCyclicPseudoRootComponentEvaluation.rootF)).bind
        (fun key => some (localizedRule4bReferencesFromRankedLabels key.rankedLabels)) =
      some [RS.R] := by
  decide +kernel

theorem root_arm_rule4bR_component_head :
    (LocalizedCyclicPseudoRootComponentEvaluation.buildRuleMajorF (.rule4b RS.R)
      rootComponentReadFrame LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
      LocalizedCyclicPseudoRootComponentEvaluation.armF
      (some LocalizedCyclicPseudoRootComponentEvaluation.rootF)).map
        (fun key => key.descriptor.head?) =
      some (some [([], [2, 1])]) := by
  decide +kernel

theorem root_closing_rule4bR_component_head :
    (LocalizedCyclicPseudoRootComponentEvaluation.buildRuleMajorF (.rule4b RS.R)
      rootComponentReadFrame LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
      LocalizedCyclicPseudoRootComponentEvaluation.closeF
      (some LocalizedCyclicPseudoRootComponentEvaluation.rootF)).map
        (fun key => key.descriptor.head?) =
      some (some [([], [2, 0])]) := by
  decide +kernel

theorem root_arm_rule4bS_component_head :
    (LocalizedCyclicPseudoRootComponentEvaluation.buildRuleMajorF (.rule4b RS.S)
      rootComponentReadFrame LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
      LocalizedCyclicPseudoRootComponentEvaluation.armF
      (some LocalizedCyclicPseudoRootComponentEvaluation.rootF)).map
        (fun key => key.descriptor.head?) =
      some (some [([], [2, 0])]) := by
  decide +kernel

theorem root_closing_rule4bS_component_head :
    (LocalizedCyclicPseudoRootComponentEvaluation.buildRuleMajorF (.rule4b RS.S)
      rootComponentReadFrame LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
      LocalizedCyclicPseudoRootComponentEvaluation.closeF
      (some LocalizedCyclicPseudoRootComponentEvaluation.rootF)).map
        (fun key => key.descriptor.head?) =
      some (some [([], [2, 1])]) := by
  decide +kernel

theorem root_arm_rule4cR_component_head :
    (LocalizedCyclicPseudoRootComponentEvaluation.buildRuleMajorF (.rule4c RS.R)
      rootComponentReadFrame LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
      LocalizedCyclicPseudoRootComponentEvaluation.armF
      (some LocalizedCyclicPseudoRootComponentEvaluation.rootF)).map
        (fun key => key.descriptor.head?) =
      some (some [([], [2, 1, 0])]) := by
  decide +kernel

theorem root_closing_rule4cR_component_head :
    (LocalizedCyclicPseudoRootComponentEvaluation.buildRuleMajorF (.rule4c RS.R)
      rootComponentReadFrame LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
      LocalizedCyclicPseudoRootComponentEvaluation.closeF
      (some LocalizedCyclicPseudoRootComponentEvaluation.rootF)).map
        (fun key => key.descriptor.head?) =
      some (some [([], [2, 0, 0])]) := by
  decide +kernel

theorem root_arm_rule4cS_component_head :
    (LocalizedCyclicPseudoRootComponentEvaluation.buildRuleMajorF (.rule4c RS.S)
      rootComponentReadFrame LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
      LocalizedCyclicPseudoRootComponentEvaluation.armF
      (some LocalizedCyclicPseudoRootComponentEvaluation.rootF)).map
        (fun key => key.descriptor.head?) =
      some (some [([], [2, 0, 0])]) := by
  decide +kernel

theorem root_closing_rule4cS_component_head :
    (LocalizedCyclicPseudoRootComponentEvaluation.buildRuleMajorF (.rule4c RS.S)
      rootComponentReadFrame LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
      LocalizedCyclicPseudoRootComponentEvaluation.closeF
      (some LocalizedCyclicPseudoRootComponentEvaluation.rootF)).map
        (fun key => key.descriptor.head?) =
      some (some [([], [2, 1, 0])]) := by
  decide +kernel

theorem root_arm_rule5RR_component_head :
    (LocalizedCyclicPseudoRootComponentEvaluation.buildRuleMajorF (.rule5 RS.R RS.R)
      rootComponentReadFrame LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
      LocalizedCyclicPseudoRootComponentEvaluation.armF
      (some LocalizedCyclicPseudoRootComponentEvaluation.rootF)).map
        (fun key => key.descriptor.head?) =
      some (some [([], [2, 1, 0, 1])]) := by
  decide +kernel

theorem root_closing_rule5RR_component_head :
    (LocalizedCyclicPseudoRootComponentEvaluation.buildRuleMajorF (.rule5 RS.R RS.R)
      rootComponentReadFrame LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
      LocalizedCyclicPseudoRootComponentEvaluation.closeF
      (some LocalizedCyclicPseudoRootComponentEvaluation.rootF)).map
        (fun key => key.descriptor.head?) =
      some (some [([], [2, 0, 0, 0])]) := by
  decide +kernel

theorem root_arm_rule5RS_component_head :
    (LocalizedCyclicPseudoRootComponentEvaluation.buildRuleMajorF (.rule5 RS.R RS.S)
      rootComponentReadFrame LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
      LocalizedCyclicPseudoRootComponentEvaluation.armF
      (some LocalizedCyclicPseudoRootComponentEvaluation.rootF)).map
        (fun key => key.descriptor.head?) =
      some (some [([], [2, 1, 0, 0])]) := by
  decide +kernel

theorem root_closing_rule5RS_component_head :
    (LocalizedCyclicPseudoRootComponentEvaluation.buildRuleMajorF (.rule5 RS.R RS.S)
      rootComponentReadFrame LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
      LocalizedCyclicPseudoRootComponentEvaluation.closeF
      (some LocalizedCyclicPseudoRootComponentEvaluation.rootF)).map
        (fun key => key.descriptor.head?) =
      some (some [([], [2, 0, 0, 1])]) := by
  decide +kernel

theorem root_arm_rule5SR_component_head :
    (LocalizedCyclicPseudoRootComponentEvaluation.buildRuleMajorF (.rule5 RS.S RS.R)
      rootComponentReadFrame LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
      LocalizedCyclicPseudoRootComponentEvaluation.armF
      (some LocalizedCyclicPseudoRootComponentEvaluation.rootF)).map
        (fun key => key.descriptor.head?) =
      some (some [([], [2, 0, 0, 1])]) := by
  decide +kernel

theorem root_closing_rule5SR_component_head :
    (LocalizedCyclicPseudoRootComponentEvaluation.buildRuleMajorF (.rule5 RS.S RS.R)
      rootComponentReadFrame LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
      LocalizedCyclicPseudoRootComponentEvaluation.closeF
      (some LocalizedCyclicPseudoRootComponentEvaluation.rootF)).map
        (fun key => key.descriptor.head?) =
      some (some [([], [2, 1, 0, 0])]) := by
  decide +kernel

theorem root_arm_rule5SS_component_head :
    (LocalizedCyclicPseudoRootComponentEvaluation.buildRuleMajorF (.rule5 RS.S RS.S)
      rootComponentReadFrame LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
      LocalizedCyclicPseudoRootComponentEvaluation.armF
      (some LocalizedCyclicPseudoRootComponentEvaluation.rootF)).map
        (fun key => key.descriptor.head?) =
      some (some [([], [2, 0, 0, 0])]) := by
  decide +kernel

theorem root_closing_rule5SS_component_head :
    (LocalizedCyclicPseudoRootComponentEvaluation.buildRuleMajorF (.rule5 RS.S RS.S)
      rootComponentReadFrame LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
      LocalizedCyclicPseudoRootComponentEvaluation.closeF
      (some LocalizedCyclicPseudoRootComponentEvaluation.rootF)).map
        (fun key => key.descriptor.head?) =
      some (some [([], [2, 1, 0, 1])]) := by
  decide +kernel

theorem root_closing_rule4a_component_references :
    (LocalizedCyclicPseudoRootComponentEvaluation.buildRuleMajorF .rule4a
      rootComponentReadFrame LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
      LocalizedCyclicPseudoRootComponentEvaluation.closeF
      (some LocalizedCyclicPseudoRootComponentEvaluation.rootF)).bind
        (fun key => some (localizedRule4bReferencesFromRankedLabels key.rankedLabels)) =
      some [RS.S] := by
  decide +kernel

/-- The two deep real auxiliary occurrences emit their own geometry-derived letters. -/
theorem deepAuxiliary_actual_referenceStates :
    referenceState pseudoReference via42Target = some (.chiral RS.R) ∧
    referenceState pseudoReference via24Target = some (.chiral RS.S) :=
  ⟨via42_referenceState_R, via24_referenceState_S⟩

private theorem carbon_outward_perm :
    (pseudoSpatialCertified.intendedLocalizedRerootChildFrames
      (directArmFrames.frame.cursorAt carbonSlot)).Perm
      (pseudoSpatialCertified.localizedCarrierOutwardChildFrames
        (fuel := carrierFuel pseudoReference)
        (directArmFrames.frame.cursorAt carbonSlot).occurrence.1) :=
  pseudoSpatialCertified.intendedLocalizedRerootChildFrames_perm_outward
    (directArmFrames.frame.cursorAt carbonSlot) directArmTarget carbon_previous
    carbon_sameRoot carbon_addressDrop carbon_addressStep carbon_duplicateFree

private theorem arm_parent_context :
    ∃ certificate : pseudoSpatialCertified.LocalizedParentFrameHistory directArmTarget,
      certificate.parent = rootTarget ∧
      rootTarget.1.node.ActiveSimple ∧
      directArmTarget.1.node.history =
        certificate.current :: rootTarget.1.node.history :=
  pseudoSpatialCertified.localizedParentFrameHistory_of_outward directArmTarget rootTarget
    directArmChild.sameRoot directArmChild.slot directArmChild.addressEq

/-! ## Second-sphere head from the senior outward child -/

private theorem sphere_of_head {V : Type*} {key : OfficialRuleMajorKey V} {z : ℕ}
    (head : key.rule1a.head? = some [([], z)]) :
    key.rule1a.getD 0 [] = [([], z)] := by
  cases rule : key.rule1a with
  | nil => simp [rule] at head
  | cons first rest =>
      simp [rule] at head
      exact head

private theorem le_foldl_max {β : Type*} (measure : β → ℕ) :
    ∀ (children : List β) (accumulator : ℕ),
      accumulator ≤ children.foldl (fun longest child => max longest (measure child)) accumulator
  | [], _ => Nat.le_refl _
  | head :: tail, accumulator => by
      simp only [List.foldl_cons]
      exact Nat.le_trans (Nat.le_max_left accumulator (measure head))
        (le_foldl_max measure tail (max accumulator (measure head)))

private theorem getD_zero_map_range {γ : Type*} {count : ℕ} (positive : 0 < count)
    (f : ℕ → γ) (fallback : γ) :
    ((List.range count).map f).getD 0 fallback = f 0 := by
  cases count with
  | zero => exact absurd positive (Nat.lt_irrefl 0)
  | succ _ =>
      rw [List.range_succ_eq_map]
      rfl

private theorem merge_first_head {V : Type*}
    (head : OfficialRuleMajorKey V) (tail : List (OfficialRuleMajorKey V)) {z : ℕ}
    (sphere : head.rule1a.getD 0 [] = [([], z)]) :
    ((OfficialRuleMajorKey.mergeChildren (head :: tail) OfficialRuleMajorKey.rule1a).getD
      0 []).head? = some ([0], z) := by
  have present : head.rule1a ≠ [] := by
    intro empty
    rw [empty] at sphere
    simp at sphere
  have countPos : 0 < OfficialRuleMajorKey.childLayerCount (head :: tail)
      OfficialRuleMajorKey.rule1a := by
    unfold OfficialRuleMajorKey.childLayerCount
    simp only [List.foldl_cons, Nat.zero_max]
    exact Nat.lt_of_lt_of_le (List.length_pos_iff.mpr present)
      (le_foldl_max (fun child : OfficialRuleMajorKey V => child.rule1a.length) tail
        head.rule1a.length)
  unfold OfficialRuleMajorKey.mergeChildren
  rw [getD_zero_map_range countPos, List.zipIdx_cons, List.flatMap_cons, sphere]
  simp [OfficialRuleMajorKey.prefixLayer, List.head?_cons]

private theorem assemble_second_head {V : Type*} [Fintype V] [DecidableEq V]
    (graph : MoleculeGraph V) (node : OfficialCIPNode V)
    (sorted : List (OfficialRuleMajorKey V)) {z : ℕ} (nonempty : sorted ≠ [])
    (sphere : (sorted.head nonempty).rule1a.getD 0 [] = [([], z)]) :
    ((OfficialRuleMajorKey.assemble (graph.officialRuleMajorRootKey node false) sorted).rule1a.getD
      1 []).head? = some ([0], z) := by
  cases sorted with
  | nil => exact (nonempty rfl).elim
  | cons head tail =>
      have sphere' : head.rule1a.getD 0 [] = [([], z)] := by simpa using sphere
      have merged := merge_first_head head tail sphere'
      simpa [OfficialRuleMajorKey.assemble, MoleculeGraph.officialRuleMajorRootKey,
        List.singleton_append, List.getD_cons_succ] using merged

private theorem compareNat_self (z : ℕ) :
    OfficialRuleMajorKey.compareNat z z = Ordering.eq := by
  unfold OfficialRuleMajorKey.compareNat
  exact Nat.compare_eq_eq.mpr rfl

private theorem compareNat_gt (a b : ℕ) (higher : b < a) :
    OfficialRuleMajorKey.compareNat a b = Ordering.gt := by
  unfold OfficialRuleMajorKey.compareNat
  exact Nat.compare_eq_gt.mpr higher

private def indexOf (atom : pseudoSpatialCertified.Atom) : Fin 9 :=
  ⟨atom.val, by rw [← spatial_atomCount]; exact atom.isLt⟩

private theorem indexOf_eq (atom : pseudoSpatialCertified.Atom) :
    atom = SA (indexOf atom) :=
  Fin.ext (by simp [indexOf, SA_val])

private theorem closing_neighbor (n : Fin 9) :
    pseudoSpatialCertified.moleculeGraph.Adj (SA ⟨4, by decide⟩) (SA n) ↔
      n.val ∈ [0, 2, 7, 8] := by
  rw [spatial_adj]
  apply Iff.trans (adj_closing n)
  fin_cases n <;> decide

private theorem closing_child_le (n : Fin 9) (mem : n.val ∈ [0, 2, 7, 8])
    (neParent : n.val ≠ 2) :
    pseudoSpatialCertified.moleculeGraph.atomZ (SA n) ≤ 17 := by
  fin_cases n <;> simp at mem neParent <;> simp [spatial_z] <;> decide

private theorem list_key_of_mem {fuel : Nat}
    {cursors : List (pseudoSpatialCertified.LocalizedRerootCursor
      (carrierFuel pseudoReference))}
    {keys : List (OfficialRuleMajorKey pseudoSpatialCertified.Atom)}
    (derived : pseudoSpatialCertified.DeclarativeLocalizedRerootRuleMajorKeyList
      fuel cursors keys)
    {cursor : pseudoSpatialCertified.LocalizedRerootCursor (carrierFuel pseudoReference)}
    (present : cursor ∈ cursors) :
    ∃ key, key ∈ keys ∧
      pseudoSpatialCertified.DeclarativeLocalizedRerootRuleMajorKey fuel cursor key := by
  cases derived with
  | nil _ => simp at present
  | cons head tail =>
      simp at present
      rcases present with rfl | later
      · exact ⟨_, List.mem_cons_self, head⟩
      · obtain ⟨key, mem, derivedKey⟩ := list_key_of_mem tail later
        exact ⟨key, List.mem_cons_of_mem _ mem, derivedKey⟩
termination_by cursors.length

private theorem child_key_head {fuel : Nat}
    {cursor : pseudoSpatialCertified.LocalizedRerootCursor (carrierFuel pseudoReference)}
    {key : OfficialRuleMajorKey pseudoSpatialCertified.Atom}
    (derived : pseudoSpatialCertified.DeclarativeLocalizedRerootRuleMajorKey fuel cursor key)
    {atom : pseudoSpatialCertified.Atom}
    (current : cursor.occurrence.1.node.current? = some atom) :
    key.rule1a.head? =
      some [([], pseudoSpatialCertified.moleculeGraph.atomZ atom)] := by
  rw [declarative_head derived, node_z _ _ current]

private theorem list_cursor_of_key {fuel : Nat}
    {cursors : List (pseudoSpatialCertified.LocalizedRerootCursor
      (carrierFuel pseudoReference))}
    {keys : List (OfficialRuleMajorKey pseudoSpatialCertified.Atom)}
    (derived : pseudoSpatialCertified.DeclarativeLocalizedRerootRuleMajorKeyList
      fuel cursors keys)
    {key : OfficialRuleMajorKey pseudoSpatialCertified.Atom}
    (present : key ∈ keys) :
    ∃ cursor, cursor ∈ cursors ∧
      pseudoSpatialCertified.DeclarativeLocalizedRerootRuleMajorKey fuel cursor key := by
  cases derived with
  | nil _ => simp at present
  | cons head tail =>
      simp at present
      rcases present with rfl | later
      · exact ⟨_, List.mem_cons_self, head⟩
      · obtain ⟨cursor, mem, derivedCursor⟩ := list_cursor_of_key tail later
        exact ⟨cursor, List.mem_cons_of_mem _ mem, derivedCursor⟩
termination_by keys.length

private theorem carbon_second :
    ((directArmFrames.stages carbonSlot).a.key.constitutional.rule1a.getD 1 []).head? =
      some ([0], 17) := by
  let slotCursor := directArmFrames.frame.cursorAt carbonSlot
  have notParent : slotCursor.occurrence.1.node.parent? ≠ some (SA ⟨8, by decide⟩) := by
    rw [carbon_parent]
    intro same
    injection same with atomEq
    have vals := congrArg Fin.val atomEq
    simp [SA_val] at vals
  have adjacent :=
    (closing_neighbor ⟨8, by decide⟩).mpr (by decide)
  obtain ⟨maxFrame, _childSlot, _addressStep, _sameRootFrame, currentMax, _nodeExtend,
      _occurrenceMem, memOut⟩ :=
    pseudoSpatialCertified.realCenter_outwardChildFrame_of_notParent fuel_enough
      slotCursor.occurrence carbon_current adjacent notParent carbon_real
  have perm := carbon_outward_perm
  have derived := stage_derived directArmFrames carbonSlot
  generalize _hkey : (directArmFrames.stages carbonSlot).a.key.constitutional = key at derived
  cases derived with
  | terminal frame empty =>
      exfalso
      have mapEq := frame.1
      unfold pseudoReference at mapEq
      simp [empty] at mapEq
      have aligned := perm
      rw [mapEq] at aligned
      have outwardNil := List.Perm.nil_eq aligned
      rw [← outwardNil] at memOut
      simp at memOut
  | branch frame nonempty childDerivations ranking descending =>
      rename_i children childKeys sorted
      have keyBound : ∀ childKey, childKey ∈ childKeys →
          ∃ z, childKey.rule1a.head? = some [([], z)] ∧ z ≤ 17 := by
        intro childKey childKeyMem
        obtain ⟨child, childMem, childDerived⟩ :=
          list_cursor_of_key childDerivations childKeyMem
        have frameEq := frame.1
        unfold pseudoReference at frameEq
        have frameMem : child.occurrence.1 ∈
            pseudoSpatialCertified.intendedLocalizedRerootChildFrames slotCursor := by
          rw [← frameEq]
          exact List.mem_map.mpr ⟨child, childMem, rfl⟩
        have outwardFrame := perm.mem_iff.mp frameMem
        obtain ⟨w, _, _, currentW, _, _, _, notParentW, adjW⟩ :=
          pseudoSpatialCertified.simpleBond_outwardFrame_extend_zero spatial_simpleBonded
            slotCursor.occurrence carbon_current carbon_real child.occurrence.1 outwardFrame
        have wNotParent : w ≠ SA ⟨2, by decide⟩ := by
          intro equal
          exact notParentW (by rw [equal, carbon_parent])
        have indexAdj : pseudoSpatialCertified.moleculeGraph.Adj (SA ⟨4, by decide⟩)
            (SA (indexOf w)) := by
          rw [indexOf_eq w] at adjW
          exact adjW
        have indexMem := (closing_neighbor (indexOf w)).mp indexAdj
        have indexNe : (indexOf w).val ≠ 2 := by
          intro zero
          apply wNotParent
          rw [indexOf_eq w]
          exact Fin.ext (by simpa [SA_val] using zero)
        refine ⟨pseudoSpatialCertified.moleculeGraph.atomZ w,
          child_key_head childDerived currentW, ?_⟩
        rw [indexOf_eq w]
        exact closing_child_le (indexOf w) indexMem indexNe
      have memIntended : maxFrame ∈
          pseudoSpatialCertified.intendedLocalizedRerootChildFrames slotCursor :=
        perm.mem_iff.mpr memOut
      have frameEq := frame.1
      unfold pseudoReference at frameEq
      rw [← frameEq] at memIntended
      obtain ⟨maxChild, maxChildMem, maxChildEq⟩ := List.mem_map.mp memIntended
      obtain ⟨maxKey, maxKeyMem, maxDerived⟩ := list_key_of_mem childDerivations maxChildMem
      have maxCurrent : maxChild.occurrence.1.node.current? = some (SA ⟨8, by decide⟩) := by
        rw [maxChildEq]
        exact currentMax
      have maxHead := child_key_head maxDerived maxCurrent
      rw [spatial_z ⟨8, by decide⟩, (z_chlorine ⟨8, by decide⟩).mpr (Or.inr rfl)] at maxHead
      cases sorted with
      | nil =>
          exact absurd (ranking.mem_iff.mpr maxKeyMem) (by simp)
      | cons headKey tail =>
          obtain ⟨z, headHead, zLe⟩ := keyBound headKey
            (ranking.mem_iff.mp List.mem_cons_self)
          have zEq : z = 17 := by
            by_contra different
            have zlt : z < 17 := Nat.lt_of_le_of_ne zLe different
            letI : Std.TransCmp (@OfficialRuleMajorKey.compare pseudoSpatialCertified.Atom) :=
              OfficialRuleMajorKey.compare_transCmp
            have childGt := compare_gt_of_heads maxHead headHead zlt
            have headLt : OfficialRuleMajorKey.compare headKey maxKey = Ordering.lt := by
              rw [← Std.OrientedCmp.gt_iff_lt]
              exact childGt
            have maxSorted : maxKey ∈ headKey :: tail := ranking.mem_iff.mpr maxKeyMem
            rcases List.mem_cons.mp maxSorted with same | later
            · rw [← same] at headHead
              have heads := headHead.symm.trans maxHead
              injection heads with layerEq
              injection layerEq with entryEq
              injection entryEq with addrEq zEq'
              exact different zEq'
            · exact (List.pairwise_cons.mp descending).1 maxKey later headLt
          have sphere : headKey.rule1a.getD 0 [] = [([], 17)] := by
            rw [sphere_of_head headHead, zEq]
          exact assemble_second_head pseudoSpatialCertified.moleculeGraph
            slotCursor.occurrence.1.node (headKey :: tail) (by simp)
            (by simpa [List.head_cons] using sphere)

theorem direct_arm_carbon_second_sphere :
    ∃ slot : Fin 4,
      directArmFrames.actualLigandAtoms slot = SA ⟨4, by decide⟩ ∧
      ((directArmFrames.stages slot).a.key.constitutional.rule1a.getD 1 []).head? =
        some ([0], 17) :=
  ⟨carbonSlot, carbonSlot_atom, carbon_second⟩

private theorem actual_via24_const_rule1a :
    ∃ key,
      LocalizedCyclicPseudoRootComponentEvaluation.buildF .rule4a
        LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
        LocalizedCyclicPseudoRootComponentEvaluation.via24F
        (some LocalizedCyclicPseudoRootComponentEvaluation.armF) = some key ∧
      key.constitutional.rule1a =
        (directArmFrames.stages carbonSlot).a.key.constitutional.rule1a := by
  let cursor := directArmFrames.frame.cursorAt carbonSlot
  let parent : pseudoSpatialCertified.LocalizedRerootCursor (carrierFuel pseudoReference) :=
    ⟨directArmTarget, none⟩
  have valid := pseudoSpatialCertified.localizedRerootChild_valid parent cursor
    (pseudoSpatialCertified.executableLocalizedRerootChildren parent)
    (pseudoSpatialCertified.executableLocalizedRerootChildren_declarative parent)
    (directArmFrames.childAt carbonSlot)
  have rootEq := congrArg
    (fun f : pseudoSpatialCertified.LocalizedCIPOccurrenceFrame => f.root)
    directArmFrame_eq_component_armF
  have rootZero : cursor.occurrence.1.root =
      LocalizedCyclicPseudoRootComponentEvaluation.SA 0 :=
    carbon_sameRoot.symm.trans rootEq
  have built := (directArmFrames.stages carbonSlot).a.built
  unfold pseudoReference at built
  rw [pseudoSpatialCertified.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized] at built
  obtain ⟨key, builtTwin, tableEq⟩ := actualRule1a_eq_rootComponent cursor valid
    (contextOccurrenceRead pseudoReference directArmTarget)
    (fuel := 2 * (carrierFuel pseudoReference + 1))
    (directArmFrames.stages carbonSlot).a.key built rootZero
  have previousEq :
      (directArmFrames.frame.cursorAt carbonSlot).previous?.map Subtype.val =
      some LocalizedCyclicPseudoRootComponentEvaluation.armF := by
    rw [carbon_previous]
    exact congrArg some directArmFrame_eq_component_armF
  simp only [cursor] at builtTwin previousEq
  rw [carbonCursor_eq_via24F] at builtTwin
  have prevBuildEq := congrArg
    (fun previous => LocalizedCyclicPseudoRootComponentEvaluation.buildF .rule4a
      LocalizedCyclicPseudoRootComponentEvaluation.evalFuel
      LocalizedCyclicPseudoRootComponentEvaluation.via24F previous) previousEq
  exact ⟨key, prevBuildEq.symm.trans builtTwin, tableEq⟩

end

end TetraStereo.OneCenter.LocalizedCyclicPseudoActualEvaluation

assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoActualEvaluation.carrierFuel_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoActualEvaluation.spatial_simpleBonded
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoActualEvaluation.root_provenance_real
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoActualEvaluation.direct_arm_first_spheres
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoActualEvaluation.direct_arm_first_sphere_separation
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoActualEvaluation.direct_arm_carbon_second_sphere
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoActualEvaluation.actualRule1a_eq_rootComponent
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoActualEvaluation.deepAuxiliary_actual_referenceStates
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoActualEvaluation.auxiliary_actual_referenceStates
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoActualEvaluation.auxiliary_generatedMap_readback
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoActualEvaluation.root_generatedView_readback
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoActualEvaluation.rootComponentRead_eq_context
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoActualEvaluation.actualRuleMajorStage_eq_rootComponent
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoActualEvaluation.root_actual_stage_eq_component
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoActualEvaluation.root_component_compound_eq_actual
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoActualEvaluation.rootComponentReadFrame_eq_concrete
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicPseudoActualEvaluation.root_component_compound_eq_actual_concrete
