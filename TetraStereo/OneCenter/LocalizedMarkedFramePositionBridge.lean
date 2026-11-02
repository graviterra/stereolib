import TetraStereo.OneCenter.LocalizedMarkedDetectedFrames
import TetraStereo.OneCenter.LocalizedMarkedRetainedOrdinaryRanking
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Raw and retained frame positions denote the same physical neighbors

At a real detected reached occurrence, source admission constructs the raw four-ligand frame.
The actual retained execution frame also enumerates those four physical neighbors. Their orders
need not agree: this module constructs a permutation from raw slots to retained slots through
the physical neighbor bijection. The argument allows finite single-bond rings and does not use
comparison results, generated-label meaning, a desired sort, or acyclicity.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedFramePositionBridge

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedMarkedReachableConfigurations LocalizedMarkedReachedFrameNeighbors
open LocalizedMarkedCertifiedTerminalRefusal LocalizedMarkedDetectedFrames
open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedMolecularSelection
open RawLocalizedChildNodeTransport
open LocalizedGenericMarkedRecalculation (frameAtoms? frameAtomsOf)

abbrev Node := RawMolecule.CanonicalBranchNode

private theorem raw_real_of_correspondence
    {official : OfficialCIPNodeProvenance} {raw : RawMolecule.CanonicalNodeProvenance}
    (corresponds : NodeProvenanceCorresponds official raw) (real : official = .realAtom) :
    raw = .realAtom := by
  cases corresponds <;> simp_all

/-- An actual retained execution frame determines a raw-to-retained slot permutation. Its raw
frame, length, distinctness and pointwise atom readback are conclusions, not input equations. -/
theorem exists_frame_position_permutation
    (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (execution : RetainedExecutionFrame descriptorMap target)
    (node : Node) (reached : Reached mol node)
    (corresponds : NodeCorresponds (fun atom : input.Atom => atom.val) target.1.node node) :
    ∃ (atoms : List Nat) (length : atoms.length = 4) (reindex : Equiv.Perm (Fin 4)),
      frameAtoms? mol node = some atoms ∧ atoms.Nodup ∧
      ∀ index : Fin 4,
        (execution.frame.cursorAt (reindex index)).occurrence.1.node.current?.map
          (fun atom : input.Atom => atom.val) =
        some (atoms.get (Fin.cast length.symm index)) := by
  classical
  have wellFormed := admissible.1.1
  have unique := admissible.1.2
  have rawSingle := raw_single mol input agreement wellFormed unique supported single
  have meaning : input.RealTetrahedralCenterNode target.1.node execution.center :=
    (input.localizedOccurrenceDescriptorCenter?_eq_some_iff target execution.center).mp
      execution.centerComputed
  have rawReal : node.provenance = .realAtom :=
    raw_real_of_correspondence corresponds.provenance meaning.1
  have current : node.atom = execution.center.1.val := by
    have mapped := corresponds.current
    rw [meaning.2] at mapped
    exact (Option.some.inj mapped).symm
  let center : input.detectedMultiCenterMolecule.Center :=
    ⟨execution.center.1, execution.center.2⟩
  let atoms := frameAtomsOf (occurrenceLigandCursors mol node)
  have rawFrame : frameAtoms? mol node = some atoms :=
    detected_frame mol input agreement admissible supported single center node reached rawReal current
  have length : atoms.length = 4 :=
    LocalizedMarkedConfigurationTransport.frame_length mol node atoms rawFrame
  have degree : (mol.canonicalIncidentNeighbors node.atom).length = 4 := by
    rw [current]
    exact detected_raw_degree mol input agreement wellFormed unique supported center
  have permutation : atoms.Perm (mol.canonicalIncidentNeighbors node.atom) := by
    rcases frame_atoms_perm_neighbors mol wellFormed rawSingle node reached atoms rawFrame with
      ⟨_, permutation⟩ | ⟨three, _⟩
    · exact permutation
    · omega
  have nodup : atoms.Nodup := permutation.nodup_iff.mpr
    (mol.canonicalIncidentNeighbors_nodup node.atom unique)
  have enough : input.certified.input.molecule.atomCount ≤ retainedCarrierFuel input :=
    Nat.le_succ _
  obtain ⟨frame, ligand, computed, ligandSpec⟩ :=
    input.exists_simpleBond_localizedOccurrenceFourLigandFrame_and_neighborEquiv single enough
      target execution.center meaning
  have actualComputed : input.localizedOccurrenceFourLigandFrame? target = some execution.frame := by
    rw [← input.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame? target]
    exact execution.frameComputed
  have frameEq : frame = execution.frame := Option.some.inj (computed.symm.trans actualComputed)
  have readsBack : ∀ index,
      (execution.frame.cursorAt index).occurrence.1.node.current? = some (ligand index).1 := by
    intro index
    simpa only [frameEq] using ligandSpec index
  let rawAtomAt : Fin 4 → Nat := fun index => atoms.get (Fin.cast length.symm index)
  have rawPositive : ∀ index, 0 < mol.bondOrder node.atom (rawAtomAt index) := by
    intro index
    apply (mol.mem_canonicalIncidentNeighbors_iff node.atom wellFormed (rawAtomAt index)).mp
    exact permutation.mem_iff.mp (List.get_mem atoms (Fin.cast length.symm index))
  have rawBound : ∀ index, rawAtomAt index < mol.atomCount := fun index =>
    (mol.bondOrder_pos_endpoint_lt wellFormed (rawPositive index)).2
  let rawNeighbor : Fin 4 → input.moleculeGraph.Neighbor execution.center.1 := fun index =>
    ⟨localizedIndexOf mol input agreement ⟨rawAtomAt index, rawBound index⟩, by
      change 0 < input.moleculeGraph.bond execution.center.1
        (localizedIndexOf mol input agreement ⟨rawAtomAt index, rawBound index⟩)
      rw [moleculeGraph_bond_eq_rawBondOrder mol input agreement wellFormed unique supported]
      change 0 < mol.bondOrder execution.center.1.val (rawAtomAt index)
      rw [← current]
      exact rawPositive index⟩
  have rawAtomAt_injective : Function.Injective rawAtomAt := by
    intro left right equal
    apply Fin.cast_injective length.symm
    exact (List.nodup_iff_injective_get.mp nodup) equal
  let toSlot : Fin 4 → Fin 4 := fun index => ligand.symm (rawNeighbor index)
  have toSlot_injective : Function.Injective toSlot := by
    intro left right equal
    have neighborEq : rawNeighbor left = rawNeighbor right := ligand.symm.injective equal
    apply rawAtomAt_injective
    exact congrArg (fun neighbor : input.moleculeGraph.Neighbor execution.center.1 =>
      neighbor.1.val) neighborEq
  let reindex : Equiv.Perm (Fin 4) := Equiv.ofBijective toSlot
    ⟨toSlot_injective, Finite.surjective_of_injective toSlot_injective⟩
  have reindex_readback : ∀ index, ligand (reindex index) = rawNeighbor index := by
    intro index
    change ligand (ligand.symm (rawNeighbor index)) = rawNeighbor index
    exact ligand.apply_symm_apply _
  refine ⟨atoms, length, reindex, rawFrame, nodup, ?_⟩
  intro index
  simpa only [Option.map_some, reindex_readback index] using
    congrArg (Option.map (fun atom : input.Atom => atom.val)) (readsBack (reindex index))

/-- Both execution and slot correspondence are constructed at a real detected carrier occurrence.
The independent descriptor map may be arbitrary; it does not select the position permutation. -/
theorem exists_retained_frame_position_permutation
    (mol : RawMolecule) (input : CertifiedLocalizedCIPInput)
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (real : target.1.node.provenance = .realAtom)
    (unit : DetectedOccurrence input.moleculeGraph)
    (targetUnit : input.molecularFrameUnit target.1 = unit.1)
    (node : Node) (reached : Reached mol node)
    (corresponds : NodeCorresponds (fun atom : input.Atom => atom.val) target.1.node node) :
    ∃ (execution : RetainedExecutionFrame descriptorMap target)
      (atoms : List Nat) (length : atoms.length = 4) (reindex : Equiv.Perm (Fin 4)),
      frameAtoms? mol node = some atoms ∧ atoms.Nodup ∧
      ∀ index : Fin 4,
        (execution.frame.cursorAt (reindex index)).occurrence.1.node.current?.map
          (fun atom : input.Atom => atom.val) =
        some (atoms.get (Fin.cast length.symm index)) := by
  obtain ⟨execution⟩ := exists_retainedExecutionFrame descriptorMap single target real unit targetUnit
  obtain ⟨atoms, length, reindex, computed, nodup, readback⟩ :=
    exists_frame_position_permutation mol input agreement admissible supported single descriptorMap
      target execution node reached corresponds
  exact ⟨execution, atoms, length, reindex, computed, nodup, readback⟩

end TetraStereo.OneCenter.LocalizedMarkedFramePositionBridge

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedFramePositionBridge.exists_frame_position_permutation
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedFramePositionBridge.exists_retained_frame_position_permutation
