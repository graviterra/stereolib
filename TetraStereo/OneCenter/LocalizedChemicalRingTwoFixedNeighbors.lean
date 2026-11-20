import TetraStereo.OneCenter.LocalizedChemicalRingActualReferenceFixing
import TetraStereo.OneCenter.MultiCenterConfiguration
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
An actual promoted-key tie between two real outward slots reconstructs an automorphism
fixing the entire target history and the promoted reference. If the history contains a
neighbor distinct from that reference, the induced nonidentity permutation of the four
ligands fixes two slots and must be odd.

The outward-slot and physical-neighbor premises are explicit. Incoming reroot slots and
forced duplicate slots are not covered. The conclusion is local oddness at this detected
center; properness at other centers and preservation of their generated labels are separate
obligations for the proposed correcting-symmetry induction.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingTwoFixedNeighbors

open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
open LocalizedCumulativeDecoratedTree LocalizedMarkedRetainedCanonicalFrame
open LocalizedMarkedRetainedMolecularSelection LocalizedMarkedRetainedOrdinaryRanking
open LocalizedMarkedRetainedPromotedRanking LocalizedMarkedRetainedStateReader
open LocalizedChemicalRingActualReferenceFixing LocalizedActualBoundaryPathRealization
open LocalizedActualBoundaryObservationReadback

/-- A nonidentity permutation of four slots fixing two distinct slots is a transposition. -/
theorem odd_of_two_fixed (p : Equiv.Perm (Fin 4)) (i j : Fin 4)
    (different : i ≠ j) (fixedI : p i = i) (fixedJ : p j = j) (nontrivial : p ≠ 1) :
    permHandedness p = -1 := by
  have finite : ∀ (p : Equiv.Perm (Fin 4)) (i j : Fin 4), i ≠ j → p i = i → p j = j →
      p ≠ 1 → ∃ a b : Fin 4, a ≠ b ∧ p = Equiv.swap a b := by decide +kernel
  obtain ⟨a, b, distinct, rfl⟩ := finite p i j different fixedI fixedJ nontrivial
  simp [permHandedness, Equiv.Perm.sign_swap distinct]

noncomputable section
open scoped Classical

/-- Atom-level boundary and reference fixes imply oddness in any four-neighbor frame;
no convention for numbering the physical ligands is required. -/
theorem local_odd_of_two_fixed_neighbors {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) (e : m.Aut) (c : m.Center)
    (centerFixed : (e : Equiv.Perm V) c.1 = c.1)
    (parent reference : V) (different : parent ≠ reference)
    (parentAdjacent : m.mol.Adj c.1 parent) (referenceAdjacent : m.mol.Adj c.1 reference)
    (parentFixed : (e : Equiv.Perm V) parent = parent)
    (referenceFixed : (e : Equiv.Perm V) reference = reference)
    (moved : ∃ atom, m.mol.Adj c.1 atom ∧ (e : Equiv.Perm V) atom ≠ atom) :
    m.centerPerm e c = c ∧ permHandedness (m.ligandPermAt e c) = -1 := by
  have fixed : m.centerPerm e c = c := Subtype.ext centerFixed
  obtain ⟨i, hi⟩ := m.ligandAtomAt_surjective c parent parentAdjacent
  obtain ⟨j, hj⟩ := m.ligandAtomAt_surjective c reference referenceAdjacent
  have distinct : i ≠ j := by
    intro same
    exact different (hi.symm.trans ((congrArg (m.ligandAtomAt c) same).trans hj))
  have fixesI : m.ligandPermAt e c i = i := by
    apply m.ligandAtomAt_injective c
    have transported := m.ligandAtomAt_ligandPermAt e c i
    rw [fixed, hi, parentFixed] at transported
    exact transported.trans hi.symm
  have fixesJ : m.ligandPermAt e c j = j := by
    apply m.ligandAtomAt_injective c
    have transported := m.ligandAtomAt_ligandPermAt e c j
    rw [fixed, hj, referenceFixed] at transported
    exact transported.trans hj.symm
  have nontrivial : m.ligandPermAt e c ≠ 1 := by
    intro trivial
    obtain ⟨atom, adjacent, changed⟩ := moved
    obtain ⟨k, hk⟩ := m.ligandAtomAt_surjective c atom adjacent
    have transported := m.ligandAtomAt_ligandPermAt e c k
    rw [fixed, trivial] at transported
    change m.ligandAtomAt c k = (e : Equiv.Perm V) (m.ligandAtomAt c k) at transported
    rw [hk] at transported
    exact changed transported.symm
  exact ⟨fixed, odd_of_two_fixed _ i j distinct fixesI fixesJ nontrivial⟩

variable (input : CertifiedLocalizedCIPInput)

/-- Actual Rule-4a trace/source data give boundary-rootedness at any real outward slot.
Only the outward geometry of the carrier edge and the slot's real provenance are premises. -/
theorem outward_slot_boundary (single : input.moleculeGraph.SimpleBonded)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (frame : RetainedExecutionFrame descriptorMap target)
    (real : target.1.node.provenance = .realAtom) (slot : Fin 4) (atom : input.Atom)
    (current : (frame.frame.cursorAt slot).occurrence.1.node.current? = some atom)
    (childReal : (frame.frame.cursorAt slot).occurrence.1.node.provenance = .realAtom)
    (sameRoot : (frame.frame.cursorAt slot).occurrence.1.root = target.1.root)
    (childSlot : Nat)
    (address : (frame.frame.cursorAt slot).occurrence.1.address = target.1.address ++ [childSlot]) :
    BoundaryRootedTree input target.1.node.history.reverse atom
        (toOfficialSourceTree (frame.stages slot).a.tree) ∧
      atom ∉ target.1.node.history ∧
      ∀ center, target.1.node.current? = some center → input.moleculeGraph.Adj center atom := by
  have computed : input.localizedOccurrenceFourLigandFrame? target = some frame.frame := by
    rw [← input.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame? target]
    exact frame.frameComputed
  have present : frame.frame.cursorAt slot ∈ frame.frame.cursors :=
    List.get_mem frame.frame.cursors (Fin.cast frame.frame.length_eq.symm slot)
  have previous := input.localizedOccurrenceFourLigandFrame_cursor_previous
    target frame.frame computed _ present
  have incoming : LocalizedRerootCursorIncomingParent input (frame.frame.cursorAt slot) := by
    refine ⟨target, previous, sameRoot.symm, ?_, ?_⟩
    · simp [address]
    · simp [address]
  have realizes := LocalizedRuleMajorSortTrace.realizes_of_trace (frame.stages slot).a.trace
  have treeIncoming := input.localizedCumulativeTreeIncoming_of_realizes _ _ realizes
    (by rw [(frame.stages slot).a.sourceEq]; exact incoming)
  have positive := input.localizedCumulativeTreePositive_of_atomCount_le
    (fuel := retainedCarrierFuel input) (by unfold retainedCarrierFuel; omega)
    (frame.stages slot).a.tree
  have generated := input.toOfficialSourceTree_generatedBy _ _ realizes positive treeIncoming
  exact outwardChild_boundaryRooted input single ⟨target, none⟩ (frame.frame.cursorAt slot)
    sameRoot childSlot address real childReal current (frame.stages slot).a.tree
    (frame.stages slot).a.sourceEq generated

section Actual

variable (single : input.moleculeGraph.SimpleBonded) (state : OccurrenceAuxState)
  (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
  (real : target.1.node.provenance = .realAtom)
  (unit : DetectedOccurrence input.moleculeGraph)
  (targetUnit : input.molecularFrameUnit target.1 = unit.1)
  (reference : input.Atom) (W D : Nat) (fallback : CompleteLigandRule5Key)

include fallback in
/-- A real outward promoted tie supplies an odd automorphism at the actual detected
auxiliary center, fixing its entire occurrence history and the local reference. Width and
height are the marker-layout bounds; no generated-source or desired-symmetry premise occurs. -/
theorem actual_outward_tie_odd_aut
    (center : input.detectedMultiCenterMolecule.Center)
    (centerCurrent : target.1.node.current? = some center.1)
    (parent : input.Atom) (parentHistory : parent ∈ target.1.node.history)
    (parentAdjacent : input.moleculeGraph.Adj center.1 parent)
    (referenceAdjacent : input.moleculeGraph.Adj center.1 reference) (different : parent ≠ reference)
    (left right : Fin 4) (a b : input.Atom) (distinct : a ≠ b)
    (currentL : ((frames input single state target real unit targetUnit).frame.cursorAt left).occurrence.1.node.current? = some a)
    (currentR : ((frames input single state target real unit targetUnit).frame.cursorAt right).occurrence.1.node.current? = some b)
    (realL : ((frames input single state target real unit targetUnit).frame.cursorAt left).occurrence.1.node.provenance = .realAtom)
    (realR : ((frames input single state target real unit targetUnit).frame.cursorAt right).occurrence.1.node.provenance = .realAtom)
    (rootL : ((frames input single state target real unit targetUnit).frame.cursorAt left).occurrence.1.root = target.1.root)
    (rootR : ((frames input single state target real unit targetUnit).frame.cursorAt right).occurrence.1.root = target.1.root)
    (slotL slotR : Nat)
    (addressL : ((frames input single state target real unit targetUnit).frame.cursorAt left).occurrence.1.address = target.1.address ++ [slotL])
    (addressR : ((frames input single state target real unit targetUnit).frame.cursorAt right).occurrence.1.address = target.1.address ++ [slotR])
    (widthL : ∀ node, ((ruleMajorTreeGraph (slotTree input single state target real unit targetUnit left)).childList node).length ≤ W)
    (heightL : (ruleMajorTreeGraph (slotTree input single state target real unit targetUnit left)).height ≤ D)
    (widthR : ∀ node, ((ruleMajorTreeGraph (slotTree input single state target real unit targetUnit right)).childList node).length ≤ W)
    (heightR : (ruleMajorTreeGraph (slotTree input single state target real unit targetUnit right)).height ≤ D)
    (tie : refinedKey input single state target real unit targetUnit reference W D left =
      refinedKey input single state target real unit targetUnit reference W D right)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph) :
    ∃ e : input.detectedMultiCenterMolecule.Aut,
      (∀ atom ∈ target.1.node.history, (e : Equiv.Perm input.Atom) atom = atom) ∧
      (e : Equiv.Perm input.Atom) a = b ∧ (e : Equiv.Perm input.Atom) reference = reference ∧
      input.detectedMultiCenterMolecule.centerPerm e center = center ∧
      permHandedness (input.detectedMultiCenterMolecule.ligandPermAt e center) = -1 := by
  let frame := frames input single state target real unit targetUnit
  obtain ⟨rootedL, _, adjacentL⟩ := outward_slot_boundary input single
    (rawStateDescriptorMap input state) target frame real left a currentL realL rootL slotL addressL
  obtain ⟨rootedR, _, adjacentR⟩ := outward_slot_boundary input single
    (rawStateDescriptorMap input state) target frame real right b currentR realR rootR slotR addressR
  have history := occurrence_history_facts input target real
  have parentOf : ∀ x : input.Atom,
      (∀ c, target.1.node.current? = some c → input.moleculeGraph.Adj c x) →
      ∀ z, target.1.node.history.reverse.getLast? = some z → input.moleculeGraph.Adj x z := by
    intro x adjacent z last
    rw [List.getLast?_reverse, ← history.2] at last
    exact input.moleculeGraph.adj_symm.mp (adjacent z last)
  obtain ⟨π, aut, boundary, image, ref⟩ := actual_tie_reference_fixed_aut input single state
    target real unit targetUnit reference W D fallback left right widthL heightL widthR heightR tie
    target.1.node.history.reverse a b rootedL rootedR charge (parentOf a adjacentL) (parentOf b adjacentR)
  let e : input.detectedMultiCenterMolecule.Aut :=
    input.moleculeGraph.detectedMultiCenterAutOfGraphAut ⟨π, aut⟩
  have fixed : ∀ atom ∈ target.1.node.history, (e : Equiv.Perm input.Atom) atom = atom := by
    intro atom member
    exact boundary atom (List.mem_reverse.mpr member)
  have centerHistory : center.1 ∈ target.1.node.history := by
    have head : target.1.node.history.head? = some center.1 := history.2.symm.trans centerCurrent
    exact List.mem_of_head? head
  have odd := local_odd_of_two_fixed_neighbors input.detectedMultiCenterMolecule e center
    (fixed center.1 centerHistory) parent reference different parentAdjacent referenceAdjacent
    (fixed parent parentHistory) ref ⟨a, adjacentL center.1 centerCurrent, by
      change π a ≠ a
      rw [image]
      exact Ne.symm distinct⟩
  exact ⟨e, fixed, image, ref, odd⟩

end Actual
end
end TetraStereo.OneCenter.LocalizedChemicalRingTwoFixedNeighbors

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingTwoFixedNeighbors.odd_of_two_fixed
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingTwoFixedNeighbors.local_odd_of_two_fixed_neighbors
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingTwoFixedNeighbors.outward_slot_boundary
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingTwoFixedNeighbors.actual_outward_tie_odd_aut
