import TetraStereo.OneCenter.LocalizedChemicalRingSelectedParentEligibility
import TetraStereo.OneCenter.LocalizedChemicalRingResidualReadingTransport
import TetraStereo.OneCenter.LocalizedChemicalRingFrameComparison
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
At a history-fixed actual occurrence, a molecular automorphism preserves the complete
empty-state comparison matrix. Finite order then forces each moved slot to tie with its
image. Such an attachment belongs to the evaluator's actual eligible population, and
its actual outward raw child is selected by `underWith`.

This derives selection from the actual molecular symmetry reconstructed from keys. It
does not assume selected references, comparison equality, sorting success, or physical
properness. It also does not assert that an arbitrary carrier Rule-1a tie is selected.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingMovedSlotEligibility

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedChemicalRingInheritedRefusalCases LocalizedChemicalRingSelectedParentEligibility
open LocalizedChemicalRingResidualReadingTransport LocalizedChemicalRingRelabel
open LocalizedChemicalRingPhysicalSense LocalizedChemicalRingFrameReadback
open LocalizedChemicalRingFrameComparison LocalizedChemicalRingLookupTransport
open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedStateReader
open LocalizedMarkedRetainedMolecularSelection
open LocalizedMarkedRetainedCanonicalFrame LocalizedMarkedRetainedPromotedRanking
open LocalizedChemicalRingSelectedRefusalWitness
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedOperationEvaluator (tiedChildren)
open LocalizedGenericMarkedRecalculation (eligibleOf)

private theorem no_increase {K : Type*} [Preorder K] (key : Fin 4 → K)
    (p : Equiv.Perm (Fin 4))
    (preserved : ∀ i j, key i < key j → key (p i) < key (p j)) (i : Fin 4) :
    ¬ key i < key (p i) := by
  intro first
  have period : p ^ 12 = 1 := by
    have finite : ∀ q : Equiv.Perm (Fin 4), q ^ 12 = 1 := by decide +kernel
    exact finite p
  have steps : ∀ n : Nat, key ((p ^ n) i) < key ((p ^ (n + 1)) i) := by
    intro n
    induction n with
    | zero => simpa using first
    | succ n ih =>
      simpa only [pow_succ', Equiv.Perm.mul_apply] using preserved _ _ ih
  have chain : ∀ n : Nat, key i < key ((p ^ (n + 1)) i) := by
    intro n
    induction n with
    | zero => simpa using first
    | succ n ih => exact lt_trans ih (steps (n + 1))
  have impossible := chain 11
  norm_num only [show 11 + 1 = 12 from rfl, period, Equiv.Perm.one_apply] at impossible
  exact (lt_irrefl _ impossible)

/-- An order-preserving action on the four actual slots cannot move their key values. -/
theorem key_fixed_of_order_action {K : Type*} [LinearOrder K] (key : Fin 4 → K)
    (p : Equiv.Perm (Fin 4))
    (preserved : ∀ i j, key i < key j → key (p i) < key (p j)) (i : Fin 4) :
    key (p i) = key i := by
  apply le_antisymm
  · exact le_of_not_gt (no_increase key p preserved i)
  · exact le_of_not_gt (no_increase (K := OrderDual K) key p
      (fun a b h => preserved b a h) i)

noncomputable section
open scoped Classical
variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (e : input.detectedMultiCenterMolecule.Aut)
  (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
  (data : OccurrenceData input mol c node) (reached : Reached mol node)
  (historyFixed : ∀ atom ∈ node.history, relabelOf input (e : Equiv.Perm input.Atom) atom = atom)

include agreement admissible supported reached historyFixed in
/-- Both the slot action and its key equality come from actual frame/comparison transport.
The keys are precisely the empty-state ordinary keys used to choose recursive children. -/
theorem actual_slot_key_action :
    ∃ p : Equiv.Perm (Fin 4),
      (∀ i, referenceAt input mol c node data (p i) =
        (e : Equiv.Perm input.Atom) (referenceAt input mol c node data i)) ∧
      ∀ i, ordinaryKeys input mol single c node data (p i) =
        ordinaryKeys input mol single c node data i := by
  let graphAut : input.moleculeGraph.Aut :=
    ⟨e, MultiCenterMolecule.Aut.mem_molAut input.detectedMultiCenterMolecule e⟩
  have sym := LocalizedChemicalRingSemanticSymmetry.structuralSymmetry_of_aut
    input mol agreement admissible supported e
  have fixedNode := mapNode_eq_of_history_fixed mol _ node reached historyFixed
  have fixedTarget : input.transportOccurrence single graphAut data.target = data.target := by
    have h := lookup_transport input mol agreement admissible supported single graphAut sym
      node reached data.target data.found
    rw [fixedNode, data.found] at h
    exact (Option.some.inj h).symm
  let unit : DetectedOccurrence input.moleculeGraph :=
    ⟨input.molecularFrameUnit data.target.1, data.detected⟩
  let execution := rawStateFrames input single [] data.target data.real unit rfl
  have meaning := (input.localizedOccurrenceDescriptorCenter?_eq_some_iff data.target
    execution.center).mp execution.centerComputed
  let ft := input.actualFrameSlotTransport single graphAut (Nat.le_succ _)
    data.target execution.center meaning
  have computed : input.localizedOccurrenceFourLigandFrame? data.target = some data.frame := by
    rw [← input.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?]
    exact data.frameExec
  have sourceFrame : ft.sourceFrame = data.frame :=
    Option.some.inj (ft.sourceComputed.symm.trans computed)
  have imageFrame : ft.imageFrame = data.frame := by
    have h := ft.imageComputed
    rw [fixedTarget, computed] at h
    exact (Option.some.inj h).symm
  have executionFrame : execution.frame = data.frame :=
    Option.some.inj (execution.frameComputed.symm.trans data.frameExec)
  have keyMatrix (a b : Fin 4) :
      rawStateBefore input [] data.target data.frame a b =
        some (compare (ordinaryKeys input mol single c node data a)
          (ordinaryKeys input mol single c node data b)) := by
    have h := rawStateBefore_eq_keys input single [] data.target data.real unit rfl a b
    change rawStateBefore input [] data.target execution.frame a b = _ at h
    simpa only [executionFrame] using h
  have preserved (a b : Fin 4) :
      compare (ordinaryKeys input mol single c node data (ft.slotPerm a))
          (ordinaryKeys input mol single c node data (ft.slotPerm b)) =
        compare (ordinaryKeys input mol single c node data a)
          (ordinaryKeys input mol single c node data b) := by
    have h := rawStateBefore_transport input single graphAut sym [] [] (List.Perm.refl [])
      (by simp) data.target execution.center ft a b
    rw [fixedTarget, sourceFrame, imageFrame, keyMatrix, keyMatrix] at h
    exact Option.some.inj h
  refine ⟨ft.slotPerm, ?_, ?_⟩
  · intro i
    have h := atomAt_transport input single graphAut data.target execution.center ft i
    rw [sourceFrame, imageFrame, data.atomAt_eq, data.atomAt_eq, Option.map_some,
      relabelOf_val] at h
    exact Fin.ext (Option.some.inj h)
  · apply key_fixed_of_order_action
    intro a b lower
    apply (completeLigandRule5Key_compare_lt_iff _ _).mp
    rw [preserved]
    exact (completeLigandRule5Key_compare_lt_iff _ _).mpr lower

include agreement admissible supported reached historyFixed in
/-- A moved actual neighboring atom is eligible under the actual ordinary comparison. -/
theorem moved_neighbor_eligible (a : input.Atom) (neighbor : input.moleculeGraph.Adj c.1 a)
    (moved : (e : Equiv.Perm input.Atom) a ≠ a) :
    a.val ∈ eligibleOf data.atoms ((order input mol single c node data).map data.read.index)
      (adjacent input mol single c node data) := by
  obtain ⟨p, atoms, keys⟩ := actual_slot_key_action input mol agreement admissible supported single
    e c node data reached historyFixed
  obtain ⟨i, atAtom⟩ := input.detectedMultiCenterMolecule.ligandAtomAt_surjective c a neighbor
  let slot := data.ligandOf.symm i
  have reference : referenceAt input mol c node data slot = a := by
    simp only [referenceAt, slot, Equiv.apply_symm_apply, atAtom]
  have changed : p slot ≠ slot := by
    intro same
    have h := atoms slot
    rw [same, reference] at h
    exact moved h.symm
  have eligible := (eligible_iff_other input mol single c node data slot).mpr
    ⟨p slot, changed, keys slot⟩
  rw [eligible_eq]
  exact List.mem_map.mpr ⟨slot, eligible, congrArg Fin.val reference⟩

include agreement admissible supported reached historyFixed single data in
/-- This is actual recursive selection, not only carrier-branch membership. The caller
may use the raw first child constructed along a witnessed path. -/
theorem moved_child_selected (a : input.Atom) (neighbor : input.moleculeGraph.Adj c.1 a)
    (moved : (e : Equiv.Perm input.Atom) a ≠ a)
    (child : RawMolecule.CanonicalBranchNode) (actualChild : child ∈ mol.canonicalChildren node)
    (atChild : child.atom = a.val) :
    child ∈ tiedChildren mol (sparseOperations input mol) [] node := by
  have eligible := moved_neighbor_eligible input mol agreement admissible supported single e c node
    data reached historyFixed a neighbor moved
  unfold tiedChildren
  rw [data.rawFrame, ordinary_eq input mol single c node data]
  exact List.mem_filter.mpr ⟨actualChild, by simpa only [List.contains_iff_mem, atChild] using eligible⟩

include agreement admissible supported reached in
/-- The symmetry already reconstructed from actual comparison keys supplies the history
fixation and moved-neighbor premises. Only the concrete raw child still needs identifying. -/
theorem matched_child_selected (state : OccurrenceAuxState)
    (reference : input.Atom) (left right : Fin 4) (a b : input.Atom) (distinct : a ≠ b)
    (w : MatchedSymmetry input single state data.target data.real
      ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl reference left right a b)
    (child : RawMolecule.CanonicalBranchNode) (actualChild : child ∈ mol.canonicalChildren node)
    (atChild : child.atom = a.val) :
    child ∈ tiedChildren mol (sparseOperations input mol) [] node := by
  have fixed : ∀ atom ∈ node.history,
      relabelOf input (w.symmetry : Equiv.Perm input.Atom) atom = atom := by
    intro value member
    have correspondence := LocalizedMarkedCarrierLookup.lookup?_sound input node data.target data.found
    rw [← correspondence.history] at member
    obtain ⟨atom, present, valueEq⟩ := List.mem_map.mp member
    rw [← valueEq, relabelOf_val, w.fixedHistory atom present]
  let frame := frames input single state data.target data.real
    ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl
  have frameEq : frame.frame = data.frame :=
    Option.some.inj (frame.frameComputed.symm.trans data.frameExec)
  have atAtom : input.detectedMultiCenterMolecule.ligandAtomAt c (data.ligandOf left) = a := by
    have h := data.atomAt_eq left
    change (data.frame.cursorAt left).occurrence.1.node.current?.map Fin.val = _ at h
    have current := w.leftCurrent
    change (frame.frame.cursorAt left).occurrence.1.node.current? = some a at current
    rw [← frameEq, current, Option.map_some] at h
    exact Fin.ext (Option.some.inj h).symm
  have neighbor : input.moleculeGraph.Adj c.1 a := by
    rw [← atAtom]
    exact input.detectedMultiCenterMolecule.ligandAtomAt_adj c (data.ligandOf left)
  have moved : (w.symmetry : Equiv.Perm input.Atom) a ≠ a := by
    rw [w.entry]
    exact Ne.symm distinct
  exact moved_child_selected input mol agreement admissible supported single w.symmetry c node data
    reached fixed a neighbor moved child actualChild atChild

end
end TetraStereo.OneCenter.LocalizedChemicalRingMovedSlotEligibility

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMovedSlotEligibility.key_fixed_of_order_action
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMovedSlotEligibility.actual_slot_key_action
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMovedSlotEligibility.moved_neighbor_eligible
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMovedSlotEligibility.moved_child_selected
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingMovedSlotEligibility.matched_child_selected
