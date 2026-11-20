import TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback
import TetraStereo.OneCenter.LocalizedOutwardRerootDependencySupport
import TetraStereo.OneCenter.LocalizedMarkedRetainedCanonicalFrame
import TetraStereo.OneCenter.LocalizedOutwardDecoratedSourceFaithfulness
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
Neighbor sealing excludes a reference from actual outward cursor subtrees, including ring
duplicates. The cursor-to-official traversal is derived from incoming-parent provenance.
Together with the absent-reference key theorem this can remove a promoted marker from an
actual comparison. No statement about reference-independent generated labels is made here.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingSealedCursorReference

open CertifiedLocalizedCIPInput LocalizedActualBoundaryPathRealization
open LocalizedCumulativeDecoratedTree (LocalizedRerootCursorIncomingParent)
open LocalizedMarkedRetainedMolecularSelection (retainedCarrierFuel)

variable (input : CertifiedLocalizedCIPInput)

private abbrev Forward (a b : OfficialCIPNode input.Atom) : Prop :=
  b ∈ input.executableOfficialCIPChildren a

private theorem forward_history {a b : OfficialCIPNode input.Atom}
    (path : Relation.ReflTransGen (Forward input) a b) : a.history ⊆ b.history := by
  induction path with
  | refl => exact fun _ h => h
  | @tail parent child path edge ih =>
      obtain ⟨next, copy, same⟩ := MolecularEvidenceTree.executableOfficialCIPChildren_extend
        input parent child edge
      rw [same, OfficialCIPNode.extend_history]
      exact fun _ h => List.mem_cons_of_mem _ (ih h)

private theorem real_or_leaf {a b : OfficialCIPNode input.Atom}
    (real : a.provenance = .realAtom)
    (path : Relation.ReflTransGen (Forward input) a b) :
    b.provenance = .realAtom ∨ b.isDuplicateLeaf = true := by
  cases path with
  | refl => exact Or.inl real
  | tail before edge =>
      rename_i parent
      obtain ⟨next, copy, same⟩ := MolecularEvidenceTree.executableOfficialCIPChildren_extend
        input parent b edge
      by_cases childReal : b.provenance = .realAtom
      · exact Or.inl childReal
      · right
        rw [same] at childReal ⊢
        exact MolecularEvidenceTree.isDuplicateLeaf_extend_of_ne parent next copy childReal

private theorem real_strict_fresh {a b : OfficialCIPNode input.Atom}
    (path : Relation.TransGen (Forward input) a b) (real : b.provenance = .realAtom)
    {atom : input.Atom} (current : b.current? = some atom) : atom ∉ a.history := by
  have lastStep {parent child : OfficialCIPNode input.Atom}
      (before : a.history ⊆ parent.history) (edge : Forward input parent child)
      (childReal : child.provenance = .realAtom) (atAtom : child.current? = some atom) :
      atom ∉ a.history := by
    obtain ⟨next, copy, same⟩ := MolecularEvidenceTree.executableOfficialCIPChildren_extend
      input parent child edge
    rw [same, OfficialCIPNode.extend_current?, Option.some.injEq] at atAtom
    rw [same] at childReal
    have fresh := ((MolecularEvidenceTree.childProvenance_eq_realAtom_iff parent next copy).mp
      childReal).2
    rw [atAtom] at fresh
    exact fun h => fresh (before h)
  cases path with
  | single edge => exact lastStep (fun _ h => h) edge real current
  | @tail parent child path edge =>
      exact lastStep (forward_history input path.to_reflTransGen) edge real current

/-- A sealed reference cannot reappear anywhere in a forward official subtree, even
as a duplicate leaf. Immediate children are handled explicitly. -/
theorem official_reference_absent (source target : OfficialCIPNode input.Atom)
    (reference : input.Atom) (sourceReal : source.provenance = .realAtom)
    (sourceAbsent : source.current? ≠ some reference)
    (sealed : ∀ atom, input.moleculeGraph.Adj atom reference → atom ∈ source.history)
    (first : ∀ child ∈ input.executableOfficialCIPChildren source,
      child.current? ≠ some reference)
    (path : Relation.ReflTransGen (fun a b => b ∈ input.executableOfficialCIPChildren a)
      source target) : target.current? ≠ some reference := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp path with rfl | strict
  · exact sourceAbsent
  cases strict with
  | single edge => exact first _ edge
  | tail before edge =>
      rename_i parent
      intro atReference
      have parentReal : parent.provenance = .realAtom := by
        rcases real_or_leaf input sourceReal before.to_reflTransGen with real | leaf
        · exact real
        · have empty := MolecularEvidenceTree.executableOfficialCIPChildren_terminal input parent leaf
          rw [empty] at edge
          cases edge
      obtain ⟨atom, atAtom⟩ := exists_current_of_mem_children input edge
      have bonded := input.adj_of_mem_executableOfficialCIPChildren parent target atom reference
        atAtom atReference edge
      exact real_strict_fresh input before parentReal atAtom (sealed atom bonded)

private theorem incoming_edge {source child : input.LocalizedRerootCursor (retainedCarrierFuel input)}
    (incoming : LocalizedRerootCursorIncomingParent input source) (edge : E input source child) :
    LocalizedRerootCursorIncomingParent input child ∧
      child.occurrence.1.node ∈ input.executableOfficialCIPChildren source.occurrence.1.node := by
  have valid := input.localizedRerootCursorValid_of_incoming source incoming
  obtain ⟨previous, previousEq, previousRoot, previousAddress, previousLength⟩ := incoming
  obtain ⟨drop, length, root, prev, _⟩ := input.outward_edge source child valid previous previousEq
    (by omega) edge
  refine ⟨⟨source.occurrence, prev, root.symm, drop.symm, length.symm⟩, ?_⟩
  have member := (input.mem_localizedCarrierOutwardChildFrames_iff
    source.occurrence.1 child.occurrence.1).mpr ⟨child.occurrence.2, root, length, drop⟩
  have derived := (input.mem_localizedOccurrences_iff _ _).mp source.occurrence.2
  have positive := input.localizedOccurrences_remaining_pos_of_atomCount_le
    (Nat.le_succ _) source.occurrence.1 source.occurrence.2
  have perm := input.localizedOutwardChildFrames_nodes_perm_executable
    source.occurrence.1 derived positive
  exact perm.subset (List.mem_map_of_mem member)

/-- Every actual descendant of an incoming cursor follows the forward official expansion.
The incoming orientation is preserved by the executable cut-neighborhood itself. -/
theorem cursor_forward_path
    (source target : input.LocalizedRerootCursor (retainedCarrierFuel input))
    (incoming : LocalizedRerootCursorIncomingParent input source)
    (path : Relation.ReflTransGen (E input) source target) :
    Relation.ReflTransGen (fun a b => b ∈ input.executableOfficialCIPChildren a)
      source.occurrence.1.node target.occurrence.1.node := by
  have result : LocalizedRerootCursorIncomingParent input target ∧
      Relation.ReflTransGen (fun a b => b ∈ input.executableOfficialCIPChildren a)
        source.occurrence.1.node target.occurrence.1.node := by
    induction path with
    | refl => exact ⟨incoming, .refl⟩
    | @tail parent child path edge ih =>
        have next := incoming_edge input ih.1 edge
        exact ⟨next.1, ih.2.tail next.2⟩
  exact result.2

/-- Molecular neighbor sealing discharges reference absence over the exact executable
cursor relation used by the sparse promoted builder. Duplicate cursors are included. -/
theorem cursor_reference_absent
    (source target : input.LocalizedRerootCursor (retainedCarrierFuel input))
    (incoming : LocalizedRerootCursorIncomingParent input source)
    (reference : input.Atom) (sourceReal : source.occurrence.1.node.provenance = .realAtom)
    (sourceAbsent : source.occurrence.1.node.current? ≠ some reference)
    (sealed : ∀ atom, input.moleculeGraph.Adj atom reference → atom ∈ source.occurrence.1.node.history)
    (first : ∀ child ∈ input.executableOfficialCIPChildren source.occurrence.1.node,
      child.current? ≠ some reference)
    (path : Relation.ReflTransGen (E input) source target) :
    target.occurrence.1.node.current? ≠ some reference :=
  official_reference_absent input _ _ reference sourceReal sourceAbsent sealed first
    (cursor_forward_path input source target incoming path)

/-- A molecular nonadjacency check supplies immediate-child absence, leaving only local
graph/history facts as the reference-exclusion hypotheses. -/
theorem cursor_reference_absent_of_not_adjacent
    (source target : input.LocalizedRerootCursor (retainedCarrierFuel input))
    (incoming : LocalizedRerootCursorIncomingParent input source)
    (reference atom : input.Atom) (sourceReal : source.occurrence.1.node.provenance = .realAtom)
    (current : source.occurrence.1.node.current? = some atom) (different : atom ≠ reference)
    (sealed : ∀ neighbor, input.moleculeGraph.Adj neighbor reference →
      neighbor ∈ source.occurrence.1.node.history)
    (notAdjacent : ¬ input.moleculeGraph.Adj atom reference)
    (path : Relation.ReflTransGen (E input) source target) :
    target.occurrence.1.node.current? ≠ some reference := by
  apply cursor_reference_absent input source target incoming reference sourceReal _ sealed _ path
  · rw [current]
    exact fun h => different (Option.some.inj h)
  · intro child member atReference
    exact notAdjacent (input.adj_of_mem_executableOfficialCIPChildren
      source.occurrence.1.node child atom reference current atReference member)

end TetraStereo.OneCenter.LocalizedChemicalRingSealedCursorReference

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSealedCursorReference.official_reference_absent
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSealedCursorReference.cursor_forward_path
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSealedCursorReference.cursor_reference_absent
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSealedCursorReference.cursor_reference_absent_of_not_adjacent
