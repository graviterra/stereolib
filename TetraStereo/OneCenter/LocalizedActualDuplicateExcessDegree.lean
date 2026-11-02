import TetraStereo.OneCenter.LocalizedMultipleBondShapeRoleRecovery
import TetraStereo.OneCenter.LocalizedOccurrenceCarrierCoverage
import TetraStereo.OneCenter.LocalizedOccurrenceRerootFrame
import TetraStereo.OneCenter.LocalizedCumulativeTreeTableReconstruction
import TetraStereo.OneCenter.LocalizedOutwardDecoratedSourceFaithfulness
import TetraStereo.OneCenter.LocalizedRealizedTreeCutEmbedding
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput



















































/-! ## Positive-copy counting -/

/-- Boolean test for the multiple-bond duplicate provenance constructor.  Unlike
`OfficialCIPNodeProvenance.isDuplicateLeaf`, this test is false for ring duplicates and
placeholders. -/
def isMultipleBondDuplicateProvenance : OfficialCIPNodeProvenance → Bool
  | OfficialCIPNodeProvenance.multipleBondDuplicate _ => true
  | _ => false

@[simp] theorem isMultipleBondDuplicateProvenance_multipleBondDuplicate (distance : Nat) :
    isMultipleBondDuplicateProvenance
      (OfficialCIPNodeProvenance.multipleBondDuplicate distance) = true :=
  rfl

@[simp] theorem isMultipleBondDuplicateProvenance_realAtom :
    isMultipleBondDuplicateProvenance OfficialCIPNodeProvenance.realAtom = false :=
  rfl

@[simp] theorem isMultipleBondDuplicateProvenance_ringDuplicate (distance : Nat) :
    isMultipleBondDuplicateProvenance
      (OfficialCIPNodeProvenance.ringDuplicate distance) = false :=
  rfl

@[simp] theorem isMultipleBondDuplicateProvenance_placeholder
    (kind : OfficialPhantomNodeKind) (distance : Nat) :
    isMultipleBondDuplicateProvenance
      (OfficialCIPNodeProvenance.placeholder kind distance) = false :=
  rfl

/-- Number of copies whose copy index is positive.  This counts expansions of a copy coordinate,
not distinct node values: equal nodes produced by different copy indices are distinct entries of
the list and are counted separately. -/
def positiveCopyCount {α : Type*} (copies : List (α × Nat)) : Nat :=
  (copies.filter fun copy => copy.2 != 0).length

theorem positiveCopyCount_append {α : Type*}
    (first second : List (α × Nat)) :
    positiveCopyCount (first ++ second) =
      positiveCopyCount first + positiveCopyCount second := by
  unfold positiveCopyCount
  rw [List.filter_append, List.length_append]

/-- Counting positive copies commutes with a flattened family of copy lists. -/
theorem positiveCopyCount_flatMap {α β : Type*}
    (sources : List α) (copies : α → List (β × Nat)) :
    positiveCopyCount (sources.flatMap copies) =
      (sources.map fun source => positiveCopyCount (copies source)).sum := by
  induction sources with
  | nil => rfl
  | cons source sources ih =>
      rw [List.flatMap_cons, positiveCopyCount_append, ih]
      rfl

/-- Re-indexing a copy list by its index preserves the number of positive copies. -/
theorem positiveCopyCount_map_pairs {α : Type*}
    (indices : List Nat) (atom : α) :
    positiveCopyCount (indices.map fun index => (atom, index)) =
      (indices.filter fun index => index != 0).length := by
  unfold positiveCopyCount
  rw [List.filter_map, List.length_map]
  rfl

/-- Exactly `n - 1` indices in `0, ..., n - 1` are positive. -/
theorem length_filter_range_bne_zero (n : Nat) :
    ((List.range n).filter fun index => index != 0).length = n - 1 := by
  cases n with
  | zero => simp
  | succ k =>
      rw [List.range_succ_eq_map, List.filter_cons]
      have dropZero : (0 != 0) = false := by
        simp
      rw [dropZero]
      simp only [Bool.false_eq_true, ↓reduceIte, List.filter_map,
        List.length_map]
      simp only [Function.comp_def]
      have all : ((List.range k).filter fun index => Nat.succ index != 0) =
          List.range k := by
        apply List.filter_eq_self.mpr
        intro index _
        simp
      rw [all]
      simp

/-- A sorted enumeration has the same sum as the `Finset.sum` over the same finite set. -/
theorem list_sum_sort_eq_finset_sum {α : Type*} [LinearOrder α]
    (s : Finset α) (f : α → Nat) :
    ((s.sort (· ≤ ·)).map f).sum = s.sum f := by
  have permuted :
      List.Perm ((s.sort (· ≤ ·)).map f) (s.toList.map f) :=
    (Finset.sort_perm_toList (s := s) (r := (· ≤ ·))).map f
  rw [List.Perm.sum_nat permuted]
  change (s.1.toList.map f).sum = s.sum f
  rw [Multiset.sum_map_toList]
  exact (Finset.sum_mk s.1 s.2 f).symm

/-- The executable neighbor enumeration contains exactly the physical excess degree of the
current atom. -/
theorem positiveCopyCount_executableOfficialNeighborCopies
    (input : CertifiedLocalizedCIPInput) (atom : input.Atom) :
    positiveCopyCount (input.executableOfficialNeighborCopies atom) =
      (input.moleculeGraph.neighborFinset atom).sum
        (fun neighbor => input.moleculeGraph.bond atom neighbor - 1) := by
  unfold CertifiedLocalizedCIPInput.executableOfficialNeighborCopies
  rw [positiveCopyCount_flatMap]
  have inner : ∀ neighbor : input.Atom,
      positiveCopyCount
        ((List.range (input.moleculeGraph.bond atom neighbor)).map
          fun copyIndex => (neighbor, copyIndex)) =
      input.moleculeGraph.bond atom neighbor - 1 := by
    intro neighbor
    rw [positiveCopyCount_map_pairs]
    exact length_filter_range_bne_zero _
  simp only [inner]
  exact list_sum_sort_eq_finset_sum
    (s := input.moleculeGraph.neighborFinset atom)
    (f := fun neighbor => input.moleculeGraph.bond atom neighbor - 1)

/-- Removing the incoming parent's index-`0` copy does not remove any positive copy, even when
the parent atom is not a neighbor. -/
theorem positiveCopyCount_filter_parent_zero {α : Type*} [BEq α] [LawfulBEq α]
    (copies : List (α × Nat)) (parent : α) :
    positiveCopyCount
      (copies.filter fun copy => !(copy.1 == parent && copy.2 == 0)) =
      positiveCopyCount copies := by
  unfold positiveCopyCount
  rw [List.filter_filter]
  congr 1
  apply List.filter_congr
  rintro ⟨atom, index⟩ _
  by_cases zero : index = 0
  · subst zero
    simp
  · have positive : (index != 0) = true := by
      simp [zero]
    have notZero : (index == 0) = false := by
      simp [zero]
    simp [positive, notZero]

/-- The executable child enumeration keeps every positive copy of every neighbor of the current
atom.  The incoming parent contributes its positive copies as well; only its index-`0` copy is
removed, independently of whether that parent is a neighbor. -/
theorem positiveCopyCount_executableOfficialChildCopies
    (input : CertifiedLocalizedCIPInput) (node : OfficialCIPNode input.Atom)
    (current : input.Atom) (currentObserved : node.current? = some current) :
    positiveCopyCount (input.executableOfficialChildCopies node) =
      (input.moleculeGraph.neighborFinset current).sum
        (fun neighbor => input.moleculeGraph.bond current neighbor - 1) := by
  cases currentEq : node.current? with
  | none =>
      rw [currentEq] at currentObserved
      simp at currentObserved
  | some actual =>
      have same : actual = current := by
        simpa [currentEq] using currentObserved
      subst actual
      cases parentEq : node.parent? with
      | none =>
          simp only [CertifiedLocalizedCIPInput.executableOfficialChildCopies,
            currentEq, parentEq]
          exact positiveCopyCount_executableOfficialNeighborCopies input current
      | some parent =>
          simp only [CertifiedLocalizedCIPInput.executableOfficialChildCopies,
            currentEq, parentEq]
          rw [positiveCopyCount_filter_parent_zero,
            positiveCopyCount_executableOfficialNeighborCopies]

/-- Extending by a copy coordinate produces a multiple-bond duplicate exactly at positive copy
indices.  No acyclicity or freeness of the child atom is used. -/
theorem isMultipleBondDuplicateProvenance_extend {V : Type*} [DecidableEq V]
    (node : OfficialCIPNode V) (next : V) (copyIndex : Nat) :
    isMultipleBondDuplicateProvenance (node.extend next copyIndex).provenance =
      (copyIndex != 0) := by
  cases copyIndex with
  | zero =>
      by_cases visited : next ∈ node.history <;>
        simp [OfficialCIPNode.extend, OfficialCIPNode.childProvenance, visited,
          isMultipleBondDuplicateProvenance]
  | succ index =>
      rw [OfficialCIPNode.extend_provenance,
        OfficialCIPNode.childProvenance_copy_pos node next (Nat.succ_ne_zero index)]
      simp [isMultipleBondDuplicateProvenance]

/-- At a non-duplicate node, the executable official children contain exactly one
`multipleBondDuplicate` node for each positive copy coordinate. -/
theorem length_filter_executableOfficialCIPChildren_multipleBondDuplicate
    (input : CertifiedLocalizedCIPInput) (node : OfficialCIPNode input.Atom)
    (notDuplicate : node.isDuplicateLeaf = false) :
    ((input.executableOfficialCIPChildren node).filter
        fun child => isMultipleBondDuplicateProvenance child.provenance).length =
      positiveCopyCount (input.executableOfficialChildCopies node) := by
  have unfolded :
      input.executableOfficialCIPChildren node =
        (input.executableOfficialChildCopies node).map
          fun copy => node.extend copy.1 copy.2 := by
    simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren, notDuplicate,
      Bool.false_eq_true, ↓reduceIte]
  rw [unfolded, List.filter_map, List.length_map]
  unfold positiveCopyCount
  congr 1
  apply List.filter_congr
  intro copy _
  simp only [Function.comp_def, isMultipleBondDuplicateProvenance_extend]

/-! ## Imported local outward slot bijection

The local slot correspondence between carrier outward child frames and the executable official
child enumerator, together with the incoming-parent cut, is the prerequisite prefix of
`TetraStereo.OneCenter.LocalizedOutwardDecoratedSourceFaithfulness` (accepted terminal snapshot
`e9a54`).  Those declarations are imported above and are deliberately not reproduced here:
duplicating them would collide at joint import.  The declarations available from that import are
`localizedOutwardCanonicalFrame` (and its four equations),
`mem_localizedCarrierOutwardChildFrames_iff`,
`mem_localizedRerootNeighborFrames_filter_previous`,
`localizedOutwardChildFrames_nodes_perm_executable`,
`intendedLocalizedRerootChildFrames_perm_outward`, and
`intendedLocalizedRerootChildFrames_nodes_perm_executable`.
-/

open LocalizedCumulativeDecoratedTree

/-! ## Actual intended children versus the executable enumeration -/

/-- A genuine incoming coordinate is the actual carrier parent: same source root, one shorter
address, and the address obtained by dropping the cursor's final slot.  This is derived from cursor
validity plus strict address decrease; no equal-node identification is used. -/
theorem previous_address_eq_dropLast_of_valid
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : cursor.previous? = some previous)
    (valid : input.LocalizedRerootCursorValid cursor)
    (genuine : previous.1.address.length <
      cursor.occurrence.1.address.length) :
    previous.1.root = cursor.occurrence.1.root ∧
      previous.1.address.length + 1 = cursor.occurrence.1.address.length ∧
        previous.1.address = cursor.occurrence.1.address.dropLast := by
  have neighbor : cursor.occurrence.1 ∈
      input.localizedRerootNeighborFrames (fuel := carrierFuel) previous.1 := by
    unfold CertifiedLocalizedCIPInput.LocalizedRerootCursorValid at valid
    rw [previousEq] at valid
    change cursor.occurrence.1 ∈ input.localizedRerootNeighborFrames
      (fuel := carrierFuel) previous.1 at valid
    exact valid
  have adjacent :=
    (input.mem_localizedRerootNeighborFrames_iff previous.1
      cursor.occurrence.1).mp neighbor |>.2
  rcases adjacent with ⟨sameRoot, parent | outward⟩
  · exfalso
    omega
  · exact ⟨sameRoot.symm, outward.1, outward.2⟩

/-! ## Orientation-general duplicate-count invariance

Two list facts drive the general orientation.  First, cutting one recorded coordinate out of a
deduplicated neighborhood removes exactly one frame.  Second, every carrier parent frame is real,
so neither the retained parent of an upward traversal nor a real recorded incoming frame can be a
multiple-bond duplicate.  Hence filtering by `multipleBondDuplicate` is unaffected by the cut.
-/

namespace CertifiedLocalizedCIPInput




theorem parentFrame_provenance_real
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    {frame : input.LocalizedCIPOccurrenceFrame}
    (present : frame ∈ input.localizedCarrierParentFrames (fuel := fuel) target.1) :
    frame.node.provenance = OfficialCIPNodeProvenance.realAtom := by
  rw [localizedCarrierParentFrames, List.mem_filter] at present
  obtain ⟨frameMem, conditions⟩ := present
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at conditions
  obtain ⟨rootEq, lengthEq, addressEq⟩ := conditions
  have nonroot : target.1.address ≠ [] := by
    intro empty
    simp [empty] at lengthEq
  obtain ⟨certificate⟩ := input.exists_localizedParentFrameHistory target nonroot
  have frameDerived :=
    (input.mem_localizedOccurrences_iff fuel frame).mp frameMem
  have parentDerived :=
    (input.mem_localizedOccurrences_iff fuel certificate.parent.1).mp certificate.parent.2
  have frameEq : frame = certificate.parent.1 :=
    input.declarativeLocalizedOccurrence_functional_at_root_address
      frameDerived parentDerived
      (rootEq.trans certificate.parent_root.symm)
      (addressEq.trans certificate.parent_address.symm)
  rw [frameEq]
  exact certificate.parent_provenance input

end CertifiedLocalizedCIPInput

/-- **Count invariance under a cut of rejected elements.**  If every element rejected by `keep`
also fails `drop`, then applying `keep` before counting by `drop` does not change the count.  This
is the list-level core of the orientation-general duplicate count: the single cut coordinate is a
real frame, hence fails the multiple-bond-duplicate test. -/
theorem length_filter_filter_eq_of_false_on_removed {α : Type*}
    (list : List α) (keep drop : α → Bool)
    (removed : ∀ item ∈ list, keep item = false → drop item = false) :
    ((list.filter keep).filter drop).length = (list.filter drop).length := by
  rw [List.filter_filter]
  have same : ∀ item ∈ list, (drop item && keep item) = drop item := by
    intro item present
    cases dropItem : drop item with
    | false => simp
    | true =>
        have keepItem : keep item = true := by
          cases keepEq : keep item with
          | false =>
              rw [removed item present keepEq] at dropItem
              exact Bool.noConfusion dropItem
          | true => rfl
        simp [keepItem]
  exact congrArg List.length (List.filter_congr same)









theorem length_filter_intended_eq_executable_multipleBondDuplicate_of_real_incoming
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (sourceDerived : input.DeclarativeLocalizedOccurrence carrierFuel
      cursor.occurrence.1)
    (rootReal : cursor.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : cursor.previous? = some previous)
    (valid : input.LocalizedRerootCursorValid cursor)
    (previousReal : previous.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom) :
    ((input.intendedLocalizedRerootChildFrames cursor).filter fun frame =>
        isMultipleBondDuplicateProvenance frame.node.provenance).length =
      ((input.executableOfficialCIPChildren cursor.occurrence.1.node).filter fun child =>
        isMultipleBondDuplicateProvenance child.provenance).length := by
  have nonDuplicate : cursor.occurrence.1.node.isDuplicateLeaf = false :=
    input.isDuplicateLeaf_eq_false_of_provenance_real _ rootReal
  have cut : input.intendedLocalizedRerootChildFrames cursor =
      (input.localizedRerootNeighborFrames (fuel := carrierFuel)
        cursor.occurrence.1).filter
        (fun frame => frame.address != previous.1.address) := by
    simp [intendedLocalizedRerootChildFrames, nonDuplicate, previousEq]
  rw [cut]
  have neighborPrevious : cursor.occurrence.1 ∈
      input.localizedRerootNeighborFrames (fuel := carrierFuel) previous.1 := by
    unfold CertifiedLocalizedCIPInput.LocalizedRerootCursorValid at valid
    rw [previousEq] at valid
    exact valid
  have previousRoot : cursor.occurrence.1.root = previous.1.root :=
    ((input.mem_localizedRerootNeighborFrames_iff (fuel := carrierFuel)
      previous.1 cursor.occurrence.1).mp neighborPrevious).2.1
  have preserve :
      (((input.localizedRerootNeighborFrames (fuel := carrierFuel)
          cursor.occurrence.1).filter
          (fun frame => frame.address != previous.1.address)).filter
        (fun frame =>
          isMultipleBondDuplicateProvenance frame.node.provenance)).length =
      ((input.localizedRerootNeighborFrames (fuel := carrierFuel)
          cursor.occurrence.1).filter
        (fun frame =>
          isMultipleBondDuplicateProvenance frame.node.provenance)).length := by
    apply length_filter_filter_eq_of_false_on_removed
    intro frame present differentAddress
    have frameRoot : frame.root = cursor.occurrence.1.root :=
      ((input.mem_localizedRerootNeighborFrames_iff (fuel := carrierFuel)
        cursor.occurrence.1 frame).mp present).2.1
    have frameEq : frame = previous.1 :=
      input.declarativeLocalizedOccurrence_functional_at_root_address
        ((input.mem_localizedOccurrences_iff carrierFuel frame).mp
          (input.mem_localizedOccurrences_of_mem_localizedRerootNeighborFrames
            cursor.occurrence.1 frame present))
        ((input.mem_localizedOccurrences_iff carrierFuel previous.1).mp previous.2)
        (frameRoot.trans previousRoot)
        ((bne_eq_false_iff_eq).mp differentAddress)
    rw [frameEq, previousReal]
    exact isMultipleBondDuplicateProvenance_realAtom
  rw [preserve]
  have parentsZero :
      ((input.localizedCarrierParentFrames (fuel := carrierFuel)
          cursor.occurrence.1).filter
        (fun frame =>
          isMultipleBondDuplicateProvenance frame.node.provenance)).length = 0 := by
    have emptyFilter :
        ((input.localizedCarrierParentFrames (fuel := carrierFuel)
            cursor.occurrence.1).filter
          (fun frame =>
            isMultipleBondDuplicateProvenance frame.node.provenance)) = [] := by
      rw [List.filter_eq_nil_iff]
      intro frame present
      rw [input.parentFrame_provenance_real (fuel := carrierFuel)
        (frame := frame) cursor.occurrence present]
      simp
    rw [emptyFilter]
    rfl
  have neighborSplit :
      ((input.localizedRerootNeighborFrames (fuel := carrierFuel)
          cursor.occurrence.1).filter
        (fun frame =>
          isMultipleBondDuplicateProvenance frame.node.provenance)).length =
      ((input.localizedCarrierParentFrames (fuel := carrierFuel)
          cursor.occurrence.1).filter
        (fun frame =>
          isMultipleBondDuplicateProvenance frame.node.provenance)).length +
      ((input.localizedCarrierOutwardChildFrames (fuel := carrierFuel)
          cursor.occurrence.1).filter
        (fun frame =>
          isMultipleBondDuplicateProvenance frame.node.provenance)).length := by
    rw [CertifiedLocalizedCIPInput.localizedRerootNeighborFrames,
      List.filter_append, List.length_append]
  rw [neighborSplit, parentsZero, Nat.zero_add]
  have positive : 0 < cursor.occurrence.1.remaining :=
    input.multipleBondRealCarrierOccurrence_remaining_pos enough cursor.occurrence rootReal
  have permuted := input.localizedOutwardChildFrames_nodes_perm_executable
    cursor.occurrence.1 sourceDerived positive
  have filtered := (permuted.filter fun node =>
    isMultipleBondDuplicateProvenance node.provenance).length_eq
  simpa only [List.filter_map, Function.comp_def, List.length_map] using filtered

/-- At a real nonterminal cursor with a genuine incoming coordinate and adequate carrier fuel,
filtering the actual intended reroot child frames by multiple-bond provenance agrees with filtering
the executable official children.  The incoming parent coordinate is cut, but its positive bond
copies remain: only the parent's slot-`0` real edge is removed.  This is the outward-only
compatibility statement; the orientation-general form is
`length_filter_intended_eq_executable_multipleBondDuplicate_of_real_incoming`. -/
theorem length_filter_intended_eq_executable_multipleBondDuplicate
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (sourceDerived : input.DeclarativeLocalizedOccurrence carrierFuel
      cursor.occurrence.1)
    (rootReal : cursor.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : cursor.previous? = some previous)
    (valid : input.LocalizedRerootCursorValid cursor)
    (genuine : previous.1.address.length <
      cursor.occurrence.1.address.length) :
    ((input.intendedLocalizedRerootChildFrames cursor).filter fun frame =>
        isMultipleBondDuplicateProvenance frame.node.provenance).length =
      ((input.executableOfficialCIPChildren cursor.occurrence.1.node).filter fun child =>
        isMultipleBondDuplicateProvenance child.provenance).length := by
  obtain ⟨previousRoot, previousLength, previousAddress⟩ :=
    previous_address_eq_dropLast_of_valid input cursor previous previousEq valid genuine
  have nonDuplicate : cursor.occurrence.1.node.isDuplicateLeaf = false :=
    input.isDuplicateLeaf_eq_false_of_provenance_real _ rootReal
  have positive : 0 < cursor.occurrence.1.remaining :=
    input.multipleBondRealCarrierOccurrence_remaining_pos enough cursor.occurrence rootReal
  have permuted := input.intendedLocalizedRerootChildFrames_nodes_perm_executable
    cursor sourceDerived previous previousEq previousRoot previousAddress
    previousLength nonDuplicate positive
  have filtered := (permuted.filter fun node =>
    isMultipleBondDuplicateProvenance node.provenance).length_eq
  simpa only [List.filter_map, Function.comp_def, List.length_map] using filtered

/-! ## Actual and shape-side duplicate-child degrees -/

namespace LocalizedCumulativeBranchShape

/-- Number of immediate shape children whose visible Rule-1b distance equals the parent's.  This is
the shape-side duplicate-child degree: it reads only erased constitutional columns and does not
depend on a reader, a cursor, or provenance. -/
def immediateDuplicateChildCount (shape : LocalizedCumulativeBranchShape) : Nat :=
  (shape.children.filter fun child =>
    child.rule1bDistance == shape.rule1bDistance).length

end LocalizedCumulativeBranchShape

namespace LocalizedCumulativeDecoratedTree

/-- Number of actual immediate children whose provenance is a multiple-bond duplicate.  Slot
occurrences are counted, so distinct copy indices with equal node values are counted separately. -/
def actualImmediateMultipleBondChildCount {input : CertifiedLocalizedCIPInput}
    {carrierFuel : Nat}
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) : Nat :=
  (tree.children.filter fun child =>
    isMultipleBondDuplicateProvenance
      child.source.occurrence.1.node.provenance).length

/-- **Actual multiple-bond duplicate excess degree.**  At a realized decorated tree whose root
cursor is a real source node, with a genuine real incoming coordinate and carrier fuel at least the
molecule's atom count, the actual number of immediate `multipleBondDuplicate` children equals the
physical excess degree of the root's current atom,
`∑ u ∈ neighborFinset v, (bond v u - 1)`.  The incoming bond contributes its positive copies; only
its slot-`0` real edge is cut.  This is the outward-only compatibility statement; see
`actualImmediateMultipleBondChildCount_eq_neighborExcessSum_of_real_incoming` for the general
orientation. -/
theorem actualImmediateMultipleBondChildCount_eq_neighborExcessSum
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (_acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (rootReal : tree.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (incoming : tree.source.previous? = some previous)
    (_previousReal : previous.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (genuine : previous.1.address.length <
      tree.source.occurrence.1.address.length)
    (v : input.Atom)
    (current : tree.source.occurrence.1.node.current? = some v) :
    tree.actualImmediateMultipleBondChildCount =
      (input.moleculeGraph.neighborFinset v).sum
        (fun neighbor => input.moleculeGraph.bond v neighbor - 1) := by
  cases realizes with
  | mk cursor children sortedChildren childrenComputed sourcePerm childrenRealize =>
      have declarative :=
        input.localizedRerootChildren?_sound cursor children childrenComputed
      simp only [localizedRootTree] at rootReal incoming valid genuine current ⊢
      have sourceDerived : input.DeclarativeLocalizedOccurrence carrierFuel
          cursor.occurrence.1 :=
        (input.mem_localizedOccurrences_iff carrierFuel
          cursor.occurrence.1).mp cursor.occurrence.2
      have cursorNotDup : cursor.occurrence.1.node.isDuplicateLeaf = false :=
        input.isDuplicateLeaf_eq_false_of_provenance_real _ rootReal
      have physical :=
        positiveCopyCount_executableOfficialChildCopies input
          cursor.occurrence.1.node v current
      have executableCount :=
        length_filter_executableOfficialCIPChildren_multipleBondDuplicate input
          cursor.occurrence.1.node cursorNotDup
      have intendedCount :=
        length_filter_intended_eq_executable_multipleBondDuplicate input enough
          cursor sourceDerived rootReal previous incoming valid genuine
      have sortedCount :
          (sortedChildren.filter fun child =>
            isMultipleBondDuplicateProvenance
              child.source.occurrence.1.node.provenance).length =
          (children.filter fun child =>
            isMultipleBondDuplicateProvenance
              child.occurrence.1.node.provenance).length := by
        have filtered := (sourcePerm.filter fun occurrence =>
          isMultipleBondDuplicateProvenance
            occurrence.occurrence.1.node.provenance).length_eq
        simpa only [List.filter_map, Function.comp_def, List.length_map]
          using filtered
      have childrenCount :
          (children.filter fun child =>
            isMultipleBondDuplicateProvenance
              child.occurrence.1.node.provenance).length =
          ((input.intendedLocalizedRerootChildFrames cursor).filter fun frame =>
            isMultipleBondDuplicateProvenance frame.node.provenance).length := by
        have mapped :
            ((children.map fun child => child.occurrence.1).filter fun frame =>
                isMultipleBondDuplicateProvenance frame.node.provenance).length =
              (children.filter fun child =>
                isMultipleBondDuplicateProvenance
                  child.occurrence.1.node.provenance).length := by
          simp only [List.filter_map, Function.comp_def, List.length_map]
        rw [← mapped, declarative.1]
      simp only [actualImmediateMultipleBondChildCount]
      rw [sortedCount, childrenCount, intendedCount, executableCount, physical]

/-- **Orientation-general actual multiple-bond duplicate excess degree.**  At a realized decorated
tree whose root cursor is a real source node, with carrier fuel at least the molecule's atom count
and an actual recorded real incoming coordinate, the actual number of immediate
`multipleBondDuplicate` children equals the physical excess degree
`∑ u ∈ neighborFinset v, (bond v u - 1)`.

The incoming coordinate may be the retained carrier parent of an upward traversal (its address
longer than the cursor's) as well as an already-cut outward child (shorter address).  No address
order is assumed: the cut removes only a real frame, and every retained carrier parent is real, so
the positive-copy count is unchanged.  The concrete child correspondence is derived from the actual
realization, never assumed. -/
theorem actualImmediateMultipleBondChildCount_eq_neighborExcessSum_of_real_incoming
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (rootReal : tree.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (incoming : tree.source.previous? = some previous)
    (previousReal : previous.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (v : input.Atom)
    (current : tree.source.occurrence.1.node.current? = some v) :
    tree.actualImmediateMultipleBondChildCount =
      (input.moleculeGraph.neighborFinset v).sum
        (fun neighbor => input.moleculeGraph.bond v neighbor - 1) := by
  cases realizes with
  | mk cursor children sortedChildren childrenComputed sourcePerm childrenRealize =>
      have declarative :=
        input.localizedRerootChildren?_sound cursor children childrenComputed
      simp only [localizedRootTree] at rootReal incoming valid current ⊢
      have sourceDerived : input.DeclarativeLocalizedOccurrence carrierFuel
          cursor.occurrence.1 :=
        (input.mem_localizedOccurrences_iff carrierFuel
          cursor.occurrence.1).mp cursor.occurrence.2
      have cursorNotDup : cursor.occurrence.1.node.isDuplicateLeaf = false :=
        input.isDuplicateLeaf_eq_false_of_provenance_real _ rootReal
      have physical :=
        positiveCopyCount_executableOfficialChildCopies input
          cursor.occurrence.1.node v current
      have executableCount :=
        length_filter_executableOfficialCIPChildren_multipleBondDuplicate input
          cursor.occurrence.1.node cursorNotDup
      have intendedCount :=
        length_filter_intended_eq_executable_multipleBondDuplicate_of_real_incoming
          input enough cursor sourceDerived rootReal previous incoming valid previousReal
      have sortedCount :
          (sortedChildren.filter fun child =>
            isMultipleBondDuplicateProvenance
              child.source.occurrence.1.node.provenance).length =
          (children.filter fun child =>
            isMultipleBondDuplicateProvenance
              child.occurrence.1.node.provenance).length := by
        have filtered := (sourcePerm.filter fun occurrence =>
          isMultipleBondDuplicateProvenance
            occurrence.occurrence.1.node.provenance).length_eq
        simpa only [List.filter_map, Function.comp_def, List.length_map]
          using filtered
      have childrenCount :
          (children.filter fun child =>
            isMultipleBondDuplicateProvenance
              child.occurrence.1.node.provenance).length =
          ((input.intendedLocalizedRerootChildFrames cursor).filter fun frame =>
            isMultipleBondDuplicateProvenance frame.node.provenance).length := by
        have mapped :
            ((children.map fun child => child.occurrence.1).filter fun frame =>
                isMultipleBondDuplicateProvenance frame.node.provenance).length =
              (children.filter fun child =>
                isMultipleBondDuplicateProvenance
                  child.occurrence.1.node.provenance).length := by
          simp only [List.filter_map, Function.comp_def, List.length_map]
        rw [← mapped, declarative.1]
      simp only [actualImmediateMultipleBondChildCount]
      rw [sortedCount, childrenCount, intendedCount, executableCount, physical]

/-- **Shape-side duplicate-child count.**  The actual multiple-bond duplicate-child count equals the
number of immediate shape children whose visible Rule-1b distance equals the parent's.  Each child
is classified by the accepted real-cursor role recovery, so no cursor identity, neighbor
multiplicity, or duplicate-fiber pairing is used. -/
theorem actualImmediateMultipleBondChildCount_eq_immediateDuplicateChildCount
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (acyclic : input.moleculeGraph.Acyclic)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (rootReal : tree.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom) :
    tree.actualImmediateMultipleBondChildCount =
      (shape tree).immediateDuplicateChildCount := by
  cases realizes with
  | mk cursor children sortedChildren childrenComputed sourcePerm childrenRealize =>
      have declarative :=
        input.localizedRerootChildren?_sound cursor children childrenComputed
      simp only [localizedRootTree] at rootReal ⊢
      have childIntended : ∀ child ∈ sortedChildren,
          child.source.occurrence.1 ∈
            input.intendedLocalizedRerootChildFrames cursor := by
        intro child childPresent
        have memMap : child.source ∈
            sortedChildren.map (fun tree => tree.source) :=
          List.mem_map.mpr ⟨child, childPresent, rfl⟩
        have memChildren : child.source ∈ children :=
          sourcePerm.mem_iff.mp memMap
        have mapped : child.source.occurrence.1 ∈
            children.map (fun child => child.occurrence.1) :=
          List.mem_map.mpr ⟨child.source, memChildren, rfl⟩
        rwa [declarative.1] at mapped
      have childFacts : ∀ child ∈ sortedChildren,
          isMultipleBondDuplicateProvenance
              child.source.occurrence.1.node.provenance =
            (child.rule1bDistance ==
              cursor.occurrence.1.node.rule1bRootDistance) := by
        intro child childPresent
        have childDistance : child.rule1bDistance =
            child.source.occurrence.1.node.rule1bRootDistance :=
          tree_rule1bDistance_eq_source (childrenRealize child childPresent)
        rcases input.child_role_recovery_of_real_cursor acyclic cursor rootReal
          child.source.occurrence.1 (childIntended child childPresent) with
          ⟨real, distance, _⟩ | ⟨d, provenance, distance, _⟩ |
            ⟨real, distance, _⟩
        · have isNot : isMultipleBondDuplicateProvenance
              child.source.occurrence.1.node.provenance = false := by
            rw [real]
            rfl
          have notEqual : (child.rule1bDistance ==
              cursor.occurrence.1.node.rule1bRootDistance) = false := by
            rw [childDistance, distance]
            exact beq_eq_false_iff_ne.mpr (by omega)
          simp only [isNot, notEqual]
        · have isDup : isMultipleBondDuplicateProvenance
              child.source.occurrence.1.node.provenance = true := by
            rw [provenance]
            rfl
          have equal : (child.rule1bDistance ==
              cursor.occurrence.1.node.rule1bRootDistance) = true := by
            rw [childDistance, distance]
            exact beq_self_eq_true _
          simp only [isDup, equal]
        · have isNot : isMultipleBondDuplicateProvenance
              child.source.occurrence.1.node.provenance = false := by
            rw [real]
            rfl
          have notEqual : (child.rule1bDistance ==
              cursor.occurrence.1.node.rule1bRootDistance) = false := by
            rw [childDistance]
            exact beq_eq_false_iff_ne.mpr (by omega)
          simp only [isNot, notEqual]
      simp only [actualImmediateMultipleBondChildCount]
      simp only [LocalizedCumulativeBranchShape.immediateDuplicateChildCount,
        table_shape_mk, table_shapeList_eq_map, List.filter_map, List.length_map]
      apply congrArg List.length
      apply List.filter_congr
      intro child childPresent
      simp only [Function.comp_apply]
      rw [table_shape_rule1bDistance child]
      exact childFacts child childPresent

/-- **Equal erased shape gives equal actual duplicate-child counts.**  The two realized trees may be
produced under different auxiliary-label readers; no reader equality is assumed. -/
theorem actualImmediateMultipleBondChildCount_eq_of_shape_eq_independent_readers
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {readRight : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel}
    (acyclic : input.moleculeGraph.Acyclic)
    (left right : LocalizedCumulativeDecoratedTree input carrierFuel)
    (leftRealizes : LocalizedCumulativeTreeRealizes input read left)
    (rightRealizes : LocalizedCumulativeTreeRealizes input readRight right)
    (leftRootReal : left.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (rightRootReal : right.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (sameShape : shape left = shape right) :
    left.actualImmediateMultipleBondChildCount =
      right.actualImmediateMultipleBondChildCount := by
  rw [actualImmediateMultipleBondChildCount_eq_immediateDuplicateChildCount
      (tree := left) acyclic leftRealizes leftRootReal,
    actualImmediateMultipleBondChildCount_eq_immediateDuplicateChildCount
      (tree := right) acyclic rightRealizes rightRootReal]
  exact congrArg
    LocalizedCumulativeBranchShape.immediateDuplicateChildCount sameShape

end LocalizedCumulativeDecoratedTree

/-- **Physical excess-sum equality from equal shape.**  Two realized real-root trees with the same
erased shape have equal physical excess degree at their real current atoms, even under different
auxiliary readers.  This composes the actual duplicate-child count with the physical sum formula; it
does not identify which physical neighbor each duplicate copy belongs to.  This is the outward-only
compatibility statement; see `neighborExcessSum_eq_of_shape_eq_of_real_incoming` for the general
orientation. -/
theorem neighborExcessSum_eq_of_shape_eq
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {readRight : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel}
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (left right : LocalizedCumulativeDecoratedTree input carrierFuel)
    (leftRealizes : LocalizedCumulativeTreeRealizes input read left)
    (rightRealizes : LocalizedCumulativeTreeRealizes input readRight right)
    (leftRootReal : left.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (rightRootReal : right.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (leftPrevious : input.LocalizedCIPOccurrence carrierFuel)
    (leftIncoming : left.source.previous? = some leftPrevious)
    (leftPreviousReal : leftPrevious.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (leftValid : input.LocalizedRerootCursorValid left.source)
    (leftGenuine : leftPrevious.1.address.length <
      left.source.occurrence.1.address.length)
    (leftV : input.Atom)
    (leftCurrent : left.source.occurrence.1.node.current? = some leftV)
    (rightPrevious : input.LocalizedCIPOccurrence carrierFuel)
    (rightIncoming : right.source.previous? = some rightPrevious)
    (rightPreviousReal : rightPrevious.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (rightValid : input.LocalizedRerootCursorValid right.source)
    (rightGenuine : rightPrevious.1.address.length <
      right.source.occurrence.1.address.length)
    (rightV : input.Atom)
    (rightCurrent : right.source.occurrence.1.node.current? = some rightV)
    (sameShape : LocalizedCumulativeDecoratedTree.shape left =
      LocalizedCumulativeDecoratedTree.shape right) :
    (input.moleculeGraph.neighborFinset leftV).sum
        (fun neighbor => input.moleculeGraph.bond leftV neighbor - 1) =
      (input.moleculeGraph.neighborFinset rightV).sum
        (fun neighbor => input.moleculeGraph.bond rightV neighbor - 1) := by
  have leftCount :=
    LocalizedCumulativeDecoratedTree.actualImmediateMultipleBondChildCount_eq_neighborExcessSum
      acyclic enough left leftRealizes leftRootReal leftPrevious leftIncoming
      leftPreviousReal leftValid leftGenuine leftV leftCurrent
  have rightCount :=
    LocalizedCumulativeDecoratedTree.actualImmediateMultipleBondChildCount_eq_neighborExcessSum
      acyclic enough right rightRealizes rightRootReal rightPrevious rightIncoming
      rightPreviousReal rightValid rightGenuine rightV rightCurrent
  have sameCount :=
    LocalizedCumulativeDecoratedTree.actualImmediateMultipleBondChildCount_eq_of_shape_eq_independent_readers
      acyclic left right leftRealizes rightRealizes leftRootReal rightRootReal
      sameShape
  rw [← leftCount, ← rightCount]
  exact sameCount

/-- **Orientation-general physical excess-sum equality from equal shape.**  The two realized
real-root trees may have arbitrary real incoming coordinates at their roots: a retained carrier
parent of an upward traversal as well as a cut outward child.  Only the actual real incoming
coordinate, its validity, and its real provenance are required; no address-order condition, desired
child correspondence, source permutation, or reader agreement is assumed.  The count identity and
the concrete source permutation are derived inside the proof. -/
theorem neighborExcessSum_eq_of_shape_eq_of_real_incoming
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {readRight : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel}
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (left right : LocalizedCumulativeDecoratedTree input carrierFuel)
    (leftRealizes : LocalizedCumulativeTreeRealizes input read left)
    (rightRealizes : LocalizedCumulativeTreeRealizes input readRight right)
    (leftRootReal : left.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (rightRootReal : right.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (leftPrevious : input.LocalizedCIPOccurrence carrierFuel)
    (leftIncoming : left.source.previous? = some leftPrevious)
    (leftPreviousReal : leftPrevious.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (leftValid : input.LocalizedRerootCursorValid left.source)
    (leftV : input.Atom)
    (leftCurrent : left.source.occurrence.1.node.current? = some leftV)
    (rightPrevious : input.LocalizedCIPOccurrence carrierFuel)
    (rightIncoming : right.source.previous? = some rightPrevious)
    (rightPreviousReal : rightPrevious.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (rightValid : input.LocalizedRerootCursorValid right.source)
    (rightV : input.Atom)
    (rightCurrent : right.source.occurrence.1.node.current? = some rightV)
    (sameShape : LocalizedCumulativeDecoratedTree.shape left =
      LocalizedCumulativeDecoratedTree.shape right) :
    (input.moleculeGraph.neighborFinset leftV).sum
        (fun neighbor => input.moleculeGraph.bond leftV neighbor - 1) =
      (input.moleculeGraph.neighborFinset rightV).sum
        (fun neighbor => input.moleculeGraph.bond rightV neighbor - 1) := by
  have leftCount :=
    LocalizedCumulativeDecoratedTree.actualImmediateMultipleBondChildCount_eq_neighborExcessSum_of_real_incoming
      enough left leftRealizes leftRootReal leftPrevious leftIncoming
      leftPreviousReal leftValid leftV leftCurrent
  have rightCount :=
    LocalizedCumulativeDecoratedTree.actualImmediateMultipleBondChildCount_eq_neighborExcessSum_of_real_incoming
      enough right rightRealizes rightRootReal rightPrevious rightIncoming
      rightPreviousReal rightValid rightV rightCurrent
  have sameCount :=
    LocalizedCumulativeDecoratedTree.actualImmediateMultipleBondChildCount_eq_of_shape_eq_independent_readers
      acyclic left right leftRealizes rightRealizes leftRootReal rightRootReal
      sameShape
  rw [← leftCount, ← rightCount]
  exact sameCount

/-! ## Per-position incoming-real API

The orientation-general count takes the recorded incoming coordinate and its real provenance
explicitly.  Inside an actual realized tree the recorded incoming coordinate of every child is the
parent cursor's occurrence, so at every position below a real node the incoming-real fact is
derived, never assumed.  The parent's own cursor validity is available as
`child_valid_of_child`.
-/

/-- **Every actual child has a real recorded previous coordinate.**  For a realized tree whose root
occurrence is real, each immediate child's `previous?` is the root occurrence itself and hence
carries `realAtom` provenance.  This supplies the incoming-real premise of the orientation-general
count at every position below a real tree root. -/
theorem exists_child_previous_real_of_rootReal
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    {slot : Nat} {child : LocalizedCumulativeDecoratedTree input carrierFuel}
    (lookup : tree.children[slot]? = some child)
    (rootReal : tree.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom) :
    ∃ previous : input.LocalizedCIPOccurrence carrierFuel,
      child.source.previous? = some previous ∧
        previous.1.node.provenance = OfficialCIPNodeProvenance.realAtom :=
  ⟨tree.source.occurrence, child_previous_of_child realizes lookup, rootReal⟩

assert_kernel_only TetraStereo.OneCenter.isMultipleBondDuplicateProvenance
assert_kernel_only TetraStereo.OneCenter.isMultipleBondDuplicateProvenance_multipleBondDuplicate
assert_kernel_only TetraStereo.OneCenter.isMultipleBondDuplicateProvenance_realAtom
assert_kernel_only TetraStereo.OneCenter.isMultipleBondDuplicateProvenance_ringDuplicate
assert_kernel_only TetraStereo.OneCenter.isMultipleBondDuplicateProvenance_placeholder
assert_kernel_only TetraStereo.OneCenter.positiveCopyCount
assert_kernel_only TetraStereo.OneCenter.positiveCopyCount_append
assert_kernel_only TetraStereo.OneCenter.positiveCopyCount_flatMap
assert_kernel_only TetraStereo.OneCenter.positiveCopyCount_map_pairs
assert_kernel_only TetraStereo.OneCenter.length_filter_range_bne_zero
assert_kernel_only TetraStereo.OneCenter.list_sum_sort_eq_finset_sum
assert_kernel_only TetraStereo.OneCenter.positiveCopyCount_executableOfficialNeighborCopies
assert_kernel_only TetraStereo.OneCenter.positiveCopyCount_filter_parent_zero
assert_kernel_only TetraStereo.OneCenter.positiveCopyCount_executableOfficialChildCopies
assert_kernel_only TetraStereo.OneCenter.isMultipleBondDuplicateProvenance_extend
assert_kernel_only TetraStereo.OneCenter.length_filter_executableOfficialCIPChildren_multipleBondDuplicate
assert_kernel_only TetraStereo.OneCenter.previous_address_eq_dropLast_of_valid
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.parentFrame_provenance_real
assert_kernel_only TetraStereo.OneCenter.length_filter_filter_eq_of_false_on_removed
assert_kernel_only TetraStereo.OneCenter.length_filter_intended_eq_executable_multipleBondDuplicate_of_real_incoming
assert_kernel_only TetraStereo.OneCenter.length_filter_intended_eq_executable_multipleBondDuplicate
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeBranchShape.immediateDuplicateChildCount
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.actualImmediateMultipleBondChildCount
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.actualImmediateMultipleBondChildCount_eq_neighborExcessSum
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.actualImmediateMultipleBondChildCount_eq_neighborExcessSum_of_real_incoming
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.actualImmediateMultipleBondChildCount_eq_immediateDuplicateChildCount
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.actualImmediateMultipleBondChildCount_eq_of_shape_eq_independent_readers
assert_kernel_only TetraStereo.OneCenter.neighborExcessSum_eq_of_shape_eq
assert_kernel_only TetraStereo.OneCenter.neighborExcessSum_eq_of_shape_eq_of_real_incoming
assert_kernel_only TetraStereo.OneCenter.exists_child_previous_real_of_rootReal

end TetraStereo.OneCenter
