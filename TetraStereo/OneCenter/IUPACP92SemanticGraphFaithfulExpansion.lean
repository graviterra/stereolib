import TetraStereo.OneCenter.AuthoritativeLocalizedRule1bConformance
import TetraStereo.OneCenter.ProductionCIPFaithfulAssembly
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

open scoped List

/-!
# Graph-native official P-92 hierarchy expansion

This module removes the semantic-source wrapper from the constitutional hierarchy compiler.
For an arbitrary finite `MoleculeGraph (Fin atomCount)` it provides a kernel-executable canonical
child enumeration, proves that enumeration permutation-equivalent to `officialCIPChildren`, and
uses the established finite-atom exhaustion theorem to construct a direct fuel-bounded recursive
`OfficialCIPSourceTree` without priority-sorting its siblings.

The results below mention neither a parser nor an IUPAC provision judgment.  They are the physical
graph layer consumed by the assumption-free eleven-row P-92 production realization.

The occurrence equivalence carried by the recursive source tree transports the indexed official
copy counts to exact declarative child multiplicities.  Together with the local semantics and the
all-addressing duplicate-distance theorem, this yields an unconditional graph-native
`FaithfulExactExpansion` for every distinct adjacent center/ligand pair.
-/

namespace MoleculeGraph

variable {atomCount : Nat}

/-- Canonical executable neighbor copies for a `Fin`-indexed molecule graph.  Sorting the neighbor
finset by the canonical `Fin` order avoids the proof-facing `Finset.toList` choice. -/
def semanticOfficialNeighborCopies (molecule : MoleculeGraph (Fin atomCount))
    (atom : Fin atomCount) : List (Fin atomCount × Nat) :=
  (molecule.neighborFinset atom).sort (· ≤ ·) |>.flatMap fun neighbor =>
    (List.range (molecule.bond atom neighbor)).map fun copyIndex =>
      (neighbor, copyIndex)

/-- The executable and proof-facing neighbor-copy lists have identical multiplicity. -/
theorem semanticOfficialNeighborCopies_perm_officialNeighborCopies
    (molecule : MoleculeGraph (Fin atomCount)) (atom : Fin atomCount) :
    List.Perm (molecule.semanticOfficialNeighborCopies atom)
      (molecule.officialNeighborCopies atom) := by
  unfold semanticOfficialNeighborCopies officialNeighborCopies
  exact
    (Finset.sort_perm_toList (molecule.neighborFinset atom) (· ≤ ·)).flatMap_right
      (fun neighbor =>
        (List.range (molecule.bond atom neighbor)).map fun copyIndex =>
          (neighbor, copyIndex))

/-- Canonical executable child copies, with exactly the zero-index back edge suppressed. -/
def semanticOfficialChildCopies (molecule : MoleculeGraph (Fin atomCount))
    (node : OfficialCIPNode (Fin atomCount)) : List (Fin atomCount × Nat) :=
  match node.current? with
  | none => []
  | some current =>
      match node.parent? with
      | none => molecule.semanticOfficialNeighborCopies current
      | some parent =>
          (molecule.semanticOfficialNeighborCopies current).filter fun copy =>
            !(copy.1 == parent && copy.2 == 0)

private theorem mappedPair_count_atom_where
    (neighbor target : Fin atomCount) (indexPredicate : Nat → Bool) :
    ∀ indices : List Nat,
      (indices.map fun copyIndex => (neighbor, copyIndex)).countP
          (fun copy => (copy.1 == target) && indexPredicate copy.2) =
        if neighbor = target then indices.countP indexPredicate else 0
  | [] => by simp
  | index :: indices => by
      simp only [List.map_cons, List.countP_cons]
      rw [mappedPair_count_atom_where neighbor target indexPredicate indices]
      by_cases same : neighbor = target
      · subst neighbor
        simp
      · simp [same]

private theorem semanticNeighborCopy_count_where_aux
    (molecule : MoleculeGraph (Fin atomCount)) (parent target : Fin atomCount)
    (indexPredicate : Nat → Bool) :
    ∀ neighbors : List (Fin atomCount), neighbors.Nodup →
      (neighbors.flatMap fun neighbor =>
          (List.range (molecule.bond parent neighbor)).map fun copyIndex =>
            (neighbor, copyIndex)).countP
            (fun copy => (copy.1 == target) && indexPredicate copy.2) =
        if target ∈ neighbors then
          (List.range (molecule.bond parent target)).countP indexPredicate
        else 0
  | [], _ => by simp
  | neighbor :: neighbors, nodup => by
      have tailNodup := (List.nodup_cons.mp nodup).2
      have targetAbsent := (List.nodup_cons.mp nodup).1
      rw [List.flatMap_cons, List.countP_append,
        mappedPair_count_atom_where neighbor target indexPredicate,
        semanticNeighborCopy_count_where_aux molecule parent target indexPredicate
          neighbors tailNodup]
      by_cases same : neighbor = target
      · subst neighbor
        simp [targetAbsent]
      · have reverse : target ≠ neighbor := Ne.symm same
        simp [same, reverse]

/-- Reusable exact occurrence count for the canonical neighbor-copy enumeration. -/
theorem semanticOfficialNeighborCopies_count_atom_where
    (molecule : MoleculeGraph (Fin atomCount)) (parent target : Fin atomCount)
    (indexPredicate : Nat → Bool) :
    (molecule.semanticOfficialNeighborCopies parent).countP
        (fun copy => (copy.1 == target) && indexPredicate copy.2) =
      (List.range (molecule.bond parent target)).countP indexPredicate := by
  unfold semanticOfficialNeighborCopies
  rw [semanticNeighborCopy_count_where_aux molecule parent target indexPredicate
    ((molecule.neighborFinset parent).sort (· ≤ ·))
    (Finset.sort_nodup (molecule.neighborFinset parent) (· ≤ ·))]
  by_cases adjacent : molecule.Adj parent target
  · have present : target ∈ (molecule.neighborFinset parent).sort (· ≤ ·) :=
      (Finset.mem_sort (r := (· ≤ ·))).mpr
        ((molecule.mem_neighborFinset parent target).mpr adjacent)
    simp [present]
  · have absent : target ∉ (molecule.neighborFinset parent).sort (· ≤ ·) := by
      intro present
      exact adjacent ((molecule.mem_neighborFinset parent target).mp
        ((Finset.mem_sort (r := (· ≤ ·))).mp present))
    have zero : molecule.bond parent target = 0 := by
      apply Nat.eq_zero_of_not_pos
      simpa [MoleculeGraph.Adj] using adjacent
    simp [absent, zero]

private theorem range_countP_not_zero (length : Nat) :
    (List.range length).countP (fun index => index != 0) = length - 1 := by
  induction length with
  | zero => simp
  | succ length inductionHypothesis =>
      rw [List.range_succ, List.countP_append, inductionHypothesis]
      cases length <;> simp

private theorem range_countP_zero (length : Nat) :
    (List.range length).countP (fun index => index == 0) =
      if 0 < length then 1 else 0 := by
  induction length with
  | zero => simp
  | succ length inductionHypothesis =>
      rw [List.range_succ, List.countP_append, inductionHypothesis]
      cases length <;> simp

private theorem countP_filter_eq_countP_and {α : Type*}
    (keep test : α → Bool) : ∀ values : List α,
    (values.filter keep).countP test =
      values.countP fun value => keep value && test value
  | [] => rfl
  | value :: values => by
      simp only [List.filter_cons, List.countP_cons]
      cases keepObserved : keep value <;> cases testObserved : test value <;>
        simp [testObserved,
          countP_filter_eq_countP_and keep test values]

/-- Exact indexed-copy count after suppressing the zero-index immediate-parent occurrence. -/
theorem semanticOfficialChildCopies_count_atom_where
    (molecule : MoleculeGraph (Fin atomCount))
    (parent : OfficialCIPNode (Fin atomCount)) (parentAtom previous target : Fin atomCount)
    (current : parent.current? = some parentAtom)
    (previousObserved : parent.parent? = some previous)
    (indexPredicate : Nat → Bool) :
    (molecule.semanticOfficialChildCopies parent).countP
        (fun copy => (copy.1 == target) && indexPredicate copy.2) =
      (List.range (molecule.bond parentAtom target)).countP fun index =>
        (!(target == previous && index == 0)) && indexPredicate index := by
  unfold semanticOfficialChildCopies
  rw [current, previousObserved]
  rw [countP_filter_eq_countP_and]
  have predicateEquality :
      (fun copy : Fin atomCount × Nat =>
        (!(copy.1 == previous && copy.2 == 0)) &&
          ((copy.1 == target) && indexPredicate copy.2)) =
      (fun copy => (copy.1 == target) &&
        ((!(target == previous && copy.2 == 0)) && indexPredicate copy.2)) := by
    funext copy
    rcases copy with ⟨copyAtom, copyIndex⟩
    by_cases copyTarget : copyAtom = target
    · subst copyAtom
      simp
    · have observedFalse : (copyAtom == target) = false :=
        beq_eq_false_iff_ne.mpr copyTarget
      simp [observedFalse]
  rw [predicateEquality]
  exact molecule.semanticOfficialNeighborCopies_count_atom_where parentAtom target
    (fun index => (!(target == previous && index == 0)) && indexPredicate index)

/-- Total occurrences of one atom are its bond multiplicity minus the suppressed parent copy. -/
theorem semanticOfficialChildCopies_count_atom
    (molecule : MoleculeGraph (Fin atomCount))
    (parent : OfficialCIPNode (Fin atomCount)) (parentAtom previous target : Fin atomCount)
    (current : parent.current? = some parentAtom)
    (previousObserved : parent.parent? = some previous) :
    (molecule.semanticOfficialChildCopies parent).countP
        (fun copy => copy.1 == target) =
      molecule.bond parentAtom target - (if target = previous then 1 else 0) := by
  have countedRaw := molecule.semanticOfficialChildCopies_count_atom_where parent
    parentAtom previous target current previousObserved (fun _ => true)
  have counted :
      (molecule.semanticOfficialChildCopies parent).countP
          (fun copy => copy.1 == target) =
        (List.range (molecule.bond parentAtom target)).countP fun index =>
          !(target == previous && index == 0) := by
    simpa using countedRaw
  rw [counted]
  by_cases same : target = previous
  · subst target
    have predicateEquality :
        (fun index : Nat => !(previous == previous && index == 0)) =
          (fun index => !(index == 0)) := by
      funext index
      apply Bool.eq_iff_iff.mpr
      simp
    have notZeroPredicateEquality :
        (fun index : Nat => !(index == 0)) = (fun index => index != 0) := by
      funext index
      apply Bool.eq_iff_iff.mpr
      simp
    rw [predicateEquality, notZeroPredicateEquality, range_countP_not_zero]
    simp
  · have predicateEquality :
        (fun index : Nat => !(target == previous && index == 0)) =
          (fun _ => true) := by
      funext index
      simp [same]
    rw [predicateEquality]
    simp [same]

/-- Nonzero copy indices give exactly `bond - 1` multiple-bond duplicates. -/
theorem semanticOfficialChildCopies_count_multiple
    (molecule : MoleculeGraph (Fin atomCount))
    (parent : OfficialCIPNode (Fin atomCount)) (parentAtom previous target : Fin atomCount)
    (current : parent.current? = some parentAtom)
    (previousObserved : parent.parent? = some previous) :
    (molecule.semanticOfficialChildCopies parent).countP
        (fun copy => (copy.1 == target) && (copy.2 != 0)) =
      molecule.bond parentAtom target - 1 := by
  rw [molecule.semanticOfficialChildCopies_count_atom_where parent parentAtom previous target
    current previousObserved (fun index => index != 0)]
  have predicateEquality :
      (fun index : Nat => (!(target == previous && index == 0)) && (index != 0)) =
        (fun index => index != 0) := by
    funext index
    by_cases zero : index = 0 <;> simp [zero]
  rw [predicateEquality, range_countP_not_zero]

/-- Zero-index historical copies are exactly the nonsuppressed ring occurrences. -/
theorem semanticOfficialChildCopies_count_ring
    (molecule : MoleculeGraph (Fin atomCount))
    (parent : OfficialCIPNode (Fin atomCount)) (parentAtom previous target : Fin atomCount)
    (current : parent.current? = some parentAtom)
    (previousObserved : parent.parent? = some previous) :
    (molecule.semanticOfficialChildCopies parent).countP
        (fun copy => (copy.1 == target) && (copy.2 == 0) &&
          decide (target ∈ parent.history)) =
      (if molecule.Adj parentAtom target ∧ target ∈ parent.history ∧ target ≠ previous
        then 1 else 0) := by
  have countedRaw := molecule.semanticOfficialChildCopies_count_atom_where parent
    parentAtom previous target current previousObserved
      (fun index => (index == 0) && decide (target ∈ parent.history))
  have counted :
      (molecule.semanticOfficialChildCopies parent).countP
          (fun copy => (copy.1 == target) && (copy.2 == 0) &&
            decide (target ∈ parent.history)) =
        (List.range (molecule.bond parentAtom target)).countP fun index =>
          (!(target == previous && index == 0)) &&
            ((index == 0) && decide (target ∈ parent.history)) := by
    simpa [Bool.and_assoc] using countedRaw
  rw [counted]
  by_cases same : target = previous
  · subst target
    have predicateEquality :
        (fun index : Nat => (!(previous == previous && index == 0)) &&
          ((index == 0) && decide (previous ∈ parent.history))) =
        (fun _ => false) := by
      funext index
      by_cases zero : index = 0 <;> simp [zero]
    rw [predicateEquality]
    simp
  · by_cases historical : target ∈ parent.history
    · have predicateEquality :
          (fun index : Nat => (!(target == previous && index == 0)) &&
            ((index == 0) && decide (target ∈ parent.history))) =
          (fun index => index == 0) := by
        funext index
        simp [same, historical]
      rw [predicateEquality, range_countP_zero]
      by_cases adjacent : molecule.Adj parentAtom target <;>
        simp [historical, same, MoleculeGraph.Adj]
    · have predicateEquality :
          (fun index : Nat => (!(target == previous && index == 0)) &&
            ((index == 0) && decide (target ∈ parent.history))) =
          (fun _ => false) := by
        funext index
        simp [historical]
      rw [predicateEquality]
      simp [historical]

/-- Zero-index fresh copies are exactly the real-atom child occurrences. -/
theorem semanticOfficialChildCopies_count_real
    (molecule : MoleculeGraph (Fin atomCount))
    (parent : OfficialCIPNode (Fin atomCount)) (parentAtom previous target : Fin atomCount)
    (current : parent.current? = some parentAtom)
    (previousObserved : parent.parent? = some previous)
    (previousInHistory : previous ∈ parent.history) :
    (molecule.semanticOfficialChildCopies parent).countP
        (fun copy => (copy.1 == target) && (copy.2 == 0) &&
          decide (target ∉ parent.history)) =
      (if molecule.Adj parentAtom target ∧ target ∉ parent.history then 1 else 0) := by
  have countedRaw := molecule.semanticOfficialChildCopies_count_atom_where parent
    parentAtom previous target current previousObserved
      (fun index => (index == 0) && decide (target ∉ parent.history))
  have counted :
      (molecule.semanticOfficialChildCopies parent).countP
          (fun copy => (copy.1 == target) && (copy.2 == 0) &&
            decide (target ∉ parent.history)) =
        (List.range (molecule.bond parentAtom target)).countP fun index =>
          (!(target == previous && index == 0)) &&
            ((index == 0) && decide (target ∉ parent.history)) := by
    simpa [Bool.and_assoc] using countedRaw
  rw [counted]
  by_cases historical : target ∈ parent.history
  · have predicateEquality :
        (fun index : Nat => (!(target == previous && index == 0)) &&
          ((index == 0) && decide (target ∉ parent.history))) =
        (fun _ => false) := by
      funext index
      simp [historical]
    rw [predicateEquality]
    simp [historical]
  · have distinct : target ≠ previous := by
      intro same
      exact historical (same.symm ▸ previousInHistory)
    have predicateEquality :
        (fun index : Nat => (!(target == previous && index == 0)) &&
          ((index == 0) && decide (target ∉ parent.history))) =
        (fun index => index == 0) := by
      funext index
      simp [historical, distinct]
    rw [predicateEquality, range_countP_zero]
    by_cases adjacent : molecule.Adj parentAtom target <;>
      simp [historical, MoleculeGraph.Adj]

/-- Executable and proof-facing child-copy lists have identical multiplicity. -/
theorem semanticOfficialChildCopies_perm_officialChildCopies
    (molecule : MoleculeGraph (Fin atomCount))
    (node : OfficialCIPNode (Fin atomCount)) :
    List.Perm (molecule.semanticOfficialChildCopies node)
      (molecule.officialChildCopies node) := by
  unfold semanticOfficialChildCopies officialChildCopies
  cases node.current? with
  | none => exact List.Perm.refl []
  | some current =>
      cases node.parent? with
      | none =>
          exact molecule.semanticOfficialNeighborCopies_perm_officialNeighborCopies current
      | some parent =>
          exact
            (molecule.semanticOfficialNeighborCopies_perm_officialNeighborCopies current).filter
              (fun copy => !(copy.1 == parent && copy.2 == 0))

/-- Kernel-executable official children for an arbitrary `Fin`-indexed physical graph. -/
def semanticOfficialCIPChildren (molecule : MoleculeGraph (Fin atomCount))
    (node : OfficialCIPNode (Fin atomCount)) : List (OfficialCIPNode (Fin atomCount)) :=
  if node.isDuplicateLeaf then []
  else
    (molecule.semanticOfficialChildCopies node).map fun copy =>
      node.extend copy.1 copy.2

/-- The executable child enumerator is exactly the official child multiset. -/
theorem semanticOfficialCIPChildren_perm_officialCIPChildren
    (molecule : MoleculeGraph (Fin atomCount))
    (node : OfficialCIPNode (Fin atomCount)) :
    List.Perm (molecule.semanticOfficialCIPChildren node)
      (molecule.officialCIPChildren node) := by
  cases duplicate : node.isDuplicateLeaf with
  | true => simp [semanticOfficialCIPChildren, officialCIPChildren, duplicate]
  | false =>
      simp only [semanticOfficialCIPChildren, officialCIPChildren, duplicate,
        Bool.false_eq_true, ↓reduceIte]
      exact (molecule.semanticOfficialChildCopies_perm_officialChildCopies node).map
        (fun copy => node.extend copy.1 copy.2)

/-- Every executable child is literally one official one-step extension. -/
theorem semanticOfficialCIPChildren_extension
    (molecule : MoleculeGraph (Fin atomCount))
    (parent child : OfficialCIPNode (Fin atomCount))
    (present : child ∈ molecule.semanticOfficialCIPChildren parent) :
    ∃ atom copyIndex, child = parent.extend atom copyIndex := by
  by_cases duplicate : parent.isDuplicateLeaf = true
  · simp [semanticOfficialCIPChildren, duplicate] at present
  · rw [semanticOfficialCIPChildren, if_neg (by simpa using duplicate),
      List.mem_map] at present
    obtain ⟨copy, _copyPresent, rfl⟩ := present
    exact ⟨copy.1, copy.2, rfl⟩

/-- Every executable child extends the stored branch history by one atom. -/
theorem semanticOfficialCIPChildren_history_length
    (molecule : MoleculeGraph (Fin atomCount))
    (parent child : OfficialCIPNode (Fin atomCount))
    (present : child ∈ molecule.semanticOfficialCIPChildren parent) :
    child.history.length = parent.history.length + 1 := by
  obtain ⟨atom, copyIndex, rfl⟩ :=
    molecule.semanticOfficialCIPChildren_extension parent child present
  exact OfficialCIPNode.extend_history_length parent atom copyIndex

/-- Graph-native official expansion never injects placeholder provenance. -/
theorem semanticOfficialCIPChildren_graphGenerated
    (molecule : MoleculeGraph (Fin atomCount))
    (parent child : OfficialCIPNode (Fin atomCount))
    (present : child ∈ molecule.semanticOfficialCIPChildren parent) :
    child.GraphGenerated := by
  obtain ⟨atom, copyIndex, rfl⟩ :=
    molecule.semanticOfficialCIPChildren_extension parent child present
  by_cases realCopy : copyIndex = 0
  · by_cases ring : atom ∈ parent.history <;>
      simp [OfficialCIPNode.GraphGenerated, OfficialCIPNode.extend,
        OfficialCIPNode.childProvenance, realCopy, ring]
  · simp [OfficialCIPNode.GraphGenerated, OfficialCIPNode.extend,
      OfficialCIPNode.childProvenance, realCopy]

/-- Every atom-bearing executable edge is a positive molecular edge. -/
theorem adj_of_mem_semanticOfficialCIPChildren
    (molecule : MoleculeGraph (Fin atomCount))
    (parent child : OfficialCIPNode (Fin atomCount))
    (parentAtom childAtom : Fin atomCount)
    (parentObserved : parent.current? = some parentAtom)
    (childObserved : child.current? = some childAtom)
    (present : child ∈ molecule.semanticOfficialCIPChildren parent) :
    molecule.Adj parentAtom childAtom := by
  exact molecule.adj_of_mem_officialCIPChildren parent child parentAtom childAtom
    parentObserved childObserved
    ((molecule.semanticOfficialCIPChildren_perm_officialCIPChildren parent).mem_iff.mp present)

/-- The canonical executable enumeration exhausts every ordinary ligand branch at the proved
`atomCount + 1` depth bound. -/
theorem semanticOfficialExpansionCompleteWithin_default
    (molecule : MoleculeGraph (Fin atomCount)) (center ligand : Fin atomCount)
    (different : ligand ≠ center) :
    OfficialExpansionCompleteWithin molecule.semanticOfficialCIPChildren (atomCount + 1)
      (OfficialCIPNode.rootFromEdge center ligand) := by
  have reference := molecule.officialExpansionCompleteWithin_rootFromEdge_default different
  have same := officialExpansionCompleteWithin_iff_of_children_perm
    molecule.semanticOfficialCIPChildren molecule.officialCIPChildren
    molecule.semanticOfficialCIPChildren_perm_officialCIPChildren
    (atomCount + 1) (OfficialCIPNode.rootFromEdge center ligand)
  apply same.mpr
  simpa using reference

/-- Direct executable recursive occurrence tree.  Unlike the exact Rule-major key compiler, this
construction does not rank siblings or consult any declarative Rule-1a comparison: it unfolds the
canonical semantic child enumeration verbatim for the supplied finite depth. -/
def buildSemanticOfficialSourceTree
    (molecule : MoleculeGraph (Fin atomCount)) :
    Nat → OfficialCIPNode (Fin atomCount) → OfficialCIPSourceTree (Fin atomCount)
  | 0, node => .node node []
  | fuel + 1, node =>
      .node node ((molecule.semanticOfficialCIPChildren node).map
        (molecule.buildSemanticOfficialSourceTree fuel))

@[simp] theorem buildSemanticOfficialSourceTree_source
    (molecule : MoleculeGraph (Fin atomCount)) (fuel : Nat)
    (node : OfficialCIPNode (Fin atomCount)) :
    (molecule.buildSemanticOfficialSourceTree fuel node).source = node := by
  cases fuel <;> rfl

/-- The direct tree contains every executable child exactly once and recursively does so at every
descendant when the supplied depth bound is complete. -/
theorem buildSemanticOfficialSourceTree_generated
    (molecule : MoleculeGraph (Fin atomCount)) :
    ∀ (fuel : Nat) (node : OfficialCIPNode (Fin atomCount)),
      OfficialExpansionCompleteWithin molecule.semanticOfficialCIPChildren fuel node →
        (molecule.buildSemanticOfficialSourceTree fuel node).GeneratedBy
          molecule.semanticOfficialCIPChildren
  | 0, node, complete => by
      simp only [buildSemanticOfficialSourceTree, OfficialCIPSourceTree.GeneratedBy,
        OfficialCIPSourceTree.ForestGeneratedBy, List.map_nil]
      exact ⟨by simpa using complete.symm, trivial⟩
  | fuel + 1, node, complete => by
      simp only [buildSemanticOfficialSourceTree, OfficialCIPSourceTree.GeneratedBy]
      constructor
      · apply List.Perm.of_eq
        induction molecule.semanticOfficialCIPChildren node with
        | nil => rfl
        | cons child children inductionHypothesis =>
            simp only [List.map_cons]
            rw [molecule.buildSemanticOfficialSourceTree_source fuel child,
              inductionHypothesis]
      · rw [OfficialCIPSourceTree.forestGeneratedBy_iff_forall]
        intro tree present
        rcases List.mem_map.mp present with ⟨child, childPresent, rfl⟩
        exact molecule.buildSemanticOfficialSourceTree_generated fuel child
          (complete child childPresent)

private theorem semanticFirstIndexOf?_eq_some_of_mem
    {V : Type*} [DecidableEq V] (atom : V) :
    ∀ {values : List V}, atom ∈ values →
      ∃ index, firstIndexOf? atom values = some index
  | [], present => by simp at present
  | value :: values, present => by
      by_cases head : value = atom
      · subst value
        exact ⟨0, firstIndexOf?_cons_self atom values⟩
      · have tailPresent : atom ∈ values :=
          (List.mem_cons.mp present).resolve_left (Ne.symm head)
        obtain ⟨index, found⟩ := semanticFirstIndexOf?_eq_some_of_mem atom tailPresent
        exact ⟨index + 1, by simp [firstIndexOf?, head, found]⟩

private theorem semanticFirstIndexOf?_eq_some_imp_getElem?
    {V : Type*} [DecidableEq V] (atom : V) :
    ∀ (values : List V) (index : Nat),
      firstIndexOf? atom values = some index → values[index]? = some atom
  | [], index, found => by simp [firstIndexOf?] at found
  | value :: values, index, found => by
      unfold firstIndexOf? at found
      by_cases head : value = atom
      · simp [head] at found
        subst index
        simp [head]
      · simp only [head, ↓reduceIte, Option.map_eq_some_iff] at found
        obtain ⟨tailIndex, tailFound, rfl⟩ := found
        simpa using semanticFirstIndexOf?_eq_some_imp_getElem?
          atom values tailIndex tailFound

/-- Stored history length agrees exactly with ranked-sibling address depth. -/
theorem semanticGeneratedSourceTree_history_length
    (molecule : MoleculeGraph (Fin atomCount))
    (tree : OfficialCIPSourceTree (Fin atomCount))
    (center ligand : Fin atomCount)
    (generated : tree.GeneratedBy molecule.semanticOfficialCIPChildren)
    (root : tree.source = OfficialCIPNode.rootFromEdge center ligand)
    (node : tree.HierarchyNode) (subtree : OfficialCIPSourceTree (Fin atomCount))
    (lookup : tree.subtreeAt? node.1 = some subtree) :
    subtree.source.history.length = node.1.length + 2 := by
  have reachable := tree.toDeclarativeDigraph.reachable node
  change Relation.ReflTransGen tree.HierarchyChild
    ⟨[], tree.nil_mem_hierarchyAddresses⟩ node at reachable
  revert subtree
  induction reachable with
  | refl =>
      intro subtree lookup
      simp only [OfficialCIPSourceTree.subtreeAt?] at lookup
      have same : tree = subtree := Option.some.inj lookup
      rw [← same, root]
      rfl
  | @tail parent node path edge inductionHypothesis =>
      intro childTree childLookup
      obtain ⟨parentTree, parentLookup, _⟩ := tree.exists_source_lookup parent
      have childPresent := generated.source_mem_of_hierarchyChild tree
        molecule.semanticOfficialCIPChildren parent node parentTree childTree
        parentLookup childLookup edge
      have parentLength := inductionHypothesis parentTree parentLookup
      have childLength := molecule.semanticOfficialCIPChildren_history_length
        parentTree.source childTree.source childPresent
      rcases edge with ⟨slot, childAddress⟩
      rw [childAddress]
      simp only [List.length_append, List.length_singleton]
      omega

/-- Generated source nodes keep the current atom at the head of their stored history. -/
theorem semanticGeneratedSourceTree_history_head
    (molecule : MoleculeGraph (Fin atomCount))
    (tree : OfficialCIPSourceTree (Fin atomCount))
    (center ligand : Fin atomCount)
    (generated : tree.GeneratedBy molecule.semanticOfficialCIPChildren)
    (root : tree.source = OfficialCIPNode.rootFromEdge center ligand)
    (node : tree.HierarchyNode) (subtree : OfficialCIPSourceTree (Fin atomCount))
    (lookup : tree.subtreeAt? node.1 = some subtree) :
    subtree.source.history.head? = subtree.source.current? := by
  have reachable := tree.toDeclarativeDigraph.reachable node
  change Relation.ReflTransGen tree.HierarchyChild
    ⟨[], tree.nil_mem_hierarchyAddresses⟩ node at reachable
  revert subtree
  induction reachable with
  | refl =>
      intro subtree lookup
      simp only [OfficialCIPSourceTree.subtreeAt?] at lookup
      have same : tree = subtree := Option.some.inj lookup
      rw [← same, root]
      rfl
  | @tail parent node path edge inductionHypothesis =>
      intro childTree childLookup
      obtain ⟨parentTree, parentLookup, _⟩ := tree.exists_source_lookup parent
      have childPresent := generated.source_mem_of_hierarchyChild tree
        molecule.semanticOfficialCIPChildren parent node parentTree childTree
        parentLookup childLookup edge
      obtain ⟨atom, copyIndex, childIdentity⟩ :=
        molecule.semanticOfficialCIPChildren_extension
          parentTree.source childTree.source childPresent
      simp [childIdentity]

/-- Stored history is monotone along one generated hierarchy edge. -/
theorem semanticGeneratedSourceTree_history_mono_of_child
    (molecule : MoleculeGraph (Fin atomCount))
    (tree : OfficialCIPSourceTree (Fin atomCount))
    (generated : tree.GeneratedBy molecule.semanticOfficialCIPChildren)
    (parent child : tree.HierarchyNode)
    (parentTree childTree : OfficialCIPSourceTree (Fin atomCount))
    (parentLookup : tree.subtreeAt? parent.1 = some parentTree)
    (childLookup : tree.subtreeAt? child.1 = some childTree)
    (edge : tree.HierarchyChild parent child) :
    ∀ atom, atom ∈ parentTree.source.history → atom ∈ childTree.source.history := by
  have childPresent := generated.source_mem_of_hierarchyChild tree
    molecule.semanticOfficialCIPChildren parent child parentTree childTree
    parentLookup childLookup edge
  obtain ⟨next, copyIndex, childIdentity⟩ :=
    molecule.semanticOfficialCIPChildren_extension
      parentTree.source childTree.source childPresent
  intro atom present
  rw [childIdentity, OfficialCIPNode.extend_history]
  exact List.mem_cons_of_mem next present

/-- Extending a source node whose stored head is known makes that head the immediate parent. -/
private theorem semantic_parent?_extend_eq_of_history_head
    {V : Type*} [DecidableEq V]
    (parent : OfficialCIPNode V) (next head : V) (copyIndex : Nat)
    (headObserved : parent.history.head? = some head) :
    (parent.extend next copyIndex).parent? = some head := by
  cases historyObserved : parent.history with
  | nil => simp [historyObserved] at headObserved
  | cons first rest =>
      have firstEq : first = head := by
        apply Option.some.inj
        simpa [historyObserved] using headObserved
      subst first
      simp [OfficialCIPNode.parent?, OfficialCIPNode.extend, historyObserved]

private theorem semantic_parent?_extend_eq_current_of_history_head
    {V : Type*} [DecidableEq V]
    (parent : OfficialCIPNode V) (next : V) (copyIndex : Nat)
    (headObserved : parent.history.head? = parent.current?) :
    (parent.extend next copyIndex).parent? = parent.current? := by
  cases historyObserved : parent.history with
  | nil =>
      rw [historyObserved] at headObserved
      simpa [OfficialCIPNode.parent?, OfficialCIPNode.extend, historyObserved] using headObserved
  | cons first rest =>
      rw [historyObserved] at headObserved
      simpa [OfficialCIPNode.parent?, OfficialCIPNode.extend, historyObserved] using headObserved

/-- The external parent remains in every generated branch history. -/
theorem semanticGeneratedSourceTree_center_mem_history
    (molecule : MoleculeGraph (Fin atomCount))
    (tree : OfficialCIPSourceTree (Fin atomCount))
    (center ligand : Fin atomCount)
    (generated : tree.GeneratedBy molecule.semanticOfficialCIPChildren)
    (root : tree.source = OfficialCIPNode.rootFromEdge center ligand)
    (node : tree.HierarchyNode) (subtree : OfficialCIPSourceTree (Fin atomCount))
    (lookup : tree.subtreeAt? node.1 = some subtree) :
    center ∈ subtree.source.history := by
  have reachable := tree.toDeclarativeDigraph.reachable node
  change Relation.ReflTransGen tree.HierarchyChild
    ⟨[], tree.nil_mem_hierarchyAddresses⟩ node at reachable
  revert subtree
  induction reachable with
  | refl =>
      intro subtree lookup
      simp only [OfficialCIPSourceTree.subtreeAt?] at lookup
      have same : tree = subtree := Option.some.inj lookup
      subst subtree
      rw [root]
      simp [OfficialCIPNode.rootFromEdge]
  | @tail parent node path edge inductionHypothesis =>
      intro childTree childLookup
      obtain ⟨parentTree, parentLookup, _⟩ := tree.exists_source_lookup parent
      exact molecule.semanticGeneratedSourceTree_history_mono_of_child tree generated
        parent node parentTree childTree parentLookup childLookup edge center
        (inductionHypothesis parentTree parentLookup)

/-- Stored branch history is monotone along every nonempty hierarchy path. -/
theorem semanticGeneratedSourceTree_history_mono_of_transGen
    (molecule : MoleculeGraph (Fin atomCount))
    (tree : OfficialCIPSourceTree (Fin atomCount))
    (generated : tree.GeneratedBy molecule.semanticOfficialCIPChildren)
    (first node : tree.HierarchyNode)
    (firstTree subtree : OfficialCIPSourceTree (Fin atomCount))
    (firstLookup : tree.subtreeAt? first.1 = some firstTree)
    (lookup : tree.subtreeAt? node.1 = some subtree)
    (path : Relation.TransGen tree.HierarchyChild first node) :
    ∀ atom, atom ∈ firstTree.source.history → atom ∈ subtree.source.history := by
  induction path generalizing subtree with
  | single edge =>
      intro atom present
      exact molecule.semanticGeneratedSourceTree_history_mono_of_child tree generated
        _ _ firstTree subtree firstLookup lookup edge atom present
  | @tail middle finalNode _path edge inductionHypothesis =>
      intro atom present
      obtain ⟨middleTree, middleLookup, _⟩ := tree.exists_source_lookup middle
      have middlePresent : atom ∈ middleTree.source.history :=
        inductionHypothesis middleTree middleLookup atom present
      apply molecule.semanticGeneratedSourceTree_history_mono_of_child tree generated
        middle finalNode middleTree subtree middleLookup lookup edge atom
      exact middlePresent

/-- A represented strict ancestor atom remains in the descendant's stored history. -/
theorem semanticGeneratedSourceTree_ancestorAtom_mem_history
    (molecule : MoleculeGraph (Fin atomCount))
    (tree : OfficialCIPSourceTree (Fin atomCount))
    (center ligand target : Fin atomCount)
    (generated : tree.GeneratedBy molecule.semanticOfficialCIPChildren)
    (root : tree.source = OfficialCIPNode.rootFromEdge center ligand)
    (node : tree.HierarchyNode) (subtree : OfficialCIPSourceTree (Fin atomCount))
    (lookup : tree.subtreeAt? node.1 = some subtree)
    (ancestor : DeclarativeCIP.RootedDigraph.AncestorAtom
      tree.toDeclarativeDigraph node target) :
    target ∈ subtree.source.history := by
  rcases ancestor with ⟨first, path, firstLabel⟩
  obtain ⟨firstTree, firstLookup, _⟩ := tree.exists_source_lookup first
  have firstCurrent : firstTree.source.current? = some target := by
    change (tree.declarativeLabel first).atom? = some target at firstLabel
    rw [tree.declarativeLabel_eq_of_subtreeAt? firstTree first firstLookup] at firstLabel
    simpa [OfficialCIPNode.toDeclarativeLabel] using firstLabel
  have firstHead := molecule.semanticGeneratedSourceTree_history_head tree center ligand
    generated root first firstTree firstLookup
  have atHead : target ∈ firstTree.source.history := by
    cases historyObserved : firstTree.source.history with
    | nil =>
        rw [historyObserved] at firstHead
        simp only [List.head?_nil] at firstHead
        rw [← firstHead] at firstCurrent
        simp at firstCurrent
    | cons head tail =>
        have headEq : head = target := by
          rw [historyObserved] at firstHead
          simp only [List.head?_cons] at firstHead
          exact Option.some.inj (firstHead.trans firstCurrent)
        subst head
        simp
  exact molecule.semanticGeneratedSourceTree_history_mono_of_transGen tree generated
    first node firstTree subtree firstLookup lookup path target atHead

/-- The independent suppressed-parent predicate is exactly equality with the stored immediate
predecessor. -/
theorem semanticGeneratedSourceTree_suppressedParentAtom_iff_eq
    (molecule : MoleculeGraph (Fin atomCount))
    (tree : OfficialCIPSourceTree (Fin atomCount))
    (center ligand parentAtom previous target : Fin atomCount)
    (generated : tree.GeneratedBy molecule.semanticOfficialCIPChildren)
    (root : tree.source = OfficialCIPNode.rootFromEdge center ligand)
    (node : tree.HierarchyNode) (subtree : OfficialCIPSourceTree (Fin atomCount))
    (lookup : tree.subtreeAt? node.1 = some subtree)
    (current : subtree.source.current? = some parentAtom)
    (previousObserved : subtree.source.parent? = some previous) :
    DeclarativeCIP.RootedDigraph.SuppressedParentAtom
        tree.toDeclarativeDigraph center target node ↔
      target = previous := by
  constructor
  · rintro (⟨atRoot, rfl⟩ | ⟨parent, edge, parentLabel⟩)
    · have addressEq : node.1 = [] := congrArg Subtype.val atRoot
      have rootLookup : tree.subtreeAt? [] = some subtree := by
        simpa [addressEq] using lookup
      simp only [OfficialCIPSourceTree.subtreeAt?] at rootLookup
      have same : tree = subtree := Option.some.inj rootLookup
      subst subtree
      rw [root] at previousObserved
      have rootParent :
          (OfficialCIPNode.rootFromEdge target ligand).parent? = some target := rfl
      exact Option.some.inj (rootParent.trans previousObserved)
    · obtain ⟨parentTree, parentLookup, _⟩ := tree.exists_source_lookup parent
      have parentCurrent : parentTree.source.current? = some target := by
        change (tree.declarativeLabel parent).atom? = some target at parentLabel
        rw [tree.declarativeLabel_eq_of_subtreeAt? parentTree parent parentLookup] at parentLabel
        simpa [OfficialCIPNode.toDeclarativeLabel] using parentLabel
      have parentHead := molecule.semanticGeneratedSourceTree_history_head tree center ligand
        generated root parent parentTree parentLookup
      have childPresent := generated.source_mem_of_hierarchyChild tree
        molecule.semanticOfficialCIPChildren parent node parentTree subtree
        parentLookup lookup edge
      obtain ⟨next, copyIndex, childIdentity⟩ :=
        molecule.semanticOfficialCIPChildren_extension
          parentTree.source subtree.source childPresent
      have childPrevious : subtree.source.parent? = some target := by
        rw [childIdentity]
        exact semantic_parent?_extend_eq_of_history_head parentTree.source next target copyIndex
          (parentHead.trans parentCurrent)
      exact Option.some.inj (childPrevious.symm.trans previousObserved)
  · intro targetEq
    subst target
    rcases tree.toDeclarativeDigraph.reachable node |>.cases_tail with atRoot | belowRoot
    · left
      have nodeEq : node = tree.toDeclarativeDigraph.root := atRoot
      have addressEq : node.1 = [] := congrArg Subtype.val nodeEq
      have rootLookup : tree.subtreeAt? [] = some subtree := by
        simpa [addressEq] using lookup
      simp only [OfficialCIPSourceTree.subtreeAt?] at rootLookup
      have same : tree = subtree := Option.some.inj rootLookup
      subst subtree
      rw [root] at previousObserved
      have previousEq : previous = center :=
        (Option.some.inj ((show
          (OfficialCIPNode.rootFromEdge center ligand).parent? = some center from rfl).trans
            previousObserved)).symm
      exact ⟨nodeEq, previousEq⟩
    · rcases belowRoot with ⟨parent, _path, edge⟩
      right
      obtain ⟨parentTree, parentLookup, _⟩ := tree.exists_source_lookup parent
      have parentHead := molecule.semanticGeneratedSourceTree_history_head tree center ligand
        generated root parent parentTree parentLookup
      have childPresent := generated.source_mem_of_hierarchyChild tree
        molecule.semanticOfficialCIPChildren parent node parentTree subtree
        parentLookup lookup edge
      obtain ⟨next, copyIndex, childIdentity⟩ :=
        molecule.semanticOfficialCIPChildren_extension
          parentTree.source subtree.source childPresent
      have parentCurrent : parentTree.source.current? = some previous := by
        have extendedParent :
            (parentTree.source.extend next copyIndex).parent? = parentTree.source.current? :=
          semantic_parent?_extend_eq_current_of_history_head parentTree.source next copyIndex
            parentHead
        rw [childIdentity] at previousObserved
        exact extendedParent.symm.trans previousObserved
      refine ⟨parent, edge, ?_⟩
      change (tree.declarativeLabel parent).atom? = some previous
      rw [tree.declarativeLabel_eq_of_subtreeAt? parentTree parent parentLookup]
      simpa [OfficialCIPNode.toDeclarativeLabel] using parentCurrent

/-- Every generated carrier occurrence has graph-generated provenance and an atom. -/
theorem semanticGeneratedSourceTree_source_valid
    (molecule : MoleculeGraph (Fin atomCount))
    (tree : OfficialCIPSourceTree (Fin atomCount))
    (center ligand : Fin atomCount)
    (generated : tree.GeneratedBy molecule.semanticOfficialCIPChildren)
    (root : tree.source = OfficialCIPNode.rootFromEdge center ligand)
    (node : tree.HierarchyNode) (subtree : OfficialCIPSourceTree (Fin atomCount))
    (lookup : tree.subtreeAt? node.1 = some subtree) :
    subtree.source.GraphGenerated ∧ ∃ atom, subtree.source.current? = some atom := by
  have reachable := tree.toDeclarativeDigraph.reachable node
  change Relation.ReflTransGen tree.HierarchyChild
    ⟨[], tree.nil_mem_hierarchyAddresses⟩ node at reachable
  revert subtree
  induction reachable with
  | refl =>
      intro subtree lookup
      simp only [OfficialCIPSourceTree.subtreeAt?] at lookup
      have same : tree = subtree := Option.some.inj lookup
      subst subtree
      rw [root]
      exact ⟨by simp [OfficialCIPNode.GraphGenerated, OfficialCIPNode.rootFromEdge],
        ⟨ligand, rfl⟩⟩
  | @tail parent node path edge inductionHypothesis =>
      intro childTree childLookup
      obtain ⟨parentTree, parentLookup, _⟩ := tree.exists_source_lookup parent
      have childPresent := generated.source_mem_of_hierarchyChild tree
        molecule.semanticOfficialCIPChildren parent node parentTree childTree
        parentLookup childLookup edge
      obtain ⟨atom, copyIndex, childIdentity⟩ :=
        molecule.semanticOfficialCIPChildren_extension
          parentTree.source childTree.source childPresent
      exact ⟨molecule.semanticOfficialCIPChildren_graphGenerated
          parentTree.source childTree.source childPresent,
        ⟨atom, by simp [childIdentity]⟩⟩

/-- Every stored reversed-history position is the external parent, the current occurrence, or a
strict represented ancestor. -/
theorem semanticGeneratedSourceTree_history_index_realized
    (molecule : MoleculeGraph (Fin atomCount))
    (tree : OfficialCIPSourceTree (Fin atomCount))
    (center ligand : Fin atomCount)
    (generated : tree.GeneratedBy molecule.semanticOfficialCIPChildren)
    (root : tree.source = OfficialCIPNode.rootFromEdge center ligand)
    (node : tree.HierarchyNode) (subtree : OfficialCIPSourceTree (Fin atomCount))
    (lookup : tree.subtreeAt? node.1 = some subtree) :
    ∀ index atom, subtree.source.history.reverse[index]? = some atom →
      (index = 0 ∧ atom = center) ∨
      (index = node.1.length + 1 ∧ subtree.source.current? = some atom) ∨
      ∃ ancestor : tree.HierarchyNode,
        Relation.TransGen tree.HierarchyChild ancestor node ∧
          (tree.declarativeLabel ancestor).atom? = some atom ∧
          index = ancestor.1.length + 1 := by
  have reachable := tree.toDeclarativeDigraph.reachable node
  change Relation.ReflTransGen tree.HierarchyChild
    ⟨[], tree.nil_mem_hierarchyAddresses⟩ node at reachable
  revert subtree
  induction reachable with
  | refl =>
      intro subtree lookup index atom observed
      simp only [OfficialCIPSourceTree.subtreeAt?] at lookup
      have same : tree = subtree := Option.some.inj lookup
      subst subtree
      rw [root] at observed
      have bound : index < 2 := by
        have := List.getElem?_eq_some_iff.mp observed
        simpa [OfficialCIPNode.rootFromEdge] using this.1
      have cases : index = 0 ∨ index = 1 := by omega
      rcases cases with rfl | rfl
      · left
        exact ⟨rfl, by simpa [OfficialCIPNode.rootFromEdge] using observed.symm⟩
      · right; left
        refine ⟨rfl, ?_⟩
        rw [root]
        simpa [OfficialCIPNode.rootFromEdge] using observed
  | @tail parent node path edge inductionHypothesis =>
      intro childTree childLookup index atom observed
      obtain ⟨parentTree, parentLookup, _⟩ := tree.exists_source_lookup parent
      have childPresent := generated.source_mem_of_hierarchyChild tree
        molecule.semanticOfficialCIPChildren parent node parentTree childTree
        parentLookup childLookup edge
      obtain ⟨next, copyIndex, childIdentity⟩ :=
        molecule.semanticOfficialCIPChildren_extension
          parentTree.source childTree.source childPresent
      have parentLength := molecule.semanticGeneratedSourceTree_history_length
        tree center ligand generated root parent parentTree parentLookup
      rw [childIdentity, OfficialCIPNode.extend_history, List.reverse_cons,
        List.getElem?_append] at observed
      by_cases before : index < parentTree.source.history.reverse.length
      · simp only [before, ↓reduceIte] at observed
        rcases inductionHypothesis parentTree parentLookup index atom observed with
          atCenter | atParentOrAncestor
        · exact Or.inl atCenter
        · rcases atParentOrAncestor with atParent | atAncestor
          · right; right
            refine ⟨parent, Relation.TransGen.single edge, ?_, atParent.1⟩
            rw [tree.declarativeLabel_eq_of_subtreeAt? parentTree parent parentLookup]
            simpa [OfficialCIPNode.toDeclarativeLabel] using atParent.2
          · rcases atAncestor with ⟨ancestor, ancestorPath, ancestorAtom, distance⟩
            right; right
            exact ⟨ancestor, ancestorPath.tail edge, ancestorAtom, distance⟩
      · simp only [before, ↓reduceIte] at observed
        have tailBound : index - parentTree.source.history.reverse.length < 1 :=
          (List.getElem?_eq_some_iff.mp observed).1
        have indexEq : index = parentTree.source.history.length := by
          simp only [List.length_reverse] at before tailBound
          omega
        have atomEq : atom = next := by
          subst index
          simpa using observed.symm
        right; left
        rcases edge with ⟨slot, address⟩
        constructor
        · rw [address]
          simp only [List.length_append, List.length_singleton]
          omega
        · simp [childIdentity, atomEq]

/-- Away from the current atom, the stored history is exactly the independent branch-ancestor
predicate. -/
theorem semanticGeneratedSourceTree_branchAncestorAtom_iff_mem_history
    (molecule : MoleculeGraph (Fin atomCount))
    (tree : OfficialCIPSourceTree (Fin atomCount))
    (center ligand parentAtom target : Fin atomCount)
    (generated : tree.GeneratedBy molecule.semanticOfficialCIPChildren)
    (root : tree.source = OfficialCIPNode.rootFromEdge center ligand)
    (node : tree.HierarchyNode) (subtree : OfficialCIPSourceTree (Fin atomCount))
    (lookup : tree.subtreeAt? node.1 = some subtree)
    (current : subtree.source.current? = some parentAtom)
    (different : target ≠ parentAtom) :
    DeclarativeCIP.RootedDigraph.BranchAncestorAtom
        tree.toDeclarativeDigraph center target node ↔
      target ∈ subtree.source.history := by
  constructor
  · rintro (rfl | ancestor)
    · exact molecule.semanticGeneratedSourceTree_center_mem_history tree target ligand
        generated root node subtree lookup
    · exact molecule.semanticGeneratedSourceTree_ancestorAtom_mem_history tree
        center ligand target generated root node subtree lookup ancestor
  · intro historical
    obtain ⟨index, firstIndex⟩ := semanticFirstIndexOf?_eq_some_of_mem target
      (List.mem_reverse.mpr historical)
    have observed := semanticFirstIndexOf?_eq_some_imp_getElem?
      target subtree.source.history.reverse index firstIndex
    have realized := molecule.semanticGeneratedSourceTree_history_index_realized tree
      center ligand generated root node subtree lookup index target observed
    rcases realized with atCenter | atCurrentOrAncestor
    · exact Or.inl atCenter.2
    · rcases atCurrentOrAncestor with atCurrent | atAncestor
      · have same : target = parentAtom :=
          Option.some.inj (atCurrent.2.symm.trans current)
        exact (different same).elim
      · rcases atAncestor with ⟨ancestor, ancestorPath, ancestorLabel, _distance⟩
        exact Or.inr ⟨ancestor, ancestorPath, ancestorLabel⟩

/-- Generated multiple-bond duplicates carry exactly their parent sphere. -/
theorem semanticOfficialCIPChildren_multipleBondDuplicate_distance
    (molecule : MoleculeGraph (Fin atomCount))
    (parent child : OfficialCIPNode (Fin atomCount))
    (present : child ∈ molecule.semanticOfficialCIPChildren parent)
    (distance : Nat)
    (provenance : child.provenance = .multipleBondDuplicate distance) :
    distance = parent.depth := by
  obtain ⟨atom, copyIndex, childIdentity⟩ :=
    molecule.semanticOfficialCIPChildren_extension parent child present
  subst child
  by_cases realCopy : copyIndex = 0
  · by_cases ring : atom ∈ parent.history <;>
      simp [OfficialCIPNode.extend, OfficialCIPNode.childProvenance,
        realCopy, ring] at provenance
  · simpa [OfficialCIPNode.extend, OfficialCIPNode.childProvenance,
      realCopy] using provenance.symm

/-- Generated ring duplicates retain the first reversed-history occurrence exactly. -/
theorem semanticOfficialCIPChildren_ringDuplicate_firstIndex
    (molecule : MoleculeGraph (Fin atomCount))
    (parent child : OfficialCIPNode (Fin atomCount))
    (present : child ∈ molecule.semanticOfficialCIPChildren parent)
    (atom : Fin atomCount) (distance : Nat)
    (current : child.current? = some atom)
    (provenance : child.provenance = .ringDuplicate distance) :
    firstIndexOf? atom parent.history.reverse = some distance := by
  obtain ⟨next, copyIndex, childIdentity⟩ :=
    molecule.semanticOfficialCIPChildren_extension parent child present
  subst child
  simp only [OfficialCIPNode.extend_current?, Option.some.injEq] at current
  subst next
  by_cases realCopy : copyIndex = 0
  · subst copyIndex
    by_cases ring : atom ∈ parent.history
    · have payload : distance = parent.duplicateRootDistance atom := by
        simpa [OfficialCIPNode.extend, OfficialCIPNode.childProvenance, ring] using
          provenance.symm
      obtain ⟨index, found⟩ := semanticFirstIndexOf?_eq_some_of_mem atom
        (List.mem_reverse.mpr ring)
      have distanceEq : distance = index := by
        rw [payload]
        simp [OfficialCIPNode.duplicateRootDistance, found]
      simpa [distanceEq] using found
    · simp [OfficialCIPNode.extend, OfficialCIPNode.childProvenance, ring] at provenance
  · simp [OfficialCIPNode.extend, OfficialCIPNode.childProvenance, realCopy] at provenance

/-- A generated recursive graph-native hierarchy has only atom-bearing children. -/
theorem semanticGeneratedSourceTree_atomBearingChildren
    (molecule : MoleculeGraph (Fin atomCount))
    (tree : OfficialCIPSourceTree (Fin atomCount))
    (generated : tree.GeneratedBy molecule.semanticOfficialCIPChildren) :
    DeclarativeCIP.RootedDigraph.AtomBearingChildren tree.toDeclarativeDigraph := by
  intro parent child edge
  obtain ⟨parentTree, parentLookup, _⟩ := tree.exists_source_lookup parent
  obtain ⟨childTree, childLookup, _⟩ := tree.exists_source_lookup child
  have present := generated.source_mem_of_hierarchyChild tree
    molecule.semanticOfficialCIPChildren parent child parentTree childTree
    parentLookup childLookup edge
  obtain ⟨atom, copyIndex, childIdentity⟩ :=
    molecule.semanticOfficialCIPChildren_extension parentTree.source childTree.source present
  refine ⟨atom, ?_⟩
  change (tree.declarativeLabel child).atom? = some atom
  rw [tree.declarativeLabel_eq_of_subtreeAt? childTree child childLookup, childIdentity]
  rfl

/-- Every atom-labelled hierarchy edge in a generated graph-native source tree follows a positive
edge of the original molecule graph. -/
theorem semanticGeneratedSourceTree_edge_adj
    (molecule : MoleculeGraph (Fin atomCount))
    (tree : OfficialCIPSourceTree (Fin atomCount))
    (generated : tree.GeneratedBy molecule.semanticOfficialCIPChildren)
    (parent child : tree.HierarchyNode) (parentAtom childAtom : Fin atomCount)
    (edge : tree.HierarchyChild parent child)
    (parentLabel : (tree.toDeclarativeDigraph.label parent).atom? = some parentAtom)
    (childLabel : (tree.toDeclarativeDigraph.label child).atom? = some childAtom) :
    molecule.Adj parentAtom childAtom := by
  obtain ⟨parentTree, parentLookup, _⟩ := tree.exists_source_lookup parent
  obtain ⟨childTree, childLookup, _⟩ := tree.exists_source_lookup child
  have present := generated.source_mem_of_hierarchyChild tree
    molecule.semanticOfficialCIPChildren parent child parentTree childTree
    parentLookup childLookup edge
  have parentCurrent : parentTree.source.current? = some parentAtom := by
    change (tree.declarativeLabel parent).atom? = some parentAtom at parentLabel
    rw [tree.declarativeLabel_eq_of_subtreeAt? parentTree parent parentLookup] at parentLabel
    simpa [OfficialCIPNode.toDeclarativeLabel] using parentLabel
  have childCurrent : childTree.source.current? = some childAtom := by
    change (tree.declarativeLabel child).atom? = some childAtom at childLabel
    rw [tree.declarativeLabel_eq_of_subtreeAt? childTree child childLookup] at childLabel
    simpa [OfficialCIPNode.toDeclarativeLabel] using childLabel
  exact molecule.adj_of_mem_semanticOfficialCIPChildren parentTree.source childTree.source
    parentAtom childAtom parentCurrent childCurrent present

private theorem semantic_mem_occurrences_of_subtreeAt?
    {V : Type*} [DecidableEq V] :
    ∀ (tree subtree : OfficialCIPSourceTree V) (address : List Nat),
      tree.subtreeAt? address = some subtree →
        (address, subtree.source) ∈ tree.occurrences
  | .node root children, subtree, [], lookup => by
      simp only [OfficialCIPSourceTree.subtreeAt?] at lookup
      have same : OfficialCIPSourceTree.node root children = subtree := Option.some.inj lookup
      subst subtree
      simp only [OfficialCIPSourceTree.occurrences, List.mem_cons]
      exact Or.inl rfl
  | .node root children, subtree, slot :: address, lookup => by
      simp only [OfficialCIPSourceTree.subtreeAt?] at lookup
      cases childLookup : children[slot]? with
      | none => simp [childLookup] at lookup
      | some child =>
          rw [childLookup] at lookup
          have descendant := semantic_mem_occurrences_of_subtreeAt?
            child subtree address lookup
          simp only [OfficialCIPSourceTree.occurrences, List.mem_cons]
          right
          rw [OfficialCIPSourceTree.mem_forestOccurrences_iff_zipIdx]
          refine ⟨(child, slot), ?_, (address, subtree.source), descendant, rfl⟩
          have slotLt := (List.getElem?_eq_some_iff.mp childLookup).1
          apply List.mem_iff_getElem.mpr
          refine ⟨slot, by simpa using slotLt, ?_⟩
          rw [List.getElem_zipIdx]
          have childEq := (List.getElem?_eq_some_iff.mp childLookup).2
          simp only [childEq, zero_add]

private theorem semantic_mem_hierarchyAddresses_of_subtreeAt?
    {V : Type*} [DecidableEq V]
    (tree subtree : OfficialCIPSourceTree V) (address : List Nat)
    (lookup : tree.subtreeAt? address = some subtree) :
    address ∈ tree.hierarchyAddresses := by
  simp only [OfficialCIPSourceTree.hierarchyAddresses, List.mem_cons, List.mem_flatMap]
  right
  refine ⟨(address, subtree.source),
    semantic_mem_occurrences_of_subtreeAt? tree subtree address lookup, ?_⟩
  rw [List.mem_inits]

private theorem semantic_subtreeAt?_singleton_get
    {V : Type*} (tree : OfficialCIPSourceTree V)
    (slot : Fin tree.children.length) :
    tree.subtreeAt? [slot.1] = some (tree.children.get slot) := by
  cases tree with
  | node source children =>
      simp [OfficialCIPSourceTree.children, OfficialCIPSourceTree.subtreeAt?]

private theorem semantic_hierarchyChild_slot_lt
    {V : Type*} [DecidableEq V]
    (tree : OfficialCIPSourceTree V) (parent child : tree.HierarchyNode)
    (parentTree : OfficialCIPSourceTree V)
    (parentLookup : tree.subtreeAt? parent.1 = some parentTree)
    (slot : Nat) (childAddress : child.1 = parent.1 ++ [slot]) :
    slot < parentTree.children.length := by
  obtain ⟨childTree, childLookup, _⟩ := tree.exists_source_lookup child
  have within : parentTree.subtreeAt? [slot] = some childTree := by
    rw [childAddress, tree.subtreeAt?_append, parentLookup] at childLookup
    simpa using childLookup
  cases parentTree with
  | node source children =>
      simp only [OfficialCIPSourceTree.subtreeAt?] at within
      cases selected : children[slot]? with
      | none => simp [selected] at within
      | some child => exact (List.getElem?_eq_some_iff.mp selected).1

/-- Immediate hierarchy children are exactly the recursive child-tree slots. -/
noncomputable def semanticHierarchyChildrenEquivFin
    {V : Type*} [DecidableEq V]
    (tree : OfficialCIPSourceTree V) (parent : tree.HierarchyNode)
    (parentTree : OfficialCIPSourceTree V)
    (parentLookup : tree.subtreeAt? parent.1 = some parentTree) :
    {child : tree.HierarchyNode // tree.HierarchyChild parent child} ≃
      Fin parentTree.children.length where
  toFun child := by
    let slot := Classical.choose child.2
    have childAddress := Classical.choose_spec child.2
    exact ⟨slot, semantic_hierarchyChild_slot_lt tree parent child.1 parentTree
      parentLookup slot childAddress⟩
  invFun slot := by
    let childTree := parentTree.children.get slot
    let address := parent.1 ++ [slot.1]
    have childLookup : tree.subtreeAt? address = some childTree := by
      rw [tree.subtreeAt?_append, parentLookup]
      exact semantic_subtreeAt?_singleton_get parentTree slot
    exact ⟨⟨address,
      semantic_mem_hierarchyAddresses_of_subtreeAt? tree childTree address childLookup⟩,
      ⟨slot.1, rfl⟩⟩
  left_inv child := by
    apply Subtype.ext
    apply Subtype.ext
    let slot := Classical.choose child.2
    have childAddress := Classical.choose_spec child.2
    change parent.1 ++ [slot] = child.1.1
    exact childAddress.symm
  right_inv slot := by
    apply Fin.ext
    let childTree := parentTree.children.get slot
    let address := parent.1 ++ [slot.1]
    let child : {child : tree.HierarchyNode // tree.HierarchyChild parent child} :=
      ⟨⟨address, semantic_mem_hierarchyAddresses_of_subtreeAt? tree childTree address (by
        rw [tree.subtreeAt?_append, parentLookup]
        exact semantic_subtreeAt?_singleton_get parentTree slot)⟩,
        ⟨slot.1, rfl⟩⟩
    have chosen := Classical.choose_spec child.2
    have singletonEq : [Classical.choose child.2] = [slot.1] :=
      List.append_cancel_left chosen.symm
    exact List.singleton_inj.mp singletonEq

/-- Generatedness upgrades child membership to an exact occurrence equivalence, retaining every
multiple-bond duplicate slot rather than quotienting equal source labels. -/
theorem semanticGeneratedSourceTree_childrenExact
    (molecule : MoleculeGraph (Fin atomCount))
    (tree : OfficialCIPSourceTree (Fin atomCount))
    (generated : tree.GeneratedBy molecule.semanticOfficialCIPChildren)
    (parent : tree.HierarchyNode) (parentTree : OfficialCIPSourceTree (Fin atomCount))
    (parentLookup : tree.subtreeAt? parent.1 = some parentTree) :
    ∃ equivalence :
        {child : tree.HierarchyNode // tree.HierarchyChild parent child} ≃
          Fin (molecule.semanticOfficialCIPChildren parentTree.source).length,
      ∀ child,
        ∃ childTree,
          tree.subtreeAt? child.1.1 = some childTree ∧
            childTree.source =
              (molecule.semanticOfficialCIPChildren parentTree.source).get
                (equivalence child) := by
  have parentGenerated := generated.of_subtreeAt?
    molecule.semanticOfficialCIPChildren parent.1 tree parentTree parentLookup
  cases parentTree with
  | node parentSource subtrees =>
      obtain ⟨permutationEquiv, permutationGet⟩ :=
        TetraStereo.OneCenter.List.Perm.exists_finEquiv_get parentGenerated.1
      let childSlots := semanticHierarchyChildrenEquivFin tree parent
        (.node parentSource subtrees) parentLookup
      let sourceSlots : Fin subtrees.length ≃
          Fin (subtrees.map OfficialCIPSourceTree.source).length :=
        finCongr (by simp)
      let equivalence := childSlots.trans (sourceSlots.trans permutationEquiv)
      refine ⟨equivalence, ?_⟩
      intro child
      let slot := childSlots child
      let childTree := subtrees.get slot
      have childAddress : child.1.1 = parent.1 ++ [slot.1] := by
        simpa [slot, childSlots, semanticHierarchyChildrenEquivFin] using
          (Classical.choose_spec child.2)
      have childLookup : tree.subtreeAt? child.1.1 = some childTree := by
        rw [childAddress, tree.subtreeAt?_append, parentLookup]
        exact semantic_subtreeAt?_singleton_get (.node parentSource subtrees) slot
      refine ⟨childTree, childLookup, ?_⟩
      calc
        childTree.source =
            (subtrees.map OfficialCIPSourceTree.source).get (sourceSlots slot) := by
              simp [childTree, sourceSlots]
        _ = (molecule.semanticOfficialCIPChildren parentSource).get
            (permutationEquiv (sourceSlots slot)) := permutationGet (sourceSlots slot)
        _ = (molecule.semanticOfficialCIPChildren parentSource).get
            (equivalence child) := by rfl

/-- Transport an arbitrary child predicate through exact recursive source occurrences. -/
theorem semanticGeneratedSourceTree_childCountWhere_eq_countP
    (molecule : MoleculeGraph (Fin atomCount))
    (tree : OfficialCIPSourceTree (Fin atomCount))
    (generated : tree.GeneratedBy molecule.semanticOfficialCIPChildren)
    (parent : tree.HierarchyNode) (parentTree : OfficialCIPSourceTree (Fin atomCount))
    (parentLookup : tree.subtreeAt? parent.1 = some parentTree)
    (nodePredicate : tree.HierarchyNode → Prop)
    (sourcePredicate : OfficialCIPNode (Fin atomCount) → Prop)
    [DecidablePred nodePredicate] [DecidablePred sourcePredicate]
    (predicateExact : ∀
      (child : {node : tree.HierarchyNode // tree.HierarchyChild parent node})
      (childTree : OfficialCIPSourceTree (Fin atomCount)),
      tree.subtreeAt? child.1.1 = some childTree →
        (nodePredicate child.1 ↔ sourcePredicate childTree.source)) :
    DeclarativeCIP.RootedDigraph.ChildCountWhere
        tree.toDeclarativeDigraph parent nodePredicate =
      (molecule.semanticOfficialCIPChildren parentTree.source).countP fun source =>
        decide (sourcePredicate source) := by
  classical
  unfold DeclarativeCIP.RootedDigraph.ChildCountWhere
  change Nat.card {node : tree.HierarchyNode //
    tree.HierarchyChild parent node ∧ nodePredicate node} = _
  obtain ⟨equivalence, childExact⟩ :=
    molecule.semanticGeneratedSourceTree_childrenExact tree generated
      parent parentTree parentLookup
  apply card_inter_equiv_countP
    (molecule.semanticOfficialCIPChildren parentTree.source)
    (fun node : tree.HierarchyNode => tree.HierarchyChild parent node)
    nodePredicate sourcePredicate equivalence
  intro child
  obtain ⟨childTree, childLookup, childSource⟩ := childExact child
  rw [← childSource]
  exact predicateExact child childTree childLookup

/-- The root of a generated semantic hierarchy has the exact independent real-ligand label. -/
theorem semanticGeneratedSourceTree_root_label
    (molecule : MoleculeGraph (Fin atomCount))
    (tree : OfficialCIPSourceTree (Fin atomCount))
    (center ligand : Fin atomCount)
    (_generated : tree.GeneratedBy molecule.semanticOfficialCIPChildren)
    (root : tree.source = OfficialCIPNode.rootFromEdge center ligand) :
    tree.toDeclarativeDigraph.label tree.toDeclarativeDigraph.root =
      ⟨some ligand, DeclarativeCIP.NodeProvenance.realAtom⟩ := by
  change tree.declarativeLabel ⟨[], tree.nil_mem_hierarchyAddresses⟩ = _
  simp [OfficialCIPSourceTree.declarativeLabel,
    OfficialCIPSourceTree.sourceAtAddress?, OfficialCIPSourceTree.subtreeAt?,
    root, OfficialCIPNode.toDeclarativeLabel, OfficialCIPNode.rootFromEdge,
    OfficialCIPNodeProvenance.toDeclarative]

/-- Every graph-native carrier label has the atom/provenance shape required by the independent
local specification. -/
theorem semanticGeneratedSourceTree_labelCompatible
    (molecule : MoleculeGraph (Fin atomCount))
    (tree : OfficialCIPSourceTree (Fin atomCount))
    (center ligand : Fin atomCount)
    (generated : tree.GeneratedBy molecule.semanticOfficialCIPChildren)
    (root : tree.source = OfficialCIPNode.rootFromEdge center ligand)
    (node : tree.HierarchyNode) :
    DeclarativeCIP.RootedDigraph.LabelCompatible
      (tree.toDeclarativeDigraph.label node) := by
  obtain ⟨subtree, lookup, _⟩ := tree.exists_source_lookup node
  obtain ⟨graphGenerated, atom, current⟩ :=
    molecule.semanticGeneratedSourceTree_source_valid tree center ligand
      generated root node subtree lookup
  change DeclarativeCIP.RootedDigraph.LabelCompatible (tree.declarativeLabel node)
  rw [tree.declarativeLabel_eq_of_subtreeAt? subtree node lookup]
  cases provenance : subtree.source.provenance with
  | realAtom =>
      simp [DeclarativeCIP.RootedDigraph.LabelCompatible,
        OfficialCIPNode.toDeclarativeLabel, OfficialCIPNodeProvenance.toDeclarative,
        provenance, current]
  | multipleBondDuplicate distance =>
      simp [DeclarativeCIP.RootedDigraph.LabelCompatible,
        OfficialCIPNode.toDeclarativeLabel, OfficialCIPNodeProvenance.toDeclarative,
        provenance, current]
  | ringDuplicate distance =>
      simp [DeclarativeCIP.RootedDigraph.LabelCompatible,
        OfficialCIPNode.toDeclarativeLabel, OfficialCIPNodeProvenance.toDeclarative,
        provenance, current]
  | placeholder kind distance =>
      simp [OfficialCIPNode.GraphGenerated, provenance] at graphGenerated

/-- Terminal provenance cannot have a generated recursive child. -/
theorem semanticGeneratedSourceTree_terminal
    (molecule : MoleculeGraph (Fin atomCount))
    (tree : OfficialCIPSourceTree (Fin atomCount))
    (center ligand : Fin atomCount)
    (generated : tree.GeneratedBy molecule.semanticOfficialCIPChildren)
    (root : tree.source = OfficialCIPNode.rootFromEdge center ligand)
    (node : tree.HierarchyNode)
    (terminal : DeclarativeCIP.RootedDigraph.ProvenanceTerminal
      (tree.toDeclarativeDigraph.label node).provenance) :
    ∀ child, ¬ tree.HierarchyChild node child := by
  intro child edge
  obtain ⟨parentTree, parentLookup, _⟩ := tree.exists_source_lookup node
  obtain ⟨childTree, childLookup, _⟩ := tree.exists_source_lookup child
  have present := generated.source_mem_of_hierarchyChild tree
    molecule.semanticOfficialCIPChildren node child parentTree childTree
    parentLookup childLookup edge
  have parentGenerated :=
    (molecule.semanticGeneratedSourceTree_source_valid tree center ligand generated root
      node parentTree parentLookup).1
  change DeclarativeCIP.RootedDigraph.ProvenanceTerminal
    (tree.declarativeLabel node).provenance at terminal
  rw [tree.declarativeLabel_eq_of_subtreeAt? parentTree node parentLookup] at terminal
  cases provenance : parentTree.source.provenance with
  | realAtom =>
      simp [OfficialCIPNode.toDeclarativeLabel,
        OfficialCIPNodeProvenance.toDeclarative, provenance,
        DeclarativeCIP.RootedDigraph.ProvenanceTerminal] at terminal
  | multipleBondDuplicate distance =>
      have duplicate : parentTree.source.isDuplicateLeaf = true := by
        simp [OfficialCIPNode.isDuplicateLeaf, provenance,
          OfficialCIPNodeProvenance.isDuplicateLeaf]
      simp [semanticOfficialCIPChildren, duplicate] at present
  | ringDuplicate distance =>
      have duplicate : parentTree.source.isDuplicateLeaf = true := by
        simp [OfficialCIPNode.isDuplicateLeaf, provenance,
          OfficialCIPNodeProvenance.isDuplicateLeaf]
      simp [semanticOfficialCIPChildren, duplicate] at present
  | placeholder kind distance =>
      simp [OfficialCIPNode.GraphGenerated, provenance] at parentGenerated

/-- The generated graph-native hierarchy satisfies every local independent expansion clause. -/
theorem semanticGeneratedSourceTree_locallyAdmissibleExpansion
    (molecule : MoleculeGraph (Fin atomCount))
    (tree : OfficialCIPSourceTree (Fin atomCount))
    (center ligand : Fin atomCount)
    (generated : tree.GeneratedBy molecule.semanticOfficialCIPChildren)
    (root : tree.source = OfficialCIPNode.rootFromEdge center ligand) :
    DeclarativeCIP.RootedDigraph.LocallyAdmissibleExpansion
      molecule ligand tree.toDeclarativeDigraph := by
  refine ⟨molecule.semanticGeneratedSourceTree_root_label tree center ligand generated root,
    molecule.semanticGeneratedSourceTree_labelCompatible tree center ligand generated root,
    ?_, ?_⟩
  · intro node terminal child
    exact molecule.semanticGeneratedSourceTree_terminal tree center ligand generated root
      node terminal child
  · intro parent child parentAtom childAtom edge parentLabel childLabel
    exact molecule.semanticGeneratedSourceTree_edge_adj tree generated parent child
      parentAtom childAtom edge parentLabel childLabel

/-- Generated graph-native source trees satisfy exact multiple-bond and ring duplicate distances
under their canonical ranked-sibling addressing. -/
theorem semanticGeneratedSourceTree_duplicateDistancesCorrect
    (molecule : MoleculeGraph (Fin atomCount))
    (tree : OfficialCIPSourceTree (Fin atomCount))
    (center ligand : Fin atomCount)
    (generated : tree.GeneratedBy molecule.semanticOfficialCIPChildren)
    (root : tree.source = OfficialCIPNode.rootFromEdge center ligand) :
    DeclarativeCIP.RootedDigraph.DuplicateDistancesCorrect
      tree.toDeclarativeDigraph center tree.declarativeAddressing := by
  intro parent child edge
  obtain ⟨parentTree, parentLookup, _⟩ := tree.exists_source_lookup parent
  obtain ⟨childTree, childLookup, _⟩ := tree.exists_source_lookup child
  have childPresent := generated.source_mem_of_hierarchyChild tree
    molecule.semanticOfficialCIPChildren parent child parentTree childTree
    parentLookup childLookup edge
  have labelIdentity := tree.declarativeLabel_eq_of_subtreeAt? childTree child childLookup
  cases label : tree.toDeclarativeDigraph.label child with
  | mk atom? provenance =>
      cases provenance with
      | realAtom => trivial
      | multipleBondDuplicate distance =>
          have sourceProvenance : childTree.source.provenance =
              OfficialCIPNodeProvenance.multipleBondDuplicate distance := by
            have observed := congrArg DeclarativeCIP.NodeLabel.provenance label
            rw [show tree.toDeclarativeDigraph.label child = tree.declarativeLabel child by rfl,
              labelIdentity] at observed
            cases source : childTree.source.provenance with
            | realAtom =>
                simp [OfficialCIPNode.toDeclarativeLabel,
                  OfficialCIPNodeProvenance.toDeclarative, source] at observed
            | multipleBondDuplicate actual =>
                simp [OfficialCIPNode.toDeclarativeLabel,
                  OfficialCIPNodeProvenance.toDeclarative, source] at observed
                subst actual
                rfl
            | ringDuplicate actual =>
                simp [OfficialCIPNode.toDeclarativeLabel,
                  OfficialCIPNodeProvenance.toDeclarative, source] at observed
            | placeholder kind actual =>
                cases kind <;> simp [OfficialCIPNode.toDeclarativeLabel,
                  OfficialCIPNodeProvenance.toDeclarative, source] at observed
          have payload := molecule.semanticOfficialCIPChildren_multipleBondDuplicate_distance
            parentTree.source childTree.source childPresent distance sourceProvenance
          have parentLength := molecule.semanticGeneratedSourceTree_history_length
            tree center ligand generated root parent parentTree parentLookup
          change distance = parent.1.length + 1
          rw [payload]
          unfold OfficialCIPNode.depth
          omega
      | ringDuplicate distance =>
          cases atom? with
          | none =>
              have atomless := congrArg DeclarativeCIP.NodeLabel.atom? label
              rw [show tree.toDeclarativeDigraph.label child = tree.declarativeLabel child by rfl,
                labelIdentity] at atomless
              obtain ⟨next, copyIndex, childIdentity⟩ :=
                molecule.semanticOfficialCIPChildren_extension
                  parentTree.source childTree.source childPresent
              simp [OfficialCIPNode.toDeclarativeLabel, childIdentity] at atomless
          | some atom =>
              have current : childTree.source.current? = some atom := by
                have observed := congrArg DeclarativeCIP.NodeLabel.atom? label
                rw [show tree.toDeclarativeDigraph.label child = tree.declarativeLabel child by rfl,
                  labelIdentity] at observed
                simpa [OfficialCIPNode.toDeclarativeLabel] using observed
              have sourceProvenance : childTree.source.provenance =
                  OfficialCIPNodeProvenance.ringDuplicate distance := by
                have observed := congrArg DeclarativeCIP.NodeLabel.provenance label
                rw [show tree.toDeclarativeDigraph.label child = tree.declarativeLabel child by rfl,
                  labelIdentity] at observed
                cases source : childTree.source.provenance with
                | realAtom =>
                    simp [OfficialCIPNode.toDeclarativeLabel,
                      OfficialCIPNodeProvenance.toDeclarative, source] at observed
                | multipleBondDuplicate actual =>
                    simp [OfficialCIPNode.toDeclarativeLabel,
                      OfficialCIPNodeProvenance.toDeclarative, source] at observed
                | ringDuplicate actual =>
                    simp [OfficialCIPNode.toDeclarativeLabel,
                      OfficialCIPNodeProvenance.toDeclarative, source] at observed
                    subst actual
                    rfl
                | placeholder kind actual =>
                    cases kind <;> simp [OfficialCIPNode.toDeclarativeLabel,
                      OfficialCIPNodeProvenance.toDeclarative, source] at observed
              have firstIndex := molecule.semanticOfficialCIPChildren_ringDuplicate_firstIndex
                parentTree.source childTree.source childPresent atom distance current
                sourceProvenance
              have historyGet := semanticFirstIndexOf?_eq_some_imp_getElem?
                atom parentTree.source.history.reverse distance firstIndex
              have realized := molecule.semanticGeneratedSourceTree_history_index_realized
                tree center ligand generated root parent parentTree parentLookup
                distance atom historyGet
              rcases realized with atCenter | atParentOrAncestor
              · exact Or.inl ⟨atCenter.2, atCenter.1⟩
              · rcases atParentOrAncestor with atParent | atAncestor
                · have adjacent := molecule.adj_of_mem_semanticOfficialCIPChildren
                    parentTree.source childTree.source atom atom atParent.2 current childPresent
                  simp [MoleculeGraph.Adj, molecule.bond_self] at adjacent
                · rcases atAncestor with
                    ⟨ancestor, ancestorPath, ancestorAtom, ancestorDistance⟩
                  exact Or.inr ⟨ancestor, ancestorPath, ancestorAtom, by
                    simpa [OfficialCIPSourceTree.declarativeAddressing] using ancestorDistance⟩
      | phantom distance => trivial
      | lonePair distance => trivial
      | auxiliary distance => trivial

/-- Exact molecular child multiplicities follow from the generated occurrence equivalence and the
canonical indexed-copy count identities. -/
theorem semanticGeneratedSourceTree_atomChildMultiplicities
    (molecule : MoleculeGraph (Fin atomCount))
    (tree : OfficialCIPSourceTree (Fin atomCount))
    (center ligand : Fin atomCount)
    (generated : tree.GeneratedBy molecule.semanticOfficialCIPChildren)
    (root : tree.source = OfficialCIPNode.rootFromEdge center ligand) :
    DeclarativeCIP.RootedDigraph.AtomChildMultiplicities
      molecule center tree.toDeclarativeDigraph := by
  classical
  intro parent parentAtom parentLabel parentReal target
  obtain ⟨parentTree, parentLookup, _⟩ := tree.exists_source_lookup parent
  change (tree.declarativeLabel parent).atom? = some parentAtom at parentLabel
  change DeclarativeCIP.RootedDigraph.ProvenanceRealAtom
    (tree.declarativeLabel parent).provenance at parentReal
  rw [tree.declarativeLabel_eq_of_subtreeAt? parentTree parent parentLookup] at parentLabel parentReal
  have parentCurrent : parentTree.source.current? = some parentAtom := by
    simpa [OfficialCIPNode.toDeclarativeLabel] using parentLabel
  have parentSourceReal :
      parentTree.source.provenance = OfficialCIPNodeProvenance.realAtom := by
    cases provenance : parentTree.source.provenance with
    | realAtom => rfl
    | multipleBondDuplicate distance =>
        simp [OfficialCIPNode.toDeclarativeLabel,
          OfficialCIPNodeProvenance.toDeclarative, provenance,
          DeclarativeCIP.RootedDigraph.ProvenanceRealAtom] at parentReal
    | ringDuplicate distance =>
        simp [OfficialCIPNode.toDeclarativeLabel,
          OfficialCIPNodeProvenance.toDeclarative, provenance,
          DeclarativeCIP.RootedDigraph.ProvenanceRealAtom] at parentReal
    | placeholder kind distance =>
        cases kind <;> simp [OfficialCIPNode.toDeclarativeLabel,
          OfficialCIPNodeProvenance.toDeclarative, provenance,
          DeclarativeCIP.RootedDigraph.ProvenanceRealAtom] at parentReal
  have historyLength := molecule.semanticGeneratedSourceTree_history_length tree
    center ligand generated root parent parentTree parentLookup
  obtain ⟨previous, previousObserved, previousInHistory⟩ :
      ∃ previous,
        parentTree.source.parent? = some previous ∧ previous ∈ parentTree.source.history := by
    cases historyObserved : parentTree.source.history with
    | nil => simp [historyObserved] at historyLength
    | cons first rest =>
        cases rest with
        | nil => simp [historyObserved] at historyLength
        | cons second tail =>
            exact ⟨second, by simp [OfficialCIPNode.parent?, historyObserved], by simp⟩
  have previousIff := molecule.semanticGeneratedSourceTree_suppressedParentAtom_iff_eq
    tree center ligand parentAtom previous target generated root parent parentTree
    parentLookup parentCurrent previousObserved
  have adjacencyDistinct : molecule.Adj parentAtom target → target ≠ parentAtom := by
    intro adjacent same
    subst target
    simp [MoleculeGraph.Adj, molecule.bond_self] at adjacent
  have historyIffOfAdjacent (adjacent : molecule.Adj parentAtom target) :
      DeclarativeCIP.RootedDigraph.BranchAncestorAtom
          tree.toDeclarativeDigraph center target parent ↔
        target ∈ parentTree.source.history :=
    molecule.semanticGeneratedSourceTree_branchAncestorAtom_iff_mem_history tree
      center ligand parentAtom target generated root parent parentTree parentLookup
      parentCurrent (adjacencyDistinct adjacent)
  have parentNotDuplicate : parentTree.source.isDuplicateLeaf = false := by
    simp [OfficialCIPNode.isDuplicateLeaf, parentSourceReal,
      OfficialCIPNodeProvenance.isDuplicateLeaf]

  have totalCount := molecule.semanticGeneratedSourceTree_childCountWhere_eq_countP
    tree generated parent parentTree parentLookup
    (fun child => (tree.toDeclarativeDigraph.label child).atom? = some target)
    (fun source => source.current? = some target) (by
      intro child childTree childLookup
      change (tree.declarativeLabel child.1).atom? = some target ↔ _
      rw [tree.declarativeLabel_eq_of_subtreeAt? childTree child.1 childLookup]
      simp [OfficialCIPNode.toDeclarativeLabel])
  have totalList :
      (molecule.semanticOfficialCIPChildren parentTree.source).countP
          (fun source => decide (source.current? = some target)) =
        (molecule.semanticOfficialChildCopies parentTree.source).countP
          (fun copy => copy.1 == target) := by
    simp only [semanticOfficialCIPChildren, parentNotDuplicate,
      Bool.false_eq_true, ↓reduceIte, List.countP_map]
    apply List.countP_congr
    intro copy _present
    rcases copy with ⟨atom, copyIndex⟩
    simp [OfficialCIPNode.extend]
  have totalCopies := molecule.semanticOfficialChildCopies_count_atom
    parentTree.source parentAtom previous target parentCurrent previousObserved

  have multipleCount := molecule.semanticGeneratedSourceTree_childCountWhere_eq_countP
    tree generated parent parentTree parentLookup
    (fun child => (tree.toDeclarativeDigraph.label child).atom? = some target ∧
      DeclarativeCIP.RootedDigraph.ProvenanceMultipleBondDuplicate
        (tree.toDeclarativeDigraph.label child).provenance)
    (fun source => source.current? = some target ∧
      ∃ distance, source.provenance = .multipleBondDuplicate distance) (by
      intro child childTree childLookup
      have childGenerated :=
        (molecule.semanticGeneratedSourceTree_source_valid tree center ligand generated root
          child.1 childTree childLookup).1
      change ((tree.declarativeLabel child.1).atom? = some target ∧
        DeclarativeCIP.RootedDigraph.ProvenanceMultipleBondDuplicate
          (tree.declarativeLabel child.1).provenance) ↔ _
      rw [tree.declarativeLabel_eq_of_subtreeAt? childTree child.1 childLookup]
      cases provenance : childTree.source.provenance with
      | realAtom => simp [OfficialCIPNode.toDeclarativeLabel,
          OfficialCIPNodeProvenance.toDeclarative, provenance,
          DeclarativeCIP.RootedDigraph.ProvenanceMultipleBondDuplicate]
      | multipleBondDuplicate distance => simp [OfficialCIPNode.toDeclarativeLabel,
          OfficialCIPNodeProvenance.toDeclarative, provenance,
          DeclarativeCIP.RootedDigraph.ProvenanceMultipleBondDuplicate]
      | ringDuplicate distance => simp [OfficialCIPNode.toDeclarativeLabel,
          OfficialCIPNodeProvenance.toDeclarative, provenance,
          DeclarativeCIP.RootedDigraph.ProvenanceMultipleBondDuplicate]
      | placeholder kind distance =>
          simp [OfficialCIPNode.GraphGenerated, provenance] at childGenerated)
  have multipleList :
      (molecule.semanticOfficialCIPChildren parentTree.source).countP
          (fun source => decide (source.current? = some target ∧
            ∃ distance, source.provenance = .multipleBondDuplicate distance)) =
        (molecule.semanticOfficialChildCopies parentTree.source).countP
          (fun copy => (copy.1 == target) && (copy.2 != 0)) := by
    simp only [semanticOfficialCIPChildren, parentNotDuplicate,
      Bool.false_eq_true, ↓reduceIte, List.countP_map]
    apply List.countP_congr
    intro copy _present
    rcases copy with ⟨atom, copyIndex⟩
    by_cases zero : copyIndex = 0
    · subst copyIndex
      by_cases historical : atom ∈ parentTree.source.history <;>
        simp [OfficialCIPNode.extend, OfficialCIPNode.childProvenance, historical]
    · simp [OfficialCIPNode.extend, OfficialCIPNode.childProvenance, zero]
  have multipleCopies := molecule.semanticOfficialChildCopies_count_multiple
    parentTree.source parentAtom previous target parentCurrent previousObserved

  have ringCount := molecule.semanticGeneratedSourceTree_childCountWhere_eq_countP
    tree generated parent parentTree parentLookup
    (fun child => (tree.toDeclarativeDigraph.label child).atom? = some target ∧
      DeclarativeCIP.RootedDigraph.ProvenanceRingDuplicate
        (tree.toDeclarativeDigraph.label child).provenance)
    (fun source => source.current? = some target ∧
      ∃ distance, source.provenance = .ringDuplicate distance) (by
      intro child childTree childLookup
      have childGenerated :=
        (molecule.semanticGeneratedSourceTree_source_valid tree center ligand generated root
          child.1 childTree childLookup).1
      change ((tree.declarativeLabel child.1).atom? = some target ∧
        DeclarativeCIP.RootedDigraph.ProvenanceRingDuplicate
          (tree.declarativeLabel child.1).provenance) ↔ _
      rw [tree.declarativeLabel_eq_of_subtreeAt? childTree child.1 childLookup]
      cases provenance : childTree.source.provenance with
      | realAtom => simp [OfficialCIPNode.toDeclarativeLabel,
          OfficialCIPNodeProvenance.toDeclarative, provenance,
          DeclarativeCIP.RootedDigraph.ProvenanceRingDuplicate]
      | multipleBondDuplicate distance => simp [OfficialCIPNode.toDeclarativeLabel,
          OfficialCIPNodeProvenance.toDeclarative, provenance,
          DeclarativeCIP.RootedDigraph.ProvenanceRingDuplicate]
      | ringDuplicate distance => simp [OfficialCIPNode.toDeclarativeLabel,
          OfficialCIPNodeProvenance.toDeclarative, provenance,
          DeclarativeCIP.RootedDigraph.ProvenanceRingDuplicate]
      | placeholder kind distance =>
          simp [OfficialCIPNode.GraphGenerated, provenance] at childGenerated)
  have ringList :
      (molecule.semanticOfficialCIPChildren parentTree.source).countP
          (fun source => decide (source.current? = some target ∧
            ∃ distance, source.provenance = .ringDuplicate distance)) =
        (molecule.semanticOfficialChildCopies parentTree.source).countP
          (fun copy => (copy.1 == target) && (copy.2 == 0) &&
            decide (target ∈ parentTree.source.history)) := by
    simp only [semanticOfficialCIPChildren, parentNotDuplicate,
      Bool.false_eq_true, ↓reduceIte, List.countP_map]
    apply List.countP_congr
    intro copy _present
    rcases copy with ⟨atom, copyIndex⟩
    by_cases zero : copyIndex = 0
    · subst copyIndex
      by_cases same : atom = target
      · subst atom
        by_cases historical : target ∈ parentTree.source.history <;>
          simp [OfficialCIPNode.extend, OfficialCIPNode.childProvenance, historical]
      · by_cases historical : atom ∈ parentTree.source.history <;>
          simp [OfficialCIPNode.extend, OfficialCIPNode.childProvenance,
            historical, same]
    · simp [OfficialCIPNode.extend, OfficialCIPNode.childProvenance, zero]
  have ringCopies := molecule.semanticOfficialChildCopies_count_ring
    parentTree.source parentAtom previous target parentCurrent previousObserved

  have realCount := molecule.semanticGeneratedSourceTree_childCountWhere_eq_countP
    tree generated parent parentTree parentLookup
    (fun child => (tree.toDeclarativeDigraph.label child).atom? = some target ∧
      DeclarativeCIP.RootedDigraph.ProvenanceRealAtom
        (tree.toDeclarativeDigraph.label child).provenance)
    (fun source => source.current? = some target ∧
      source.provenance = .realAtom) (by
      intro child childTree childLookup
      have childGenerated :=
        (molecule.semanticGeneratedSourceTree_source_valid tree center ligand generated root
          child.1 childTree childLookup).1
      change ((tree.declarativeLabel child.1).atom? = some target ∧
        DeclarativeCIP.RootedDigraph.ProvenanceRealAtom
          (tree.declarativeLabel child.1).provenance) ↔ _
      rw [tree.declarativeLabel_eq_of_subtreeAt? childTree child.1 childLookup]
      cases provenance : childTree.source.provenance with
      | realAtom => simp [OfficialCIPNode.toDeclarativeLabel,
          OfficialCIPNodeProvenance.toDeclarative, provenance,
          DeclarativeCIP.RootedDigraph.ProvenanceRealAtom]
      | multipleBondDuplicate distance => simp [OfficialCIPNode.toDeclarativeLabel,
          OfficialCIPNodeProvenance.toDeclarative, provenance,
          DeclarativeCIP.RootedDigraph.ProvenanceRealAtom]
      | ringDuplicate distance => simp [OfficialCIPNode.toDeclarativeLabel,
          OfficialCIPNodeProvenance.toDeclarative, provenance,
          DeclarativeCIP.RootedDigraph.ProvenanceRealAtom]
      | placeholder kind distance =>
          simp [OfficialCIPNode.GraphGenerated, provenance] at childGenerated)
  have realList :
      (molecule.semanticOfficialCIPChildren parentTree.source).countP
          (fun source => decide (source.current? = some target ∧
            source.provenance = .realAtom)) =
        (molecule.semanticOfficialChildCopies parentTree.source).countP
          (fun copy => (copy.1 == target) && (copy.2 == 0) &&
            decide (target ∉ parentTree.source.history)) := by
    simp only [semanticOfficialCIPChildren, parentNotDuplicate,
      Bool.false_eq_true, ↓reduceIte, List.countP_map]
    apply List.countP_congr
    intro copy _present
    rcases copy with ⟨atom, copyIndex⟩
    by_cases zero : copyIndex = 0
    · subst copyIndex
      by_cases historical : atom ∈ parentTree.source.history <;>
        by_cases same : atom = target <;>
          simp [OfficialCIPNode.extend, OfficialCIPNode.childProvenance,
            historical, same]
    · simp [OfficialCIPNode.extend, OfficialCIPNode.childProvenance, zero]
  have realCopies := molecule.semanticOfficialChildCopies_count_real
    parentTree.source parentAtom previous target parentCurrent previousObserved previousInHistory

  refine ⟨?_, ?_, ?_, ?_⟩
  · change DeclarativeCIP.RootedDigraph.ChildCountWhere tree.toDeclarativeDigraph parent
        (fun child => (tree.toDeclarativeDigraph.label child).atom? = some target) = _
    calc
      _ = (molecule.semanticOfficialCIPChildren parentTree.source).countP
          (fun source => decide (source.current? = some target)) := totalCount
      _ = (molecule.semanticOfficialChildCopies parentTree.source).countP
          (fun copy => copy.1 == target) := totalList
      _ = molecule.bond parentAtom target -
          (if target = previous then 1 else 0) := totalCopies
      _ = molecule.bond parentAtom target -
          (if DeclarativeCIP.RootedDigraph.SuppressedParentAtom
            tree.toDeclarativeDigraph center target parent then 1 else 0) := by
              by_cases same : target = previous
              · rw [if_pos same, if_pos (previousIff.mpr same)]
              · rw [if_neg same, if_neg (fun suppressed => same (previousIff.mp suppressed))]
  · change DeclarativeCIP.RootedDigraph.ChildCountWhere tree.toDeclarativeDigraph parent
        (fun child => (tree.toDeclarativeDigraph.label child).atom? = some target ∧
          DeclarativeCIP.RootedDigraph.ProvenanceMultipleBondDuplicate
            (tree.toDeclarativeDigraph.label child).provenance) = _
    calc
      _ = (molecule.semanticOfficialCIPChildren parentTree.source).countP
          (fun source => decide (source.current? = some target ∧
            ∃ distance, source.provenance = .multipleBondDuplicate distance)) := multipleCount
      _ = (molecule.semanticOfficialChildCopies parentTree.source).countP
          (fun copy => (copy.1 == target) && (copy.2 != 0)) := multipleList
      _ = molecule.bond parentAtom target - 1 := multipleCopies
  · change DeclarativeCIP.RootedDigraph.ChildCountWhere tree.toDeclarativeDigraph parent
        (fun child => (tree.toDeclarativeDigraph.label child).atom? = some target ∧
          DeclarativeCIP.RootedDigraph.ProvenanceRingDuplicate
            (tree.toDeclarativeDigraph.label child).provenance) = _
    calc
      _ = (molecule.semanticOfficialCIPChildren parentTree.source).countP
          (fun source => decide (source.current? = some target ∧
            ∃ distance, source.provenance = .ringDuplicate distance)) := ringCount
      _ = (molecule.semanticOfficialChildCopies parentTree.source).countP
          (fun copy => (copy.1 == target) && (copy.2 == 0) &&
            decide (target ∈ parentTree.source.history)) := ringList
      _ = if molecule.Adj parentAtom target ∧ target ∈ parentTree.source.history ∧
          target ≠ previous then 1 else 0 := ringCopies
      _ = if molecule.Adj parentAtom target ∧
          DeclarativeCIP.RootedDigraph.BranchAncestorAtom
            tree.toDeclarativeDigraph center target parent ∧
          ¬DeclarativeCIP.RootedDigraph.SuppressedParentAtom
            tree.toDeclarativeDigraph center target parent then 1 else 0 := by
              congr 1
              apply propext
              constructor
              · rintro ⟨adjacent, historical, notPrevious⟩
                exact ⟨adjacent, (historyIffOfAdjacent adjacent).mpr historical,
                  fun suppressed => notPrevious (previousIff.mp suppressed)⟩
              · rintro ⟨adjacent, ancestor, notSuppressed⟩
                exact ⟨adjacent, (historyIffOfAdjacent adjacent).mp ancestor,
                  fun same => notSuppressed (previousIff.mpr same)⟩
  · change DeclarativeCIP.RootedDigraph.ChildCountWhere tree.toDeclarativeDigraph parent
        (fun child => (tree.toDeclarativeDigraph.label child).atom? = some target ∧
          DeclarativeCIP.RootedDigraph.ProvenanceRealAtom
            (tree.toDeclarativeDigraph.label child).provenance) = _
    calc
      _ = (molecule.semanticOfficialCIPChildren parentTree.source).countP
          (fun source => decide (source.current? = some target ∧
            source.provenance = .realAtom)) := realCount
      _ = (molecule.semanticOfficialChildCopies parentTree.source).countP
          (fun copy => (copy.1 == target) && (copy.2 == 0) &&
            decide (target ∉ parentTree.source.history)) := realList
      _ = if molecule.Adj parentAtom target ∧
          target ∉ parentTree.source.history then 1 else 0 := realCopies
      _ = if molecule.Adj parentAtom target ∧
          ¬DeclarativeCIP.RootedDigraph.BranchAncestorAtom
            tree.toDeclarativeDigraph center target parent then 1 else 0 := by
              congr 1
              apply propext
              constructor
              · rintro ⟨adjacent, notHistorical⟩
                exact ⟨adjacent, fun ancestor =>
                  notHistorical ((historyIffOfAdjacent adjacent).mp ancestor)⟩
              · rintro ⟨adjacent, notAncestor⟩
                exact ⟨adjacent, fun historical =>
                  notAncestor ((historyIffOfAdjacent adjacent).mpr historical)⟩

/-- A proof-carrying graph-native official hierarchy package.  It contains the exact key and the
recursive physical source tree; later child-count and duplicate-distance algebra can refine its
`toDeclarativeDigraph` to `FaithfulExactExpansion` without returning to a source format. -/
structure SemanticOfficialHierarchy
    (molecule : MoleculeGraph (Fin atomCount)) (center ligand : Fin atomCount) where
  tree : OfficialCIPSourceTree (Fin atomCount)
  generated : tree.GeneratedBy molecule.semanticOfficialCIPChildren
  rootSource : tree.source = OfficialCIPNode.rootFromEdge center ligand

/-- The canonical hierarchy value is computed directly from the canonical semantic child
enumerator.  Its data contains no proof-facing priority sort and no reviewed Rule-1a relation. -/
def semanticOfficialHierarchy
    (molecule : MoleculeGraph (Fin atomCount)) (center ligand : Fin atomCount)
    (different : ligand ≠ center) : SemanticOfficialHierarchy molecule center ligand where
  tree := molecule.buildSemanticOfficialSourceTree (atomCount + 1)
    (OfficialCIPNode.rootFromEdge center ligand)
  generated := molecule.buildSemanticOfficialSourceTree_generated (atomCount + 1)
    (OfficialCIPNode.rootFromEdge center ligand)
    (molecule.semanticOfficialExpansionCompleteWithin_default center ligand different)
  rootSource := molecule.buildSemanticOfficialSourceTree_source (atomCount + 1)
    (OfficialCIPNode.rootFromEdge center ligand)

/-- Every distinct adjacent candidate pair has a complete graph-native official hierarchy.
Adjacency is retained for the final faithful-expansion assembly rather than used to make the
structural compiler total. -/
theorem semanticOfficialHierarchy_exists
    (molecule : MoleculeGraph (Fin atomCount)) (center ligand : Fin atomCount)
    (different : ligand ≠ center) (_rootBond : molecule.Adj center ligand) :
    Nonempty (SemanticOfficialHierarchy molecule center ligand) := by
  exact ⟨molecule.semanticOfficialHierarchy center ligand different⟩

/-- The declarative graph carried by every graph-native hierarchy has atom-bearing children. -/
theorem SemanticOfficialHierarchy.atomBearingChildren
    {molecule : MoleculeGraph (Fin atomCount)} {center ligand : Fin atomCount}
    (hierarchy : SemanticOfficialHierarchy molecule center ligand) :
    DeclarativeCIP.RootedDigraph.AtomBearingChildren hierarchy.tree.toDeclarativeDigraph :=
  molecule.semanticGeneratedSourceTree_atomBearingChildren hierarchy.tree hierarchy.generated

/-- The hierarchy package satisfies the complete local independent expansion semantics. -/
theorem SemanticOfficialHierarchy.locallyAdmissibleExpansion
    {molecule : MoleculeGraph (Fin atomCount)} {center ligand : Fin atomCount}
    (hierarchy : SemanticOfficialHierarchy molecule center ligand) :
    DeclarativeCIP.RootedDigraph.LocallyAdmissibleExpansion
      molecule ligand hierarchy.tree.toDeclarativeDigraph :=
  molecule.semanticGeneratedSourceTree_locallyAdmissibleExpansion hierarchy.tree
    center ligand hierarchy.generated hierarchy.rootSource

/-- The hierarchy package has correct duplicate distances under the canonical addressing. -/
theorem SemanticOfficialHierarchy.duplicateDistancesCorrect
    {molecule : MoleculeGraph (Fin atomCount)} {center ligand : Fin atomCount}
    (hierarchy : SemanticOfficialHierarchy molecule center ligand) :
    DeclarativeCIP.RootedDigraph.DuplicateDistancesCorrect
      hierarchy.tree.toDeclarativeDigraph center hierarchy.tree.declarativeAddressing :=
  molecule.semanticGeneratedSourceTree_duplicateDistancesCorrect hierarchy.tree
    center ligand hierarchy.generated hierarchy.rootSource

/-- The hierarchy package realizes the exact official child multiplicities at every real atom. -/
theorem SemanticOfficialHierarchy.atomChildMultiplicities
    {molecule : MoleculeGraph (Fin atomCount)} {center ligand : Fin atomCount}
    (hierarchy : SemanticOfficialHierarchy molecule center ligand) :
    DeclarativeCIP.RootedDigraph.AtomChildMultiplicities
      molecule center hierarchy.tree.toDeclarativeDigraph :=
  molecule.semanticGeneratedSourceTree_atomChildMultiplicities hierarchy.tree
    center ligand hierarchy.generated hierarchy.rootSource

/-- Final assembly after exact official-copy counting.  All chemically structural clauses are
discharged by the graph-native hierarchy itself; the sole explicit premise is the occurrence-count
identity isolated by `AtomChildMultiplicities`. -/
theorem SemanticOfficialHierarchy.faithfulExactExpansion_of_atomChildMultiplicities
    {molecule : MoleculeGraph (Fin atomCount)} {center ligand : Fin atomCount}
    (hierarchy : SemanticOfficialHierarchy molecule center ligand)
    (rootBond : molecule.Adj center ligand)
    (multiplicities : DeclarativeCIP.RootedDigraph.AtomChildMultiplicities
      molecule center hierarchy.tree.toDeclarativeDigraph) :
    DeclarativeCIP.RootedDigraph.FaithfulExactExpansion
      molecule center ligand hierarchy.tree.toDeclarativeDigraph := by
  exact DeclarativeCIP.RootedDigraph.faithfulExactExpansion_of_components
    molecule center ligand hierarchy.tree.toDeclarativeDigraph
    hierarchy.locallyAdmissibleExpansion hierarchy.tree.declarativeAddressing
    multiplicities rootBond hierarchy.atomBearingChildren
    hierarchy.duplicateDistancesCorrect

/-- Every graph-native official hierarchy over an adjacent root edge is a faithful exact
declarative expansion, with no external occurrence-count or source-format premise. -/
theorem SemanticOfficialHierarchy.faithfulExactExpansion
    {molecule : MoleculeGraph (Fin atomCount)} {center ligand : Fin atomCount}
    (hierarchy : SemanticOfficialHierarchy molecule center ligand)
    (rootBond : molecule.Adj center ligand) :
    DeclarativeCIP.RootedDigraph.FaithfulExactExpansion
      molecule center ligand hierarchy.tree.toDeclarativeDigraph :=
  hierarchy.faithfulExactExpansion_of_atomChildMultiplicities rootBond
    hierarchy.atomChildMultiplicities

/-- Every distinct adjacent center/ligand pair admits a complete graph-native official hierarchy
whose declarative graph is a faithful exact molecular expansion. -/
theorem semanticOfficialFaithfulExactExpansion_exists
    (molecule : MoleculeGraph (Fin atomCount)) (center ligand : Fin atomCount)
    (different : ligand ≠ center) (rootBond : molecule.Adj center ligand) :
    ∃ hierarchy : SemanticOfficialHierarchy molecule center ligand,
      DeclarativeCIP.RootedDigraph.FaithfulExactExpansion molecule center ligand
        hierarchy.tree.toDeclarativeDigraph := by
  rcases molecule.semanticOfficialHierarchy_exists center ligand different rootBond with
    ⟨hierarchy⟩
  exact ⟨hierarchy, hierarchy.faithfulExactExpansion rootBond⟩

end MoleculeGraph

end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.MoleculeGraph.semanticOfficialCIPChildren_perm_officialCIPChildren
assert_kernel_only
  TetraStereo.OneCenter.MoleculeGraph.buildSemanticOfficialSourceTree_generated
assert_kernel_only
  TetraStereo.OneCenter.MoleculeGraph.semanticGeneratedSourceTree_atomBearingChildren
assert_kernel_only
  TetraStereo.OneCenter.MoleculeGraph.semanticGeneratedSourceTree_edge_adj
assert_kernel_only
  TetraStereo.OneCenter.MoleculeGraph.semanticOfficialHierarchy_exists
assert_kernel_only
  TetraStereo.OneCenter.MoleculeGraph.semanticGeneratedSourceTree_locallyAdmissibleExpansion
assert_kernel_only
  TetraStereo.OneCenter.MoleculeGraph.semanticGeneratedSourceTree_duplicateDistancesCorrect
assert_kernel_only
  TetraStereo.OneCenter.MoleculeGraph.semanticGeneratedSourceTree_atomChildMultiplicities
assert_kernel_only
  TetraStereo.OneCenter.MoleculeGraph.SemanticOfficialHierarchy.atomChildMultiplicities
assert_kernel_only
  TetraStereo.OneCenter.MoleculeGraph.SemanticOfficialHierarchy.faithfulExactExpansion_of_atomChildMultiplicities
assert_kernel_only
  TetraStereo.OneCenter.MoleculeGraph.SemanticOfficialHierarchy.faithfulExactExpansion
assert_kernel_only
  TetraStereo.OneCenter.MoleculeGraph.semanticOfficialFaithfulExactExpansion_exists
