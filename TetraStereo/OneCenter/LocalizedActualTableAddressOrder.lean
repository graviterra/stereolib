import TetraStereo.OneCenter.LocalizedSparsePhysicalFirstDifference
import TetraStereo.OneCenter.LocalizedSparseSupportAlignment
import TetraStereo.OneCenter.LocalizedRealizedTreeCutEmbedding
import TetraStereo.OneCenter.LocalizedParentFrameHistory
import TetraStereo.OneCenter.Source2013ActualParentComparison
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput
open SparsePhysicalFirstDifference
open DeclarativeCIP

























































namespace LocalizedActualTableAddressOrder

/-! ## Address comparison below a shared sibling slot -/

/-- Prefixing both compared addresses with the same sibling slot does not change the executed
address comparison. -/
theorem AddressCompare_cons_cons_self (slot : ℕ) (left right : List ℕ) :
    AddressCompare (slot :: left) (slot :: right) = AddressCompare left right := by
  unfold AddressCompare
  rw [List.compareLex_cons_cons, compareNat_eq_iff_eq.mpr rfl, Ordering.eq_then]

/-- Addresses whose first sibling slots differ are decided by those slots: the strictly smaller
slot precedes. -/
theorem AddressCompare_cons_cons_of_lt {leftSlot rightSlot : ℕ} (before : leftSlot < rightSlot)
    (left right : List ℕ) :
    AddressCompare (leftSlot :: left) (rightSlot :: right) = Ordering.lt := by
  unfold AddressCompare
  rw [List.compareLex_cons_cons, compareNat_lt_iff_lt.mpr before, Ordering.lt_then]

/-! ## Blockwise ordering of the slot-indexed merge -/

/-- Prefixing every address of an increasing row with one fixed slot preserves row order. -/
theorem prefixLayer_pairwise {α : Type*} (slot : ℕ) (row : List (OfficialSparseEntry α))
    (sorted : row.Pairwise fun left right => AddressCompare left.1 right.1 = Ordering.lt) :
    (OfficialRuleMajorKey.prefixLayer slot row).Pairwise
      (fun left right => AddressCompare left.1 right.1 = Ordering.lt) := by
  unfold OfficialRuleMajorKey.prefixLayer
  rw [List.pairwise_map]
  exact sorted.imp fun {left right} less => by
    simpa using (AddressCompare_cons_cons_self slot left.1 right.1).trans less

/-- The `zipIdx` enumeration is strictly increasing in its slot component. -/
theorem pairwise_indices_zipIdx {α : Type*} (values : List α) :
    values.zipIdx.Pairwise fun left right => left.2 < right.2 := by
  apply List.pairwise_map.mp
  rw [List.zipIdx_map_snd]
  exact List.pairwise_lt_range'

/-- One sphere of a slot-indexed merge is address increasing whenever every involved child row
is.  Different slots are decided by `AddressCompare_cons_cons_of_lt`; equal slots cannot occur in
the `zipIdx` enumeration. -/
theorem mergePairs_zipIdx_pairwise {α : Type*} (values : List α)
    (layers : α → List (List (OfficialSparseEntry ℕ))) (depth : ℕ)
    (increasing : ∀ value ∈ values, RowsIncreasing (layers value)) :
    (SparseAddress.mergePairs values.zipIdx
        (fun value => (layers value).getD depth [])).Pairwise
      (fun left right => AddressCompare left.1 right.1 = Ordering.lt) := by
  show (values.zipIdx.flatMap fun pair =>
      OfficialRuleMajorKey.prefixLayer pair.2
        ((fun value => (layers value).getD depth []) pair.1)).Pairwise
    (fun left right => AddressCompare left.1 right.1 = Ordering.lt)
  rw [List.pairwise_flatMap]
  constructor
  · intro pair present
    have valueMem : pair.1 ∈ values := List.fst_mem_of_mem_zipIdx present
    exact prefixLayer_pairwise pair.2 ((layers pair.1).getD depth [])
      (increasing pair.1 valueMem depth)
  · exact (pairwise_indices_zipIdx values).imp fun {leftPair rightPair} slots => by
      intro leftEntry leftMem rightEntry rightMem
      rw [OfficialRuleMajorKey.prefixLayer, List.mem_map] at leftMem rightMem
      obtain ⟨leftInner, _leftInnerMem, leftEq⟩ := leftMem
      obtain ⟨rightInner, _rightInnerMem, rightEq⟩ := rightMem
      rw [← leftEq, ← rightEq]
      exact AddressCompare_cons_cons_of_lt slots leftInner.1 rightInner.1

/-! ## Address order of the actual compiled table -/

/-- **Every row of the actual cumulative table is strictly lexicographically address
increasing**, for every decorated tree and every observation.

The proof is by induction on the intrinsic height.  Sphere zero is the singleton root sphere.
Sphere `depth + 1` is the slot-prefixed merge of the child tables' sphere `depth`, which is empty
past the merge's layer count.  In the nonempty case the merge is a `flatMap` of child blocks; each
block is increasing by the induction hypothesis, and two distinct blocks are decided by their
`zipIdx` slots.  The observation function is never inspected, so the result is independent of
chemical sibling priority, of the sort trace, and of the physical domain. -/
theorem table_rowsIncreasing {input : CertifiedLocalizedCIPInput} {carrierFuel : ℕ}
    (observe : LocalizedCumulativeDecoratedTree input carrierFuel → ℕ) :
    ∀ tree : LocalizedCumulativeDecoratedTree input carrierFuel,
      RowsIncreasing (LocalizedCumulativeDecoratedTree.table observe tree) := by
  intro tree
  have main : ∀ n : ℕ, ∀ candidate : LocalizedCumulativeDecoratedTree input carrierFuel,
      LocalizedCumulativeDecoratedTree.height candidate ≤ n →
        RowsIncreasing (LocalizedCumulativeDecoratedTree.table observe candidate) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro k inductionHypothesis candidate bound depth
    cases depth with
    | zero =>
        rw [LocalizedCumulativeDecoratedTree.table_getD_zero]
        refine List.pairwise_cons.mpr ⟨?_, List.Pairwise.nil⟩
        intro entry present
        simp at present
    | succ depth =>
        rw [LocalizedCumulativeDecoratedTree.table_eq_root_merge,
          LocalizedCumulativeDecoratedTree.getD_root_cons]
        unfold LocalizedCumulativeDecoratedTree.mergeLocalizedTreeChildTables
        rw [SparseAddress.mergePairTable_getD]
        by_cases inside :
            depth < LocalizedCumulativeDecoratedTree.localizedTreeChildLayerCount
              (candidate.children.map (LocalizedCumulativeDecoratedTree.table observe))
        · rw [if_pos inside]
          refine mergePairs_zipIdx_pairwise
            (candidate.children.map (LocalizedCumulativeDecoratedTree.table observe)) id depth ?_
          intro value present
          obtain ⟨child, childMem, same⟩ := List.mem_map.mp present
          rw [← same]
          refine inductionHypothesis (LocalizedCumulativeDecoratedTree.height child) ?_
            child (le_refl _)
          have smaller :=
            LocalizedCumulativeDecoratedTree.height_lt_height_of_mem candidate childMem
          omega
        · rw [if_neg inside]
          exact List.Pairwise.nil
  exact main (LocalizedCumulativeDecoratedTree.height tree) tree (le_refl _)




theorem table_wellFormed {input : CertifiedLocalizedCIPInput} {carrierFuel : ℕ}
    (observe : LocalizedCumulativeDecoratedTree input carrierFuel → ℕ)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    SparseTableWellFormed (LocalizedCumulativeDecoratedTree.table observe tree) :=
  table_wellFormed_of_order observe tree (table_rowsIncreasing observe tree)

/-! ## The address schedule is observation-independent

The compiled sphere at `depth + 1` depends on the observation only through the *values* stored at
the addresses; the addresses themselves are generated by `zipIdx` and `prefixLayer` and by the
child list alone.  The next results make that explicit and package it in
`SparseSupportAlignment.SameAddressRows`, so a Rule-1b, mass, or any other observation column built
from the same decorated tree can be compared on the Rule-1a address schedule without assuming
anything about chemical sibling priority or about the observation type. -/

/-- Prefixing a row with a slot and then reading its addresses is the same as reading the
addresses first and prefixing each one. -/
theorem prefixLayer_map_fst {α : Type*} (slot : ℕ) (row : List (OfficialSparseEntry α)) :
    (OfficialRuleMajorKey.prefixLayer slot row).map Prod.fst =
      (row.map Prod.fst).map fun address => slot :: address := by
  simp only [OfficialRuleMajorKey.prefixLayer, List.map_map]
  rfl

/-- `flatMap` respects pointwise equality of the block function. -/
theorem flatMap_congr_of_mem {γ δ : Type*} (values : List γ) (left right : γ → List δ)
    (agree : ∀ value ∈ values, left value = right value) :
    values.flatMap left = values.flatMap right := by
  induction values with
  | nil => rfl
  | cons value rest inductionHypothesis =>
      simp only [List.flatMap_cons]
      rw [agree value (by simp),
        inductionHypothesis (fun other present => agree other (by simp [present]))]

/-- The `zipIdx` of a mapped list, with the mapped values and the original slots. -/
theorem zipIdx_map_eq {γ δ : Type*} (values : List γ) (embed : γ → δ) :
    (values.map embed).zipIdx = values.zipIdx.map fun pair => (embed pair.1, pair.2) := by
  rw [List.zipIdx_map]
  apply List.map_congr_left
  intro pair _
  cases pair with
  | mk value slot => rfl

/-- A slot-indexed merge of a mapped child list is the same merge indexed by the original
children. -/
theorem mergePairs_map_zipIdx {γ δ α : Type*} (values : List γ) (embed : γ → δ)
    (block : δ → List (OfficialSparseEntry α)) :
    SparseAddress.mergePairs (values.map embed).zipIdx block =
      values.zipIdx.flatMap fun pair =>
        OfficialRuleMajorKey.prefixLayer pair.2 (block (embed pair.1)) := by
  unfold SparseAddress.mergePairs
  rw [zipIdx_map_eq]
  rw [List.flatMap_map (f := fun pair : γ × ℕ => (embed pair.1, pair.2))
    (g := fun pair => OfficialRuleMajorKey.prefixLayer pair.2 (block pair.1))]

/-- The layer count of a list of child tables depends only on the children's heights, hence not
on the observed column. -/
theorem localizedTreeChildLayerCount_map_eq {input : CertifiedLocalizedCIPInput}
    {carrierFuel : ℕ} {α : Type*}
    (observe : LocalizedCumulativeDecoratedTree input carrierFuel → α)
    (children : List (LocalizedCumulativeDecoratedTree input carrierFuel)) :
    LocalizedCumulativeDecoratedTree.localizedTreeChildLayerCount
        (children.map (LocalizedCumulativeDecoratedTree.table observe)) =
      children.foldl
        (fun longest child => max longest (LocalizedCumulativeDecoratedTree.height child)) 0 := by
  unfold LocalizedCumulativeDecoratedTree.localizedTreeChildLayerCount
  have general : ∀ init : ℕ,
      (children.map (LocalizedCumulativeDecoratedTree.table observe)).foldl
          (fun longest table => max longest table.length) init =
        children.foldl
          (fun longest child => max longest (LocalizedCumulativeDecoratedTree.height child))
          init := by
    intro init
    rw [List.foldl_map]
    induction children generalizing init with
    | nil => rfl
    | cons child rest inductionHypothesis =>
        simp only [List.foldl_cons]
        rw [LocalizedCumulativeDecoratedTree.table_length_eq_height]
        exact inductionHypothesis
          (max init (LocalizedCumulativeDecoratedTree.height child))
  exact general 0

/-- Child layer counts, and hence the number of merged spheres, agree between any two observed
columns of the same tree. -/
theorem localizedTreeChildLayerCount_eq {input : CertifiedLocalizedCIPInput} {carrierFuel : ℕ}
    {α β : Type*}
    (leftObserve : LocalizedCumulativeDecoratedTree input carrierFuel → α)
    (rightObserve : LocalizedCumulativeDecoratedTree input carrierFuel → β)
    (children : List (LocalizedCumulativeDecoratedTree input carrierFuel)) :
    LocalizedCumulativeDecoratedTree.localizedTreeChildLayerCount
        (children.map (LocalizedCumulativeDecoratedTree.table leftObserve)) =
      LocalizedCumulativeDecoratedTree.localizedTreeChildLayerCount
        (children.map (LocalizedCumulativeDecoratedTree.table rightObserve)) := by
  rw [localizedTreeChildLayerCount_map_eq leftObserve children,
    localizedTreeChildLayerCount_map_eq rightObserve children]

/-- One merged sphere has the same address list for any two observed columns whose child rows
have the same addresses.  Values are never inspected. -/
theorem mergePairs_children_map_map_fst_eq {γ α β : Type*} (children : List γ)
    (leftTable : γ → List (List (OfficialSparseEntry α)))
    (rightTable : γ → List (List (OfficialSparseEntry β)))
    (rows : ∀ child ∈ children, ∀ depth,
      ((leftTable child).getD depth []).map Prod.fst =
        ((rightTable child).getD depth []).map Prod.fst)
    (depth : ℕ) :
    (SparseAddress.mergePairs (children.map leftTable).zipIdx
        (fun table => table.getD depth [])).map Prod.fst =
      (SparseAddress.mergePairs (children.map rightTable).zipIdx
        (fun table => table.getD depth [])).map Prod.fst := by
  rw [mergePairs_map_zipIdx children leftTable (fun table => table.getD depth []),
    mergePairs_map_zipIdx children rightTable (fun table => table.getD depth [])]
  simp only [List.map_flatMap]
  apply flatMap_congr_of_mem
  intro pair present
  have childMem : pair.1 ∈ children := List.fst_mem_of_mem_zipIdx present
  simp only [prefixLayer_map_fst, rows pair.1 childMem depth]

/-- **The addresses in every sphere are independent of the observed column.**  This is proved by
height induction, exactly as row order is: sphere zero is the root address, and sphere `depth + 1`
is the slot-prefixed merge whose addresses depend only on the child list and the child rows at
`depth`. -/
theorem table_addresses_getD {input : CertifiedLocalizedCIPInput} {carrierFuel : ℕ}
    {α β : Type*}
    (leftObserve : LocalizedCumulativeDecoratedTree input carrierFuel → α)
    (rightObserve : LocalizedCumulativeDecoratedTree input carrierFuel → β)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) (depth : ℕ) :
    ((LocalizedCumulativeDecoratedTree.table leftObserve tree).getD depth []).map Prod.fst =
      ((LocalizedCumulativeDecoratedTree.table rightObserve tree).getD depth []).map Prod.fst := by
  have main : ∀ n : ℕ, ∀ candidate : LocalizedCumulativeDecoratedTree input carrierFuel,
      LocalizedCumulativeDecoratedTree.height candidate ≤ n → ∀ depth,
        ((LocalizedCumulativeDecoratedTree.table leftObserve candidate).getD depth []).map
            Prod.fst =
          ((LocalizedCumulativeDecoratedTree.table rightObserve candidate).getD depth []).map
            Prod.fst := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro k inductionHypothesis candidate bound depth
    cases depth with
    | zero =>
        rw [LocalizedCumulativeDecoratedTree.table_getD_zero leftObserve candidate,
          LocalizedCumulativeDecoratedTree.table_getD_zero rightObserve candidate]
        rfl
    | succ depth =>
        conv_lhs =>
          rw [LocalizedCumulativeDecoratedTree.table_eq_root_merge leftObserve,
            LocalizedCumulativeDecoratedTree.getD_root_cons]
        conv_rhs =>
          rw [LocalizedCumulativeDecoratedTree.table_eq_root_merge rightObserve,
            LocalizedCumulativeDecoratedTree.getD_root_cons]
        unfold LocalizedCumulativeDecoratedTree.mergeLocalizedTreeChildTables
        simp only [SparseAddress.mergePairTable_getD]
        have countEq :=
          localizedTreeChildLayerCount_eq leftObserve rightObserve candidate.children
        simp only [countEq]
        by_cases inside :
            depth < LocalizedCumulativeDecoratedTree.localizedTreeChildLayerCount
              (candidate.children.map
                (LocalizedCumulativeDecoratedTree.table rightObserve))
        · simp only [if_pos inside]
          exact mergePairs_children_map_map_fst_eq candidate.children
            (LocalizedCumulativeDecoratedTree.table leftObserve)
            (LocalizedCumulativeDecoratedTree.table rightObserve)
            (fun child childMem childDepth =>
              inductionHypothesis (LocalizedCumulativeDecoratedTree.height child)
                (by
                  have smaller :=
                    LocalizedCumulativeDecoratedTree.height_lt_height_of_mem candidate childMem
                  omega)
                child (le_refl _) childDepth)
            depth
        · simp only [if_neg inside]
          rfl
  exact main (LocalizedCumulativeDecoratedTree.height tree) tree (le_refl _) depth

/-- **Unconditional observation-independence of the actual table's address rows.**  A table built
from a decorated tree with any observation type has exactly the same sphere count and sphere
addresses as the Rule-1a table of the same tree.  This is the `SameAddressRows` input required by
`SparseSupportAlignment.compareSparseLayers_eq_compareLex_of_agreesWithRule1a`. -/
theorem SameAddressRows_table {input : CertifiedLocalizedCIPInput} {carrierFuel : ℕ}
    {α : Type*}
    (observe : LocalizedCumulativeDecoratedTree input carrierFuel → α)
    (reference : LocalizedCumulativeDecoratedTree input carrierFuel → ℕ)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    SparseSupportAlignment.SameAddressRows
      (LocalizedCumulativeDecoratedTree.table observe tree)
      (LocalizedCumulativeDecoratedTree.table reference tree) where
  lengthEq := by
    rw [LocalizedCumulativeDecoratedTree.table_length_eq_height observe tree,
      LocalizedCumulativeDecoratedTree.table_length_eq_height reference tree]
  rows := table_addresses_getD observe reference tree


theorem SameAddressRows_table_observations {input : CertifiedLocalizedCIPInput}
    {carrierFuel : ℕ}
    (observeLeft observeRight : LocalizedCumulativeDecoratedTree input carrierFuel → ℕ)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    SparseSupportAlignment.SameAddressRows
      (LocalizedCumulativeDecoratedTree.table observeLeft tree)
      (LocalizedCumulativeDecoratedTree.table observeRight tree) :=
  SameAddressRows_table observeLeft observeRight tree

/-! ## Positivity of a table, without inventing values on placeholders -/

/-- A table is positive whenever positivity is carried by a child-closed predicate that holds at
the root and implies a positive observation.  No value is assigned to a node outside the
predicate. -/
theorem table_tablePositive_of_closed {input : CertifiedLocalizedCIPInput}
    {carrierFuel : ℕ}
    (observe : LocalizedCumulativeDecoratedTree input carrierFuel → ℕ)
    (predicate : LocalizedCumulativeDecoratedTree input carrierFuel → Prop)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (root : predicate tree)
    (closed : ∀ parent, predicate parent → ∀ child ∈ parent.children, predicate child)
    (positive : ∀ node, predicate node → 0 < observe node) :
    TablePositive (LocalizedCumulativeDecoratedTree.table observe tree) := by
  have main : ∀ n : ℕ, ∀ candidate : LocalizedCumulativeDecoratedTree input carrierFuel,
      LocalizedCumulativeDecoratedTree.height candidate ≤ n → predicate candidate →
        TablePositive (LocalizedCumulativeDecoratedTree.table observe candidate) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro k inductionHypothesis candidate bound candidatePredicate depth entry present
    cases depth with
    | zero =>
        rw [LocalizedCumulativeDecoratedTree.table_getD_zero] at present
        have entryEq : entry = ([], observe candidate) := by simpa using present
        rw [entryEq]
        exact positive candidate candidatePredicate
    | succ depth =>
        rw [LocalizedCumulativeDecoratedTree.table_eq_root_merge,
          LocalizedCumulativeDecoratedTree.getD_root_cons] at present
        unfold LocalizedCumulativeDecoratedTree.mergeLocalizedTreeChildTables at present
        rw [SparseAddress.mergePairTable_getD] at present
        by_cases inside :
            depth < LocalizedCumulativeDecoratedTree.localizedTreeChildLayerCount
              (candidate.children.map (LocalizedCumulativeDecoratedTree.table observe))
        · rw [if_pos inside] at present
          rw [SparseAddress.mergePairs, List.mem_flatMap] at present
          obtain ⟨pair, pairMem, entryMem⟩ := present
          rw [OfficialRuleMajorKey.prefixLayer, List.mem_map] at entryMem
          obtain ⟨inner, innerMem, entryEq⟩ := entryMem
          have valueMem : pair.1 ∈
              candidate.children.map (LocalizedCumulativeDecoratedTree.table observe) :=
            List.fst_mem_of_mem_zipIdx pairMem
          obtain ⟨child, childMem, same⟩ := List.mem_map.mp valueMem
          rw [← same] at innerMem
          have childPredicate : predicate child :=
            closed candidate candidatePredicate child childMem
          have innerPositive : 0 < inner.2 := by
            refine inductionHypothesis (LocalizedCumulativeDecoratedTree.height child) ?_
              child (le_refl _) childPredicate depth inner innerMem
            have smaller :=
              LocalizedCumulativeDecoratedTree.height_lt_height_of_mem candidate childMem
            omega
          rw [← entryEq]
          exact innerPositive
        · rw [if_neg inside] at present
          simp at present
  exact main (LocalizedCumulativeDecoratedTree.height tree) tree (le_refl _) root

/-- A table is positive whenever every node observation is positive.  This is the general
observable form; it makes no assumption about the provenance of the tree. -/
theorem table_tablePositive_of_observe_positive {input : CertifiedLocalizedCIPInput}
    {carrierFuel : ℕ}
    (observe : LocalizedCumulativeDecoratedTree input carrierFuel → ℕ)
    (positive : ∀ node : LocalizedCumulativeDecoratedTree input carrierFuel, 0 < observe node)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    TablePositive (LocalizedCumulativeDecoratedTree.table observe tree) :=
  table_tablePositive_of_closed observe (fun _ => True) tree trivial
    (fun _ _ _ _ => trivial) (fun node _ => positive node)

/-! ## Atomic-number positivity from actual provenance -/

/-- Every atom of the certified input's constitutional graph has a positive atomic number. -/
theorem moleculeGraph_atomZ_positive (input : CertifiedLocalizedCIPInput)
    (atom : Fin input.certified.input.molecule.atomCount) :
    0 < input.moleculeGraph.atomZ atom :=
  (SemanticMolecule.toLocalizedMoleculeGraph_atomicNumber_supported
    input.certified.input.molecule atom).1

/-- Every child of a realized tree is itself realized. -/
theorem realizes_of_mem_child {input : CertifiedLocalizedCIPInput} {carrierFuel : ℕ}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    {child : LocalizedCumulativeDecoratedTree input carrierFuel}
    (present : child ∈ tree.children) :
    LocalizedCumulativeTreeRealizes input read child := by
  cases realizes with
  | mk cursor children sortedChildren sortedChildrenComputed sourcePerm childrenRealize =>
      exact childrenRealize child (by simpa only [localizedRootTree] using present)

/-- The atomic number recorded at a realized node is positive: it is the certified input's
atomic number of the physical atom carried by that node. -/
theorem atomicNumber_positive_of_realizes {input : CertifiedLocalizedCIPInput}
    {carrierFuel : ℕ}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree) :
    0 < tree.atomicNumber := by
  rw [atomicNumber_eq_atomZ singleBonded acyclic realizes]
  exact moleculeGraph_atomZ_positive input _

/-- **The actual atomic-number table is positive.**  Only realized nodes (actual provenance) are
used; no placeholder node is assigned a positivity hypothesis. -/
theorem table_atomicNumber_positive_of_realizes {input : CertifiedLocalizedCIPInput}
    {carrierFuel : ℕ}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree) :
    TablePositive (LocalizedCumulativeDecoratedTree.table
      (fun node => node.atomicNumber) tree) :=
  table_tablePositive_of_closed
    (observe := fun node => node.atomicNumber)
    (predicate := fun node =>
      LocalizedCumulativeTreeRealizes input read node ∧ 0 < node.atomicNumber)
    tree ⟨realizes, atomicNumber_positive_of_realizes singleBonded acyclic realizes⟩
    (fun _parent parentPredicate _child childMem =>
      ⟨realizes_of_mem_child parentPredicate.1 childMem,
        atomicNumber_positive_of_realizes singleBonded acyclic
          (realizes_of_mem_child parentPredicate.1 childMem)⟩)
    (fun _node nodePredicate => nodePredicate.2)

/-! ## First-difference corollaries for the actual table -/

/-- The executed Rule-1a comparison of two compiled tree tables is the independent relational
first difference, with table well-formedness discharged unconditionally and positivity supplied
pointwise by the observation. -/
theorem table_compareSparseLayers_eq_firstDifference_of_observe_positive
    {input : CertifiedLocalizedCIPInput} {carrierFuel : ℕ}
    {observeLeft observeRight : LocalizedCumulativeDecoratedTree input carrierFuel → ℕ}
    (positiveLeft : ∀ node, 0 < observeLeft node)
    (positiveRight : ∀ node, 0 < observeRight node)
    (leftTree rightTree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (outcome : Ordering) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (LocalizedCumulativeDecoratedTree.table observeLeft leftTree)
        (LocalizedCumulativeDecoratedTree.table observeRight rightTree) = outcome ↔
      FirstDifferenceOutcome
        (fun position result =>
          DescendingNatOutcome
            (tableValue (LocalizedCumulativeDecoratedTree.table observeLeft leftTree) position)
            (tableValue (LocalizedCumulativeDecoratedTree.table observeRight rightTree) position)
            result)
        outcome :=
  table_compareSparseLayers_eq_firstDifference
    (table_wellFormed observeLeft leftTree) (table_wellFormed observeRight rightTree)
    (table_tablePositive_of_observe_positive observeLeft positiveLeft leftTree)
    (table_tablePositive_of_observe_positive observeRight positiveRight rightTree) outcome

/-- **Unconditional actual Rule-1a first difference on the atomic-number column.**  For two
realized decorated trees of the same certified input, the executed comparison of the compiled
atomic-number tables is exactly the independent relational first difference of their addressed
observations.  No well-formedness, order or positivity hypothesis remains. -/
theorem table_atomicNumber_compareSparseLayers_eq_firstDifference
    {input : CertifiedLocalizedCIPInput} {carrierFuel : ℕ}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {readLeft readRight :
      input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {leftTree rightTree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizesLeft : LocalizedCumulativeTreeRealizes input readLeft leftTree)
    (realizesRight : LocalizedCumulativeTreeRealizes input readRight rightTree)
    (outcome : Ordering) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) leftTree)
        (LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) rightTree) =
          outcome ↔
      FirstDifferenceOutcome
        (fun position result =>
          DescendingNatOutcome
            (tableValue
              (LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) leftTree)
              position)
            (tableValue
              (LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) rightTree)
              position)
            result)
        outcome :=
  table_compareSparseLayers_eq_firstDifference
    (table_wellFormed (fun node => node.atomicNumber) leftTree)
    (table_wellFormed (fun node => node.atomicNumber) rightTree)
    (table_atomicNumber_positive_of_realizes singleBonded acyclic realizesLeft)
    (table_atomicNumber_positive_of_realizes singleBonded acyclic realizesRight) outcome









/-- Later-column comparison on the common address schedule, from a Rule-1a tie.  Table
well-formedness of the reference columns is discharged unconditionally; positivity of the two
reference columns and the tie remain explicit hypotheses. -/
theorem laterTable_compareSparseLayers_eq_compareLex_of_rule1aTie
    {input : CertifiedLocalizedCIPInput} {carrierFuel : ℕ} {α : Type*}
    {leftTree rightTree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (rule1aObserveLeft rule1aObserveRight :
      LocalizedCumulativeDecoratedTree input carrierFuel → ℕ)
    (positiveLeft : TablePositive
      (LocalizedCumulativeDecoratedTree.table rule1aObserveLeft leftTree))
    (positiveRight : TablePositive
      (LocalizedCumulativeDecoratedTree.table rule1aObserveRight rightTree))
    (tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (LocalizedCumulativeDecoratedTree.table rule1aObserveLeft leftTree)
      (LocalizedCumulativeDecoratedTree.table rule1aObserveRight rightTree) = Ordering.eq)
    (leftObserve rightObserve : LocalizedCumulativeDecoratedTree input carrierFuel → α)
    (compareObservation : α → α → Ordering) :
    OfficialRuleMajorKey.compareSparseLayers compareObservation
        (LocalizedCumulativeDecoratedTree.table leftObserve leftTree)
        (LocalizedCumulativeDecoratedTree.table rightObserve rightTree) =
      List.compareLex compareObservation
        ((LocalizedCumulativeDecoratedTree.table leftObserve leftTree).flatten.map Prod.snd)
        ((LocalizedCumulativeDecoratedTree.table rightObserve rightTree).flatten.map Prod.snd) :=
  SparseSupportAlignment.compareSparseLayers_eq_compareLex_of_agreesWithRule1a
    (table_wellFormed rule1aObserveLeft leftTree)
    (table_wellFormed rule1aObserveRight rightTree)
    positiveLeft positiveRight tied
    (SameAddressRows_table leftObserve rule1aObserveLeft leftTree)
    (SameAddressRows_table rightObserve rule1aObserveRight rightTree)
    compareObservation

/-- Later-column comparison with the actual atomic-number Rule-1a column: well-formedness and
positivity are both discharged from the realized trees, so the only remaining hypothesis is the
Rule-1a tie. -/
theorem laterTable_compareSparseLayers_eq_compareLex_of_atomicNumberTie
    {input : CertifiedLocalizedCIPInput} {carrierFuel : ℕ} {α : Type*}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {readLeft readRight :
      input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {leftTree rightTree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizesLeft : LocalizedCumulativeTreeRealizes input readLeft leftTree)
    (realizesRight : LocalizedCumulativeTreeRealizes input readRight rightTree)
    (tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) leftTree)
      (LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) rightTree) =
        Ordering.eq)
    (leftObserve rightObserve : LocalizedCumulativeDecoratedTree input carrierFuel → α)
    (compareObservation : α → α → Ordering) :
    OfficialRuleMajorKey.compareSparseLayers compareObservation
        (LocalizedCumulativeDecoratedTree.table leftObserve leftTree)
        (LocalizedCumulativeDecoratedTree.table rightObserve rightTree) =
      List.compareLex compareObservation
        ((LocalizedCumulativeDecoratedTree.table leftObserve leftTree).flatten.map Prod.snd)
        ((LocalizedCumulativeDecoratedTree.table rightObserve rightTree).flatten.map Prod.snd) :=
  SparseSupportAlignment.compareSparseLayers_eq_compareLex_of_agreesWithRule1a
    (table_wellFormed (fun node => node.atomicNumber) leftTree)
    (table_wellFormed (fun node => node.atomicNumber) rightTree)
    (table_atomicNumber_positive_of_realizes singleBonded acyclic realizesLeft)
    (table_atomicNumber_positive_of_realizes singleBonded acyclic realizesRight)
    tied
    (SameAddressRows_table leftObserve (fun node => node.atomicNumber) leftTree)
    (SameAddressRows_table rightObserve (fun node => node.atomicNumber) rightTree)
    compareObservation

/-! ## General actual node provenance: current atoms and atomic-number positivity

The results in this section remove the `SimpleBonded`/`Acyclic` restrictions from every
atomic-number positivity and Rule-1a endpoint above.  Nothing else is weakened or strengthened:
the trees are still actual generated occurrences (`LocalizedCumulativeTreeRealizes`), the labels
are still the official labels, and the tables are still the compiled `zipIdx` address schedule.
Only the unnecessary physical-domain restriction is dropped, because the Rule-1a atomic number is
carried by every provenance class and every actual carrier occurrence has a current atom. -/

/-- Every actual reroot cursor is atom-bearing: its occurrence belongs to the certified carrier,
and every carrier occurrence carries a current atom, regardless of provenance class. -/
theorem rerootCursor_node_current_isSome
    (input : CertifiedLocalizedCIPInput) {carrierFuel : ℕ}
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    cursor.occurrence.1.node.current?.isSome = true := by
  have derived : input.DeclarativeLocalizedOccurrence carrierFuel cursor.occurrence.1 :=
    (input.mem_localizedOccurrences_iff carrierFuel cursor.occurrence.1).mp
      cursor.occurrence.2
  exact input.declarativeLocalizedOccurrence_node_current_isSome derived

/-- The current atom of an actual reroot cursor's occurrence. -/
theorem exists_current_of_rerootCursor
    (input : CertifiedLocalizedCIPInput) {carrierFuel : ℕ}
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    ∃ atom : input.Atom, cursor.occurrence.1.node.current? = some atom :=
  Option.isSome_iff_exists.mp (rerootCursor_node_current_isSome input cursor)

/-- A realized node's atomic number is the certified molecule's atomic number of an actual atom
carried by that node's occurrence.  The witness is the current atom of the actual carrier
occurrence; its existence is derived from carrier membership, not from single-bondedness or
acyclicity, and the label identity holds for every provenance class. -/
theorem atomicNumber_eq_atomZ_of_realizes_general
    {input : CertifiedLocalizedCIPInput} {carrierFuel : ℕ}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree) :
    ∃ atom : input.Atom,
      tree.source.occurrence.1.node.current? = some atom ∧
        tree.atomicNumber = input.moleculeGraph.atomZ atom := by
  cases realizes with
  | mk cursor children sortedChildren childrenComputed sourcePerm childrenRealize =>
      obtain ⟨atom, currentEq⟩ := exists_current_of_rerootCursor input cursor
      refine ⟨atom, currentEq, ?_⟩
      show (ofLex (input.moleculeGraph.officialNodeAtomLabel
        cursor.occurrence.1.node)).1 = input.moleculeGraph.atomZ atom
      exact MoleculeGraph.officialNodeAtomLabel_first_eq_atomZ_of_current
        input.moleculeGraph cursor.occurrence.1.node atom currentEq

/-- The atomic number recorded at a realized node is positive, with no single-bondedness or
acyclicity hypothesis: the certified input's element records supply element positivity. -/
theorem atomicNumber_positive_of_realizes_general
    {input : CertifiedLocalizedCIPInput} {carrierFuel : ℕ}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree) :
    0 < tree.atomicNumber := by
  obtain ⟨atom, _currentEq, atomZEq⟩ :=
    atomicNumber_eq_atomZ_of_realizes_general realizes
  rw [atomZEq]
  exact moleculeGraph_atomZ_positive input atom

/-- **Child-closed positivity lift through actual realization.**  Positivity of an observed
column is required only at nodes that carry actual generated provenance; the predicate is closed
under children by `realizes_of_mem_child`.  No arbitrary-tree positivity and no physical-domain
hypothesis is introduced. -/
theorem table_tablePositive_of_realizes {input : CertifiedLocalizedCIPInput}
    {carrierFuel : ℕ}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {observe : LocalizedCumulativeDecoratedTree input carrierFuel → ℕ}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (positive : ∀ node : LocalizedCumulativeDecoratedTree input carrierFuel,
      LocalizedCumulativeTreeRealizes input read node → 0 < observe node) :
    TablePositive (LocalizedCumulativeDecoratedTree.table observe tree) :=
  table_tablePositive_of_closed observe
    (fun node => LocalizedCumulativeTreeRealizes input read node) tree realizes
    (fun _parent parentRealizes _child childMem =>
      realizes_of_mem_child parentRealizes childMem)
    positive

/-- **The actual atomic-number table is positive for every actual generated provenance.**  This
generalizes `table_atomicNumber_positive_of_realizes`: no single-bondedness or acyclicity is
assumed, and only realized nodes are used. -/
theorem table_atomicNumber_positive_of_realizes_general
    {input : CertifiedLocalizedCIPInput} {carrierFuel : ℕ}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree) :
    TablePositive (LocalizedCumulativeDecoratedTree.table
      (fun node => node.atomicNumber) tree) :=
  table_tablePositive_of_realizes realizes
    (fun _node nodeRealizes => atomicNumber_positive_of_realizes_general nodeRealizes)

/-- **General actual Rule-1a first difference on the atomic-number column.**  For two realized
decorated trees, the executed comparison of the compiled atomic-number tables is exactly the
independent relational first difference of their addressed observations.  No well-formedness,
order, positivity, single-bondedness or acyclicity hypothesis remains. -/
theorem table_atomicNumber_compareSparseLayers_eq_firstDifference_general
    {input : CertifiedLocalizedCIPInput} {carrierFuel : ℕ}
    {readLeft readRight :
      input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {leftTree rightTree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizesLeft : LocalizedCumulativeTreeRealizes input readLeft leftTree)
    (realizesRight : LocalizedCumulativeTreeRealizes input readRight rightTree)
    (outcome : Ordering) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) leftTree)
        (LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) rightTree) =
          outcome ↔
      FirstDifferenceOutcome
        (fun position result =>
          DescendingNatOutcome
            (tableValue
              (LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) leftTree)
              position)
            (tableValue
              (LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) rightTree)
              position)
            result)
        outcome :=
  table_compareSparseLayers_eq_firstDifference
    (table_wellFormed (fun node => node.atomicNumber) leftTree)
    (table_wellFormed (fun node => node.atomicNumber) rightTree)
    (table_atomicNumber_positive_of_realizes_general realizesLeft)
    (table_atomicNumber_positive_of_realizes_general realizesRight) outcome

/-! ## The actual-Z tie and common-address readback

`actualZtie` is the executed Rule-1a equality of the two actual atomic-number tables.  Under it,
the two tables have the same address support and the same readbacks at every address, so any
later column (Rule-1b distance, mass, descriptor) can be compared on the common schedule without
assuming an independent sort or a physical domain. -/

/-- The actual atomic-number Rule-1a tables of two decorated occurrence trees tie. -/
def actualZtie {input : CertifiedLocalizedCIPInput} {carrierFuel : ℕ}
    (leftTree rightTree : LocalizedCumulativeDecoratedTree input carrierFuel) : Prop :=
  OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
    (LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) leftTree)
    (LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) rightTree) =
      Ordering.eq

/-- Definitional unfolding of the actual-Z tie. -/
theorem actualZtie_iff {input : CertifiedLocalizedCIPInput} {carrierFuel : ℕ}
    (leftTree rightTree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    actualZtie leftTree rightTree ↔
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) leftTree)
        (LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) rightTree) =
          Ordering.eq :=
  Iff.rfl

/-- **Common-address readback under an actual-Z tie.**  At every address, present or absent, the
actual atomic-number tables read back the same value.  This is the weighted readback prerequisite
for reconstructing observations from an actual key on the common schedule. -/
theorem actualZtie_tableValue_eq
    {input : CertifiedLocalizedCIPInput} {carrierFuel : ℕ}
    {readLeft readRight :
      input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {leftTree rightTree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizesLeft : LocalizedCumulativeTreeRealizes input readLeft leftTree)
    (realizesRight : LocalizedCumulativeTreeRealizes input readRight rightTree)
    (tied : actualZtie leftTree rightTree) :
    ∀ position,
      tableValue
        (LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) leftTree)
        position =
      tableValue
        (LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) rightTree)
        position :=
  tableValue_eq_of_compareSparseLayers_eq
    (table_wellFormed (fun node => node.atomicNumber) leftTree)
    (table_wellFormed (fun node => node.atomicNumber) rightTree)
    (table_atomicNumber_positive_of_realizes_general realizesLeft)
    (table_atomicNumber_positive_of_realizes_general realizesRight)
    ((actualZtie_iff leftTree rightTree).mp tied)

/-- **Common address support under an actual-Z tie.**  A tie forces the two actual atomic-number
tables to carry exactly the same addresses, so later columns are read on a common schedule. -/
theorem actualZtie_sameSupport
    {input : CertifiedLocalizedCIPInput} {carrierFuel : ℕ}
    {readLeft readRight :
      input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {leftTree rightTree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizesLeft : LocalizedCumulativeTreeRealizes input readLeft leftTree)
    (realizesRight : LocalizedCumulativeTreeRealizes input readRight rightTree)
    (tied : actualZtie leftTree rightTree) :
    ∀ position,
      SparseSupportAlignment.HasAddress
        (LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) leftTree)
        position ↔
      SparseSupportAlignment.HasAddress
        (LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) rightTree)
        position :=
  sameSupport_of_compareSparseLayers_eq
    (table_wellFormed (fun node => node.atomicNumber) leftTree)
    (table_wellFormed (fun node => node.atomicNumber) rightTree)
    (table_atomicNumber_positive_of_realizes_general realizesLeft)
    (table_atomicNumber_positive_of_realizes_general realizesRight)
    ((actualZtie_iff leftTree rightTree).mp tied)

/-- **Actual-Z tie as the first difference returning `eq`.**  The tie is exactly the statement
that the independent relational first difference of the two addressed atomic-number observations
is `eq`; no positivity hypothesis remains. -/
theorem actualZtie_iff_firstDifference
    {input : CertifiedLocalizedCIPInput} {carrierFuel : ℕ}
    {readLeft readRight :
      input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {leftTree rightTree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizesLeft : LocalizedCumulativeTreeRealizes input readLeft leftTree)
    (realizesRight : LocalizedCumulativeTreeRealizes input readRight rightTree) :
    actualZtie leftTree rightTree ↔
      FirstDifferenceOutcome
        (fun position result =>
          DescendingNatOutcome
            (tableValue
              (LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) leftTree)
              position)
            (tableValue
              (LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) rightTree)
              position)
            result)
        Ordering.eq :=
  table_atomicNumber_compareSparseLayers_eq_firstDifference_general
    realizesLeft realizesRight Ordering.eq

/-- **Later-column comparison on the common addresses from an actual-Z tie.**  For any two later
observation columns of the same trees and any scalar comparator, the executed later-column
comparison is the pointwise comparison of the flattened observations along the common address
schedule.  No single-bondedness, acyclicity or independent sort assumption remains: the schedule
is the actual tree's own `zipIdx`/`prefixLayer` address order. -/
theorem laterTable_compareSparseLayers_eq_compareLex_of_actualZtie
    {input : CertifiedLocalizedCIPInput} {carrierFuel : ℕ} {α : Type*}
    {readLeft readRight :
      input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {leftTree rightTree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizesLeft : LocalizedCumulativeTreeRealizes input readLeft leftTree)
    (realizesRight : LocalizedCumulativeTreeRealizes input readRight rightTree)
    (tied : actualZtie leftTree rightTree)
    (leftObserve rightObserve : LocalizedCumulativeDecoratedTree input carrierFuel → α)
    (compareObservation : α → α → Ordering) :
    OfficialRuleMajorKey.compareSparseLayers compareObservation
        (LocalizedCumulativeDecoratedTree.table leftObserve leftTree)
        (LocalizedCumulativeDecoratedTree.table rightObserve rightTree) =
      List.compareLex compareObservation
        ((LocalizedCumulativeDecoratedTree.table leftObserve leftTree).flatten.map Prod.snd)
        ((LocalizedCumulativeDecoratedTree.table rightObserve rightTree).flatten.map Prod.snd) :=
  SparseSupportAlignment.compareSparseLayers_eq_compareLex_of_agreesWithRule1a
    (table_wellFormed (fun node => node.atomicNumber) leftTree)
    (table_wellFormed (fun node => node.atomicNumber) rightTree)
    (table_atomicNumber_positive_of_realizes_general realizesLeft)
    (table_atomicNumber_positive_of_realizes_general realizesRight)
    ((actualZtie_iff leftTree rightTree).mp tied)
    (SameAddressRows_table leftObserve (fun node => node.atomicNumber) leftTree)
    (SameAddressRows_table rightObserve (fun node => node.atomicNumber) rightTree)
    compareObservation

/-- **An actual-key Rule-1a tie is the actual-Z tie of its matched trees.**  This lets later
columns compare on the trees' common address schedule whenever the actual cumulative keys tie at
Rule 1a, without re-deriving the key/tree table equality at the consumer. -/
theorem key_rule1a_tie_iff_actualZtie
    {input : CertifiedLocalizedCIPInput} {carrierFuel : ℕ}
    {leftTree rightTree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {stageLeft stageRight : LocalizedCumulativeRule45Stage}
    {leftKey rightKey : input.LocalizedRerootCumulativeRule45Key}
    (matchedLeft : LocalizedCumulativeTreeTableMatch stageLeft leftTree leftKey)
    (matchedRight : LocalizedCumulativeTreeTableMatch stageRight rightTree rightKey) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        leftKey.constitutional.rule1a rightKey.constitutional.rule1a = Ordering.eq ↔
      actualZtie leftTree rightTree := by
  have leftEq : leftKey.constitutional.rule1a =
      LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) leftTree := by
    simpa using matchedLeft.1.symm
  have rightEq : rightKey.constitutional.rule1a =
      LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) rightTree := by
    simpa using matchedRight.1.symm
  rw [leftEq, rightEq]
  exact Iff.rfl

/-- **Actual-key Rule-1a first difference.**  When two realized trees are matched by actual
cumulative keys (`LocalizedCumulativeTreeTableMatch`), the executed comparison of the keys'
constitutional Rule-1a tables is exactly the independent relational first difference of the
key-level atomic-number readbacks.  No single-bondedness or acyclicity is assumed. -/
theorem key_rule1a_compareSparseLayers_eq_firstDifference_general
    {input : CertifiedLocalizedCIPInput} {carrierFuel : ℕ}
    {readLeft readRight :
      input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {leftTree rightTree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizesLeft : LocalizedCumulativeTreeRealizes input readLeft leftTree)
    (realizesRight : LocalizedCumulativeTreeRealizes input readRight rightTree)
    {stageLeft stageRight : LocalizedCumulativeRule45Stage}
    {leftKey rightKey : input.LocalizedRerootCumulativeRule45Key}
    (matchedLeft : LocalizedCumulativeTreeTableMatch stageLeft leftTree leftKey)
    (matchedRight : LocalizedCumulativeTreeTableMatch stageRight rightTree rightKey)
    (outcome : Ordering) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        leftKey.constitutional.rule1a rightKey.constitutional.rule1a = outcome ↔
      FirstDifferenceOutcome
        (fun position result =>
          DescendingNatOutcome
            (tableValue leftKey.constitutional.rule1a position)
            (tableValue rightKey.constitutional.rule1a position)
            result)
        outcome := by
  have leftEq : leftKey.constitutional.rule1a =
      LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) leftTree := by
    simpa using matchedLeft.1.symm
  have rightEq : rightKey.constitutional.rule1a =
      LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) rightTree := by
    simpa using matchedRight.1.symm
  rw [leftEq, rightEq]
  exact table_atomicNumber_compareSparseLayers_eq_firstDifference_general
    realizesLeft realizesRight outcome

end LocalizedActualTableAddressOrder

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.AddressCompare_cons_cons_self
assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.AddressCompare_cons_cons_of_lt
assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.prefixLayer_pairwise
assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.pairwise_indices_zipIdx
assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.mergePairs_zipIdx_pairwise
assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.table_rowsIncreasing
assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.table_wellFormed
assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.prefixLayer_map_fst
assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.flatMap_congr_of_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.zipIdx_map_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.mergePairs_map_zipIdx
assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.localizedTreeChildLayerCount_map_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.localizedTreeChildLayerCount_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.mergePairs_children_map_map_fst_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.table_addresses_getD
assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.SameAddressRows_table
assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.SameAddressRows_table_observations
assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.table_tablePositive_of_closed
assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.table_tablePositive_of_observe_positive
assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.moleculeGraph_atomZ_positive
assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.realizes_of_mem_child
assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.atomicNumber_positive_of_realizes
assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.table_atomicNumber_positive_of_realizes
assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.table_compareSparseLayers_eq_firstDifference_of_observe_positive
assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.table_atomicNumber_compareSparseLayers_eq_firstDifference
assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.laterTable_compareSparseLayers_eq_compareLex_of_rule1aTie
assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.laterTable_compareSparseLayers_eq_compareLex_of_atomicNumberTie
assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.rerootCursor_node_current_isSome
assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.exists_current_of_rerootCursor
assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.atomicNumber_eq_atomZ_of_realizes_general
assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.atomicNumber_positive_of_realizes_general
assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.table_tablePositive_of_realizes
assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.table_atomicNumber_positive_of_realizes_general
assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.table_atomicNumber_compareSparseLayers_eq_firstDifference_general
assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.actualZtie
assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.actualZtie_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.actualZtie_tableValue_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.actualZtie_sameSupport
assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.actualZtie_iff_firstDifference
assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.laterTable_compareSparseLayers_eq_compareLex_of_actualZtie
assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.key_rule1a_tie_iff_actualZtie
assert_kernel_only TetraStereo.OneCenter.LocalizedActualTableAddressOrder.key_rule1a_compareSparseLayers_eq_firstDifference_general
