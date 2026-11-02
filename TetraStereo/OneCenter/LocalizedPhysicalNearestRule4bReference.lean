import TetraStereo.OneCenter.LocalizedCumulativeTreeObservableFaithfulness
import TetraStereo.OneCenter.LocalizedUniqueNearestRule4bReference
import TetraStereo.OneCenter.LocalizedCumulativeAssemblyRecovery
import TetraStereo.OneCenter.LocalizedAcyclicRerootNeighborCorrespondence
import TetraStereo.OneCenter.LocalizedRerootChildrenExecutable
import TetraStereo.OneCenter.LocalizedRerootFuelCompleteness
import TetraStereo.OneCenter.LocalizedOutwardRerootDependencySupport
import TetraStereo.OneCenter.LocalizedRealizedTreeCutEmbedding
import TetraStereo.OneCenter.LocalizedRealizedTreeCutEquivalence
import TetraStereo.OneCenter.LocalizedEmptyRule4bReferenceDecoding
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput

namespace LocalizedCumulativeDecoratedTree

/-!
# Physical depth spheres of a realized decorated occurrence tree

This file connects the actual decorated occurrence tree produced by the cumulative reroot builder
to physical branch distance.  The first layer is purely combinatorial: at every tree depth, the
label entries of the tree's addressed table are exactly the decorations of the tree nodes at that
depth, in left-to-right sibling order.  The sibling addresses and rank prefixes are forgotten by
the projection `Prod.snd`, so the result speaks about observations, not about carrier coordinates.
-/

/-- The decorations of all tree nodes at exactly one depth, in left-to-right sibling order. -/
def observationsAtDepth {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat} {α : Type*}
    (observe : LocalizedCumulativeDecoratedTree input carrierFuel → α) :
    Nat → LocalizedCumulativeDecoratedTree input carrierFuel → List α
  | 0, tree => [observe tree]
  | depth + 1, tree =>
      tree.children.flatMap fun child => observationsAtDepth observe depth child

/-- `prefixLayer` changes addresses only: the observed values are unchanged. -/
private theorem prefixLayer_map_snd {α : Type*} (slot : Nat)
    (layer : List (OfficialSparseEntry α)) :
    (OfficialRuleMajorKey.prefixLayer slot layer).map Prod.snd = layer.map Prod.snd := by
  unfold OfficialRuleMajorKey.prefixLayer
  rw [List.map_map]
  exact List.map_congr_left fun _ _ => rfl

/-- The first block of a slot-indexed merge. -/
private theorem mergePairs_cons {β α : Type*} (head : β × Nat) (tail : List (β × Nat))
    (block : β → List (OfficialSparseEntry α)) :
    SparseAddress.mergePairs (head :: tail) block =
      OfficialRuleMajorKey.prefixLayer head.2 (block head.1) ++
        SparseAddress.mergePairs tail block := rfl

/-- The slot-indexed merge preserves, in order, all observed values contributed by its blocks. -/
private theorem mergePairs_map_snd {β α : Type*} (pairs : List (β × Nat))
    (block : β → List (OfficialSparseEntry α)) :
    (SparseAddress.mergePairs pairs block).map Prod.snd =
      pairs.flatMap fun pair => (block pair.1).map Prod.snd := by
  induction pairs with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [mergePairs_cons, List.map_append, prefixLayer_map_snd, inductionHypothesis,
        List.flatMap_cons]

/-- Flattening the indexed list while ignoring the index is ordinary flattening. -/
private theorem zipIdx_flatMap_fst_from {β γ : Type*} (start : Nat) (values : List β)
    (f : β → List γ) :
    (values.zipIdx start).flatMap (fun pair => f pair.1) = values.flatMap f := by
  induction values generalizing start with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [List.zipIdx_cons, inductionHypothesis]

/-- A flat map of empty blocks is empty. -/
private theorem flatMap_eq_nil_of_forall {β γ : Type*} (values : List β) (f : β → List γ)
    (empty : ∀ value ∈ values, f value = []) :
    values.flatMap f = [] := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [List.flatMap_cons, empty head (by simp),
        inductionHypothesis (fun value present => empty value (by simp [present]))]
      rfl

/-- Every child table is no longer than the merge's selected row count. -/
private theorem table_length_le_localizedTreeChildLayerCount {α : Type*}
    (tables : List (List (List (OfficialSparseEntry α))))
    {table : List (List (OfficialSparseEntry α))} (present : table ∈ tables) :
    table.length ≤ localizedTreeChildLayerCount tables := by
  unfold localizedTreeChildLayerCount
  exact CumulativeAssembly.measure_le_foldl_max (fun table => table.length) tables table present

/-- The values of one sphere of the slot-indexed child merge are the concatenation, in sibling
order, of the corresponding spheres of the child tables.  Prefixes are forgotten. -/
private theorem mergeLocalizedTreeChildTables_getD_map_snd {α : Type*}
    (tables : List (List (List (OfficialSparseEntry α)))) (depth : Nat) :
    ((mergeLocalizedTreeChildTables tables).getD depth []).map Prod.snd =
      tables.flatMap fun table => (table.getD depth []).map Prod.snd := by
  unfold mergeLocalizedTreeChildTables
  rw [SparseAddress.mergePairTable_getD]
  by_cases inRange : depth < localizedTreeChildLayerCount tables
  · rw [if_pos inRange, mergePairs_map_snd]
    exact zipIdx_flatMap_fst_from 0 tables
      (fun table => (table.getD depth []).map Prod.snd)
  · rw [if_neg inRange]
    have everyEmpty : ∀ table ∈ tables, table.getD depth [] = [] := by
      intro table present
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by
          have bounded := table_length_le_localizedTreeChildLayerCount tables present
          omega)]
      rfl
    rw [flatMap_eq_nil_of_forall tables
      (fun table => (table.getD depth []).map Prod.snd)
      (by
        intro table present
        have empty := everyEmpty table present
        simpa using congrArg (fun layer => layer.map Prod.snd) empty)]
    rfl

/-- At depth zero the table contains exactly the root decoration. -/
private theorem table_getD_zero {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {α : Type*}
    (observe : LocalizedCumulativeDecoratedTree input carrierFuel → α)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    (table observe tree).getD 0 [] = [([], observe tree)] := by
  rw [table_eq_root_merge]
  rfl

/-- At positive depth the table contains exactly the merged child spheres. -/
private theorem table_getD_succ {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {α : Type*}
    (observe : LocalizedCumulativeDecoratedTree input carrierFuel → α)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) (depth : Nat) :
    (table observe tree).getD (depth + 1) [] =
      (mergeLocalizedTreeChildTables
        (tree.children.map (table observe))).getD depth [] := by
  rw [table_eq_root_merge]
  rfl

/-- **Depth sphere of an addressed tree table.**  Forgetting addresses from the table sphere at
depth `d` gives exactly the decorations of the tree nodes at depth `d`, in left-to-right sibling
order.  No duplicate-freedom, adjacency, or physical premise is used: this is the table-side
counting identity. -/
theorem table_getD_map_snd {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat} {α : Type*}
    (observe : LocalizedCumulativeDecoratedTree input carrierFuel → α)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) (depth : Nat) :
    ((table observe tree).getD depth []).map Prod.snd =
      observationsAtDepth observe depth tree := by
  induction depth generalizing tree with
  | zero =>
      rw [table_getD_zero]
      rfl
  | succ depth inductionHypothesis =>
      rw [table_getD_succ, mergeLocalizedTreeChildTables_getD_map_snd,
        List.flatMap_map]
      unfold observationsAtDepth
      apply List.flatMap_congr
      intro child childPresent
      exact inductionHypothesis child

/-- The label table's sphere at depth `d` forgets addresses to exactly the labels of the nodes at
depth `d`. -/
theorem labelTable_getD_map_snd {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) (depth : Nat) :
    ((tree.labelTable.getD depth []).map Prod.snd) =
      observationsAtDepth (fun node => node.label) depth tree :=
  table_getD_map_snd (fun node => node.label) tree depth

/-! ## Branch positions and their address length

The remaining combinatorial input for physical distance is the fact that every executed child
strictly lengthens the root-relative address.  At the branch attachment the incoming cut is
absent; below it, the incoming cut is copied into `previous?`, and every executable child other
than that cut has strictly longer address by `outward_edge`.
-/

/-- A cursor lying on the outward branch from the attachment: either the attachment itself, or a
path-valid cursor whose recorded incoming coordinate has strictly shorter address. -/
private def BranchCursorState {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (rootCursor cursor : input.LocalizedRerootCursor carrierFuel) : Prop :=
  cursor = rootCursor ∨
    (input.LocalizedRerootCursorValid cursor ∧
      ∃ previous : input.LocalizedCIPOccurrence carrierFuel,
        cursor.previous? = some previous ∧
          previous.1.address.length < cursor.occurrence.1.address.length)

/-- One child step of a realized tree on the outward branch strictly lengthens the address and
preserves the branch state. -/
private theorem branch_child_step
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {rootCursor : input.LocalizedRerootCursor carrierFuel}
    (rootAddress : rootCursor.occurrence.1.address = [])
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (state : BranchCursorState rootCursor tree.source)
    {slot : Nat} {child : LocalizedCumulativeDecoratedTree input carrierFuel}
    (lookup : tree.children[slot]? = some child) :
    child.source.occurrence.1.address.length =
        tree.source.occurrence.1.address.length + 1 ∧
      BranchCursorState rootCursor child.source := by
  have edge := mem_executable_of_child realizes lookup
  have derived := input.executableLocalizedRerootChildren_declarative tree.source
  have childIntended : child.source.occurrence.1 ∈
      input.intendedLocalizedRerootChildFrames tree.source := by
    rw [← derived.1]
    exact List.mem_map.mpr ⟨child.source, edge, rfl⟩
  have neighbor := input.mem_localizedRerootNeighborFrames_of_mem_intended
    tree.source child.source.occurrence.1 childIntended
  have characterized :=
    (input.mem_localizedRerootNeighborFrames_iff tree.source.occurrence.1
      child.source.occurrence.1).mp neighbor
  have childPrevious := input.executableLocalizedRerootChildren_previous
    tree.source child.source edge
  have childValid := input.localizedRerootChild_valid tree.source child.source
    (input.executableLocalizedRerootChildren tree.source) derived edge
  rcases state with sourceRoot | ⟨valid, previous, previousEq, previousShorter⟩
  · rcases characterized.2 with ⟨_sameRoot, parent | outward⟩
    · have impossibleLength : child.source.occurrence.1.address.length + 1 =
          tree.source.occurrence.1.address.length := parent.1
      rw [sourceRoot, rootAddress] at impossibleLength
      simp only [List.length_nil] at impossibleLength
      omega
    · refine ⟨outward.1.symm, Or.inr ⟨childValid, tree.source.occurrence, childPrevious, ?_⟩⟩
      omega
  · rcases input.outward_edge tree.source child.source valid previous previousEq previousShorter
      edge with ⟨_dropLast, childLength, _rootEq, childPrevious', childValid'⟩
    exact ⟨childLength,
      Or.inr ⟨childValid', tree.source.occurrence, childPrevious', by omega⟩⟩

/-- Along any successful descent from a node on the outward branch, the source address length is
the starting length plus the position depth. -/
private theorem subtreeAt?_source_address_length_relative
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {rootCursor : input.LocalizedRerootCursor carrierFuel}
    (rootAddress : rootCursor.occurrence.1.address = [])
    {path : List Nat}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (state : BranchCursorState rootCursor tree.source)
    {node : LocalizedCumulativeDecoratedTree input carrierFuel}
    (lookup : subtreeAt? tree path = some node) :
    node.source.occurrence.1.address.length =
      tree.source.occurrence.1.address.length + path.length := by
  induction path generalizing tree with
  | nil =>
      rw [subtreeAt?_nil] at lookup
      have nodeEq : node = tree := (Option.some.inj lookup).symm
      subst node
      simp
  | cons slot rest inductionHypothesis =>
      rw [subtreeAt?_cons_eq_some_iff] at lookup
      obtain ⟨child, childLookup, restLookup⟩ := lookup
      have step := branch_child_step rootAddress realizes state childLookup
      have childResult := inductionHypothesis
        (realizes_of_child realizes childLookup) step.2 restLookup
      rw [childResult, step.1, List.length_cons]
      omega

/-- **Position depth is address length.**  For a realized tree whose root source is the addressed
branch attachment, the physical address length of the cursor at any actual tree position equals
the length of that position's sibling-slot path. -/
theorem positionSource_address_length
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {rootCursor : input.LocalizedRerootCursor carrierFuel}
    (rootAddress : rootCursor.occurrence.1.address = [])
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (sourceEq : tree.source = rootCursor)
    (p : Position tree) :
    (positionSource p).occurrence.1.address.length = p.val.length := by
  have relative := subtreeAt?_source_address_length_relative rootAddress realizes
    (Or.inl sourceEq) (positionNode_spec p)
  simpa [positionSource, sourceEq, rootAddress] using relative

/-- A cursor already on a strict outward branch: path-valid and reached from a strictly shorter
incoming address. -/
private def OutwardCursorState {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel) : Prop :=
  input.LocalizedRerootCursorValid cursor ∧
    ∃ previous : input.LocalizedCIPOccurrence carrierFuel,
      cursor.previous? = some previous ∧
        previous.1.address.length < cursor.occurrence.1.address.length

/-- A child of an outward cursor again moves strictly outward. -/
private theorem branch_child_step_outward
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (state : OutwardCursorState tree.source)
    {slot : Nat} {child : LocalizedCumulativeDecoratedTree input carrierFuel}
    (lookup : tree.children[slot]? = some child) :
    child.source.occurrence.1.address.length =
        tree.source.occurrence.1.address.length + 1 ∧
      OutwardCursorState child.source := by
  have edge := mem_executable_of_child realizes lookup
  rcases state with ⟨valid, previous, previousEq, previousShorter⟩
  rcases input.outward_edge tree.source child.source valid previous previousEq previousShorter
      edge with ⟨_dropLast, childLength, _rootEq, childPrevious, childValid⟩
  exact ⟨childLength, childValid, tree.source.occurrence, childPrevious, by omega⟩

/-- Along a strict outward branch, position depth is exactly address growth from the branch
attachment. -/
private theorem subtreeAt?_source_address_length_relative_outward
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {path : List Nat}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (state : OutwardCursorState tree.source)
    {node : LocalizedCumulativeDecoratedTree input carrierFuel}
    (lookup : subtreeAt? tree path = some node) :
    node.source.occurrence.1.address.length =
      tree.source.occurrence.1.address.length + path.length := by
  induction path generalizing tree with
  | nil =>
      rw [subtreeAt?_nil] at lookup
      have nodeEq : node = tree := (Option.some.inj lookup).symm
      subst node
      simp
  | cons slot rest inductionHypothesis =>
      rw [subtreeAt?_cons_eq_some_iff] at lookup
      obtain ⟨child, childLookup, restLookup⟩ := lookup
      have step := branch_child_step_outward realizes state childLookup
      have childResult := inductionHypothesis
        (realizes_of_child realizes childLookup) step.2 restLookup
      rw [childResult, step.1, List.length_cons]
      omega

/-- **Branch position depth.**  For a realized tree rooted at a cursor that arrived strictly
outward from its incoming coordinate, the address length at any position is the attachment
address length plus the position depth.  The actual top branch cursor has address `[slot]` and
incoming root occurrence, so this is the relation needed for branch-relative physical distance;
it deliberately does not identify the attachment address length with zero. -/
theorem positionSource_address_length_of_previous
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {startCursor : input.LocalizedRerootCursor carrierFuel}
    (valid : input.LocalizedRerootCursorValid startCursor)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : startCursor.previous? = some previous)
    (previousShorter : previous.1.address.length < startCursor.occurrence.1.address.length)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (sourceEq : tree.source = startCursor)
    (p : Position tree) :
    (positionSource p).occurrence.1.address.length =
      startCursor.occurrence.1.address.length + p.val.length := by
  have state : OutwardCursorState tree.source := by
    rw [sourceEq]
    exact ⟨valid, previous, previousEq, previousShorter⟩
  have relative := subtreeAt?_source_address_length_relative_outward realizes
    state (positionNode_spec p)
  simpa [positionSource, sourceEq] using relative

/-- Every actual child of a realized tree keeps the occurrence root of its source. -/
private theorem branch_child_source_root_eq
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    {slot : Nat} {child : LocalizedCumulativeDecoratedTree input carrierFuel}
    (lookup : tree.children[slot]? = some child) :
    child.source.occurrence.1.root = tree.source.occurrence.1.root := by
  have edge := mem_executable_of_child realizes lookup
  have derived := input.executableLocalizedRerootChildren_declarative tree.source
  have childIntended : child.source.occurrence.1 ∈
      input.intendedLocalizedRerootChildFrames tree.source := by
    rw [← derived.1]
    exact List.mem_map.mpr ⟨child.source, edge, rfl⟩
  have neighbor := input.mem_localizedRerootNeighborFrames_of_mem_intended
    tree.source child.source.occurrence.1 childIntended
  exact ((input.mem_localizedRerootNeighborFrames_iff tree.source.occurrence.1
    child.source.occurrence.1).mp neighbor).2.1

/-- Along any successful descent in a realized tree, the occurrence root is preserved. -/
private theorem subtreeAt?_source_root_eq
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    {path : List Nat} {node : LocalizedCumulativeDecoratedTree input carrierFuel}
    (lookup : subtreeAt? tree path = some node) :
    node.source.occurrence.1.root = tree.source.occurrence.1.root := by
  induction path generalizing tree with
  | nil =>
      rw [subtreeAt?_nil] at lookup
      have nodeEq : node = tree := (Option.some.inj lookup).symm
      subst node
      rfl
  | cons slot rest inductionHypothesis =>
      rw [subtreeAt?_cons_eq_some_iff] at lookup
      obtain ⟨child, childLookup, restLookup⟩ := lookup
      exact (inductionHypothesis (realizes_of_child realizes childLookup) restLookup).trans
        (branch_child_source_root_eq realizes childLookup)

/-- Every actual position source keeps the occurrence root of the tree source. -/
private theorem positionSource_root_eq
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree) (p : Position tree) :
    (positionSource p).occurrence.1.root = tree.source.occurrence.1.root :=
  subtreeAt?_source_root_eq realizes (positionNode_spec p)

/-- Uppercase chiral descriptors in a label-only observation list, in list order. -/
def chiralDescriptorsOfObservations :
    List (Option LocalizedAuxiliaryLabel) → List RS
  | [] => []
  | none :: rest => chiralDescriptorsOfObservations rest
  | some (.pseudoasymmetric _) :: rest => chiralDescriptorsOfObservations rest
  | some (.chiral descriptor) :: rest => descriptor :: chiralDescriptorsOfObservations rest

/-- Extracting upper-case chiral descriptors from an addressed sparse sphere is the same as
forgetting the addresses and then extracting them from the label list. -/
private theorem chiralObservationsInLayer_eq_of_map_snd
    (layer : List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))) :
    localizedRule4bChiralObservationsInLayer layer =
      chiralDescriptorsOfObservations (layer.map Prod.snd) := by
  induction layer with
  | nil => rfl
  | cons head rest inductionHypothesis =>
      rcases head with ⟨address, label⟩
      cases label with
      | none =>
          simpa [localizedRule4bChiralObservationsInLayer,
            chiralDescriptorsOfObservations] using inductionHypothesis
      | some label =>
          cases label with
          | pseudoasymmetric descriptor =>
              simpa [localizedRule4bChiralObservationsInLayer,
                chiralDescriptorsOfObservations] using inductionHypothesis
          | chiral descriptor =>
              show descriptor :: localizedRule4bChiralObservationsInLayer rest =
                descriptor :: chiralDescriptorsOfObservations (rest.map Prod.snd)
              rw [inductionHypothesis]

/-- **Tree-depth chiral observations.**  The chiral observations that Rule 4b reads from the
label sphere at tree depth `d` are exactly the chiral labels of the realized tree nodes at that
depth, in left-to-right sibling order. -/
theorem labelTable_chiralObservations
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) (depth : Nat) :
    localizedRule4bChiralObservationsInLayer (tree.labelTable.getD depth []) =
      chiralDescriptorsOfObservations
        (observationsAtDepth (fun node => node.label) depth tree) := by
  rw [chiralObservationsInLayer_eq_of_map_snd, labelTable_getD_map_snd]





theorem key_labels_chiralObservations_of_labelTable_eq
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (labelTableEq : tree.labelTable = key.labels) (depth : Nat) :
    localizedRule4bChiralObservationsInLayer (key.labels.getD depth []) =
      chiralDescriptorsOfObservations
        (observationsAtDepth (fun node => node.label) depth tree) := by
  rw [← labelTableEq, labelTable_chiralObservations]

/-- **A realized node carries the reader's value at its own actual cursor.**  Actual tree
provenance constructs every node as the actual root tree at a real cursor, whose `label` field is
the reader value at that cursor. -/
theorem subtreeAt?_node_label_eq_read
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    {path : List Nat} {node : LocalizedCumulativeDecoratedTree input carrierFuel}
    (lookup : subtreeAt? tree path = some node) :
    node.label = read node.source := by
  induction path generalizing tree with
  | nil =>
      rw [subtreeAt?_nil] at lookup
      have nodeEq : node = tree := (Option.some.inj lookup).symm
      subst node
      cases realizes with
      | mk cursor children sortedChildren childrenComputed sourcePerm childrenRealize =>
          rfl
  | cons slot rest inductionHypothesis =>
      rw [subtreeAt?_cons_eq_some_iff] at lookup
      obtain ⟨child, childLookup, restLookup⟩ := lookup
      exact inductionHypothesis (realizes_of_child realizes childLookup) restLookup

/-- **The realized node at a position carries the reader's value at its actual source.** -/
theorem positionNode_label_eq_read
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree) (p : Position tree) :
    (positionNode p).label = read (positionSource p) :=
  subtreeAt?_node_label_eq_read realizes (positionNode_spec p)

end LocalizedCumulativeDecoratedTree

/-- A valid reroot cursor and its recorded incoming coordinate share the occurrence root. -/
private theorem cursor_root_eq_of_valid
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {cursor : input.LocalizedRerootCursor carrierFuel}
    (valid : input.LocalizedRerootCursorValid cursor)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : cursor.previous? = some previous) :
    cursor.occurrence.1.root = previous.1.root := by
  have neighbor : cursor.occurrence.1 ∈
      input.localizedRerootNeighborFrames (fuel := carrierFuel) previous.1 := by
    unfold LocalizedRerootCursorValid at valid
    rw [previousEq] at valid
    change cursor.occurrence.1 ∈
      input.localizedRerootNeighborFrames (fuel := carrierFuel) previous.1 at valid
    exact valid
  exact ((input.mem_localizedRerootNeighborFrames_iff previous.1
    cursor.occurrence.1).mp neighbor).2.1

/-- **The actual reader is the actual whole state along an outward branch.**

Consider a realized tree built with the actual restricted dependency reader over the state
projection, whose root cursor was reached strictly outward from its recorded incoming coordinate,
and let that incoming coordinate be the dependency target.  Then at every tree position the node's
actual label is the whole-state value at the position's actual occurrence.  The proof uses only
the actual provenance of the reader, the root preservation of actual child steps, and the strict
address growth of the outward branch.  No read value, desired label, selector, layer hypothesis,
or marking correspondence is supplied. -/
theorem positionNode_label_eq_state_of_outward
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input
      (fun cursor => input.localizedDependencyLabel target
        (input.localizedDependencyView state target) cursor) tree)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (previousShorter : previous.1.address.length < tree.source.occurrence.1.address.length)
    (targetEq : previous = target)
    (p : Position tree) :
    (positionNode p).label = state (positionSource p).occurrence := by
  rw [LocalizedCumulativeDecoratedTree.positionNode_label_eq_read realizes p]
  have sameRoot : tree.source.occurrence.1.root = previous.1.root :=
    cursor_root_eq_of_valid valid previous previousEq
  have rootEq : (positionSource p).occurrence.1.root = target.1.root := by
    rw [LocalizedCumulativeDecoratedTree.positionSource_root_eq realizes p, sameRoot,
      targetEq]
  have lengthLt : target.1.address.length <
      (positionSource p).occurrence.1.address.length := by
    rw [← targetEq]
    have relative :=
      LocalizedCumulativeDecoratedTree.positionSource_address_length_of_previous
      (input := input) (carrierFuel := carrierFuel)
      (read := fun cursor => input.localizedDependencyLabel target
        (input.localizedDependencyView state target) cursor)
      (startCursor := tree.source) valid previous previousEq previousShorter realizes rfl p
    rw [relative]
    omega
  exact input.localizedDependencyLabel_eq_state_of_dependency target state
    (positionSource p) ⟨rootEq, lengthLt⟩

/-- Every successful production Rule-4a cumulative build has an actual decorated occurrence tree
with the actual cursor as root, the actual key's four tables, the exact label table of the actual
key's `labels`, and full recursive actual child provenance. -/
theorem exists_decoratedTree_of_buildLocalizedRerootCumulativeRule45Key?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (computed : input.buildLocalizedRerootCumulativeRule45Key?
      stage target view fuel cursor = some key) :
    ∃ tree : LocalizedCumulativeDecoratedTree input carrierFuel,
      tree.source = cursor ∧
        LocalizedCumulativeTreeTableMatch stage tree key ∧
          tree.labelTable = key.labels ∧
            LocalizedCumulativeTreeRealizes input
              (fun cursor => input.localizedDependencyLabel target view cursor) tree := by
  have withRead : input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage
      (fun cursor => input.localizedDependencyLabel target view cursor) fuel cursor = some key := by
    rw [input.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
      stage target view fuel cursor]
    exact computed
  obtain ⟨tree, treeSource, tableMatch, labelTableEq, realizes, _children, _childrenComputed,
    _sourcePerm⟩ :=
    exists_decoratedTree_of_buildWithRead_labelTable input stage
      (fun cursor => input.localizedDependencyLabel target view cursor) fuel cursor key withRead
  exact ⟨tree, treeSource, tableMatch, labelTableEq, realizes⟩

/-- **Actual Rule-4a selector from tree-depth observations.**  If a successful production build's
actual tree has no chiral label at any earlier tree depth and exactly `descriptor` at the target
tree depth, then the selector computed from the actual key's hierarchy-ranked labels is the
singleton `[descriptor]`. -/
theorem buildLocalizedRerootCumulativeRule45Key?_referenceSelection_singleton_of_tree_observations
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (labelTableEq : tree.labelTable = key.labels)
    (depth : Nat) (descriptor : RS)
    (computed : input.buildLocalizedRerootCumulativeRule45Key?
      stage target view fuel cursor = some key)
    (before : ∀ earlier < depth,
      LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
        (LocalizedCumulativeDecoratedTree.observationsAtDepth
          (fun node => node.label) earlier tree) = [])
    (atDepth : LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
      (LocalizedCumulativeDecoratedTree.observationsAtDepth
        (fun node => node.label) depth tree) = [descriptor]) :
    localizedRule4bReferencesFromRankedLabels key.rankedLabels = [descriptor] := by
  apply buildLocalizedRerootCumulativeRule45Key?_referenceSelection_singleton_of_first_uniqueChiral
    input stage target view fuel cursor key depth descriptor computed
  · intro earlier bound
    rw [LocalizedCumulativeDecoratedTree.key_labels_chiralObservations_of_labelTable_eq
      tree key labelTableEq earlier]
    exact before earlier bound
  · rw [LocalizedCumulativeDecoratedTree.key_labels_chiralObservations_of_labelTable_eq
      tree key labelTableEq depth]
    exact atDepth

/-- **Actual Rule-4bc singleton reading from tree-depth observations.**  On a successful
production compound build, the Rule-4a tree of the retained key supplies the layer observations;
the same no-earlier/exactly-one premises yield one actual reading whose reference is the
prescribed descriptor. -/
theorem buildLocalizedRerootCompoundRule4bcKey?_readings_singleton_of_tree_observations
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule4bcKey)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (labelTableEq : tree.labelTable = key.rule4aKey.labels)
    (depth : Nat) (descriptor : RS)
    (computed : input.buildLocalizedRerootCompoundRule4bcKey?
      target view fuel cursor = some key)
    (before : ∀ earlier < depth,
      LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
        (LocalizedCumulativeDecoratedTree.observationsAtDepth
          (fun node => node.label) earlier tree) = [])
    (atDepth : LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
      (LocalizedCumulativeDecoratedTree.observationsAtDepth
        (fun node => node.label) depth tree) = [descriptor]) :
    ∃ reading : input.LocalizedRerootRule4bcReading,
      key.readings = [reading] ∧ reading.reference? = some descriptor := by
  apply buildLocalizedRerootCompoundRule4bcKey?_readings_singleton_of_first_uniqueChiral
    input target view fuel cursor key depth descriptor computed
  · intro earlier bound
    rw [LocalizedCumulativeDecoratedTree.key_labels_chiralObservations_of_labelTable_eq
      tree key.rule4aKey labelTableEq earlier]
    exact before earlier bound
  · rw [LocalizedCumulativeDecoratedTree.key_labels_chiralObservations_of_labelTable_eq
      tree key.rule4aKey labelTableEq depth]
    exact atDepth
















section PhysicalDepthSphere

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}

/-- Flattening a slot-indexed list while ignoring the index. -/
private theorem zipIdx_flatMap_fst_from_physical {β γ : Type*} (start : Nat)
    (values : List β) (f : β → List γ) :
    (values.zipIdx start).flatMap (fun pair => f pair.1) = values.flatMap f := by
  induction values generalizing start with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [List.zipIdx_cons, inductionHypothesis]

/-- The addressed nodes at one tree depth, in the same left-to-right order as
`observationsAtDepth`.  Each address is the root-first sibling-slot path of the node. -/
private def nodesWithAddress
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    Nat → List (List Nat × LocalizedCumulativeDecoratedTree input carrierFuel)
  | 0 => [([], tree)]
  | depth + 1 =>
      (tree.children.zipIdx 0).flatMap fun pair =>
        (nodesWithAddress pair.1 depth).map fun childPair =>
          (pair.2 :: childPair.1, childPair.2)

/-- Forgetting addresses from the addressed nodes is exactly the observation list. -/
private theorem observationsAtDepth_eq_nodesWithAddress_map {α : Type*}
    (observe : LocalizedCumulativeDecoratedTree input carrierFuel → α) :
    ∀ (depth : Nat) (tree : LocalizedCumulativeDecoratedTree input carrierFuel),
      LocalizedCumulativeDecoratedTree.observationsAtDepth observe depth tree =
        (nodesWithAddress tree depth).map (fun pair => observe pair.2) := by
  intro depth
  induction depth with
  | zero =>
      intro tree
      rfl
  | succ depth inductionHypothesis =>
      intro tree
      rw [show LocalizedCumulativeDecoratedTree.observationsAtDepth observe (depth + 1) tree =
          tree.children.flatMap
            (fun child =>
              LocalizedCumulativeDecoratedTree.observationsAtDepth observe depth child) from rfl]
      rw [show nodesWithAddress tree (depth + 1) =
          (tree.children.zipIdx 0).flatMap (fun pair =>
            (nodesWithAddress pair.1 depth).map fun childPair =>
              (pair.2 :: childPair.1, childPair.2)) from rfl]
      rw [List.map_flatMap]
      simp only [List.map_map, Function.comp_def]
      rw [zipIdx_flatMap_fst_from_physical 0 tree.children
        (fun child => (nodesWithAddress child depth).map (fun pair => observe pair.2))]
      apply List.flatMap_congr
      intro child _
      exact inductionHypothesis child

/-- Every addressed node is the actual subtree at its address, and its address length is the
depth at which it was collected. -/
private theorem nodesWithAddress_valid
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel} {depth : Nat}
    {pair : List Nat × LocalizedCumulativeDecoratedTree input carrierFuel}
    (present : pair ∈ nodesWithAddress tree depth) :
    subtreeAt? tree pair.1 = some pair.2 ∧
      pair.1.length = depth := by
  induction depth generalizing tree pair with
  | zero =>
      simp only [nodesWithAddress, List.mem_singleton] at present
      rcases present with rfl
      simp
  | succ depth inductionHypothesis =>
      simp only [nodesWithAddress, List.mem_flatMap, List.mem_map] at present
      obtain ⟨block, blockPresent, childPair, childPresent, pairEq⟩ := present
      obtain ⟨child, slot⟩ := block
      rcases pairEq with rfl
      obtain ⟨childLookup, childLength⟩ := inductionHypothesis childPresent
      have slotLookup : tree.children[slot]? = some child :=
        List.mem_zipIdx_iff_getElem?.mp blockPresent
      constructor
      · rw [subtreeAt?_cons, slotLookup]
        simpa using childLookup
      · simp [childLength]

/-- A flat map whose blocks are individually `Nodup` and pairwise disjoint is `Nodup`. -/
private theorem nodup_flatMap_of_pairwise {α β : Type*}
    (values : List α) (block : α → List β)
    (blocksNodup : ∀ value ∈ values, (block value).Nodup)
    (cross : values.Pairwise fun left right =>
      ∀ x ∈ block left, ∀ y ∈ block right, x ≠ y) :
    (values.flatMap block).Nodup := by
  induction values with
  | nil => simp
  | cons head tail inductionHypothesis =>
      rw [List.flatMap_cons, List.nodup_append]
      have crossParts := List.pairwise_cons.mp cross
      refine ⟨blocksNodup head (by simp),
        inductionHypothesis (fun value present => blocksNodup value (by simp [present]))
          crossParts.2, ?_⟩
      intro x xPresent y yPresent
      rw [List.mem_flatMap] at yPresent
      obtain ⟨value, valuePresent, yBlock⟩ := yPresent
      exact crossParts.1 value (by simp [valuePresent]) x xPresent y yBlock

/-- The addresses of the nodes at a fixed depth are pairwise distinct. -/
private theorem nodesWithAddress_paths_nodup
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) (depth : Nat) :
    ((nodesWithAddress tree depth).map Prod.fst).Nodup := by
  induction depth generalizing tree with
  | zero => simp [nodesWithAddress]
  | succ depth inductionHypothesis =>
      rw [show nodesWithAddress tree (depth + 1) =
          (tree.children.zipIdx 0).flatMap (fun pair =>
            (nodesWithAddress pair.1 depth).map fun childPair =>
              (pair.2 :: childPair.1, childPair.2)) from rfl]
      rw [List.map_flatMap]
      simp only [List.map_map, Function.comp_def]
      apply nodup_flatMap_of_pairwise
      · intro pair _
        have reshaped :
            (nodesWithAddress pair.1 depth).map (fun childPair => pair.2 :: childPair.1) =
              ((nodesWithAddress pair.1 depth).map Prod.fst).map
                (fun path => pair.2 :: path) := by
          rw [List.map_map]
          rfl
        rw [reshaped]
        exact List.Nodup.map (f := fun path => pair.2 :: path)
          (fun _ _ same => (List.cons.inj same).2) (inductionHypothesis pair.1)
      · have slotsPairwise :
            (tree.children.zipIdx 0).Pairwise (fun left right => left.2 ≠ right.2) := by
          have slotsNodup : ((tree.children.zipIdx 0).map Prod.snd).Nodup := by
            rw [List.zipIdx_map_snd 0 tree.children]
            exact List.nodup_range'
          exact List.pairwise_map.mp slotsNodup
        refine slotsPairwise.imp ?_
        intro left right different x xPresent y yPresent same
        rw [List.mem_map] at xPresent yPresent
        obtain ⟨leftPair, _, xEq⟩ := xPresent
        obtain ⟨rightPair, _, yEq⟩ := yPresent
        rw [← xEq, ← yEq] at same
        exact different (List.cons.inj same).1

/-- The position whose node is an addressed node at the depth where it was collected. -/
private def positionOfNodesWithAddress
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel} {depth : Nat}
    {pair : List Nat × LocalizedCumulativeDecoratedTree input carrierFuel}
    (present : pair ∈ nodesWithAddress tree depth) :
    Position tree :=
  ⟨pair.1, by
    rw [subtreeAt?_isSome_iff]
    exact ⟨pair.2, (nodesWithAddress_valid present).1⟩⟩

private theorem positionOfNodesWithAddress_val
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel} {depth : Nat}
    {pair : List Nat × LocalizedCumulativeDecoratedTree input carrierFuel}
    (present : pair ∈ nodesWithAddress tree depth) :
    (positionOfNodesWithAddress present).val = pair.1 := rfl

private theorem positionOfNodesWithAddress_node
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel} {depth : Nat}
    {pair : List Nat × LocalizedCumulativeDecoratedTree input carrierFuel}
    (present : pair ∈ nodesWithAddress tree depth) :
    positionNode (positionOfNodesWithAddress present) = pair.2 := by
  apply Option.some.inj
  exact (positionNode_spec (positionOfNodesWithAddress present)).symm.trans
    (nodesWithAddress_valid present).1

private theorem positionOfNodesWithAddress_length
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel} {depth : Nat}
    {pair : List Nat × LocalizedCumulativeDecoratedTree input carrierFuel}
    (present : pair ∈ nodesWithAddress tree depth) :
    (positionOfNodesWithAddress present).val.length = depth := by
  rw [positionOfNodesWithAddress_val]
  exact (nodesWithAddress_valid present).2

/-- The chiral descriptors extracted from a label list are exactly the descriptors carried by
upper-case chiral entries. -/
private theorem mem_chiralDescriptorsOfObservations_iff
    (labels : List (Option LocalizedAuxiliaryLabel)) (descriptor : RS) :
    descriptor ∈ LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations labels ↔
      ∃ label ∈ labels, label = some (.chiral descriptor) := by
  induction labels with
  | nil => simp [LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations]
  | cons head tail inductionHypothesis =>
      cases head with
      | none =>
          simpa [LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations]
            using inductionHypothesis
      | some label =>
          cases label with
          | pseudoasymmetric value =>
              simpa [LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations]
                using inductionHypothesis
          | chiral value =>
              simp [LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations,
                inductionHypothesis]

/-- A label list with no upper-case chiral entry has no chiral descriptors. -/
private theorem chiralDescriptorsOfObservations_eq_nil_iff
    (labels : List (Option LocalizedAuxiliaryLabel)) :
    LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations labels = [] ↔
      ∀ label ∈ labels, ∀ descriptor : RS, label ≠ some (.chiral descriptor) := by
  rw [List.eq_nil_iff_forall_not_mem]
  constructor
  · intro empty label present descriptor same
    exact empty descriptor ((mem_chiralDescriptorsOfObservations_iff labels descriptor).mpr
      ⟨label, present, same⟩)
  · intro noChiral descriptor present
    obtain ⟨label, labelPresent, same⟩ :=
      (mem_chiralDescriptorsOfObservations_iff labels descriptor).mp present
    exact noChiral label labelPresent descriptor same

/-- If at most one index of a label list carries an upper-case chiral entry, the extracted chiral
descriptor list has length at most one. -/
private theorem chiralDescriptorsOfObservations_length_le_one
    (labels : List (Option LocalizedAuxiliaryLabel))
    (atMostOne : ∀ (i j : Nat) (hi : i < labels.length) (hj : j < labels.length),
      (∃ descriptor : RS, labels[i]'hi = some (.chiral descriptor)) →
      (∃ descriptor : RS, labels[j]'hj = some (.chiral descriptor)) → i = j) :
    (LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations labels).length ≤ 1 := by
  induction labels with
  | nil => simp [LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations]
  | cons head tail inductionHypothesis =>
      have tailAtMostOne :
          ∀ (i j : Nat) (hi : i < tail.length) (hj : j < tail.length),
            (∃ descriptor : RS, tail[i]'hi = some (.chiral descriptor)) →
            (∃ descriptor : RS, tail[j]'hj = some (.chiral descriptor)) → i = j := by
        intro i j hi hj hiChiral hjChiral
        have boundI : i + 1 < (head :: tail).length := by simp [hi]
        have boundJ : j + 1 < (head :: tail).length := by simp [hj]
        have evalI : (head :: tail)[i + 1]'boundI = tail[i]'hi := by simp
        have evalJ : (head :: tail)[j + 1]'boundJ = tail[j]'hj := by simp
        obtain ⟨descriptorI, indexI⟩ := hiChiral
        obtain ⟨descriptorJ, indexJ⟩ := hjChiral
        have consI : ∃ descriptor : RS,
            (head :: tail)[i + 1]'boundI = some (.chiral descriptor) :=
          ⟨descriptorI, by rw [evalI]; exact indexI⟩
        have consJ : ∃ descriptor : RS,
            (head :: tail)[j + 1]'boundJ = some (.chiral descriptor) :=
          ⟨descriptorJ, by rw [evalJ]; exact indexJ⟩
        exact Nat.succ.inj (atMostOne (i + 1) (j + 1) boundI boundJ consI consJ)
      cases head with
      | none =>
          simpa [LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations]
            using inductionHypothesis tailAtMostOne
      | some label =>
          cases label with
          | pseudoasymmetric value =>
              simpa [LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations]
                using inductionHypothesis tailAtMostOne
          | chiral value =>
              have noChiralTail : ∀ next ∈ tail, ∀ descriptor : RS,
                  next ≠ some (.chiral descriptor) := by
                intro next nextPresent descriptor nextChiral
                obtain ⟨k, kBound, kEq⟩ := List.mem_iff_getElem.mp nextPresent
                have boundZero : 0 < (some (.chiral value) :: tail).length := by simp
                have boundSucc : k + 1 < (some (.chiral value) :: tail).length := by
                  simp [kBound]
                have evalSucc : (some (.chiral value) :: tail)[k + 1]'boundSucc =
                    some (.chiral descriptor) := by
                  simp [kEq, nextChiral]
                have sameIndex := atMostOne 0 (k + 1) boundZero boundSucc
                  ⟨value, by simp⟩ ⟨descriptor, evalSucc⟩
                exact Nat.succ_ne_zero k sameIndex.symm
              have tailEmpty :
                  LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations tail = [] :=
                (chiralDescriptorsOfObservations_eq_nil_iff tail).mpr noChiralTail
              simp [LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations, tailEmpty]

/-- Every node at a tree depth is observed at that depth. -/
private theorem position_label_mem_observationsAtDepth
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (p : Position tree) :
    (positionNode p).label ∈
      LocalizedCumulativeDecoratedTree.observationsAtDepth
        (fun node => node.label) p.val.length tree := by
  obtain ⟨path, property⟩ := p
  revert property
  revert tree
  induction path with
  | nil =>
      intro tree property
      change (positionNode (⟨[], property⟩ : Position tree)).label ∈
        LocalizedCumulativeDecoratedTree.observationsAtDepth
          (fun node => node.label) 0 tree
      rw [positionNode_eq_tree_of_val_eq_nil (p := (⟨[], property⟩ : Position tree)) rfl]
      simp [LocalizedCumulativeDecoratedTree.observationsAtDepth]
  | cons slot rest inductionHypothesis =>
      intro tree property
      obtain ⟨child, lookup, q, qVal, nodeEq⟩ :=
        exists_child_of_position_cons
          (p := (⟨slot :: rest, property⟩ : Position tree)) rfl
      have presentChild : child ∈ tree.children := List.mem_of_getElem? lookup
      change (positionNode (⟨slot :: rest, property⟩ : Position tree)).label ∈
        LocalizedCumulativeDecoratedTree.observationsAtDepth
          (fun node => node.label) (Nat.succ rest.length) tree
      rw [LocalizedCumulativeDecoratedTree.observationsAtDepth]
      apply List.mem_flatMap.mpr
      refine ⟨child, presentChild, ?_⟩
      have qProperty : (subtreeAt? child rest).isSome = true := by
        rw [← qVal]
        exact q.property
      have nodeRest : positionNode (⟨rest, qProperty⟩ : Position child) = positionNode q := by
        apply Option.some.inj
        calc
          some (positionNode (⟨rest, qProperty⟩ : Position child)) =
              subtreeAt? child rest := (positionNode_spec _).symm
          _ = subtreeAt? child q.val := by rw [qVal]
          _ = some (positionNode q) := positionNode_spec q
      have observed := inductionHypothesis (tree := child) qProperty
      rw [nodeRest] at observed
      rw [nodeEq]
      exact observed

/-- Every observation at a tree depth is the label of some position at that depth. -/
private theorem exists_position_of_mem_observationsAtDepth {depth : Nat}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {label : Option LocalizedAuxiliaryLabel}
    (present : label ∈
      LocalizedCumulativeDecoratedTree.observationsAtDepth
        (fun node => node.label) depth tree) :
    ∃ p : Position tree, p.val.length = depth ∧ (positionNode p).label = label := by
  induction depth generalizing tree with
  | zero =>
      rw [LocalizedCumulativeDecoratedTree.observationsAtDepth] at present
      simp only [List.mem_singleton] at present
      refine ⟨rootPosition tree, rfl, ?_⟩
      rw [positionNode_rootPosition]
      exact present.symm
  | succ depth inductionHypothesis =>
      rw [LocalizedCumulativeDecoratedTree.observationsAtDepth] at present
      rw [List.mem_flatMap] at present
      obtain ⟨child, childPresent, labelPresent⟩ := present
      obtain ⟨slot, lookup⟩ := List.mem_iff_getElem?.mp childPresent
      obtain ⟨q, qLength, qLabel⟩ := inductionHypothesis labelPresent
      let lifted : Position tree :=
        ⟨slot :: q.val, by
          rw [subtreeAt?_isSome_iff]
          exact ⟨positionNode q, by
            rw [subtreeAt?_cons_eq_some_iff]
            exact ⟨child, lookup, positionNode_spec q⟩⟩⟩
      have liftedNode : positionNode lifted = positionNode q := by
        apply Option.some.inj
        exact (positionNode_spec lifted).symm.trans (by
          rw [subtreeAt?_cons_eq_some_iff]
          exact ⟨child, lookup, positionNode_spec q⟩)
      refine ⟨lifted, ?_, ?_⟩
      · change (slot :: q.val).length = depth + 1
        simp [qLength]
      · rw [liftedNode, qLabel]









variable {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}

/-- Copying a walk along equal endpoints preserves pathhood. -/
private theorem walk_isPath_copy {G : SimpleGraph input.Atom} {u v u' v' : input.Atom}
    {walk : G.Walk u v} (path : walk.IsPath) (startEq : u = u') (endEq : v = v') :
    (walk.copy startEq endEq).IsPath := by
  rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_copy]
  exact (SimpleGraph.Walk.isPath_def walk).mp path

/-- **A simple physical walk along a residual address suffix.**  From a base position, a list of
further sibling slots and a target position whose address is the base address followed by those
slots, the physical atom of the target is reached from the physical atom of the base by a simple
walk whose length is the number of suffix slots.  Every atom on the walk is the atom of a position
no shallower than the base. -/
private theorem exists_walk_to_position_aux
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    {oAtom pAtom : input.Atom}
    (oObserved : tree.source.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (base : Position tree) (slots : List Nat) (target : Position tree)
    (targetVal : target.val = base.val ++ slots) :
    ∃ walk : (input.moleculeGraph.underlyingSimpleGraph).Walk
        (positionAtom singleBonded acyclic base)
        (positionAtom singleBonded acyclic target),
      walk.IsPath ∧ walk.length = slots.length ∧
        (∀ x ∈ walk.support, ∃ q : Position tree,
          positionAtom singleBonded acyclic q = x ∧
            base.val.length ≤ q.val.length) := by
  induction slots generalizing base target with
  | nil =>
      have targetEq : target = base := Subtype.ext (by simpa using targetVal)
      subst target
      refine ⟨SimpleGraph.Walk.nil, SimpleGraph.Walk.IsPath.nil, by simp, ?_⟩
      intro x xPresent
      rw [SimpleGraph.Walk.support_nil, List.mem_singleton] at xPresent
      subst x
      exact ⟨base, rfl, le_rfl⟩
  | cons slot rest inductionHypothesis =>
      have midSome : (subtreeAt? tree (base.val ++ [slot])).isSome = true := by
        apply subtreeAt?_isSome_iff _ |>.mpr
        have spec := positionNode_spec target
        rw [targetVal] at spec
        rw [show base.val ++ (slot :: rest) = (base.val ++ [slot]) ++ rest by simp] at spec
        rw [subtreeAt?_append] at spec
        obtain ⟨node, lookup, _⟩ := Option.bind_eq_some_iff.mp spec
        exact ⟨node, lookup⟩
      let mid : Position tree := ⟨base.val ++ [slot], midSome⟩
      have adjacent : input.moleculeGraph.Adj
          (positionAtom singleBonded acyclic base)
          (positionAtom singleBonded acyclic mid) :=
        (positionAtom_adjacent_iff_positionAdjacent singleBonded acyclic enough realizes
          previous previousEq sameRoot valid oObserved pObserved incomingEdge base mid).mpr
          (Or.inl ⟨slot, rfl⟩)
      have adjacentGraph : (input.moleculeGraph.underlyingSimpleGraph).Adj
          (positionAtom singleBonded acyclic base)
          (positionAtom singleBonded acyclic mid) := adjacent
      have targetRest : target.val = mid.val ++ rest := by
        rw [show mid.val = base.val ++ [slot] from rfl, targetVal]
        simp
      obtain ⟨walkRest, restPath, restLength, restSupport⟩ :=
        inductionHypothesis mid target targetRest
      have fresh : positionAtom singleBonded acyclic base ∉ walkRest.support := by
        intro present
        obtain ⟨q, qAtom, qLength⟩ := restSupport _ present
        have qEq : q = base :=
          positionAtom_injective singleBonded acyclic enough realizes previous previousEq
            sameRoot oObserved pObserved q base qAtom
        rw [qEq] at qLength
        have midLength : mid.val.length = base.val.length + 1 := by simp [mid]
        omega
      refine ⟨SimpleGraph.Walk.cons adjacentGraph walkRest, ?_, ?_, ?_⟩
      · exact restPath.cons fresh
      · simp [restLength]
      · intro x xPresent
        rw [SimpleGraph.Walk.support_cons] at xPresent
        rcases List.mem_cons.mp xPresent with same | inRest
        · subst x
          exact ⟨base, rfl, le_rfl⟩
        · obtain ⟨q, qAtom, qLength⟩ := restSupport x inRest
          exact ⟨q, qAtom, le_trans (by simp [mid]) qLength⟩

/-- **A simple physical walk to any tree position.**  The walk starts at the branch attachment and
has length exactly the position's address length. -/
private theorem exists_walk_to_position
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    {oAtom pAtom : input.Atom}
    (oObserved : tree.source.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (p : Position tree) :
    ∃ walk : (input.moleculeGraph.underlyingSimpleGraph).Walk oAtom
        (positionAtom singleBonded acyclic p),
      walk.IsPath ∧ walk.length = p.val.length := by
  obtain ⟨walk, path, length, _support⟩ :=
    exists_walk_to_position_aux singleBonded acyclic enough realizes previous previousEq valid
      sameRoot oObserved pObserved incomingEdge (rootPosition tree) p.val p (by simp [rootPosition])
  have startEq : positionAtom singleBonded acyclic (rootPosition tree) = oAtom :=
    positionAtom_rootPosition singleBonded acyclic tree oObserved
  refine ⟨walk.copy startEq rfl, ?_, ?_⟩
  · exact walk_isPath_copy path startEq rfl
  · rw [SimpleGraph.Walk.length_copy]
    exact length

/-- The physical sphere of radius `distance` around an attachment atom: the atoms reached by an
actual simple walk of exactly that length.  This is physical branch distance from the attachment,
not the stored original-root Rule-1b distance. -/
def PhysicalSimpleSphere (graph : SimpleGraph input.Atom) (attachment : input.Atom)
    (distance : Nat) : Set input.Atom :=
  {atom | ∃ walk : graph.Walk attachment atom, walk.IsPath ∧ walk.length = distance}

/-- **Physical unique nearest chiral centre gives the actual tree's depth observations.**

The reader labels a position with an upper-case chiral descriptor exactly when the physical marked
function marks its atom with that descriptor.  If `center` is a marked atom of the incoming physical
cut branch, lies at simple-walk distance `distance` from the attachment, and is the unique marked
branch atom at that radius with no marked branch atom at any smaller radius, then the actual tree
has no chiral label at any earlier depth and exactly `descriptor` at depth `distance`.

The hypothesis `uniqueAt` is the physical uniqueness of the nearest centre; it is not a tree-layer
selection, an alignment, or a reference-selection assumption.  The separate `reader` hypothesis is
the semantic reader correspondence; it is deliberately kept distinct from the actual selected
reference proved downstream. -/
theorem tree_observations_of_physicalUniqueNearest
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    {oAtom pAtom : input.Atom}
    (oObserved : tree.source.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (marked : input.Atom → Option RS)
    (reader : ∀ (p : Position tree) (descriptor : RS),
      (positionNode p).label = some (.chiral descriptor) ↔
        marked (positionAtom singleBonded acyclic p) = some descriptor)
    {center : input.Atom} {descriptor : RS} {distance : Nat}
    (centerMarked : marked center = some descriptor)
    (centerMember : center ∈
      AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom)
    (centerSphere : center ∈
      PhysicalSimpleSphere input.moleculeGraph.underlyingSimpleGraph oAtom distance)
    (noEarlier : ∀ (y : input.Atom) (r : RS),
      y ∈ AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom →
        marked y = some r →
          ∀ walk : (input.moleculeGraph.underlyingSimpleGraph).Walk oAtom y,
            walk.IsPath → walk.length < distance → False)
    (uniqueAt : ∀ (y : input.Atom) (r : RS),
      y ∈ AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom →
        marked y = some r →
          ∀ walk : (input.moleculeGraph.underlyingSimpleGraph).Walk oAtom y,
            walk.IsPath → walk.length = distance → y = center) :
    (∀ earlier < distance,
      LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
        (LocalizedCumulativeDecoratedTree.observationsAtDepth
          (fun node => node.label) earlier tree) = []) ∧
    (LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
      (LocalizedCumulativeDecoratedTree.observationsAtDepth
        (fun node => node.label) distance tree) = [descriptor]) := by
  constructor
  · intro earlier earlierLt
    rw [chiralDescriptorsOfObservations_eq_nil_iff]
    intro label present descriptorAt same
    obtain ⟨p, pLength, pLabel⟩ := exists_position_of_mem_observationsAtDepth present
    have markedP : marked (positionAtom singleBonded acyclic p) = some descriptorAt :=
      (reader p descriptorAt).mp (by rw [pLabel]; exact same)
    have memberP : positionAtom singleBonded acyclic p ∈
        AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom :=
      positionAtom_mem_cutBranch singleBonded acyclic enough realizes previous previousEq valid
        oObserved pObserved incomingEdge p
    obtain ⟨walk, walkPath, walkLength⟩ :=
      exists_walk_to_position singleBonded acyclic enough realizes previous previousEq valid
        sameRoot oObserved pObserved incomingEdge p
    exact noEarlier (positionAtom singleBonded acyclic p) descriptorAt memberP markedP walk
      walkPath (by rw [walkLength, pLength]; exact earlierLt)
  · let labels := LocalizedCumulativeDecoratedTree.observationsAtDepth
      (fun node => node.label) distance tree
    change LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations labels =
      [descriptor]
    have descriptorMem : descriptor ∈
        LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations labels := by
      obtain ⟨p, pAtom⟩ :=
        exists_position_of_mem_cutBranch singleBonded acyclic enough realizes previous previousEq
          valid sameRoot oObserved pObserved incomingEdge centerMember
      have pMarked : marked (positionAtom singleBonded acyclic p) = some descriptor := by
        rw [pAtom]
        exact centerMarked
      have pChiral : (positionNode p).label = some (.chiral descriptor) :=
        (reader p descriptor).mpr pMarked
      have pLength : p.val.length = distance := by
        obtain ⟨walkP, walkPPath, walkPLength⟩ :=
          exists_walk_to_position singleBonded acyclic enough realizes previous previousEq valid
            sameRoot oObserved pObserved incomingEdge p
        obtain ⟨centerWalk, centerPath, centerLength⟩ := centerSphere
        have pathsEq :
            (⟨walkP.copy rfl pAtom, walk_isPath_copy walkPPath rfl pAtom⟩ :
              (input.moleculeGraph.underlyingSimpleGraph).Path oAtom center) =
              ⟨centerWalk, centerPath⟩ :=
          acyclic.path_unique _ _
        have lengthEq : (walkP.copy rfl pAtom).length = centerWalk.length :=
          congrArg (fun path => path.val.length) pathsEq
        rw [← walkPLength, ← SimpleGraph.Walk.length_copy walkP rfl pAtom, lengthEq, centerLength]
      have memLength : descriptor ∈
          LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
            (LocalizedCumulativeDecoratedTree.observationsAtDepth
              (fun node => node.label) p.val.length tree) :=
        (mem_chiralDescriptorsOfObservations_iff
          (LocalizedCumulativeDecoratedTree.observationsAtDepth
            (fun node => node.label) p.val.length tree) descriptor).mpr
          ⟨(positionNode p).label, position_label_mem_observationsAtDepth p, pChiral⟩
      rwa [pLength] at memLength
    have addressLength : (nodesWithAddress tree distance).length = labels.length := by
      dsimp only [labels]
      rw [observationsAtDepth_eq_nodesWithAddress_map]
      simp
    have atMostOne : ∀ (i j : Nat) (hi : i < labels.length) (hj : j < labels.length),
        (∃ r : RS, labels[i]'hi = some (.chiral r)) →
          (∃ r : RS, labels[j]'hj = some (.chiral r)) → i = j := by
      intro i j hi hj chiralI chiralJ
      have boundI : i < (nodesWithAddress tree distance).length := by
        rw [addressLength]
        exact hi
      have boundJ : j < (nodesWithAddress tree distance).length := by
        rw [addressLength]
        exact hj
      have memberI : (nodesWithAddress tree distance)[i]'boundI ∈
          nodesWithAddress tree distance := List.getElem_mem boundI
      have memberJ : (nodesWithAddress tree distance)[j]'boundJ ∈
          nodesWithAddress tree distance := List.getElem_mem boundJ
      let pI : Position tree := positionOfNodesWithAddress memberI
      let pJ : Position tree := positionOfNodesWithAddress memberJ
      have pIVal : pI.val = ((nodesWithAddress tree distance)[i]'boundI).1 :=
        positionOfNodesWithAddress_val memberI
      have pJVal : pJ.val = ((nodesWithAddress tree distance)[j]'boundJ).1 :=
        positionOfNodesWithAddress_val memberJ
      have pILength : pI.val.length = distance :=
        positionOfNodesWithAddress_length memberI
      have pJLength : pJ.val.length = distance :=
        positionOfNodesWithAddress_length memberJ
      have pINode : positionNode pI = ((nodesWithAddress tree distance)[i]'boundI).2 :=
        positionOfNodesWithAddress_node memberI
      have pJNode : positionNode pJ = ((nodesWithAddress tree distance)[j]'boundJ).2 :=
        positionOfNodesWithAddress_node memberJ
      have labelI : labels[i]'hi =
          ((nodesWithAddress tree distance)[i]'boundI).2.label := by
        have left : labels[i]? = some (labels[i]'hi) := List.getElem?_eq_getElem hi
        have right : (nodesWithAddress tree distance)[i]? =
            some ((nodesWithAddress tree distance)[i]'boundI) :=
          List.getElem?_eq_getElem boundI
        have mapped : labels[i]? =
            ((nodesWithAddress tree distance)[i]?).map (fun pair => pair.2.label) := by
          dsimp only [labels]
          rw [observationsAtDepth_eq_nodesWithAddress_map]
          rw [List.getElem?_map]
        rw [left, right] at mapped
        exact Option.some.inj (by simpa using mapped)
      have labelJ : labels[j]'hj =
          ((nodesWithAddress tree distance)[j]'boundJ).2.label := by
        have left : labels[j]? = some (labels[j]'hj) := List.getElem?_eq_getElem hj
        have right : (nodesWithAddress tree distance)[j]? =
            some ((nodesWithAddress tree distance)[j]'boundJ) :=
          List.getElem?_eq_getElem boundJ
        have mapped : labels[j]? =
            ((nodesWithAddress tree distance)[j]?).map (fun pair => pair.2.label) := by
          dsimp only [labels]
          rw [observationsAtDepth_eq_nodesWithAddress_map]
          rw [List.getElem?_map]
        rw [left, right] at mapped
        exact Option.some.inj (by simpa using mapped)
      obtain ⟨ri, chiralIIndex⟩ := chiralI
      obtain ⟨rj, chiralJIndex⟩ := chiralJ
      have markedI : marked (positionAtom singleBonded acyclic pI) = some ri :=
        (reader pI ri).mp (by rw [pINode]; exact labelI.symm.trans chiralIIndex)
      have markedJ : marked (positionAtom singleBonded acyclic pJ) = some rj :=
        (reader pJ rj).mp (by rw [pJNode]; exact labelJ.symm.trans chiralJIndex)
      have cutI : positionAtom singleBonded acyclic pI ∈
          AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom :=
        positionAtom_mem_cutBranch singleBonded acyclic enough realizes previous previousEq valid
          oObserved pObserved incomingEdge pI
      have cutJ : positionAtom singleBonded acyclic pJ ∈
          AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom :=
        positionAtom_mem_cutBranch singleBonded acyclic enough realizes previous previousEq valid
          oObserved pObserved incomingEdge pJ
      obtain ⟨walkI, walkIPath, walkILength⟩ :=
        exists_walk_to_position singleBonded acyclic enough realizes previous previousEq valid
          sameRoot oObserved pObserved incomingEdge pI
      obtain ⟨walkJ, walkJPath, walkJLength⟩ :=
        exists_walk_to_position singleBonded acyclic enough realizes previous previousEq valid
          sameRoot oObserved pObserved incomingEdge pJ
      have atomI : positionAtom singleBonded acyclic pI = center :=
        uniqueAt (positionAtom singleBonded acyclic pI) ri cutI markedI walkI walkIPath
          (by rw [walkILength, pILength])
      have atomJ : positionAtom singleBonded acyclic pJ = center :=
        uniqueAt (positionAtom singleBonded acyclic pJ) rj cutJ markedJ walkJ walkJPath
          (by rw [walkJLength, pJLength])
      have positionsEq : pI = pJ :=
        positionAtom_injective singleBonded acyclic enough realizes previous previousEq sameRoot
          oObserved pObserved pI pJ (atomI.trans atomJ.symm)
      have addressesEq : ((nodesWithAddress tree distance)[i]'boundI).1 =
          ((nodesWithAddress tree distance)[j]'boundJ).1 := by
        rw [← pIVal, ← pJVal, positionsEq]
      have mapEq : ((nodesWithAddress tree distance).map Prod.fst)[i]'
            (by simpa using boundI) =
          ((nodesWithAddress tree distance).map Prod.fst)[j]'
            (by simpa using boundJ) := by
        simp only [List.getElem_map]
        exact addressesEq
      exact (nodesWithAddress_paths_nodup tree distance).getElem_inj_iff.mp mapEq
    have lengthLe : (LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
        labels).length ≤ 1 :=
      chiralDescriptorsOfObservations_length_le_one labels atMostOne
    have lengthPos : 0 < (LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
        labels).length := List.length_pos_of_mem descriptorMem
    have lengthOne : (LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
        labels).length = 1 := by omega
    obtain ⟨only, onlyEq⟩ := List.length_eq_one_iff.mp lengthOne
    have onlyDescriptor : only = descriptor := by
      have present : descriptor ∈ [only] := onlyEq ▸ descriptorMem
      have equal : descriptor = only := by simpa using present
      exact equal.symm
    rw [onlyEq, onlyDescriptor]

end PhysicalDepthSphere

/-! ## Actual Rule-4b singleton reference from a physical unique nearest centre

These endpoints compose the depth-observation transfer above with the actual selector wrappers.
The reader correspondence remains an explicit semantic premise; the actual reference selection is
the conclusion, not an assumption. -/

/-- **Actual Rule-4a singleton reference from a physical unique nearest chiral centre.** -/
theorem buildLocalizedRerootCumulativeRule45Key?_referenceSelection_singleton_of_physicalUniqueNearest
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (labelTableEq : tree.labelTable = key.labels)
    (computed : input.buildLocalizedRerootCumulativeRule45Key?
      stage target view fuel cursor = some key)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    {oAtom pAtom : input.Atom}
    (oObserved : tree.source.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (marked : input.Atom → Option RS)
    (reader : ∀ (p : Position tree) (descriptor : RS),
      (positionNode p).label = some (.chiral descriptor) ↔
        marked (positionAtom singleBonded acyclic p) = some descriptor)
    {center : input.Atom} {descriptor : RS} {distance : Nat}
    (centerMarked : marked center = some descriptor)
    (centerMember : center ∈
      AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom)
    (centerSphere : center ∈
      PhysicalSimpleSphere input.moleculeGraph.underlyingSimpleGraph oAtom distance)
    (noEarlier : ∀ (y : input.Atom) (r : RS),
      y ∈ AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom →
        marked y = some r →
          ∀ walk : (input.moleculeGraph.underlyingSimpleGraph).Walk oAtom y,
            walk.IsPath → walk.length < distance → False)
    (uniqueAt : ∀ (y : input.Atom) (r : RS),
      y ∈ AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom →
        marked y = some r →
          ∀ walk : (input.moleculeGraph.underlyingSimpleGraph).Walk oAtom y,
            walk.IsPath → walk.length = distance → y = center) :
    localizedRule4bReferencesFromRankedLabels key.rankedLabels = [descriptor] := by
  obtain ⟨before, atDepth⟩ :=
    tree_observations_of_physicalUniqueNearest singleBonded acyclic enough realizes previous
      previousEq valid sameRoot oObserved pObserved incomingEdge marked reader centerMarked
      centerMember centerSphere noEarlier uniqueAt
  exact buildLocalizedRerootCumulativeRule45Key?_referenceSelection_singleton_of_tree_observations
    input stage target view fuel cursor key tree labelTableEq distance descriptor computed
    before atDepth

/-- **Actual Rule-4bc singleton reading from a physical unique nearest chiral centre.** -/
theorem buildLocalizedRerootCompoundRule4bcKey?_readings_singleton_of_physicalUniqueNearest
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule4bcKey)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (labelTableEq : tree.labelTable = key.rule4aKey.labels)
    (computed : input.buildLocalizedRerootCompoundRule4bcKey?
      target view fuel cursor = some key)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    {oAtom pAtom : input.Atom}
    (oObserved : tree.source.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (marked : input.Atom → Option RS)
    (reader : ∀ (p : Position tree) (descriptor : RS),
      (positionNode p).label = some (.chiral descriptor) ↔
        marked (positionAtom singleBonded acyclic p) = some descriptor)
    {center : input.Atom} {descriptor : RS} {distance : Nat}
    (centerMarked : marked center = some descriptor)
    (centerMember : center ∈
      AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom)
    (centerSphere : center ∈
      PhysicalSimpleSphere input.moleculeGraph.underlyingSimpleGraph oAtom distance)
    (noEarlier : ∀ (y : input.Atom) (r : RS),
      y ∈ AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom →
        marked y = some r →
          ∀ walk : (input.moleculeGraph.underlyingSimpleGraph).Walk oAtom y,
            walk.IsPath → walk.length < distance → False)
    (uniqueAt : ∀ (y : input.Atom) (r : RS),
      y ∈ AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom →
        marked y = some r →
          ∀ walk : (input.moleculeGraph.underlyingSimpleGraph).Walk oAtom y,
            walk.IsPath → walk.length = distance → y = center) :
    ∃ reading : input.LocalizedRerootRule4bcReading,
      key.readings = [reading] ∧ reading.reference? = some descriptor := by
  obtain ⟨before, atDepth⟩ :=
    tree_observations_of_physicalUniqueNearest singleBonded acyclic enough realizes previous
      previousEq valid sameRoot oObserved pObserved incomingEdge marked reader centerMarked
      centerMember centerSphere noEarlier uniqueAt
  exact buildLocalizedRerootCompoundRule4bcKey?_readings_singleton_of_tree_observations
    input target view fuel cursor key tree labelTableEq distance descriptor computed before atDepth

/-! ### Endpoints with the actual builder tree recovered, not supplied

The preceding endpoints take the decorated tree and its label-table equality as premises.  The
actual-builder existence theorem of this module recovers both from the build computation itself:
the tree realizes the dependency read, its source is the supplied cursor, and its label table is
the compiled key's label list.  What remains as an explicit premise is exactly the semantic reader
correspondence and the physical unique-nearest data; no desired per-depth label premise survives. -/

/-- **Actual Rule-4a singleton reference from the actual builder and a physical unique nearest
chiral centre.**  The decorated tree, its realization and `tree.labelTable = key.labels` are all
obtained from the successful build rather than assumed. -/
theorem buildLocalizedRerootCumulativeRule45Key?_referenceSelection_singleton_of_actualPhysicalUniqueNearest
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (computed : input.buildLocalizedRerootCumulativeRule45Key?
      stage target view fuel cursor = some key)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : cursor.previous? = some previous)
    (valid : input.LocalizedRerootCursorValid cursor)
    (sameRoot : cursor.occurrence.1.root = previous.1.root)
    {oAtom pAtom : input.Atom}
    (oObserved : cursor.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (marked : input.Atom → Option RS)
    (reader : ∀ (tree : LocalizedCumulativeDecoratedTree input carrierFuel),
      LocalizedCumulativeTreeRealizes input
        (fun cursor => input.localizedDependencyLabel target view cursor) tree →
      ∀ (p : Position tree) (descriptor : RS),
        (positionNode p).label = some (.chiral descriptor) ↔
          marked (positionAtom singleBonded acyclic p) = some descriptor)
    {center : input.Atom} {descriptor : RS} {distance : Nat}
    (centerMarked : marked center = some descriptor)
    (centerMember : center ∈
      AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom)
    (centerSphere : center ∈
      PhysicalSimpleSphere input.moleculeGraph.underlyingSimpleGraph oAtom distance)
    (noEarlier : ∀ (y : input.Atom) (r : RS),
      y ∈ AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom →
        marked y = some r →
          ∀ walk : (input.moleculeGraph.underlyingSimpleGraph).Walk oAtom y,
            walk.IsPath → walk.length < distance → False)
    (uniqueAt : ∀ (y : input.Atom) (r : RS),
      y ∈ AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom →
        marked y = some r →
          ∀ walk : (input.moleculeGraph.underlyingSimpleGraph).Walk oAtom y,
            walk.IsPath → walk.length = distance → y = center) :
    localizedRule4bReferencesFromRankedLabels key.rankedLabels = [descriptor] := by
  obtain ⟨tree, treeSource, _tableMatch, labelTableEq, realizes⟩ :=
    exists_decoratedTree_of_buildLocalizedRerootCumulativeRule45Key? input stage target view
      fuel cursor key computed
  rw [← treeSource] at previousEq valid sameRoot oObserved
  exact
    buildLocalizedRerootCumulativeRule45Key?_referenceSelection_singleton_of_physicalUniqueNearest
      input stage target view fuel cursor key tree labelTableEq computed singleBonded acyclic
      enough realizes previous previousEq valid sameRoot oObserved pObserved incomingEdge marked
      (reader tree realizes) centerMarked centerMember centerSphere noEarlier uniqueAt

/-- **Actual Rule-4bc singleton reading from the actual builder and a physical unique nearest
chiral centre.**  The Rule-4a tree is recovered from the compound build through the retained-key
computation, so neither the tree nor its label-table equality is assumed. -/
theorem buildLocalizedRerootCompoundRule4bcKey?_readings_singleton_of_actualPhysicalUniqueNearest
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule4bcKey)
    (computed : input.buildLocalizedRerootCompoundRule4bcKey?
      target view fuel cursor = some key)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : cursor.previous? = some previous)
    (valid : input.LocalizedRerootCursorValid cursor)
    (sameRoot : cursor.occurrence.1.root = previous.1.root)
    {oAtom pAtom : input.Atom}
    (oObserved : cursor.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (marked : input.Atom → Option RS)
    (reader : ∀ (tree : LocalizedCumulativeDecoratedTree input carrierFuel),
      LocalizedCumulativeTreeRealizes input
        (fun cursor => input.localizedDependencyLabel target view cursor) tree →
      ∀ (p : Position tree) (descriptor : RS),
        (positionNode p).label = some (.chiral descriptor) ↔
          marked (positionAtom singleBonded acyclic p) = some descriptor)
    {center : input.Atom} {descriptor : RS} {distance : Nat}
    (centerMarked : marked center = some descriptor)
    (centerMember : center ∈
      AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom)
    (centerSphere : center ∈
      PhysicalSimpleSphere input.moleculeGraph.underlyingSimpleGraph oAtom distance)
    (noEarlier : ∀ (y : input.Atom) (r : RS),
      y ∈ AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom →
        marked y = some r →
          ∀ walk : (input.moleculeGraph.underlyingSimpleGraph).Walk oAtom y,
            walk.IsPath → walk.length < distance → False)
    (uniqueAt : ∀ (y : input.Atom) (r : RS),
      y ∈ AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom →
        marked y = some r →
          ∀ walk : (input.moleculeGraph.underlyingSimpleGraph).Walk oAtom y,
            walk.IsPath → walk.length = distance → y = center) :
    ∃ reading : input.LocalizedRerootRule4bcReading,
      key.readings = [reading] ∧ reading.reference? = some descriptor := by
  have computedRule4a :=
    input.buildLocalizedRerootCompoundRule4bcKey?_rule4aKey target view fuel cursor key computed
  obtain ⟨tree, treeSource, _tableMatch, labelTableEq, realizes⟩ :=
    exists_decoratedTree_of_buildLocalizedRerootCumulativeRule45Key? input .rule4a target view
      fuel cursor key.rule4aKey computedRule4a
  rw [← treeSource] at previousEq valid sameRoot oObserved
  exact
    buildLocalizedRerootCompoundRule4bcKey?_readings_singleton_of_physicalUniqueNearest
      input target view fuel cursor key tree labelTableEq computed singleBonded acyclic enough
      realizes previous previousEq valid sameRoot oObserved pObserved incomingEdge marked
      (reader tree realizes) centerMarked centerMember centerSphere noEarlier uniqueAt

/-! ### Source-specific actual state join

The two endpoints below replace the global reader correspondence by a source-specific
classification of the actual state.  The tree is the actual tree recovered from the successful
build at the fixed cursor, and the per-position reader is derived from the actual restricted
dependency reader over the state projection rather than supplied.  The remaining semantic premise
is stated only for trees with this fixed source; it does not quantify over arbitrary roots. -/

/-- **Actual Rule-4a singleton reference from a source-specific actual state classification.** -/
theorem buildLocalizedRerootCumulativeRule45Key?_referenceSelection_singleton_of_actualPhysicalUniqueNearest_state
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (computed : input.buildLocalizedRerootCumulativeRule45Key?
      stage target (input.localizedDependencyView state target) fuel cursor = some key)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : cursor.previous? = some previous)
    (previousShorter : previous.1.address.length < cursor.occurrence.1.address.length)
    (valid : input.LocalizedRerootCursorValid cursor)
    (targetEq : previous = target)
    {oAtom pAtom : input.Atom}
    (oObserved : cursor.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (marked : input.Atom → Option RS)
    (stateClass : ∀ (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
      (_realizes : LocalizedCumulativeTreeRealizes input
        (fun cursor => input.localizedDependencyLabel target
          (input.localizedDependencyView state target) cursor) tree)
      (_sourceEq : tree.source = cursor) (p : Position tree) (descriptor : RS),
        state (positionSource p).occurrence = some (.chiral descriptor) ↔
          marked (positionAtom singleBonded acyclic p) = some descriptor)
    {center : input.Atom} {descriptor : RS} {distance : Nat}
    (centerMarked : marked center = some descriptor)
    (centerMember : center ∈
      AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom)
    (centerSphere : center ∈
      PhysicalSimpleSphere input.moleculeGraph.underlyingSimpleGraph oAtom distance)
    (noEarlier : ∀ (y : input.Atom) (r : RS),
      y ∈ AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom →
        marked y = some r →
          ∀ walk : (input.moleculeGraph.underlyingSimpleGraph).Walk oAtom y,
            walk.IsPath → walk.length < distance → False)
    (uniqueAt : ∀ (y : input.Atom) (r : RS),
      y ∈ AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom →
        marked y = some r →
          ∀ walk : (input.moleculeGraph.underlyingSimpleGraph).Walk oAtom y,
            walk.IsPath → walk.length = distance → y = center) :
    localizedRule4bReferencesFromRankedLabels key.rankedLabels = [descriptor] := by
  obtain ⟨tree, treeSource, _tableMatch, labelTableEq, realizes⟩ :=
    exists_decoratedTree_of_buildLocalizedRerootCumulativeRule45Key? input stage target
      (input.localizedDependencyView state target) fuel cursor key computed
  rw [← treeSource] at previousEq valid oObserved previousShorter
  have sameRoot : tree.source.occurrence.1.root = previous.1.root :=
    cursor_root_eq_of_valid valid previous previousEq
  have reader : ∀ (p : Position tree) (descriptor : RS),
      (positionNode p).label = some (.chiral descriptor) ↔
        marked (positionAtom singleBonded acyclic p) = some descriptor := by
    intro p descriptor
    rw [positionNode_label_eq_state_of_outward target state realizes valid previous previousEq
      previousShorter targetEq p]
    exact stateClass tree realizes treeSource p descriptor
  exact
    buildLocalizedRerootCumulativeRule45Key?_referenceSelection_singleton_of_physicalUniqueNearest
      input stage target (input.localizedDependencyView state target) fuel cursor key tree
      labelTableEq computed singleBonded acyclic enough realizes previous previousEq valid
      sameRoot oObserved pObserved incomingEdge marked reader centerMarked centerMember
      centerSphere noEarlier uniqueAt

/-- **Actual Rule-4bc singleton reading from a source-specific actual state classification.** -/
theorem buildLocalizedRerootCompoundRule4bcKey?_readings_singleton_of_actualPhysicalUniqueNearest_state
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule4bcKey)
    (computed : input.buildLocalizedRerootCompoundRule4bcKey?
      target (input.localizedDependencyView state target) fuel cursor = some key)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : cursor.previous? = some previous)
    (previousShorter : previous.1.address.length < cursor.occurrence.1.address.length)
    (valid : input.LocalizedRerootCursorValid cursor)
    (targetEq : previous = target)
    {oAtom pAtom : input.Atom}
    (oObserved : cursor.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (marked : input.Atom → Option RS)
    (stateClass : ∀ (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
      (_realizes : LocalizedCumulativeTreeRealizes input
        (fun cursor => input.localizedDependencyLabel target
          (input.localizedDependencyView state target) cursor) tree)
      (_sourceEq : tree.source = cursor) (p : Position tree) (descriptor : RS),
        state (positionSource p).occurrence = some (.chiral descriptor) ↔
          marked (positionAtom singleBonded acyclic p) = some descriptor)
    {center : input.Atom} {descriptor : RS} {distance : Nat}
    (centerMarked : marked center = some descriptor)
    (centerMember : center ∈
      AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom)
    (centerSphere : center ∈
      PhysicalSimpleSphere input.moleculeGraph.underlyingSimpleGraph oAtom distance)
    (noEarlier : ∀ (y : input.Atom) (r : RS),
      y ∈ AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom →
        marked y = some r →
          ∀ walk : (input.moleculeGraph.underlyingSimpleGraph).Walk oAtom y,
            walk.IsPath → walk.length < distance → False)
    (uniqueAt : ∀ (y : input.Atom) (r : RS),
      y ∈ AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom →
        marked y = some r →
          ∀ walk : (input.moleculeGraph.underlyingSimpleGraph).Walk oAtom y,
            walk.IsPath → walk.length = distance → y = center) :
    ∃ reading : input.LocalizedRerootRule4bcReading,
      key.readings = [reading] ∧ reading.reference? = some descriptor := by
  have computedRule4a := input.buildLocalizedRerootCompoundRule4bcKey?_rule4aKey target
    (input.localizedDependencyView state target) fuel cursor key computed
  obtain ⟨tree, treeSource, _tableMatch, labelTableEq, realizes⟩ :=
    exists_decoratedTree_of_buildLocalizedRerootCumulativeRule45Key? input .rule4a target
      (input.localizedDependencyView state target) fuel cursor key.rule4aKey computedRule4a
  rw [← treeSource] at previousEq valid oObserved previousShorter
  have sameRoot : tree.source.occurrence.1.root = previous.1.root :=
    cursor_root_eq_of_valid valid previous previousEq
  have reader : ∀ (p : Position tree) (descriptor : RS),
      (positionNode p).label = some (.chiral descriptor) ↔
        marked (positionAtom singleBonded acyclic p) = some descriptor := by
    intro p descriptor
    rw [positionNode_label_eq_state_of_outward target state realizes valid previous previousEq
      previousShorter targetEq p]
    exact stateClass tree realizes treeSource p descriptor
  exact
    buildLocalizedRerootCompoundRule4bcKey?_readings_singleton_of_physicalUniqueNearest
      input target (input.localizedDependencyView state target) fuel cursor key tree labelTableEq
      computed singleBonded acyclic enough realizes previous previousEq valid sameRoot oObserved
      pObserved incomingEdge marked reader centerMarked centerMember centerSphere noEarlier
      uniqueAt








/-- **No physical mark means no chiral observation at any depth.**  Every tree node lies at a
position whose atom is in the physical cut branch, so the marking-`none` hypothesis reaches every
observation through the reader correspondence. -/
theorem tree_observations_chiralFree_of_noPhysicalMarked
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (_sameRoot : tree.source.occurrence.1.root = previous.1.root)
    {oAtom pAtom : input.Atom}
    (oObserved : tree.source.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (marked : input.Atom → Option RS)
    (reader : ∀ (p : Position tree) (descriptor : RS),
      (positionNode p).label = some (.chiral descriptor) ↔
        marked (positionAtom singleBonded acyclic p) = some descriptor)
    (noPhysicalMarked : ∀ (y : input.Atom),
      y ∈ AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom →
        marked y = none) :
    ∀ depth,
      LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
        (LocalizedCumulativeDecoratedTree.observationsAtDepth
          (fun node => node.label) depth tree) = [] := by
  intro depth
  rw [chiralDescriptorsOfObservations_eq_nil_iff]
  intro label present descriptor chiral
  obtain ⟨p, _pDepth, pLabel⟩ := exists_position_of_mem_observationsAtDepth present
  have nodeChiral : (positionNode p).label = some (.chiral descriptor) :=
    pLabel.trans chiral
  have markedSome := (reader p descriptor).mp nodeChiral
  have markedNone := noPhysicalMarked (positionAtom singleBonded acyclic p)
    (positionAtom_mem_cutBranch singleBonded acyclic enough realizes previous previousEq valid
      oObserved pObserved incomingEdge p)
  rw [markedNone] at markedSome
  cases markedSome

/-- **An unmarked physical branch has a chiral-free actual label table.**  Reading every entry of
the compiled key's layers back through the tree's exact label table and the reader correspondence
shows that no entry is an uppercase chiral label. -/
theorem labels_chiralFree_of_noPhysicalMarked
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    {oAtom pAtom : input.Atom}
    (oObserved : tree.source.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (marked : input.Atom → Option RS)
    (reader : ∀ (p : Position tree) (descriptor : RS),
      (positionNode p).label = some (.chiral descriptor) ↔
        marked (positionAtom singleBonded acyclic p) = some descriptor)
    (noPhysicalMarked : ∀ (y : input.Atom),
      y ∈ AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom →
        marked y = none)
    {key : input.LocalizedRerootCumulativeRule45Key}
    (labelTableEq : tree.labelTable = key.labels) :
    LocalizedLabelLayersChiralFree key.labels := by
  intro layer layerMem entry entryMem descriptor chiral
  obtain ⟨depth, hdepth⟩ := List.mem_iff_getElem?.mp layerMem
  have layerEq : key.labels.getD depth [] = layer := by
    rw [List.getD_eq_getElem?_getD, hdepth]
    rfl
  have entryIn : entry ∈ tree.labelTable.getD depth [] := by
    rw [labelTableEq, layerEq]
    exact entryMem
  have mapEq := LocalizedCumulativeDecoratedTree.labelTable_getD_map_snd tree depth
  have observed : entry.2 ∈
      LocalizedCumulativeDecoratedTree.observationsAtDepth
        (fun node => node.label) depth tree := by
    rw [← mapEq]
    exact List.mem_map.mpr ⟨entry, entryIn, rfl⟩
  have free :=
    tree_observations_chiralFree_of_noPhysicalMarked input singleBonded acyclic enough realizes
      previous previousEq valid sameRoot oObserved pObserved incomingEdge marked reader
      noPhysicalMarked depth
  rw [chiralDescriptorsOfObservations_eq_nil_iff] at free
  exact free entry.2 observed descriptor chiral

/-- **Actual Rule-4a empty selector from an unmarked physical branch.**  The actual builder tree
and its exact label table are recovered from the computation; the physical branch being unmarked
forces the executable selection to be empty. -/
theorem buildLocalizedRerootCumulativeRule45Key?_referenceSelection_eq_nil_of_actualNoPhysicalMarked
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (computed : input.buildLocalizedRerootCumulativeRule45Key?
      stage target view fuel cursor = some key)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : cursor.previous? = some previous)
    (valid : input.LocalizedRerootCursorValid cursor)
    (sameRoot : cursor.occurrence.1.root = previous.1.root)
    {oAtom pAtom : input.Atom}
    (oObserved : cursor.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (marked : input.Atom → Option RS)
    (reader : ∀ (tree : LocalizedCumulativeDecoratedTree input carrierFuel),
      LocalizedCumulativeTreeRealizes input
        (fun cursor => input.localizedDependencyLabel target view cursor) tree →
      ∀ (p : Position tree) (descriptor : RS),
        (positionNode p).label = some (.chiral descriptor) ↔
          marked (positionAtom singleBonded acyclic p) = some descriptor)
    (noPhysicalMarked : ∀ (y : input.Atom),
      y ∈ AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom →
        marked y = none) :
    localizedRule4bReferencesFromRankedLabels key.rankedLabels = [] := by
  obtain ⟨tree, treeSource, _tableMatch, labelTableEq, realizes⟩ :=
    exists_decoratedTree_of_buildLocalizedRerootCumulativeRule45Key? input stage target view
      fuel cursor key computed
  rw [← treeSource] at previousEq valid sameRoot oObserved
  have free :=
    labels_chiralFree_of_noPhysicalMarked input singleBonded acyclic enough realizes previous
      previousEq valid sameRoot oObserved pObserved incomingEdge marked (reader tree realizes)
      noPhysicalMarked labelTableEq
  exact
    (input.buildLocalizedRerootCumulativeRule45Key?_referenceSelection_eq_nil_iff_labels_chiralFree
      stage target view fuel cursor key computed).mpr free

/-- **Actual Rule-4bc empty reading from an unmarked physical branch.**  The compound build's
retained Rule-4a key selects nothing, so the actual reading list is the single no-reference
reading produced by the executable builder. -/
theorem buildLocalizedRerootCompoundRule4bcKey?_readings_singleton_of_actualNoPhysicalMarked
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule4bcKey)
    (computed : input.buildLocalizedRerootCompoundRule4bcKey?
      target view fuel cursor = some key)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : cursor.previous? = some previous)
    (valid : input.LocalizedRerootCursorValid cursor)
    (sameRoot : cursor.occurrence.1.root = previous.1.root)
    {oAtom pAtom : input.Atom}
    (oObserved : cursor.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (marked : input.Atom → Option RS)
    (reader : ∀ (tree : LocalizedCumulativeDecoratedTree input carrierFuel),
      LocalizedCumulativeTreeRealizes input
        (fun cursor => input.localizedDependencyLabel target view cursor) tree →
      ∀ (p : Position tree) (descriptor : RS),
        (positionNode p).label = some (.chiral descriptor) ↔
          marked (positionAtom singleBonded acyclic p) = some descriptor)
    (noPhysicalMarked : ∀ (y : input.Atom),
      y ∈ AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom →
        marked y = none) :
    ∃ reading : input.LocalizedRerootRule4bcReading,
      key.readings = [reading] ∧ reading.reference? = none ∧
        input.buildLocalizedRerootRule4bcReading?
          target view fuel cursor none = some reading := by
  have computedRule4a :=
    input.buildLocalizedRerootCompoundRule4bcKey?_rule4aKey target view fuel cursor key computed
  obtain ⟨tree, treeSource, _tableMatch, labelTableEq, realizes⟩ :=
    exists_decoratedTree_of_buildLocalizedRerootCumulativeRule45Key? input .rule4a target view
      fuel cursor key.rule4aKey computedRule4a
  rw [← treeSource] at previousEq valid sameRoot oObserved
  have free :=
    labels_chiralFree_of_noPhysicalMarked input singleBonded acyclic enough realizes previous
      previousEq valid sameRoot oObserved pObserved incomingEdge marked (reader tree realizes)
      noPhysicalMarked labelTableEq
  have selectionNil :
      localizedRule4bReferencesFromRankedLabels key.rule4aKey.rankedLabels = [] :=
    (input.buildLocalizedRerootCumulativeRule45Key?_referenceSelection_eq_nil_iff_labels_chiralFree
      .rule4a target view fuel cursor key.rule4aKey computedRule4a).mpr free
  have referencesNil : key.references = [] := by
    rw [input.buildLocalizedRerootCompoundRule4bcKey?_references_eq target view fuel cursor key
      computed]
    exact selectionNil
  exact input.buildLocalizedRerootCompoundRule4bcKey?_readings_singleton_of_references_eq_nil
    target view fuel cursor key computed referencesNil

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.observationsAtDepth
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.table_getD_map_snd
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.labelTable_getD_map_snd
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.positionSource_address_length
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.positionSource_address_length_of_previous
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.subtreeAt?_node_label_eq_read
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.positionNode_label_eq_read
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.labelTable_chiralObservations
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.key_labels_chiralObservations_of_labelTable_eq
assert_kernel_only TetraStereo.OneCenter.exists_decoratedTree_of_buildLocalizedRerootCumulativeRule45Key?
assert_kernel_only TetraStereo.OneCenter.buildLocalizedRerootCumulativeRule45Key?_referenceSelection_singleton_of_tree_observations
assert_kernel_only TetraStereo.OneCenter.buildLocalizedRerootCompoundRule4bcKey?_readings_singleton_of_tree_observations
assert_kernel_only TetraStereo.OneCenter.PhysicalSimpleSphere
assert_kernel_only TetraStereo.OneCenter.tree_observations_of_physicalUniqueNearest
assert_kernel_only TetraStereo.OneCenter.positionNode_label_eq_state_of_outward
assert_kernel_only TetraStereo.OneCenter.buildLocalizedRerootCumulativeRule45Key?_referenceSelection_singleton_of_physicalUniqueNearest
assert_kernel_only TetraStereo.OneCenter.buildLocalizedRerootCompoundRule4bcKey?_readings_singleton_of_physicalUniqueNearest
assert_kernel_only TetraStereo.OneCenter.buildLocalizedRerootCumulativeRule45Key?_referenceSelection_singleton_of_actualPhysicalUniqueNearest
assert_kernel_only TetraStereo.OneCenter.buildLocalizedRerootCompoundRule4bcKey?_readings_singleton_of_actualPhysicalUniqueNearest
assert_kernel_only TetraStereo.OneCenter.buildLocalizedRerootCumulativeRule45Key?_referenceSelection_singleton_of_actualPhysicalUniqueNearest_state
assert_kernel_only TetraStereo.OneCenter.buildLocalizedRerootCompoundRule4bcKey?_readings_singleton_of_actualPhysicalUniqueNearest_state
assert_kernel_only TetraStereo.OneCenter.tree_observations_chiralFree_of_noPhysicalMarked
assert_kernel_only TetraStereo.OneCenter.labels_chiralFree_of_noPhysicalMarked
assert_kernel_only TetraStereo.OneCenter.buildLocalizedRerootCumulativeRule45Key?_referenceSelection_eq_nil_of_actualNoPhysicalMarked
assert_kernel_only TetraStereo.OneCenter.buildLocalizedRerootCompoundRule4bcKey?_readings_singleton_of_actualNoPhysicalMarked
