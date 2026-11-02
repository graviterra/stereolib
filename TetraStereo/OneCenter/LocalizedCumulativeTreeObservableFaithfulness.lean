import TetraStereo.OneCenter.LocalizedCumulativeKeyObservableOrder
import TetraStereo.OneCenter.LocalizedParametricCumulativeLabels
import TetraStereo.OneCenter.LocalizedSparseAddressReconstruction
import TetraStereo.KernelOnly
import Mathlib.Data.List.Perm.Basic

set_option autoImplicit false

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput

/-!
# Source-erased decorated occurrence trees for the actual cumulative reroot builder

`LocalizedParametricCumulativeLabels.buildLocalizedRerootCumulativeRule45KeyWithRead?` compiles the
actual cumulative Rules-4a--5 key over the actual `localizedRerootChildren?` frame, the actual
cumulative sibling sort and the actual constitutional/descriptor/label merges.
`LocalizedCumulativeKeyObservableOrder` proves that the shipped comparator reads exactly the
addressed Rule-1a, Rule-1b and Rule-2 spheres together with the cumulative descriptor, and that
equality of those four tables is exactly comparator equality.  Neither module identifies the key
with the *decorated occurrence tree* that the builder actually traverses.

This module supplies the tree-side vocabulary:

* `LocalizedCumulativeDecoratedTree` records, at one actual occurrence, the actual source cursor,
  the Rule-1a atomic number, the Rule-1b root distance, the Rule-2 isotope mass, the actual
  arbitrary-reader label and the children *in the actual sorted sibling order*.
* `table` compiles such a tree into exactly the addressed sparse shape used by the actual builder:
  one root sphere followed by the slot-prefixed merge of the child tables.
* `observation` and `shape` erase the source cursors, giving the source-erased decorated tree and
  the label-free constitutional shape that later comparisons are stated on.
* `tables` collects the four comparison-visible columns of one tree.
* `labelTable` compiles the tree's exact optional-label column, i.e. the observation-state table
  that is *not* read by the shipped comparator.

The provenance field (`source`) is a proof witness only.  It is never read by any comparator and is
erased in every equality statement.  `none` labels are kept as a distinct fifth case; no claim is
made that an absent observation is chemically uninformative.

## Actual successful builds

`exists_decoratedTree_of_buildWithRead` inducts on the actual fuel of
`buildLocalizedRerootCumulativeRule45KeyWithRead?`.  From the actual child `mapM`, the actual
sibling sort and `List.perm_comp_forall₂`, it produces one sorted decorated occurrence tree whose
root source is the actual cursor, whose four tables equal the actual key's constitutional and
descriptor observations (`LocalizedCumulativeTreeTableMatch`), and whose child sources are an
actual permutation of the actual `localizedRerootChildren?` frame.  The conclusion also carries
`LocalizedCumulativeTreeRealizes`, the recursive actual provenance: every node below the root is
again an actual `localizedRootTree` at its actual cursor with the actual reader value, an actual
`localizedRerootChildren?` frame and an actual sorted child permutation.  No provenance or table
equality is assumed: the sort permutation is the production sort's own permutation and the child
witnesses are the induction hypotheses of the same actual builder.

`exists_decoratedTree_of_buildWithRead_fullMatch` is the strengthened endpoint proved by the same
fuel induction: it additionally carries `LocalizedCumulativeTreeLabelMatch`, the exact equality
`tree.labelTable = key.labels` of the tree's optional-label table with the actual key's exact-label
merge.  The label merge is threaded alongside the four comparator-visible tables at every child,
so the equality is compositional over the actual sorted child keys rather than assumed at the root.
`exists_decoratedTree_of_buildWithRead_labelTable` exposes that additional equality next to the
original conclusions; `exists_decoratedTree_of_buildWithRead` remains the label-free projection,
with unchanged statement.

`compareLocalizedRerootCumulativeRule45Keys_eq_iff_treeTables_eq` is the numerical frontdoor: for
two actual successful builds, the shipped comparator returns `eq` exactly when the four addressed
tables of the two decorated trees agree.  This module does not reconstruct observations from
tables, and does not derive tree height or layer non-emptiness; those are separate modules.
-/

/-! ## Decorations, observations and shapes -/

/-- The comparison-visible decoration of one actual branch occurrence.  The optional label is the
actual value returned by the reader at that occurrence; it is recovered from the cumulative
priority vector only under a label-faithful Rule-5 stage. -/
structure LocalizedCumulativeBranchDecoration where
  /-- Rule-1a atomic-number column at this occurrence. -/
  atomicNumber : Nat
  /-- Rule-1b original-root distance at this occurrence. -/
  rule1bDistance : Nat
  /-- Rule-2 isotope-mass column at this occurrence. -/
  isotopeMass : Nat
  /-- Actual arbitrary-reader optional label at this occurrence. -/
  label : Option LocalizedAuxiliaryLabel
  deriving DecidableEq, Repr

/-- A source-erased rooted decorated occurrence tree.  This is the object two successful actual
builds are compared by; it carries no cursor and no identity. -/
structure LocalizedCumulativeBranchObservation where
  /-- The decoration at the root of this subtree. -/
  decoration : LocalizedCumulativeBranchDecoration
  /-- The children, in the actual sorted sibling order. -/
  children : List LocalizedCumulativeBranchObservation

/-- A source-erased rooted branch shape: the three constitutional columns only. -/
structure LocalizedCumulativeBranchShape where
  /-- Rule-1a atomic-number column at this occurrence. -/
  atomicNumber : Nat
  /-- Rule-1b original-root distance at this occurrence. -/
  rule1bDistance : Nat
  /-- Rule-2 isotope-mass column at this occurrence. -/
  isotopeMass : Nat
  /-- The children, in the actual sorted sibling order. -/
  children : List LocalizedCumulativeBranchShape

/-- The four comparison-visible addressed tables of a decorated tree.  The descriptor column has
already specialised the cumulative priority vector to a stage, so no stage index remains. -/
structure LocalizedCumulativeTreeTables where
  /-- Addressed Rule-1a table. -/
  rule1a : List (List (OfficialSparseEntry Nat))
  /-- Addressed Rule-1b table. -/
  rule1b : List (List (OfficialSparseEntry Nat))
  /-- Addressed Rule-2 table. -/
  rule2 : List (List (OfficialSparseEntry Nat))
  /-- Addressed cumulative Rules-4a--5 descriptor table. -/
  descriptor : List (List (OfficialSparseEntry (List Nat)))

/-- One sorted decorated occurrence, retaining the actual source cursor as a proof witness. -/
structure LocalizedCumulativeDecoratedTree
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat) where
  /-- The actual occurrence cursor reached by the actual builder at this node. -/
  source : input.LocalizedRerootCursor carrierFuel
  /-- Rule-1a atomic number read from the actual node label. -/
  atomicNumber : Nat
  /-- Rule-1b original-root distance read from the actual node. -/
  rule1bDistance : Nat
  /-- Rule-2 isotope mass read from the actual node label. -/
  isotopeMass : Nat
  /-- The actual value returned by the arbitrary reader at this cursor. -/
  label : Option LocalizedAuxiliaryLabel
  /-- Children in the actual descending cumulative sibling order. -/
  children : List (LocalizedCumulativeDecoratedTree input carrierFuel)

/-! ## Erasure -/

namespace LocalizedCumulativeDecoratedTree

mutual
  /-- Erase every source cursor and keep only the comparison-visible decoration. -/
  def observation {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat} :
      LocalizedCumulativeDecoratedTree input carrierFuel →
        LocalizedCumulativeBranchObservation
    | ⟨_source, atomicNumber, rule1bDistance, isotopeMass, label, children⟩ =>
        { decoration :=
            { atomicNumber := atomicNumber
              rule1bDistance := rule1bDistance
              isotopeMass := isotopeMass
              label := label }
          children := observationList children }
    termination_by tree => sizeOf tree
    decreasing_by
      simp_wf

  /-- Erase every source cursor from a list of decorated trees. -/
  def observationList {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat} :
      List (LocalizedCumulativeDecoratedTree input carrierFuel) →
        List LocalizedCumulativeBranchObservation
    | [] => []
    | child :: children => observation child :: observationList children
    termination_by children => sizeOf children
    decreasing_by
      all_goals (simp_wf <;> omega)
end

mutual
  /-- Erase every source cursor and keep only the three constitutional columns. -/
  def shape {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat} :
      LocalizedCumulativeDecoratedTree input carrierFuel →
        LocalizedCumulativeBranchShape
    | ⟨_source, atomicNumber, rule1bDistance, isotopeMass, _label, children⟩ =>
        { atomicNumber := atomicNumber
          rule1bDistance := rule1bDistance
          isotopeMass := isotopeMass
          children := shapeList children }
    termination_by tree => sizeOf tree
    decreasing_by
      simp_wf

  /-- Erase every source cursor from a list of constitutional shapes. -/
  def shapeList {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat} :
      List (LocalizedCumulativeDecoratedTree input carrierFuel) →
        List LocalizedCumulativeBranchShape
    | [] => []
    | child :: children => shape child :: shapeList children
    termination_by children => sizeOf children
    decreasing_by
      all_goals (simp_wf <;> omega)
end

/-! ## The addressed sparse shape of a decorated tree -/

/-- Maximum sphere count among a list of addressed tables. -/
def localizedTreeChildLayerCount {α : Type*}
    (tables : List (List (List (OfficialSparseEntry α)))) : Nat :=
  tables.foldl (fun longest table => max longest table.length) 0

/-- The slot-indexed merge used by every actual cumulative merge: each child table's sphere
`depth` is prefixed by that child's final sorted sibling slot. -/
def mergeLocalizedTreeChildTables {α : Type*}
    (tables : List (List (List (OfficialSparseEntry α)))) :
    List (List (OfficialSparseEntry α)) :=
  SparseAddress.mergePairTable tables.zipIdx id (localizedTreeChildLayerCount tables)

mutual
  /-- Compile one decorated tree into the addressed sparse shape of one observation column. -/
  def table {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat} {α : Type*}
      (observe : LocalizedCumulativeDecoratedTree input carrierFuel → α) :
      LocalizedCumulativeDecoratedTree input carrierFuel →
        List (List (OfficialSparseEntry α))
    | ⟨source, atomicNumber, rule1bDistance, isotopeMass, label, children⟩ =>
        [[([], observe ⟨source, atomicNumber, rule1bDistance, isotopeMass, label, children⟩)]] ++
          mergeLocalizedTreeChildTables (tableList observe children)
    termination_by tree => sizeOf tree
    decreasing_by
      simp_wf

  /-- Compile every child table in sorted sibling order. -/
  def tableList {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat} {α : Type*}
      (observe : LocalizedCumulativeDecoratedTree input carrierFuel → α) :
      List (LocalizedCumulativeDecoratedTree input carrierFuel) →
        List (List (List (OfficialSparseEntry α)))
    | [] => []
    | child :: children => table observe child :: tableList observe children
    termination_by children => sizeOf children
    decreasing_by
      all_goals (simp_wf <;> omega)
end

theorem table_eq {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat} {α : Type*}
    (observe : LocalizedCumulativeDecoratedTree input carrierFuel → α)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    table observe tree =
      [[([], observe tree)]] ++ mergeLocalizedTreeChildTables (tableList observe tree.children) := by
  cases tree with
  | mk source atomicNumber rule1bDistance isotopeMass label children =>
      rw [table]

theorem tableList_eq_map {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat} {α : Type*}
    (observe : LocalizedCumulativeDecoratedTree input carrierFuel → α) :
    ∀ children : List (LocalizedCumulativeDecoratedTree input carrierFuel),
      tableList observe children = children.map (table observe)
  | [] => by
      rw [tableList]
      rfl
  | child :: children => by
      rw [tableList, tableList_eq_map observe children]
      rfl

/-- A tree table is its root sphere followed by the merge of the child tables. -/
theorem table_eq_root_merge {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat} {α : Type*}
    (observe : LocalizedCumulativeDecoratedTree input carrierFuel → α)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    table observe tree =
      [[([], observe tree)]] ++
        mergeLocalizedTreeChildTables (tree.children.map (table observe)) := by
  rw [table_eq, tableList_eq_map]

/-- The four comparison-visible tables of a decorated tree. -/
def tables {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    LocalizedCumulativeTreeTables where
  rule1a := table (fun node => node.atomicNumber) tree
  rule1b := table (fun node => node.rule1bDistance) tree
  rule2 := table (fun node => node.isotopeMass) tree
  descriptor := table (fun node => localizedCumulativeRule45Priority stage node.label) tree

/-- The exact-label table of a decorated tree (observation state, not comparison-visible). -/
def labelTable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))) :=
  table (fun node => node.label) tree

/-- The exact-label table is the generic addressed table of the optional-label projection. -/
theorem labelTable_eq_table {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    tree.labelTable = table (fun node => node.label) tree := rfl

@[simp] theorem tables_rule1a {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    (tree.tables stage).rule1a = table (fun node => node.atomicNumber) tree := rfl

@[simp] theorem tables_rule1b {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    (tree.tables stage).rule1b = table (fun node => node.rule1bDistance) tree := rfl

@[simp] theorem tables_rule2 {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    (tree.tables stage).rule2 = table (fun node => node.isotopeMass) tree := rfl

@[simp] theorem tables_descriptor {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    (tree.tables stage).descriptor =
      table (fun node => localizedCumulativeRule45Priority stage node.label) tree := rfl

end LocalizedCumulativeDecoratedTree

/-! ## Alignment of the tree tables with the actual cumulative merges -/

namespace LocalizedCumulativeDecoratedTree

/-- The actual constitutional merge is the generic slot-pair merge at the row count it selects. -/
theorem mergeChildren_eq_mergePairTable {V γ : Type*}
    (children : List (OfficialRuleMajorKey V))
    (layers : OfficialRuleMajorKey V → List (List (OfficialSparseEntry γ))) :
    OfficialRuleMajorKey.mergeChildren children layers =
      SparseAddress.mergePairTable children.zipIdx layers
        (OfficialRuleMajorKey.childLayerCount children layers) :=
  rfl

/-- Rewriting the values of a slot-pair merge rewrites the layer function. -/
theorem mergePairTable_zipIdx_map_gen {β α γ : Type*}
    (values : List β) (layerOf : β → α)
    (layers : α → List (List (OfficialSparseEntry γ))) (count : Nat) :
    SparseAddress.mergePairTable (values.map layerOf).zipIdx layers count =
      SparseAddress.mergePairTable values.zipIdx
        (fun value => layers (layerOf value)) count := by
  simp [SparseAddress.mergePairTable, SparseAddress.mergePairs,
    List.zipIdx_map, List.flatMap_map, Prod.map]

/-- The generic row count of mapped tables is the actual `childLayerCount`. -/
theorem localizedTreeChildLayerCount_map_eq_childLayerCount {V γ : Type*}
    (values : List (OfficialRuleMajorKey V))
    (layers : OfficialRuleMajorKey V → List (List (OfficialSparseEntry γ))) :
    localizedTreeChildLayerCount (values.map layers) =
      OfficialRuleMajorKey.childLayerCount values layers := by
  simp [localizedTreeChildLayerCount, OfficialRuleMajorKey.childLayerCount,
    List.foldl_map]

/-- A tree table whose per-child column is a constitutional projection merges exactly as the
actual `OfficialRuleMajorKey.mergeChildren` over the actual sorted child keys. -/
theorem mergeLocalizedTreeChildTables_map_comp_eq_mergeChildren {V β γ : Type*}
    (values : List β)
    (layerOf : β → OfficialRuleMajorKey V)
    (column : OfficialRuleMajorKey V → List (List (OfficialSparseEntry γ))) :
    mergeLocalizedTreeChildTables (values.map fun value => column (layerOf value)) =
      OfficialRuleMajorKey.mergeChildren (values.map layerOf) column := by
  have hmap : (values.map fun value => column (layerOf value)) =
      (values.map layerOf).map column := by
    induction values with
    | nil => rfl
    | cons value rest ih => simp [ih]
  rw [mergeChildren_eq_mergePairTable]
  unfold mergeLocalizedTreeChildTables
  rw [hmap]
  rw [mergePairTable_zipIdx_map_gen]
  rw [localizedTreeChildLayerCount_map_eq_childLayerCount]
  have hlayers : (fun value => id (column value)) = column := by
    funext value
    rfl
  rw [hlayers]

/-- The actual cumulative descriptor merge is the generic slot-pair merge at its own row count. -/
theorem mergeLocalizedRerootDescriptorChildren_eq_mergePairTable
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    input.mergeLocalizedRerootDescriptorChildren children =
      SparseAddress.mergePairTable children.zipIdx (fun child => child.descriptor)
        (input.localizedRerootDescriptorChildLayerCount children) :=
  rfl

/-- The generic row count of the descriptor tables is the actual descriptor row count. -/
theorem localizedTreeChildLayerCount_descriptor_eq
    (input : CertifiedLocalizedCIPInput)
    (values : List input.LocalizedRerootCumulativeRule45Key) :
    localizedTreeChildLayerCount (values.map fun child => child.descriptor) =
      input.localizedRerootDescriptorChildLayerCount values := by
  simp [localizedTreeChildLayerCount, localizedRerootDescriptorChildLayerCount,
    List.foldl_map]

/-- A tree descriptor table merges exactly as the actual cumulative descriptor merge over the
actual sorted child keys. -/
theorem mergeLocalizedTreeChildTables_descriptor_eq
    (input : CertifiedLocalizedCIPInput)
    (values : List input.LocalizedRerootCumulativeRule45Key) :
    mergeLocalizedTreeChildTables (values.map fun child => child.descriptor) =
      input.mergeLocalizedRerootDescriptorChildren values := by
  rw [mergeLocalizedRerootDescriptorChildren_eq_mergePairTable]
  unfold mergeLocalizedTreeChildTables
  rw [mergePairTable_zipIdx_map_gen]
  rw [localizedTreeChildLayerCount_descriptor_eq]
  have hlayers :
      (fun value : input.LocalizedRerootCumulativeRule45Key => id value.descriptor) =
        (fun child : input.LocalizedRerootCumulativeRule45Key => child.descriptor) := by
    funext value
    rfl
  rw [hlayers]

/-- The actual cumulative exact-label merge is the generic slot-pair merge at its own row count.
This is the exact optional-label analogue of the descriptor alignment; it does not identify the
exact-label table with any comparator-visible column. -/
theorem mergeLocalizedRerootLabelChildren_eq_mergePairTable
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    input.mergeLocalizedRerootLabelChildren children =
      SparseAddress.mergePairTable children.zipIdx (fun child => child.labels)
        (input.localizedRerootLabelChildLayerCount children) :=
  rfl

/-- The generic row count of the exact-label tables is the actual exact-label row count. -/
theorem localizedTreeChildLayerCount_label_eq
    (input : CertifiedLocalizedCIPInput)
    (values : List input.LocalizedRerootCumulativeRule45Key) :
    localizedTreeChildLayerCount (values.map fun child => child.labels) =
      input.localizedRerootLabelChildLayerCount values := by
  simp [localizedTreeChildLayerCount, localizedRerootLabelChildLayerCount,
    List.foldl_map]

/-- A tree exact-label table merges exactly as the actual cumulative exact-label merge over the
actual sorted child keys.  This is the compositional step that lets the label equality descend
through every addressed child sphere. -/
theorem mergeLocalizedTreeChildTables_label_eq
    (input : CertifiedLocalizedCIPInput)
    (values : List input.LocalizedRerootCumulativeRule45Key) :
    mergeLocalizedTreeChildTables (values.map fun child => child.labels) =
      input.mergeLocalizedRerootLabelChildren values := by
  rw [mergeLocalizedRerootLabelChildren_eq_mergePairTable]
  unfold mergeLocalizedTreeChildTables
  rw [mergePairTable_zipIdx_map_gen]
  rw [localizedTreeChildLayerCount_label_eq]
  have hlayers :
      (fun value : input.LocalizedRerootCumulativeRule45Key => id value.labels) =
        (fun child : input.LocalizedRerootCumulativeRule45Key => child.labels) := by
    funext value
    rfl
  rw [hlayers]

end LocalizedCumulativeDecoratedTree

open LocalizedCumulativeDecoratedTree

/-! ## The decorated tree actually produced by a successful actual build -/

/-- The decorated occurrence rooted at an actual cursor, carrying the actual sorted child trees. -/
def localizedRootTree (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (label : Option LocalizedAuxiliaryLabel)
    (children : List (LocalizedCumulativeDecoratedTree input carrierFuel)) :
    LocalizedCumulativeDecoratedTree input carrierFuel where
  source := cursor
  atomicNumber :=
    (ofLex (input.moleculeGraph.officialNodeAtomLabel cursor.occurrence.1.node)).1
  rule1bDistance := cursor.occurrence.1.node.rule1bRootDistance
  isotopeMass :=
    (ofLex (input.moleculeGraph.officialNodeAtomLabel cursor.occurrence.1.node)).2
  label := label
  children := children

/-- The exact four comparison-visible tables of one actual cumulative key. -/
def localizedTreeTablesOfKey (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootCumulativeRule45Key) : LocalizedCumulativeTreeTables where
  rule1a := key.constitutional.rule1a
  rule1b := key.constitutional.rule1b
  rule2 := key.constitutional.rule2
  descriptor := key.descriptor

/-- One actual key matched by one decorated tree: the four tables the comparator reads agree at
every addressed sphere. -/
def LocalizedCumulativeTreeTableMatch
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (key : input.LocalizedRerootCumulativeRule45Key) : Prop :=
  (tree.tables stage).rule1a = key.constitutional.rule1a ∧
    (tree.tables stage).rule1b = key.constitutional.rule1b ∧
      (tree.tables stage).rule2 = key.constitutional.rule2 ∧
        (tree.tables stage).descriptor = key.descriptor

/-- Exact optional-label match: the tree's observation-state label table is the actual key's
exact-label merge at every addressed sphere.  This is strictly stronger than the
comparison-visible table match and is not read by the shipped comparator. -/
def LocalizedCumulativeTreeLabelMatch
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (key : input.LocalizedRerootCumulativeRule45Key) : Prop :=
  tree.labelTable = key.labels

/-- The strengthened local match carried by every actual child witness: both the four
comparator-visible addressed tables and the exact optional-label table agree with the actual key.
`treeTableMatch_localizedRootTree_branch` and `labelTable_localizedRootTree_branch` are the
compositional branch steps; the inductive `LocalizedCumulativeTreeRealizes` remains unchanged. -/
structure LocalizedCumulativeTreeFullMatch
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (key : input.LocalizedRerootCumulativeRule45Key) : Prop where
  /-- The four addressed tables the shipped comparator reads agree at every sphere. -/
  tableMatch : LocalizedCumulativeTreeTableMatch stage tree key
  /-- The exact optional-label table agrees at every addressed sphere. -/
  labelMatch : LocalizedCumulativeTreeLabelMatch tree key

/-- Unfold an exact-label match to the underlying table equality. -/
theorem labelTable_eq_labels_of_labelMatch
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (matched : LocalizedCumulativeTreeLabelMatch tree key) :
    tree.labelTable = key.labels := by
  simpa only [LocalizedCumulativeTreeLabelMatch] using matched

/-- The exact-label table agrees with the actual key at every addressed sphere. -/
theorem labelTable_getD_eq_labels_getD_of_labelMatch
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (matched : LocalizedCumulativeTreeLabelMatch tree key)
    (depth : Nat) :
    tree.labelTable.getD depth [] = key.labels.getD depth [] := by
  rw [labelTable_eq_labels_of_labelMatch tree key matched]

/-- A full match exposes the exact-label table equality. -/
theorem labelTable_eq_labels_of_fullMatch
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {stage : LocalizedCumulativeRule45Stage}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (matched : LocalizedCumulativeTreeFullMatch stage tree key) :
    tree.labelTable = key.labels :=
  labelTable_eq_labels_of_labelMatch tree key matched.labelMatch

/-- Recursive actual provenance of a decorated occurrence tree.  Every node is the actual
`localizedRootTree` built at an actual cursor with the reader's actual value; its children are the
actual sorted child trees whose sources permute the actual `localizedRerootChildren?` frame, and
every sorted child recursively realizes the same provenance. -/
inductive LocalizedCumulativeTreeRealizes
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel) :
    LocalizedCumulativeDecoratedTree input carrierFuel → Prop
  | mk (cursor : input.LocalizedRerootCursor carrierFuel)
      (children : List (input.LocalizedRerootCursor carrierFuel))
      (sortedChildren : List (LocalizedCumulativeDecoratedTree input carrierFuel))
      (childrenComputed : input.localizedRerootChildren? cursor = some children)
      (sourcePerm : (sortedChildren.map (fun tree => tree.source)).Perm children)
      (childrenRealize : ∀ tree ∈ sortedChildren,
        LocalizedCumulativeTreeRealizes input read tree) :
      LocalizedCumulativeTreeRealizes input read
        (localizedRootTree input cursor (read cursor) sortedChildren)

/-- A table match identifies the tree's four tables with the key's four tables. -/
theorem tables_eq_localizedTreeTablesOfKey_of_match
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (matched : LocalizedCumulativeTreeTableMatch stage tree key) :
    tree.tables stage = localizedTreeTablesOfKey input key := by
  obtain ⟨rule1aEq, rule1bEq, rule2Eq, descriptorEq⟩ := matched
  calc tree.tables stage
      = ⟨(tree.tables stage).rule1a, (tree.tables stage).rule1b,
          (tree.tables stage).rule2, (tree.tables stage).descriptor⟩ := rfl
    _ = ⟨key.constitutional.rule1a, key.constitutional.rule1b,
          key.constitutional.rule2, key.descriptor⟩ := by
        rw [rule1aEq, rule1bEq, rule2Eq, descriptorEq]
    _ = localizedTreeTablesOfKey input key := rfl

private theorem map_eq_map_of_forall₂ {α β γ : Type*} {r : α → β → Prop}
    {f : α → γ} {g : β → γ} (left : List α) (right : List β)
    (hrel : List.Forall₂ r left right) (hfg : ∀ a b, r a b → f a = g b) :
    left.map f = right.map g := by
  induction hrel with
  | nil => rfl
  | cons hab htail ih => simp [hfg _ _ hab, ih]

/-- Membership on the right of a `Forall₂` exposes the paired left element and its relation. -/
private theorem exists_of_mem_right_forall₂ {α β : Type*} {r : α → β → Prop}
    {left : List α} {right : List β} (hrel : List.Forall₂ r left right) :
    ∀ b ∈ right, ∃ a ∈ left, r a b := by
  induction hrel with
  | nil =>
      intro b member
      simp at member
  | cons head tail ih =>
      intro b member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨_, by simp, head⟩
      · obtain ⟨a, aMember, related⟩ := ih b member
        exact ⟨a, by simp [aMember], related⟩

/-- Witness lifting through an actual successful child `mapM`: the resulting child sources are
exactly the actual child cursors and every actual child key is matched by its tree. -/
private theorem witnesses_of_mapM_some
    {A B T : Type*} (f : A → Option B) (source : T → A)
    (R : B → T → Prop)
    (witness : ∀ a b, f a = some b → ∃ t, source t = a ∧ R b t) :
    ∀ xs ys, xs.mapM f = some ys →
      ∃ ts, ts.map source = xs ∧ List.Forall₂ R ys ts
  | [], ys, computed => by
      simp at computed
      subst ys
      exact ⟨[], rfl, List.Forall₂.nil⟩
  | x :: xs, ys, computed => by
      rw [List.mapM_cons] at computed
      cases headComputed : f x with
      | none => simp [headComputed] at computed
      | some y =>
          cases tailComputed : xs.mapM f with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst ys
              obtain ⟨tree, treeSource, treeGood⟩ := witness x y headComputed
              obtain ⟨trees, treesSource, treesGood⟩ :=
                witnesses_of_mapM_some f source R witness xs tail tailComputed
              exact ⟨tree :: trees, by simp [treeSource, treesSource],
                List.Forall₂.cons treeGood treesGood⟩

/-- A terminal actual key is matched by the terminal decorated occurrence at the same cursor. -/
private theorem treeTableMatch_localizedRootTree_terminal
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (label : Option LocalizedAuxiliaryLabel) :
    LocalizedCumulativeTreeTableMatch stage
      (localizedRootTree input cursor label [])
      { constitutional :=
          input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node true
        descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
        labels := [[([], label)]]
        rankedLabels := [[([], label)]] } := by
  unfold LocalizedCumulativeTreeTableMatch
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [tables_rule1a, table_eq_root_merge]
    simp [localizedRootTree, mergeLocalizedTreeChildTables,
      localizedTreeChildLayerCount, SparseAddress.mergePairTable,
      SparseAddress.mergePairs, MoleculeGraph.officialRuleMajorRootKey]
  · rw [tables_rule1b, table_eq_root_merge]
    simp [localizedRootTree, mergeLocalizedTreeChildTables,
      localizedTreeChildLayerCount, SparseAddress.mergePairTable,
      SparseAddress.mergePairs, MoleculeGraph.officialRuleMajorRootKey]
  · rw [tables_rule2, table_eq_root_merge]
    simp [localizedRootTree, mergeLocalizedTreeChildTables,
      localizedTreeChildLayerCount, SparseAddress.mergePairTable,
      SparseAddress.mergePairs, MoleculeGraph.officialRuleMajorRootKey]
  · rw [tables_descriptor, table_eq_root_merge]
    simp [localizedRootTree, mergeLocalizedTreeChildTables,
      localizedTreeChildLayerCount, SparseAddress.mergePairTable,
      SparseAddress.mergePairs]

/-- A terminal actual key's exact-label table is the terminal occurrence's root-only label
table.  This is the label-side analogue of `treeTableMatch_localizedRootTree_terminal`. -/
private theorem labelTable_localizedRootTree_terminal
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (label : Option LocalizedAuxiliaryLabel) :
    LocalizedCumulativeTreeLabelMatch
      (localizedRootTree input cursor label [])
      { constitutional :=
          input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node true
        descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
        labels := [[([], label)]]
        rankedLabels := [[([], label)]] } := by
  unfold LocalizedCumulativeTreeLabelMatch
  rw [labelTable_eq_table, table_eq_root_merge]
  simp [localizedRootTree, mergeLocalizedTreeChildTables,
    localizedTreeChildLayerCount, SparseAddress.mergePairTable,
    SparseAddress.mergePairs]

/-- A branching actual key is matched by the decorated occurrence rooted at the same cursor with
the actual sorted child trees; the argument is the actual sort permutation lifted over the actual
per-child witnesses. -/
private theorem treeTableMatch_localizedRootTree_branch
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (label : Option LocalizedAuxiliaryLabel)
    (sortedKeys : List input.LocalizedRerootCumulativeRule45Key)
    (sortedTrees : List (LocalizedCumulativeDecoratedTree input carrierFuel))
    (hrel : List.Forall₂
      (fun key tree => LocalizedCumulativeTreeTableMatch stage tree key)
      sortedKeys sortedTrees) :
    LocalizedCumulativeTreeTableMatch stage
      (localizedRootTree input cursor label sortedTrees)
      { constitutional := OfficialRuleMajorKey.assemble
          (input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node false)
          (sortedKeys.map fun child => child.constitutional)
        descriptor := [[([], localizedCumulativeRule45Priority stage label)]] ++
          input.mergeLocalizedRerootDescriptorChildren sortedKeys
        labels := [[([], label)]] ++ input.mergeLocalizedRerootLabelChildren sortedKeys
        rankedLabels := [[([], label)]] ++
          input.mergeLocalizedRerootRankedLabelChildren sortedKeys } := by
  unfold LocalizedCumulativeTreeTableMatch
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hmap :
        sortedKeys.map (fun key => key.constitutional.rule1a) =
          sortedTrees.map (table (fun node => node.atomicNumber)) :=
      map_eq_map_of_forall₂ sortedKeys sortedTrees hrel
        (fun key tree matched => by
          simpa only [tables_rule1a] using matched.1.symm)
    rw [tables_rule1a, table_eq_root_merge]
    simp only [localizedRootTree]
    rw [← hmap, mergeLocalizedTreeChildTables_map_comp_eq_mergeChildren]
    simp only [OfficialRuleMajorKey.assemble, MoleculeGraph.officialRuleMajorRootKey]
  · have hmap :
        sortedKeys.map (fun key => key.constitutional.rule1b) =
          sortedTrees.map (table (fun node => node.rule1bDistance)) :=
      map_eq_map_of_forall₂ sortedKeys sortedTrees hrel
        (fun key tree matched => by
          simpa only [tables_rule1b] using matched.2.1.symm)
    rw [tables_rule1b, table_eq_root_merge]
    simp only [localizedRootTree]
    rw [← hmap, mergeLocalizedTreeChildTables_map_comp_eq_mergeChildren]
    simp only [OfficialRuleMajorKey.assemble, MoleculeGraph.officialRuleMajorRootKey]
  · have hmap :
        sortedKeys.map (fun key => key.constitutional.rule2) =
          sortedTrees.map (table (fun node => node.isotopeMass)) :=
      map_eq_map_of_forall₂ sortedKeys sortedTrees hrel
        (fun key tree matched => by
          simpa only [tables_rule2] using matched.2.2.1.symm)
    rw [tables_rule2, table_eq_root_merge]
    simp only [localizedRootTree]
    rw [← hmap, mergeLocalizedTreeChildTables_map_comp_eq_mergeChildren]
    simp only [OfficialRuleMajorKey.assemble, MoleculeGraph.officialRuleMajorRootKey]
  · have hmap :
        sortedKeys.map (fun key => key.descriptor) =
          sortedTrees.map
            (table (fun node => localizedCumulativeRule45Priority stage node.label)) :=
      map_eq_map_of_forall₂ sortedKeys sortedTrees hrel
        (fun key tree matched => by
          simpa only [tables_descriptor] using matched.2.2.2.symm)
    rw [tables_descriptor, table_eq_root_merge]
    simp only [localizedRootTree]
    rw [← hmap, mergeLocalizedTreeChildTables_descriptor_eq]

/-- A branching actual key's exact-label table is composed from the actual sorted child label
tables by the actual label merge.  The premise is the per-child label relation produced by the
induction hypotheses; no root-level label equality is assumed. -/
private theorem labelTable_localizedRootTree_branch
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (label : Option LocalizedAuxiliaryLabel)
    (sortedKeys : List input.LocalizedRerootCumulativeRule45Key)
    (sortedTrees : List (LocalizedCumulativeDecoratedTree input carrierFuel))
    (hrel : List.Forall₂
      (fun key tree => LocalizedCumulativeTreeLabelMatch tree key)
      sortedKeys sortedTrees) :
    LocalizedCumulativeTreeLabelMatch
      (localizedRootTree input cursor label sortedTrees)
      { constitutional := OfficialRuleMajorKey.assemble
          (input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node false)
          (sortedKeys.map fun child => child.constitutional)
        descriptor := [[([], localizedCumulativeRule45Priority stage label)]] ++
          input.mergeLocalizedRerootDescriptorChildren sortedKeys
        labels := [[([], label)]] ++ input.mergeLocalizedRerootLabelChildren sortedKeys
        rankedLabels := [[([], label)]] ++
          input.mergeLocalizedRerootRankedLabelChildren sortedKeys } := by
  unfold LocalizedCumulativeTreeLabelMatch
  have hmap :
      sortedKeys.map (fun key => key.labels) =
        sortedTrees.map (table (fun node => node.label)) :=
    map_eq_map_of_forall₂ sortedKeys sortedTrees hrel
      (fun key tree matched => by
        have treeEq : tree.labelTable = key.labels := matched
        exact treeEq.symm)
  rw [labelTable_eq_table, table_eq_root_merge]
  simp only [localizedRootTree]
  rw [← hmap, mergeLocalizedTreeChildTables_label_eq]

/-! ## Forward actual construction -/

/-- Strengthened actual construction: in addition to all conclusions of
`exists_decoratedTree_of_buildWithRead`, the produced tree's exact optional-label table equals the
actual key's exact-label merge at every addressed sphere.  Both the four comparator-visible tables
and the exact-label table are carried through the actual `mapM` witness and the actual sibling
sort at every child, so the label equality is compositional rather than assumed. -/
theorem exists_decoratedTree_of_buildWithRead_fullMatch
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootCumulativeRule45Key),
      CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?
        input stage read fuel cursor = some key →
      ∃ tree : LocalizedCumulativeDecoratedTree input carrierFuel,
        tree.source = cursor ∧
          LocalizedCumulativeTreeFullMatch stage tree key ∧
            LocalizedCumulativeTreeRealizes input read tree ∧
              ∃ children : List (input.LocalizedRerootCursor carrierFuel),
                input.localizedRerootChildren? cursor = some children ∧
                  (tree.children.map (fun node => node.source)).Perm children := by
  intro fuel
  induction fuel with
  | zero =>
      intro cursor key built
      unfold CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead? at built
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at built
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at built
            subst key
            exact ⟨localizedRootTree input cursor (read cursor) [], rfl,
              { tableMatch :=
                  treeTableMatch_localizedRootTree_terminal input stage cursor (read cursor)
                labelMatch :=
                  labelTable_localizedRootTree_terminal input stage cursor (read cursor) },
              LocalizedCumulativeTreeRealizes.mk cursor children []
                childrenComputed (by simp [terminal])
                (by intro tree member; simp at member),
              [], by simp [terminal], by simp [localizedRootTree]⟩
          · simp [childrenComputed, terminal] at built
  | succ fuel ih =>
      intro cursor key built
      unfold CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead? at built
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at built
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at built
            subst key
            exact ⟨localizedRootTree input cursor (read cursor) [], rfl,
              { tableMatch :=
                  treeTableMatch_localizedRootTree_terminal input stage cursor (read cursor)
                labelMatch :=
                  labelTable_localizedRootTree_terminal input stage cursor (read cursor) },
              LocalizedCumulativeTreeRealizes.mk cursor children []
                childrenComputed (by simp [terminal])
                (by intro tree member; simp at member),
              [], by simp [terminal], by simp [localizedRootTree]⟩
          · cases childKeysComputed : children.mapM
                (CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?
                  input stage read fuel) with
            | none =>
                simp [childrenComputed, terminal, childKeysComputed] at built
            | some childKeys =>
                simp [childrenComputed, terminal, childKeysComputed] at built
                subst key
                have hwit : ∀ (child : input.LocalizedRerootCursor carrierFuel)
                    (childKey : input.LocalizedRerootCumulativeRule45Key),
                    CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?
                      input stage read fuel child = some childKey →
                    ∃ tree : LocalizedCumulativeDecoratedTree input carrierFuel,
                      tree.source = child ∧
                        LocalizedCumulativeTreeFullMatch stage tree childKey ∧
                          LocalizedCumulativeTreeRealizes input read tree := by
                  intro child childKey childBuilt
                  obtain ⟨tree, treeSource, treeMatch, treeRealizes, _⟩ :=
                    ih child childKey childBuilt
                  exact ⟨tree, treeSource, treeMatch, treeRealizes⟩
                obtain ⟨childTrees, childSource, childRel⟩ :=
                  witnesses_of_mapM_some
                    (CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?
                      input stage read fuel)
                    (fun tree => tree.source)
                    (fun key tree =>
                      LocalizedCumulativeTreeFullMatch stage tree key ∧
                        LocalizedCumulativeTreeRealizes input read tree)
                    hwit children childKeys childKeysComputed
                obtain ⟨sortedTrees, sortedRel, sortedPerm⟩ :=
                  List.perm_comp_forall₂
                    (input.sortLocalizedRerootCumulativeRule45Keys_perm childKeys) childRel
                have sourcePerm :
                    (sortedTrees.map (fun tree => tree.source)).Perm children := by
                  simpa [childSource] using sortedPerm.map (fun tree => tree.source)
                have sortedTableRel : List.Forall₂
                    (fun key tree => LocalizedCumulativeTreeTableMatch stage tree key)
                    (input.sortLocalizedRerootCumulativeRule45Keys childKeys) sortedTrees :=
                  List.Forall₂.imp (fun key tree related => related.1.tableMatch) sortedRel
                have sortedLabelRel : List.Forall₂
                    (fun key tree => LocalizedCumulativeTreeLabelMatch tree key)
                    (input.sortLocalizedRerootCumulativeRule45Keys childKeys) sortedTrees :=
                  List.Forall₂.imp (fun key tree related => related.1.labelMatch) sortedRel
                have sortedRealizes : ∀ tree ∈ sortedTrees,
                    LocalizedCumulativeTreeRealizes input read tree := by
                  intro tree member
                  obtain ⟨key, _, related⟩ :=
                    exists_of_mem_right_forall₂ sortedRel tree member
                  exact related.2
                refine ⟨localizedRootTree input cursor (read cursor) sortedTrees, rfl,
                  { tableMatch :=
                      treeTableMatch_localizedRootTree_branch stage cursor (read cursor)
                        (input.sortLocalizedRerootCumulativeRule45Keys childKeys)
                        sortedTrees sortedTableRel
                    labelMatch :=
                      labelTable_localizedRootTree_branch stage cursor (read cursor)
                        (input.sortLocalizedRerootCumulativeRule45Keys childKeys)
                        sortedTrees sortedLabelRel },
                  LocalizedCumulativeTreeRealizes.mk cursor children sortedTrees
                    childrenComputed sourcePerm sortedRealizes,
                  children, rfl, ?_⟩
                · simpa [localizedRootTree] using sourcePerm

/-- Every successful actual cumulative build is matched by an actual sorted decorated occurrence
tree.  The root source is the actual cursor, the four tables are the actual key's constitutional
and descriptor observations, and the child sources are an actual permutation of the actual
`localizedRerootChildren?` frame.  The conclusion also carries the full recursive actual
provenance `LocalizedCumulativeTreeRealizes`: every node below the root is an actual
`localizedRootTree` with an actual child frame and an actual sorted child permutation.  The proof
is the label-free projection of `exists_decoratedTree_of_buildWithRead_fullMatch`, which inducts on
the actual fuel; the sort permutation is the production sort's own
`sortLocalizedRerootCumulativeRule45Keys_perm`. -/
theorem exists_decoratedTree_of_buildWithRead
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootCumulativeRule45Key),
      CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?
        input stage read fuel cursor = some key →
      ∃ tree : LocalizedCumulativeDecoratedTree input carrierFuel,
        tree.source = cursor ∧
          LocalizedCumulativeTreeTableMatch stage tree key ∧
            LocalizedCumulativeTreeRealizes input read tree ∧
              ∃ children : List (input.LocalizedRerootCursor carrierFuel),
                input.localizedRerootChildren? cursor = some children ∧
                  (tree.children.map (fun node => node.source)).Perm children := by
  intro fuel cursor key built
  obtain ⟨tree, treeSource, fullMatch, treeRealizes, children, childrenComputed, sourcePerm⟩ :=
    exists_decoratedTree_of_buildWithRead_fullMatch input stage read fuel cursor key built
  exact ⟨tree, treeSource, fullMatch.tableMatch, treeRealizes,
    children, childrenComputed, sourcePerm⟩

/-- Additional endpoint exposing the exact-label provenance: every successful actual cumulative
build admits a decorated tree whose source is the actual cursor, whose four comparator-visible
tables match the actual key, whose exact optional-label table equals the actual key's `labels` at
every addressed sphere, and which carries the full recursive actual provenance. -/
theorem exists_decoratedTree_of_buildWithRead_labelTable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootCumulativeRule45Key),
      CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?
        input stage read fuel cursor = some key →
      ∃ tree : LocalizedCumulativeDecoratedTree input carrierFuel,
        tree.source = cursor ∧
          LocalizedCumulativeTreeTableMatch stage tree key ∧
            tree.labelTable = key.labels ∧
              LocalizedCumulativeTreeRealizes input read tree ∧
                ∃ children : List (input.LocalizedRerootCursor carrierFuel),
                  input.localizedRerootChildren? cursor = some children ∧
                    (tree.children.map (fun node => node.source)).Perm children := by
  intro fuel cursor key built
  obtain ⟨tree, treeSource, fullMatch, treeRealizes, children, childrenComputed, sourcePerm⟩ :=
    exists_decoratedTree_of_buildWithRead_fullMatch input stage read fuel cursor key built
  exact ⟨tree, treeSource, fullMatch.tableMatch,
    labelTable_eq_labels_of_fullMatch fullMatch,
    treeRealizes, children, childrenComputed, sourcePerm⟩

/-- Exact numerical frontdoor: for two actual successful builds, the shipped cumulative comparator
returns `eq` exactly when the four addressed tables of their actual decorated trees agree. -/
theorem compareLocalizedRerootCumulativeRule45Keys_eq_iff_treeTables_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (leftKey rightKey : input.LocalizedRerootCumulativeRule45Key)
    (leftTree rightTree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (leftMatch : LocalizedCumulativeTreeTableMatch stage leftTree leftKey)
    (rightMatch : LocalizedCumulativeTreeTableMatch stage rightTree rightKey) :
    input.compareLocalizedRerootCumulativeRule45Keys leftKey rightKey = Ordering.eq ↔
      leftTree.tables stage = rightTree.tables stage := by
  rw [input.compareLocalizedRerootCumulativeRule45Keys_eq_iff_observable_eq]
  constructor
  · intro observableEq
    have rule1aEq : leftKey.constitutional.rule1a = rightKey.constitutional.rule1a := by
      have := congrArg LocalizedCumulativeRule45Observable.rule1a observableEq
      simpa only [localizedRerootCumulativeRule45Observable] using this
    have rule1bEq : leftKey.constitutional.rule1b = rightKey.constitutional.rule1b := by
      have := congrArg LocalizedCumulativeRule45Observable.rule1b observableEq
      simpa only [localizedRerootCumulativeRule45Observable] using this
    have rule2Eq : leftKey.constitutional.rule2 = rightKey.constitutional.rule2 := by
      have := congrArg LocalizedCumulativeRule45Observable.rule2 observableEq
      simpa only [localizedRerootCumulativeRule45Observable] using this
    have descriptorEq : leftKey.descriptor = rightKey.descriptor := by
      have := congrArg LocalizedCumulativeRule45Observable.descriptor observableEq
      simpa only [localizedRerootCumulativeRule45Observable] using this
    rw [tables_eq_localizedTreeTablesOfKey_of_match stage leftTree leftKey leftMatch,
      tables_eq_localizedTreeTablesOfKey_of_match stage rightTree rightKey rightMatch]
    calc localizedTreeTablesOfKey input leftKey
        = ⟨leftKey.constitutional.rule1a, leftKey.constitutional.rule1b,
            leftKey.constitutional.rule2, leftKey.descriptor⟩ := rfl
      _ = ⟨rightKey.constitutional.rule1a, rightKey.constitutional.rule1b,
            rightKey.constitutional.rule2, rightKey.descriptor⟩ := by
            rw [rule1aEq, rule1bEq, rule2Eq, descriptorEq]
      _ = localizedTreeTablesOfKey input rightKey := rfl
  · intro tablesEq
    have keyTablesEq : localizedTreeTablesOfKey input leftKey =
        localizedTreeTablesOfKey input rightKey := by
      rw [← tables_eq_localizedTreeTablesOfKey_of_match stage leftTree leftKey leftMatch,
        ← tables_eq_localizedTreeTablesOfKey_of_match stage rightTree rightKey rightMatch]
      exact tablesEq
    have rule1aEq : leftKey.constitutional.rule1a = rightKey.constitutional.rule1a := by
      have := congrArg LocalizedCumulativeTreeTables.rule1a keyTablesEq
      simpa only [localizedTreeTablesOfKey] using this
    have rule1bEq : leftKey.constitutional.rule1b = rightKey.constitutional.rule1b := by
      have := congrArg LocalizedCumulativeTreeTables.rule1b keyTablesEq
      simpa only [localizedTreeTablesOfKey] using this
    have rule2Eq : leftKey.constitutional.rule2 = rightKey.constitutional.rule2 := by
      have := congrArg LocalizedCumulativeTreeTables.rule2 keyTablesEq
      simpa only [localizedTreeTablesOfKey] using this
    have descriptorEq : leftKey.descriptor = rightKey.descriptor := by
      have := congrArg LocalizedCumulativeTreeTables.descriptor keyTablesEq
      simpa only [localizedTreeTablesOfKey] using this
    calc input.localizedRerootCumulativeRule45Observable leftKey
        = ⟨leftKey.constitutional.rule1a, leftKey.constitutional.rule1b,
            leftKey.constitutional.rule2, leftKey.descriptor⟩ := rfl
      _ = ⟨rightKey.constitutional.rule1a, rightKey.constitutional.rule1b,
            rightKey.constitutional.rule2, rightKey.descriptor⟩ := by
            rw [rule1aEq, rule1bEq, rule2Eq, descriptorEq]
      _ = input.localizedRerootCumulativeRule45Observable rightKey := rfl

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeBranchDecoration
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeBranchObservation
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeBranchShape
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeTreeTables
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.observation
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.observationList
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.shape
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.shapeList
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.localizedTreeChildLayerCount
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.mergeLocalizedTreeChildTables
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.table
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.tableList
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.table_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.tableList_eq_map
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.table_eq_root_merge
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.tables
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.labelTable
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.labelTable_eq_table
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.tables_rule1a
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.tables_rule1b
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.tables_rule2
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.tables_descriptor
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.mergeChildren_eq_mergePairTable
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.mergePairTable_zipIdx_map_gen
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.localizedTreeChildLayerCount_map_eq_childLayerCount
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.mergeLocalizedTreeChildTables_map_comp_eq_mergeChildren
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.mergeLocalizedRerootDescriptorChildren_eq_mergePairTable
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.localizedTreeChildLayerCount_descriptor_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.mergeLocalizedTreeChildTables_descriptor_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.mergeLocalizedRerootLabelChildren_eq_mergePairTable
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.localizedTreeChildLayerCount_label_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeDecoratedTree.mergeLocalizedTreeChildTables_label_eq
assert_kernel_only TetraStereo.OneCenter.localizedRootTree
assert_kernel_only TetraStereo.OneCenter.localizedTreeTablesOfKey
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeTreeTableMatch
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeTreeLabelMatch
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeTreeFullMatch
assert_kernel_only TetraStereo.OneCenter.labelTable_eq_labels_of_labelMatch
assert_kernel_only TetraStereo.OneCenter.labelTable_getD_eq_labels_getD_of_labelMatch
assert_kernel_only TetraStereo.OneCenter.labelTable_eq_labels_of_fullMatch
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeTreeRealizes
assert_kernel_only TetraStereo.OneCenter.tables_eq_localizedTreeTablesOfKey_of_match
assert_kernel_only TetraStereo.OneCenter.exists_decoratedTree_of_buildWithRead_fullMatch
assert_kernel_only TetraStereo.OneCenter.exists_decoratedTree_of_buildWithRead_labelTable
assert_kernel_only TetraStereo.OneCenter.exists_decoratedTree_of_buildWithRead
assert_kernel_only TetraStereo.OneCenter.compareLocalizedRerootCumulativeRule45Keys_eq_iff_treeTables_eq
