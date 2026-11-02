import TetraStereo.OneCenter.LocalizedCumulativeTreeObservableFaithfulness
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput

/-!
# Reconstructing sorted decorated trees from the actual cumulative sparse tables

`LocalizedCumulativeTreeObservableFaithfulness` defines the source-erased decorated occurrence tree
`LocalizedCumulativeDecoratedTree` produced by the actual cumulative reroot builder, the erasure maps
`observation` (decoration including the arbitrary-reader label) and `shape` (the three
constitutional columns only), and the addressed sparse `table` compiled from such a tree.  Its module
comment states the intended reconstruction theorem, but the present module is where the
reconstruction itself is proved.

This module establishes, for the exact `table` used there and with no additional data supplied:

* **Intrinsic height.**  `height` is `1 + max` of the child heights, and `heightList` is the
  corresponding list maximum.  For *any* observation function `observe`,
  `table_length_eq_height` shows that the compiled table has exactly `height` spheres, and
  `table_sphere_nonempty` shows that every sphere below the height is nonempty.  Neither result
  depends on the label: the root sphere is the singleton `([], observe root)` even when the label
  is `none`.
* **Sphere separation.**  `table_getD_zero` exposes the root sphere as the singleton
  `[([], observe root)]`; `table_getD_one_length` shows that the first child sphere holds exactly
  one entry per child, so the sphere determines the child count without any supplied length.
* **Normalized child reconstruction.**  `normalizedChildTable_tail_eq_table` strips the final
  sibling slot from every sphere of the merged tail and trims the trailing padding with the
  normalized `SparseAddress.normalizedChildTable` of `LocalizedSparseAddressReconstruction`.  It
  returns the child's *entire* table, with no child sphere count and no supplied child length.  The
  only shape hypothesis, the nonemptiness of every retained sphere, is derived here from
  `table_sphere_nonempty`, not assumed.
* **Constitutional shape recovery.**  `table_shape_eq_of_constitutional_tables_eq` proves, by induction on
  intrinsic height, that equality of the three constitutional tables determines the source-erased
  shape.  No label premise and no descriptor column is used, so the result cannot be circular in a
  Rule-5 label argument.
* **Decorated recovery.**  `table_observation_eq_of_tables_eq` proves the same for a fully decorated
  observation, given any pointwise label injectivity hypothesis on the descriptor column; the two
  trees may even use *different* observation functions for that column, which is what lets the two
  compared builds use different own Rule-4b references.  Two instantiations are supplied from the
  five-case injectivity of `LocalizedSparseAddressReconstruction`: the
  `rule5NoRule4bReference` stage and the `rule5` stage with a *common* Rule-5 reference and
  possibly different own Rule-4b references
  (`observation_eq_of_rule5_commonReference_columns_eq`).

Source cursors are proof witnesses only and are erased before every equality statement; no
statement here demands equal cursors, equal child correspondences, or equal tree lengths.  This
module is generic over the tree definitions: it does not construct a builder.  Composing these
injectivity results with an actual-builder success theorem yields faithfulness of the physical keys;
the present module alone does not assert that the builder succeeds, so it does not by itself claim
that actual keys are physically faithful.
-/

namespace LocalizedCumulativeDecoratedTree

/-! ## Intrinsic height

`height` is the intrinsic `1 + max` height of a decorated tree, and `heightList` the maximum over a
list of children.  They are defined mutually so that the well-founded recursion is structural in the
spine of the tree. -/

mutual
/-- Intrinsic height: one for the root plus the maximum child height. -/
def height {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat} :
    LocalizedCumulativeDecoratedTree input carrierFuel → Nat
  | ⟨_source, _atomicNumber, _rule1bDistance, _isotopeMass, _label, children⟩ =>
      1 + heightList children
  termination_by tree => sizeOf tree
  decreasing_by
    simp_wf

/-- Maximum intrinsic height over a list of children (`0` for the empty list). -/
def heightList {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat} :
    List (LocalizedCumulativeDecoratedTree input carrierFuel) → Nat
  | [] => 0
  | child :: children => max (height child) (heightList children)
  termination_by children => sizeOf children
  decreasing_by
    all_goals (simp_wf <;> omega)
end

/-! ## Unfolding equations

`height` and `heightList` are defined by well-founded recursion, so their defining equations are
not definitional.  These lemmas record the equations explicitly.  Each proof tries the available
unfolding mechanisms in turn, so the result does not depend on which one the compiler exposes. -/

/-- The defining equation of `height` at one concrete node. -/
theorem table_height_mk {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (source : input.LocalizedRerootCursor carrierFuel)
    (atomicNumber rule1bDistance isotopeMass : Nat)
    (label : Option LocalizedAuxiliaryLabel)
    (children : List (LocalizedCumulativeDecoratedTree input carrierFuel)) :
    height ⟨source, atomicNumber, rule1bDistance, isotopeMass, label, children⟩ =
      1 + heightList children := by
  rw [height]

/-- The defining equation of `heightList` at the empty list. -/
theorem table_heightList_nil {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat} :
    heightList ([] : List (LocalizedCumulativeDecoratedTree input carrierFuel)) = 0 := by
  rw [heightList]

/-- The defining equation of `heightList` at a cons. -/
theorem table_heightList_cons {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (child : LocalizedCumulativeDecoratedTree input carrierFuel)
    (children : List (LocalizedCumulativeDecoratedTree input carrierFuel)) :
    heightList (child :: children) = max (height child) (heightList children) := by
  rw [heightList]

/-- Every child is bounded by the list maximum. -/
theorem height_le_heightList {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (children : List (LocalizedCumulativeDecoratedTree input carrierFuel))
    {child : LocalizedCumulativeDecoratedTree input carrierFuel}
    (present : child ∈ children) : height child ≤ heightList children := by
  induction children with
  | nil => cases present
  | cons head tail inductionHypothesis =>
      rw [table_heightList_cons]
      rcases List.mem_cons.mp present with same | tailPresent
      · rw [same]
        exact le_max_left _ _
      · exact le_trans (inductionHypothesis tailPresent) (le_max_right _ _)

/-- A tall child is strictly lower than its parent. -/
theorem height_lt_height_of_mem {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    {child : LocalizedCumulativeDecoratedTree input carrierFuel}
    (present : child ∈ tree.children) : height child < height tree := by
  cases tree with
  | mk source atomicNumber rule1bDistance isotopeMass label children =>
      rw [table_height_mk]
      have bounded := height_le_heightList children present
      omega

/-- Every tree has height at least one. -/
theorem one_le_height {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) : 1 ≤ height tree := by
  cases tree with
  | mk source atomicNumber rule1bDistance isotopeMass label children =>
      rw [table_height_mk]
      omega

/-- A depth below the list maximum is realised by an actual child at that depth.  The child is
returned together with its exact sibling index, which is the slot used by the sparse merge. -/
theorem exists_getElem?_height_gt_of_lt_heightList
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (children : List (LocalizedCumulativeDecoratedTree input carrierFuel)) (depth : Nat)
    (deep : depth < heightList children) :
    ∃ (index : Nat) (child : LocalizedCumulativeDecoratedTree input carrierFuel),
      children[index]? = some child ∧ depth < height child := by
  induction children with
  | nil =>
      rw [table_heightList_nil] at deep
      omega
  | cons head tail inductionHypothesis =>
      rw [table_heightList_cons] at deep
      by_cases headDeep : depth < height head
      · exact ⟨0, head, rfl, headDeep⟩
      · have tailDeep : depth < heightList tail := by omega
        obtain ⟨index, child, atIndex, childDeep⟩ := inductionHypothesis tailDeep
        refine ⟨index + 1, child, ?_, childDeep⟩
        simpa using atIndex

/-! ## A foldl maximum from an arbitrary seed -/

/-- A left fold with `max` is insensitive to its seed beyond the seed's own contribution. -/
theorem foldl_max_length_eq_max {β : Type*} (init : Nat) (values : List β)
    (length : β → Nat) :
    values.foldl (fun longest value => max longest (length value)) init =
      max init (values.foldl (fun longest value => max longest (length value)) 0) := by
  induction values generalizing init with
  | nil => simp
  | cons head tail inductionHypothesis =>
      simp only [List.foldl_cons]
      have zeroMax : max 0 (length head) = length head := by omega
      rw [zeroMax, inductionHypothesis (max init (length head)),
        inductionHypothesis (length head)]
      omega

/-- One cons step of the merged layer count. -/
theorem localizedTreeChildLayerCount_map_cons {α : Type*}
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (observe : LocalizedCumulativeDecoratedTree input carrierFuel → α)
    (child : LocalizedCumulativeDecoratedTree input carrierFuel)
    (children : List (LocalizedCumulativeDecoratedTree input carrierFuel)) :
    localizedTreeChildLayerCount ((child :: children).map (table observe)) =
      max ((table observe child).length)
        (localizedTreeChildLayerCount (children.map (table observe))) := by
  simp only [localizedTreeChildLayerCount, List.map_cons, List.foldl_cons]
  rw [foldl_max_length_eq_max (init := max 0 ((table observe child).length))
    (values := children.map (table observe)) (length := fun entry => entry.length)]
  omega

/-- The merged layer count is the maximum child height, once every child table has its own
intrinsic height as length. -/
theorem localizedTreeChildLayerCount_map_eq_heightList {α : Type*}
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (observe : LocalizedCumulativeDecoratedTree input carrierFuel → α)
    (children : List (LocalizedCumulativeDecoratedTree input carrierFuel))
    (lengths : ∀ child ∈ children, (table observe child).length = height child) :
    localizedTreeChildLayerCount (children.map (table observe)) = heightList children := by
  induction children with
  | nil =>
      rw [table_heightList_nil]
      rfl
  | cons head tail inductionHypothesis =>
      rw [table_heightList_cons, localizedTreeChildLayerCount_map_cons,
        lengths head (by simp),
        inductionHypothesis (fun child present => lengths child (List.mem_cons_of_mem head present))]

/-! ## Root sphere, child sphere and table length -/

/-- Dropping the one-sphere root prefix of a table recovers the child merge, stated with the
successor index so that it applies to all depths uniformly. -/
theorem getD_root_cons {α : Type*} (root : List α) (right : List (List α))
    (depth : Nat) (fallback : List α) :
    ([root] ++ right).getD (depth + 1) fallback = right.getD depth fallback := by
  rw [Nat.add_comm depth 1]
  exact SparseAddress.getD_append_one_add root right depth fallback

/-- The root sphere is the singleton root observation, whatever the label is. -/
theorem table_getD_zero {α : Type*}{input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (observe : LocalizedCumulativeDecoratedTree input carrierFuel → α)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    (table observe tree).getD 0 [] = [([], observe tree)] := by
  rw [table_eq_root_merge]
  rfl

/-- A slot-indexed flatMap of singleton blocks has exactly one entry per merged value. -/
theorem length_flatMap_zipIdx_prefixLayer_of_singleton {β α : Type*}
    (values : List β) (block : β → List (OfficialSparseEntry α))
    (singleton : ∀ value ∈ values, (block value).length = 1) (start : Nat) :
    ((values.zipIdx start).flatMap fun pair =>
        OfficialRuleMajorKey.prefixLayer pair.2 (block pair.1)).length = values.length := by
  induction values generalizing start with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [List.zipIdx_cons, List.flatMap_cons, List.length_append]
      have headLength : (OfficialRuleMajorKey.prefixLayer start (block head)).length = 1 := by
        rw [OfficialRuleMajorKey.prefixLayer, List.length_map]
        exact singleton head (by simp)
      rw [headLength, inductionHypothesis
        (fun value present => singleton value (List.mem_cons_of_mem head present)) (start + 1)]
      simp only [List.length_cons]
      omega

/-- Every compiled observation table has exactly the intrinsic height as sphere count. -/
theorem table_length_eq_height {α : Type*}{input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (observe : LocalizedCumulativeDecoratedTree input carrierFuel → α)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    (table observe tree).length = height tree := by
  have main : ∀ n : Nat, ∀ candidate : LocalizedCumulativeDecoratedTree input carrierFuel,
      height candidate ≤ n → (table observe candidate).length = height candidate := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro k inductionHypothesis candidate bound
    cases candidate with
    | mk source atomicNumber rule1bDistance isotopeMass label children =>
        rw [table_eq_root_merge, table_height_mk, mergeLocalizedTreeChildTables,
          SparseAddress.mergePairTable]
        have lengths : ∀ child ∈ children, (table observe child).length = height child := by
          intro child present
          refine inductionHypothesis (height child) ?_ child (le_refl _)
          have bounded := height_lt_height_of_mem
            ⟨source, atomicNumber, rule1bDistance, isotopeMass, label, children⟩ present
          omega
        have countEq : localizedTreeChildLayerCount (children.map (table observe)) =
            heightList children :=
          localizedTreeChildLayerCount_map_eq_heightList observe children lengths
        rw [countEq]
        simp
        omega
  exact main (height tree) tree (le_refl _)

/-- The first child sphere holds exactly one entry per child: the sphere determines the child
count without any supplied tree length. -/
theorem table_getD_one_length {α : Type*}{input : CertifiedLocalizedCIPInput}
    {carrierFuel : Nat}
    (observe : LocalizedCumulativeDecoratedTree input carrierFuel → α)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    ((table observe tree).getD 1 []).length = tree.children.length := by
  cases tree with
  | mk source atomicNumber rule1bDistance isotopeMass label children =>
      rw [table_eq_root_merge, getD_root_cons, mergeLocalizedTreeChildTables,
        SparseAddress.mergePairTable_getD]
      by_cases positive : 0 < localizedTreeChildLayerCount (children.map (table observe))
      · rw [if_pos positive]
        have singleton : ∀ entry ∈ children.map (table observe),
            (entry.getD 0 []).length = 1 := by
          intro entry present
          obtain ⟨child, _, same⟩ := List.mem_map.mp present
          rw [← same, table_getD_zero]
          rfl
        simpa [SparseAddress.mergePairs] using
          length_flatMap_zipIdx_prefixLayer_of_singleton (children.map (table observe))
            (fun entry => (id entry).getD 0 []) singleton 0
      · rw [if_neg positive]
        have empty : children = [] := by
          cases children with
          | nil => rfl
          | cons child rest =>
              exfalso
              have bounded : (table observe child).length ≤
                  localizedTreeChildLayerCount ((child :: rest).map (table observe)) :=
                (SparseAddress.le_foldl_max ((child :: rest).map (table observe))
                  (fun entry => entry.length) 0).2 (table observe child)
                  (List.mem_map.mpr ⟨child, by simp, rfl⟩)
              have positiveLength : 0 < (table observe child).length := by
                rw [table_length_eq_height]
                exact one_le_height child
              omega
        simp [empty]

/-- The root column determines the root value: the zero sphere is the singleton
`([], observe root)`.  The two tables may even come from different observation functions. -/
theorem table_observe_root_eq {α : Type*} {input : CertifiedLocalizedCIPInput}
    {carrierFuel : Nat}
    (fObs gObs : LocalizedCumulativeDecoratedTree input carrierFuel → α)
    (t1 t2 : LocalizedCumulativeDecoratedTree input carrierFuel)
    (same : table fObs t1 = table gObs t2) : fObs t1 = gObs t2 := by
  have rootSame : (table fObs t1).getD 0 [] = (table gObs t2).getD 0 [] :=
    congrArg (fun entries => entries.getD 0 []) same
  have first := table_getD_zero fObs t1
  have second := table_getD_zero gObs t2
  rw [first, second] at rootSame
  simpa using rootSame

/-- The first child sphere determines the number of children, with no supplied tree length. -/
theorem table_childCount_eq_of_table_eq {α : Type*} {input : CertifiedLocalizedCIPInput}
    {carrierFuel : Nat}
    (fObs gObs : LocalizedCumulativeDecoratedTree input carrierFuel → α)
    (t1 t2 : LocalizedCumulativeDecoratedTree input carrierFuel)
    (same : table fObs t1 = table gObs t2) : t1.children.length = t2.children.length := by
  have countSame : ((table fObs t1).getD 1 []).length =
      ((table gObs t2).getD 1 []).length :=
    congrArg (fun entries => (entries.getD 1 []).length) same
  have first := table_getD_one_length fObs t1
  have second := table_getD_one_length gObs t2
  rw [first, second] at countSame
  exact countSame

/-- Every sphere below a table's length is nonempty.  In particular the root sphere is the
singleton `([], observe root)`, so an absent (`none`) label still contributes a nonempty sphere. -/
theorem table_sphere_nonempty {α : Type*}{input : CertifiedLocalizedCIPInput}
    {carrierFuel : Nat}
    (observe : LocalizedCumulativeDecoratedTree input carrierFuel → α)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    ∀ depth, depth < height tree → (table observe tree).getD depth [] ≠ [] := by
  have main : ∀ n : Nat, ∀ candidate : LocalizedCumulativeDecoratedTree input carrierFuel,
      height candidate ≤ n → ∀ depth, depth < height candidate →
        (table observe candidate).getD depth [] ≠ [] := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro k inductionHypothesis candidate bound depth deep
    cases candidate with
    | mk source atomicNumber rule1bDistance isotopeMass label children =>
        cases depth with
        | zero =>
            rw [table_getD_zero]
            simp
        | succ depth =>
            rw [table_height_mk] at deep
            have inside : depth < heightList children := by omega
            obtain ⟨index, child, atIndex, childDeep⟩ :=
              exists_getElem?_height_gt_of_lt_heightList children depth inside
            have lengths : ∀ current ∈ children, (table observe current).length = height current :=
              fun current _ => table_length_eq_height observe current
            have countEq : localizedTreeChildLayerCount (children.map (table observe)) =
                heightList children :=
              localizedTreeChildLayerCount_map_eq_heightList observe children lengths
            have childSphere : (table observe child).getD depth [] ≠ [] := by
              refine inductionHypothesis (height child) ?_ child (le_refl _) depth childDeep
              have present := List.mem_of_getElem? atIndex
              have bounded := height_lt_height_of_mem
                ⟨source, atomicNumber, rule1bDistance, isotopeMass, label, children⟩ present
              omega
            rw [table_eq_root_merge, getD_root_cons, mergeLocalizedTreeChildTables,
              SparseAddress.mergePairTable_getD, if_pos (by rw [countEq]; exact inside)]
            intro flatNil
            have member : (table observe child, index) ∈
                (children.map (table observe)).zipIdx := by
              rw [List.mk_mem_zipIdx_iff_getElem?]
              simp [List.getElem?_map, atIndex]
            have flatNil' : ((children.map (table observe)).zipIdx.flatMap
                fun pair => OfficialRuleMajorKey.prefixLayer pair.2
                  ((id pair.1).getD depth [])) = [] := flatNil
            have blockNil : OfficialRuleMajorKey.prefixLayer index
                ((table observe child).getD depth []) = [] := by
              simpa using (List.flatMap_eq_nil_iff.mp flatNil')
                (table observe child, index) member
            have lengthZero :
                (OfficialRuleMajorKey.prefixLayer index
                  ((table observe child).getD depth [])).length = 0 := by
              rw [blockNil]
              rfl
            rw [OfficialRuleMajorKey.prefixLayer, List.length_map] at lengthZero
            exact childSphere (List.length_eq_zero_iff.mp lengthZero)
  exact main (height tree) tree (le_refl _)

/-! ## Normalized child reconstruction from the actual tree table -/

/-- The tail of a tree table is exactly the slot-indexed merge of the child tables. -/
theorem table_tail_eq_merge {α : Type*}{input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (observe : LocalizedCumulativeDecoratedTree input carrierFuel → α)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    (table observe tree).tail =
      mergeLocalizedTreeChildTables (tree.children.map (table observe)) := by
  rw [table_eq_root_merge]
  rfl

/-- **Normalized child reconstruction.**  Selecting the final sibling slot from every sphere of the
merged tail, dropping that leading slot and trimming the trailing empty padding returns the child's
entire table.  No child length, child height, or child-table correspondence is supplied; the only
nonemptiness hypothesis of the generic sparse inverse is discharged by
`table_sphere_nonempty`. -/
theorem normalizedChildTable_tail_eq_table {α : Type*}{input : CertifiedLocalizedCIPInput}
    {carrierFuel : Nat}
    (observe : LocalizedCumulativeDecoratedTree input carrierFuel → α)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) (slot : Nat)
    (child : LocalizedCumulativeDecoratedTree input carrierFuel)
    (atSlot : tree.children[slot]? = some child) :
    SparseAddress.normalizedChildTable slot (table observe tree).tail = table observe child := by
  rw [table_tail_eq_merge, mergeLocalizedTreeChildTables]
  refine SparseAddress.mergePairTable_normalizedChildTable
    (tree.children.map (table observe)) id
    (localizedTreeChildLayerCount (tree.children.map (table observe))) slot
    (table observe child) ?bound ?atSlot' ?nonempty
  · exact (SparseAddress.le_foldl_max (tree.children.map (table observe))
      (fun entry => entry.length) 0).2 (table observe child)
      (List.mem_map.mpr ⟨child, List.mem_of_getElem? atSlot, rfl⟩)
  · simp [List.getElem?_map, atSlot]
  · intro depth deep
    exact table_sphere_nonempty observe child depth
      (by simpa [table_length_eq_height] using deep)

/-! ## Erasure lists are maps -/

/-- The defining equation of `shape` at one concrete node. -/
theorem table_shape_mk {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (source : input.LocalizedRerootCursor carrierFuel)
    (atomicNumber rule1bDistance isotopeMass : Nat)
    (label : Option LocalizedAuxiliaryLabel)
    (children : List (LocalizedCumulativeDecoratedTree input carrierFuel)) :
    shape ⟨source, atomicNumber, rule1bDistance, isotopeMass, label, children⟩ =
      { atomicNumber := atomicNumber
        rule1bDistance := rule1bDistance
        isotopeMass := isotopeMass
        children := shapeList children } := by
  rw [shape]

/-- The defining equation of `observation` at one concrete node. -/
theorem table_observation_mk {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (source : input.LocalizedRerootCursor carrierFuel)
    (atomicNumber rule1bDistance isotopeMass : Nat)
    (label : Option LocalizedAuxiliaryLabel)
    (children : List (LocalizedCumulativeDecoratedTree input carrierFuel)) :
    observation ⟨source, atomicNumber, rule1bDistance, isotopeMass, label, children⟩ =
      { decoration :=
          { atomicNumber := atomicNumber
            rule1bDistance := rule1bDistance
            isotopeMass := isotopeMass
            label := label }
        children := observationList children } := by
  rw [observation]

/-- Erasing a list of constitutional shapes is the pointwise map of `shape`. -/
theorem table_shapeList_eq_map {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat} :
    ∀ children : List (LocalizedCumulativeDecoratedTree input carrierFuel),
      shapeList children = children.map shape
  | [] => by
      rw [shapeList]
      rfl
  | child :: children => by
      rw [shapeList, table_shapeList_eq_map children]
      rfl

/-- Erasing a list of decorated observations is the pointwise map of `observation`. -/
theorem table_observationList_eq_map {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat} :
    ∀ children : List (LocalizedCumulativeDecoratedTree input carrierFuel),
      observationList children = children.map observation
  | [] => by
      rw [observationList]
      rfl
  | child :: children => by
      rw [observationList, table_observationList_eq_map children]
      rfl

/-! ## Constitutional shape recovery -/

/-- **Three constitutional tables determine the source-erased shape.**  The proof is by induction
on intrinsic height.  The root decoration is read off sphere zero, the child count off sphere one,
and each child's complete table is recovered by `normalizedChildTable_tail_eq_table` before the
induction hypothesis is applied.  No label, descriptor, source cursor or child correspondence is
used. -/
theorem table_shape_eq_of_constitutional_tables_eq {input : CertifiedLocalizedCIPInput}
    {carrierFuel : Nat}
    (t1 t2 : LocalizedCumulativeDecoratedTree input carrierFuel)
    (hRule1a : table (fun node => node.atomicNumber) t1 =
      table (fun node => node.atomicNumber) t2)
    (hRule1b : table (fun node => node.rule1bDistance) t1 =
      table (fun node => node.rule1bDistance) t2)
    (hRule2 : table (fun node => node.isotopeMass) t1 =
      table (fun node => node.isotopeMass) t2) :
    shape t1 = shape t2 := by
  have main : ∀ n : Nat, ∀ candidate1 : LocalizedCumulativeDecoratedTree input carrierFuel,
      height candidate1 ≤ n → ∀ candidate2 : LocalizedCumulativeDecoratedTree input carrierFuel,
        table (fun node => node.atomicNumber) candidate1 =
          table (fun node => node.atomicNumber) candidate2 →
        table (fun node => node.rule1bDistance) candidate1 =
          table (fun node => node.rule1bDistance) candidate2 →
        table (fun node => node.isotopeMass) candidate1 =
          table (fun node => node.isotopeMass) candidate2 →
        shape candidate1 = shape candidate2 := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro k inductionHypothesis candidate1 bound candidate2 hRule1a hRule1b hRule2
    cases candidate1 with
    | mk source1 atomic1 dist1 mass1 label1 children1 =>
      cases candidate2 with
      | mk source2 atomic2 dist2 mass2 label2 children2 =>
        have atomicEq : atomic1 = atomic2 := by
          simpa using table_observe_root_eq (fun node => node.atomicNumber)
            (fun node => node.atomicNumber) _ _ hRule1a
        have distEq : dist1 = dist2 := by
          simpa using table_observe_root_eq (fun node => node.rule1bDistance)
            (fun node => node.rule1bDistance) _ _ hRule1b
        have massEq : mass1 = mass2 := by
          simpa using table_observe_root_eq (fun node => node.isotopeMass)
            (fun node => node.isotopeMass) _ _ hRule2
        have childCount : children1.length = children2.length :=
          table_childCount_eq_of_table_eq (fun node => node.atomicNumber)
            (fun node => node.atomicNumber) _ _ hRule1a
        have childShape : ∀ (index : Nat)
            (child1 child2 : LocalizedCumulativeDecoratedTree input carrierFuel),
            children1[index]? = some child1 → children2[index]? = some child2 →
              shape child1 = shape child2 := by
          intro index child1 child2 atFirst atSecond
          have firstAtomic : table (fun node => node.atomicNumber) child1 =
              table (fun node => node.atomicNumber) child2 := by
            have tails : (table (fun node => node.atomicNumber)
                ⟨source1, atomic1, dist1, mass1, label1, children1⟩).tail =
                (table (fun node => node.atomicNumber)
                  ⟨source2, atomic2, dist2, mass2, label2, children2⟩).tail :=
              congrArg List.tail hRule1a
            calc table (fun node => node.atomicNumber) child1
                = SparseAddress.normalizedChildTable index
                    (table (fun node => node.atomicNumber)
                      ⟨source1, atomic1, dist1, mass1, label1, children1⟩).tail :=
                  (normalizedChildTable_tail_eq_table _ _ index child1 atFirst).symm
              _ = SparseAddress.normalizedChildTable index
                    (table (fun node => node.atomicNumber)
                      ⟨source2, atomic2, dist2, mass2, label2, children2⟩).tail := by
                  rw [tails]
              _ = table (fun node => node.atomicNumber) child2 :=
                  normalizedChildTable_tail_eq_table _ _ index child2 atSecond
          have firstDist : table (fun node => node.rule1bDistance) child1 =
              table (fun node => node.rule1bDistance) child2 := by
            have tails : (table (fun node => node.rule1bDistance)
                ⟨source1, atomic1, dist1, mass1, label1, children1⟩).tail =
                (table (fun node => node.rule1bDistance)
                  ⟨source2, atomic2, dist2, mass2, label2, children2⟩).tail :=
              congrArg List.tail hRule1b
            calc table (fun node => node.rule1bDistance) child1
                = SparseAddress.normalizedChildTable index
                    (table (fun node => node.rule1bDistance)
                      ⟨source1, atomic1, dist1, mass1, label1, children1⟩).tail :=
                  (normalizedChildTable_tail_eq_table _ _ index child1 atFirst).symm
              _ = SparseAddress.normalizedChildTable index
                    (table (fun node => node.rule1bDistance)
                      ⟨source2, atomic2, dist2, mass2, label2, children2⟩).tail := by
                  rw [tails]
              _ = table (fun node => node.rule1bDistance) child2 :=
                  normalizedChildTable_tail_eq_table _ _ index child2 atSecond
          have firstMass : table (fun node => node.isotopeMass) child1 =
              table (fun node => node.isotopeMass) child2 := by
            have tails : (table (fun node => node.isotopeMass)
                ⟨source1, atomic1, dist1, mass1, label1, children1⟩).tail =
                (table (fun node => node.isotopeMass)
                  ⟨source2, atomic2, dist2, mass2, label2, children2⟩).tail :=
              congrArg List.tail hRule2
            calc table (fun node => node.isotopeMass) child1
                = SparseAddress.normalizedChildTable index
                    (table (fun node => node.isotopeMass)
                      ⟨source1, atomic1, dist1, mass1, label1, children1⟩).tail :=
                  (normalizedChildTable_tail_eq_table _ _ index child1 atFirst).symm
              _ = SparseAddress.normalizedChildTable index
                    (table (fun node => node.isotopeMass)
                      ⟨source2, atomic2, dist2, mass2, label2, children2⟩).tail := by
                  rw [tails]
              _ = table (fun node => node.isotopeMass) child2 :=
                  normalizedChildTable_tail_eq_table _ _ index child2 atSecond
          refine inductionHypothesis (height child1) ?_ child1 (le_refl _) child2
            firstAtomic firstDist firstMass
          have smaller := height_lt_height_of_mem
            ⟨source1, atomic1, dist1, mass1, label1, children1⟩
            (List.mem_of_getElem? atFirst)
          omega
        have childrenEq : shapeList children1 = shapeList children2 := by
          rw [table_shapeList_eq_map, table_shapeList_eq_map]
          apply List.ext_getElem (by simpa using childCount)
          intro index inFirst inSecond
          rw [List.getElem_map, List.getElem_map]
          exact childShape index _ _ (List.getElem?_eq_getElem (by simpa using inFirst))
            (List.getElem?_eq_getElem (by simpa using inSecond))
        simp only [table_shape_mk, atomicEq, distEq, massEq, childrenEq]
  exact main (height t1) t1 (le_refl _) t2 hRule1a hRule1b hRule2

/-! ## Decorated observation recovery -/

/-- **Four columns determine the source-erased decorated observation.**  The descriptor column may
use a *different* observation function on the two trees; the only requirement is a pointwise label
injectivity hypothesis `fObs left = gObs right → left = right`.  The three constitutional columns
carry the shape, and the descriptor column carries the label at every addressed node. -/
theorem table_observation_eq_of_tables_eq {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (fObs gObs : Option LocalizedAuxiliaryLabel → List Nat)
    (injective : ∀ left right, fObs left = gObs right → left = right)
    (t1 t2 : LocalizedCumulativeDecoratedTree input carrierFuel)
    (hRule1a : table (fun node => node.atomicNumber) t1 =
      table (fun node => node.atomicNumber) t2)
    (hRule1b : table (fun node => node.rule1bDistance) t1 =
      table (fun node => node.rule1bDistance) t2)
    (hRule2 : table (fun node => node.isotopeMass) t1 =
      table (fun node => node.isotopeMass) t2)
    (hDescriptor : table (fun node => fObs node.label) t1 =
      table (fun node => gObs node.label) t2) :
    observation t1 = observation t2 := by
  have main : ∀ n : Nat, ∀ candidate1 : LocalizedCumulativeDecoratedTree input carrierFuel,
      height candidate1 ≤ n → ∀ candidate2 : LocalizedCumulativeDecoratedTree input carrierFuel,
        table (fun node => node.atomicNumber) candidate1 =
          table (fun node => node.atomicNumber) candidate2 →
        table (fun node => node.rule1bDistance) candidate1 =
          table (fun node => node.rule1bDistance) candidate2 →
        table (fun node => node.isotopeMass) candidate1 =
          table (fun node => node.isotopeMass) candidate2 →
        table (fun node => fObs node.label) candidate1 =
          table (fun node => gObs node.label) candidate2 →
        observation candidate1 = observation candidate2 := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro k inductionHypothesis candidate1 bound candidate2 hRule1a hRule1b hRule2 hDescriptor
    cases candidate1 with
    | mk source1 atomic1 dist1 mass1 label1 children1 =>
      cases candidate2 with
      | mk source2 atomic2 dist2 mass2 label2 children2 =>
        have atomicEq : atomic1 = atomic2 := by
          simpa using table_observe_root_eq
            (fun (node : LocalizedCumulativeDecoratedTree input carrierFuel) =>
              node.atomicNumber)
            (fun (node : LocalizedCumulativeDecoratedTree input carrierFuel) =>
              node.atomicNumber) _ _ hRule1a
        have distEq : dist1 = dist2 := by
          simpa using table_observe_root_eq
            (fun (node : LocalizedCumulativeDecoratedTree input carrierFuel) =>
              node.rule1bDistance)
            (fun (node : LocalizedCumulativeDecoratedTree input carrierFuel) =>
              node.rule1bDistance) _ _ hRule1b
        have massEq : mass1 = mass2 := by
          simpa using table_observe_root_eq
            (fun (node : LocalizedCumulativeDecoratedTree input carrierFuel) =>
              node.isotopeMass)
            (fun (node : LocalizedCumulativeDecoratedTree input carrierFuel) =>
              node.isotopeMass) _ _ hRule2
        have labelEq : label1 = label2 := by
          have rootSame := table_observe_root_eq
            (fun (node : LocalizedCumulativeDecoratedTree input carrierFuel) =>
              fObs node.label)
            (fun (node : LocalizedCumulativeDecoratedTree input carrierFuel) =>
              gObs node.label) _ _ hDescriptor
          exact injective label1 label2 (by simpa using rootSame)
        have childCount : children1.length = children2.length :=
          table_childCount_eq_of_table_eq
            (fun (node : LocalizedCumulativeDecoratedTree input carrierFuel) =>
              node.atomicNumber)
            (fun (node : LocalizedCumulativeDecoratedTree input carrierFuel) =>
              node.atomicNumber) _ _ hRule1a
        have childObservation : ∀ (index : Nat)
            (child1 child2 : LocalizedCumulativeDecoratedTree input carrierFuel),
            children1[index]? = some child1 → children2[index]? = some child2 →
              observation child1 = observation child2 := by
          intro index child1 child2 atFirst atSecond
          have firstAtomic : table (fun node => node.atomicNumber) child1 =
              table (fun node => node.atomicNumber) child2 := by
            have tails : (table (fun node => node.atomicNumber)
                ⟨source1, atomic1, dist1, mass1, label1, children1⟩).tail =
                (table (fun node => node.atomicNumber)
                  ⟨source2, atomic2, dist2, mass2, label2, children2⟩).tail :=
              congrArg List.tail hRule1a
            calc table (fun node => node.atomicNumber) child1
                = SparseAddress.normalizedChildTable index
                    (table (fun node => node.atomicNumber)
                      ⟨source1, atomic1, dist1, mass1, label1, children1⟩).tail :=
                  (normalizedChildTable_tail_eq_table _ _ index child1 atFirst).symm
              _ = SparseAddress.normalizedChildTable index
                    (table (fun node => node.atomicNumber)
                      ⟨source2, atomic2, dist2, mass2, label2, children2⟩).tail := by
                  rw [tails]
              _ = table (fun node => node.atomicNumber) child2 :=
                  normalizedChildTable_tail_eq_table _ _ index child2 atSecond
          have firstDist : table (fun node => node.rule1bDistance) child1 =
              table (fun node => node.rule1bDistance) child2 := by
            have tails : (table (fun node => node.rule1bDistance)
                ⟨source1, atomic1, dist1, mass1, label1, children1⟩).tail =
                (table (fun node => node.rule1bDistance)
                  ⟨source2, atomic2, dist2, mass2, label2, children2⟩).tail :=
              congrArg List.tail hRule1b
            calc table (fun node => node.rule1bDistance) child1
                = SparseAddress.normalizedChildTable index
                    (table (fun node => node.rule1bDistance)
                      ⟨source1, atomic1, dist1, mass1, label1, children1⟩).tail :=
                  (normalizedChildTable_tail_eq_table _ _ index child1 atFirst).symm
              _ = SparseAddress.normalizedChildTable index
                    (table (fun node => node.rule1bDistance)
                      ⟨source2, atomic2, dist2, mass2, label2, children2⟩).tail := by
                  rw [tails]
              _ = table (fun node => node.rule1bDistance) child2 :=
                  normalizedChildTable_tail_eq_table _ _ index child2 atSecond
          have firstMass : table (fun node => node.isotopeMass) child1 =
              table (fun node => node.isotopeMass) child2 := by
            have tails : (table (fun node => node.isotopeMass)
                ⟨source1, atomic1, dist1, mass1, label1, children1⟩).tail =
                (table (fun node => node.isotopeMass)
                  ⟨source2, atomic2, dist2, mass2, label2, children2⟩).tail :=
              congrArg List.tail hRule2
            calc table (fun node => node.isotopeMass) child1
                = SparseAddress.normalizedChildTable index
                    (table (fun node => node.isotopeMass)
                      ⟨source1, atomic1, dist1, mass1, label1, children1⟩).tail :=
                  (normalizedChildTable_tail_eq_table _ _ index child1 atFirst).symm
              _ = SparseAddress.normalizedChildTable index
                    (table (fun node => node.isotopeMass)
                      ⟨source2, atomic2, dist2, mass2, label2, children2⟩).tail := by
                  rw [tails]
              _ = table (fun node => node.isotopeMass) child2 :=
                  normalizedChildTable_tail_eq_table _ _ index child2 atSecond
          have firstDescriptor : table (fun node => fObs node.label) child1 =
              table (fun node => gObs node.label) child2 := by
            have tails : (table (fun node => fObs node.label)
                ⟨source1, atomic1, dist1, mass1, label1, children1⟩).tail =
                (table (fun node => gObs node.label)
                  ⟨source2, atomic2, dist2, mass2, label2, children2⟩).tail :=
              congrArg List.tail hDescriptor
            calc table (fun node => fObs node.label) child1
                = SparseAddress.normalizedChildTable index
                    (table (fun node => fObs node.label)
                      ⟨source1, atomic1, dist1, mass1, label1, children1⟩).tail :=
                  (normalizedChildTable_tail_eq_table _ _ index child1 atFirst).symm
              _ = SparseAddress.normalizedChildTable index
                    (table (fun node => gObs node.label)
                      ⟨source2, atomic2, dist2, mass2, label2, children2⟩).tail := by
                  rw [tails]
              _ = table (fun node => gObs node.label) child2 :=
                  normalizedChildTable_tail_eq_table _ _ index child2 atSecond
          refine inductionHypothesis (height child1) ?_ child1 (le_refl _) child2
            firstAtomic firstDist firstMass firstDescriptor
          have smaller := height_lt_height_of_mem
            ⟨source1, atomic1, dist1, mass1, label1, children1⟩
            (List.mem_of_getElem? atFirst)
          omega
        have childrenEq : observationList children1 = observationList children2 := by
          rw [table_observationList_eq_map, table_observationList_eq_map]
          apply List.ext_getElem (by simpa using childCount)
          intro index inFirst inSecond
          rw [List.getElem_map, List.getElem_map]
          exact childObservation index _ _ (List.getElem?_eq_getElem (by simpa using inFirst))
            (List.getElem?_eq_getElem (by simpa using inSecond))
        simp only [table_observation_mk, atomicEq, distEq, massEq, labelEq, childrenEq]
  exact main (height t1) t1 (le_refl _) t2 hRule1a hRule1b hRule2 hDescriptor

/-! ## Stage-level column equalities -/

/-- **The three constitutional columns determine the shape, whatever descriptor stage is used.**
The stage index of `tables` is phantom: no descriptor column is read here, so this result cannot be
circular in a Rule-5 label argument. -/
theorem table_shape_eq_of_columns_eq {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (stageLeft stageRight : LocalizedCumulativeRule45Stage)
    (t1 t2 : LocalizedCumulativeDecoratedTree input carrierFuel)
    (hRule1a : (tables stageLeft t1).rule1a = (tables stageRight t2).rule1a)
    (hRule1b : (tables stageLeft t1).rule1b = (tables stageRight t2).rule1b)
    (hRule2 : (tables stageLeft t1).rule2 = (tables stageRight t2).rule2) :
    shape t1 = shape t2 :=
  table_shape_eq_of_constitutional_tables_eq t1 t2
    (by simpa using hRule1a) (by simpa using hRule1b) (by simpa using hRule2)

/-- Same-stage form: equality of the whole four-column table structure at one stage determines the
source-erased shape. -/
theorem table_shape_eq_of_tables_eq {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (t1 t2 : LocalizedCumulativeDecoratedTree input carrierFuel)
    (same : tables stage t1 = tables stage t2) : shape t1 = shape t2 :=
  table_shape_eq_of_columns_eq stage stage t1 t2
    (congrArg (fun entry => entry.rule1a) same)
    (congrArg (fun entry => entry.rule1b) same)
    (congrArg (fun entry => entry.rule2) same)

/-- **Decorated observation recovery for a common Rule-5 reference stage.**  The two compared
builds may use different own Rule-4b references; only the common Rule-5 reference must agree.
The determination is the five-case injectivity
`localizedCumulativeRule45Priority_rule5_commonReference_injective`. -/
theorem table_observation_eq_of_rule5_commonReference_columns_eq
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (ownLeft ownRight commonReference : RS)
    (t1 t2 : LocalizedCumulativeDecoratedTree input carrierFuel)
    (hRule1a : (tables (LocalizedCumulativeRule45Stage.rule5 ownLeft commonReference) t1).rule1a =
      (tables (LocalizedCumulativeRule45Stage.rule5 ownRight commonReference) t2).rule1a)
    (hRule1b : (tables (LocalizedCumulativeRule45Stage.rule5 ownLeft commonReference) t1).rule1b =
      (tables (LocalizedCumulativeRule45Stage.rule5 ownRight commonReference) t2).rule1b)
    (hRule2 : (tables (LocalizedCumulativeRule45Stage.rule5 ownLeft commonReference) t1).rule2 =
      (tables (LocalizedCumulativeRule45Stage.rule5 ownRight commonReference) t2).rule2)
    (hDescriptor :
      (tables (LocalizedCumulativeRule45Stage.rule5 ownLeft commonReference) t1).descriptor =
      (tables (LocalizedCumulativeRule45Stage.rule5 ownRight commonReference) t2).descriptor) :
    observation t1 = observation t2 :=
  table_observation_eq_of_tables_eq
    (fun label => localizedCumulativeRule45Priority
      (LocalizedCumulativeRule45Stage.rule5 ownLeft commonReference) label)
    (fun label => localizedCumulativeRule45Priority
      (LocalizedCumulativeRule45Stage.rule5 ownRight commonReference) label)
    (fun left right same =>
      localizedCumulativeRule45Priority_rule5_commonReference_injective
        ownLeft ownRight commonReference left right same)
    t1 t2 (by simpa using hRule1a) (by simpa using hRule1b) (by simpa using hRule2)
    (by simpa using hDescriptor)

/-- **Decorated observation recovery for a common `rule5NoRule4bReference` stage.** -/
theorem table_observation_eq_of_rule5NoRule4bReference_columns_eq
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (reference : RS)
    (t1 t2 : LocalizedCumulativeDecoratedTree input carrierFuel)
    (hRule1a :
      (tables (LocalizedCumulativeRule45Stage.rule5NoRule4bReference reference) t1).rule1a =
      (tables (LocalizedCumulativeRule45Stage.rule5NoRule4bReference reference) t2).rule1a)
    (hRule1b :
      (tables (LocalizedCumulativeRule45Stage.rule5NoRule4bReference reference) t1).rule1b =
      (tables (LocalizedCumulativeRule45Stage.rule5NoRule4bReference reference) t2).rule1b)
    (hRule2 :
      (tables (LocalizedCumulativeRule45Stage.rule5NoRule4bReference reference) t1).rule2 =
      (tables (LocalizedCumulativeRule45Stage.rule5NoRule4bReference reference) t2).rule2)
    (hDescriptor :
      (tables (LocalizedCumulativeRule45Stage.rule5NoRule4bReference reference) t1).descriptor =
      (tables (LocalizedCumulativeRule45Stage.rule5NoRule4bReference reference) t2).descriptor) :
    observation t1 = observation t2 :=
  table_observation_eq_of_tables_eq
    (localizedCumulativeRule45Priority
      (LocalizedCumulativeRule45Stage.rule5NoRule4bReference reference))
    (localizedCumulativeRule45Priority
      (LocalizedCumulativeRule45Stage.rule5NoRule4bReference reference))
    (fun left right same =>
      localizedCumulativeRule45Priority_rule5NoRule4bReference_injective
        reference left right same)
    t1 t2 (by simpa using hRule1a) (by simpa using hRule1b) (by simpa using hRule2)
    (by simpa using hDescriptor)

/-- Same-stage form for a full `rule5` stage. -/
theorem table_observation_eq_of_tables_eq_rule5
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (ownReference rule5Reference : RS)
    (t1 t2 : LocalizedCumulativeDecoratedTree input carrierFuel)
    (same : tables (LocalizedCumulativeRule45Stage.rule5 ownReference rule5Reference) t1 =
      tables (LocalizedCumulativeRule45Stage.rule5 ownReference rule5Reference) t2) :
    observation t1 = observation t2 :=
  table_observation_eq_of_rule5_commonReference_columns_eq
    ownReference ownReference rule5Reference t1 t2
    (congrArg (fun entry => entry.rule1a) same)
    (congrArg (fun entry => entry.rule1b) same)
    (congrArg (fun entry => entry.rule2) same)
    (congrArg (fun entry => entry.descriptor) same)

/-! ## Kernel-authority guards -/

assert_kernel_only height
assert_kernel_only heightList
assert_kernel_only table_height_mk
assert_kernel_only table_heightList_nil
assert_kernel_only table_heightList_cons
assert_kernel_only height_le_heightList
assert_kernel_only height_lt_height_of_mem
assert_kernel_only one_le_height
assert_kernel_only exists_getElem?_height_gt_of_lt_heightList
assert_kernel_only foldl_max_length_eq_max
assert_kernel_only localizedTreeChildLayerCount_map_cons
assert_kernel_only localizedTreeChildLayerCount_map_eq_heightList
assert_kernel_only getD_root_cons
assert_kernel_only table_getD_zero
assert_kernel_only length_flatMap_zipIdx_prefixLayer_of_singleton
assert_kernel_only table_length_eq_height
assert_kernel_only table_getD_one_length
assert_kernel_only table_observe_root_eq
assert_kernel_only table_childCount_eq_of_table_eq
assert_kernel_only table_sphere_nonempty
assert_kernel_only table_tail_eq_merge
assert_kernel_only normalizedChildTable_tail_eq_table
assert_kernel_only table_shape_mk
assert_kernel_only table_observation_mk
assert_kernel_only table_shapeList_eq_map
assert_kernel_only table_observationList_eq_map
assert_kernel_only table_shape_eq_of_constitutional_tables_eq
assert_kernel_only table_observation_eq_of_tables_eq
assert_kernel_only table_shape_eq_of_columns_eq
assert_kernel_only table_shape_eq_of_tables_eq
assert_kernel_only table_observation_eq_of_rule5_commonReference_columns_eq
assert_kernel_only table_observation_eq_of_rule5NoRule4bReference_columns_eq
assert_kernel_only table_observation_eq_of_tables_eq_rule5

end LocalizedCumulativeDecoratedTree

end TetraStereo.OneCenter
