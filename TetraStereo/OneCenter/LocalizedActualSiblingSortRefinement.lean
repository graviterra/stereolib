import TetraStereo.OneCenter.LocalizedActualSiblingPhysicalKind
import TetraStereo.OneCenter.LocalizedSameStageKindComparison
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 100000










































namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput
open LocalizedCumulativeDecoratedTree
open SameStageKindComparison

namespace ActualSiblingSortRefinement

section Generic

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}

/-! ## The descriptor observation -/

/-- The cumulative Rule-4/5 observation that the descriptor column records at each occurrence. -/
def descriptorObservation (stage : LocalizedCumulativeRule45Stage)
    (node : LocalizedCumulativeDecoratedTree input carrierFuel) : List Nat :=
  localizedCumulativeRule45Priority stage node.label

/-! ## Alignment relations

A *row* is one addressed sparse sphere; a *table* is the list of spheres of one descriptor
column; *tables* are the compiled tables of the children of one node, in sorted sibling order. -/

/-- One sphere's entries are aligned at the shared stage. -/
abbrev RowAligned (stage : LocalizedCumulativeRule45Stage)
    (rowL rowR : List (OfficialSparseEntry (List Nat))) : Prop :=
  List.Forall₂ (FocusAligned stage) rowL rowR

/-- Two descriptor tables are aligned sphere by sphere. -/
abbrev TableAligned (stage : LocalizedCumulativeRule45Stage)
    (tableL tableR : List (List (OfficialSparseEntry (List Nat)))) : Prop :=
  List.Forall₂ (RowAligned stage) tableL tableR

/-- A list of child tables is aligned child by child. -/
abbrev TablesAligned (stage : LocalizedCumulativeRule45Stage)
    (tablesL tablesR : List (List (List (OfficialSparseEntry (List Nat))))) : Prop :=
  List.Forall₂ (TableAligned stage) tablesL tablesR

/-! ## List algebra for indexed alignment -/

/-- Pointwise lifting where the step is allowed to read the common sibling slot.  The left list is
fixed, so the lookup hypothesis is always taken in the *full* child list; the right list is
generalised because the recursion walks its suffixes. -/
theorem forall₂_imp_of_lookup_at {α β : Type*} {r s : α → β → Prop} (left : List α) :
    ∀ {right : List β}, List.Forall₂ r left right →
      (∀ (i : Nat) (a : α) (b : β), left[i]? = some a → right[i]? = some b → r a b → s a b) →
      List.Forall₂ s left right := by
  induction left with
  | nil =>
      intro right h step
      cases h with
      | nil => exact List.Forall₂.nil
  | cons head tail ih =>
      intro right h step
      cases h with
      | cons related rest =>
          refine List.Forall₂.cons (step 0 head _ rfl rfl related) (ih rest ?_)
          intro i a b atA atB
          exact step (i + 1) a b (by simpa using atA) (by simpa using atB)

/-- Pointwise lifting along a pointwise map of both sides. -/
theorem forall₂_map {α β γ δ : Type*} {r : α → β → Prop} {s : γ → δ → Prop}
    {f : α → γ} {g : β → δ} {left : List α} {right : List β}
    (h : List.Forall₂ r left right) (step : ∀ a b, r a b → s (f a) (g b)) :
    List.Forall₂ s (left.map f) (right.map g) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons head tail ih =>
      rw [List.map_cons, List.map_cons]
      exact List.Forall₂.cons (step _ _ head) ih

/-- Concatenation of aligned lists is aligned. -/
theorem forall₂_append {α β : Type*} {r : α → β → Prop}
    {leftL leftR : List α} {rightL rightR : List β}
    (first : List.Forall₂ r leftL rightL) (second : List.Forall₂ r leftR rightR) :
    List.Forall₂ r (leftL ++ leftR) (rightL ++ rightR) := by
  induction first with
  | nil => exact second
  | cons head tail ih => exact List.Forall₂.cons head ih

/-- Pointwise alignment over an explicit index range. -/
theorem forall₂_range'_map {α β : Type*} (r : α → β → Prop) (f : Nat → α) (g : Nat → β)
    (step : ∀ n, r (f n) (g n)) :
    ∀ (start count : Nat),
      List.Forall₂ r ((List.range' start count).map f) ((List.range' start count).map g)
  | _start, 0 => List.Forall₂.nil
  | start, count + 1 => by
      rw [List.range'_succ, List.map_cons, List.map_cons]
      exact List.Forall₂.cons (step start) (forall₂_range'_map r f g step (start + 1) count)

/-! ## Row and merge alignment -/

/-- A table aligned at every sphere stays aligned at every `getD` sphere. -/
theorem forall₂_getD {stage : LocalizedCumulativeRule45Stage}
    {tableL tableR : List (List (OfficialSparseEntry (List Nat)))}
    (aligned : TableAligned stage tableL tableR) (depth : Nat) :
    RowAligned stage (tableL.getD depth []) (tableR.getD depth []) := by
  induction aligned generalizing depth with
  | nil => exact List.Forall₂.nil
  | cons head tail ih =>
      cases depth with
      | zero => simpa using head
      | succ depth => simpa using ih depth

/-- Prefixing both sides of an aligned entry by one sibling slot keeps it aligned: the address
gains the same slot and every cumulative component is untouched. -/
theorem focusAligned_prefix {stage : LocalizedCumulativeRule45Stage} (slot : Nat)
    {left right : OfficialSparseEntry (List Nat)} (aligned : FocusAligned stage left right) :
    FocusAligned stage (slot :: left.1, left.2) (slot :: right.1, right.2) where
  addressEq := by rw [aligned.addressEq]
  lengthEq := aligned.lengthEq
  bound := aligned.bound
  before := aligned.before
  controlled := aligned.controlled

/-- Prefixing a whole aligned row by one sibling slot keeps it aligned. -/
theorem forall₂_prefixLayer {stage : LocalizedCumulativeRule45Stage} (slot : Nat)
    {rowL rowR : List (OfficialSparseEntry (List Nat))}
    (aligned : RowAligned stage rowL rowR) :
    RowAligned stage (OfficialRuleMajorKey.prefixLayer slot rowL)
      (OfficialRuleMajorKey.prefixLayer slot rowR) := by
  unfold OfficialRuleMajorKey.prefixLayer
  induction aligned with
  | nil => exact List.Forall₂.nil
  | cons head tail ih =>
      rw [List.map_cons, List.map_cons]
      exact List.Forall₂.cons (focusAligned_prefix slot head) ih

/-- Merging aligned child tables at one sphere preserves alignment.  The merge walks the children
in sorted sibling order, prefixes each child's block by that child's slot, and concatenates. -/
theorem forall₂_mergePairs {stage : LocalizedCumulativeRule45Stage}
    {tablesL tablesR : List (List (List (OfficialSparseEntry (List Nat))))}
    (aligned : TablesAligned stage tablesL tablesR) :
    ∀ (depth start : Nat),
      RowAligned stage
        (SparseAddress.mergePairs (tablesL.zipIdx start) (fun table => table.getD depth []))
        (SparseAddress.mergePairs (tablesR.zipIdx start) (fun table => table.getD depth [])) := by
  induction aligned with
  | nil =>
      intro depth start
      simp only [List.zipIdx_nil, SparseAddress.mergePairs, List.flatMap_nil]
      exact List.Forall₂.nil
  | cons head tail ih =>
      intro depth start
      simp only [List.zipIdx_cons, SparseAddress.mergePairs, List.flatMap_cons]
      exact forall₂_append (forall₂_prefixLayer start (forall₂_getD head depth))
        (ih depth (start + 1))

/-- The whole sphere table of a slot-indexed merge of aligned child tables is aligned. -/
theorem forall₂_mergePairTable {stage : LocalizedCumulativeRule45Stage}
    {tablesL tablesR : List (List (List (OfficialSparseEntry (List Nat))))}
    (aligned : TablesAligned stage tablesL tablesR) (count : Nat) :
    TableAligned stage
      (SparseAddress.mergePairTable tablesL.zipIdx id count)
      (SparseAddress.mergePairTable tablesR.zipIdx id count) := by
  unfold SparseAddress.mergePairTable
  rw [List.range_eq_range']
  exact forall₂_range'_map (RowAligned stage) _ _
    (fun depth => forall₂_mergePairs aligned depth 0) 0 count

/-- The layer count of pointwise length-equal child tables is the same on both sides. -/
theorem foldl_layerCount_eq {stage : LocalizedCumulativeRule45Stage}
    {tablesL tablesR : List (List (List (OfficialSparseEntry (List Nat))))}
    (aligned : TablesAligned stage tablesL tablesR) :
    ∀ (startL startR : Nat), startL = startR →
      tablesL.foldl (fun longest table => max longest table.length) startL =
        tablesR.foldl (fun longest table => max longest table.length) startR := by
  induction aligned with
  | nil => intro startL startR same; rw [same]
  | cons head tail ih =>
      intro startL startR same
      subst same
      simp only [List.foldl_cons]
      rw [List.Forall₂.length_eq head]
      exact ih _ _ rfl

/-- The merge width used by both actual tables agrees. -/
theorem localizedTreeChildLayerCount_eq {stage : LocalizedCumulativeRule45Stage}
    {tablesL tablesR : List (List (List (OfficialSparseEntry (List Nat))))}
    (aligned : TablesAligned stage tablesL tablesR) :
    localizedTreeChildLayerCount tablesL = localizedTreeChildLayerCount tablesR :=
  foldl_layerCount_eq aligned 0 0 rfl

/-- Merging aligned child tables preserves alignment at the actual merge width. -/
theorem mergeLocalizedTreeChildTables_forall₂ {stage : LocalizedCumulativeRule45Stage}
    {tablesL tablesR : List (List (List (OfficialSparseEntry (List Nat))))}
    (aligned : TablesAligned stage tablesL tablesR) :
    TableAligned stage
      (mergeLocalizedTreeChildTables tablesL) (mergeLocalizedTreeChildTables tablesR) := by
  unfold mergeLocalizedTreeChildTables
  rw [localizedTreeChildLayerCount_eq aligned]
  exact forall₂_mergePairTable aligned _

/-! ## Addressed label kinds -/

/-- Every actual subtree found by a root-first lookup carries a `none` or chiral label. -/
def AddressedNoneOrChiral (tree : LocalizedCumulativeDecoratedTree input carrierFuel) : Prop :=
  ∀ (addr : List Nat) (node : LocalizedCumulativeDecoratedTree input carrierFuel),
    subtreeAt? tree addr = some node → NoneOrChiral node.label

/-- At every raw address where both trees have a subtree, the two labels have the same `none`
status. -/
def AddressedSameKind (treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel) : Prop :=
  ∀ (addr : List Nat) (nodeL nodeR : LocalizedCumulativeDecoratedTree input carrierFuel),
    subtreeAt? treeL addr = some nodeL → subtreeAt? treeR addr = some nodeR →
      SameKind nodeL.label nodeR.label

/-- Addressed kinds restrict to any actual child found at a slot. -/
theorem addressedNoneOrChiral_of_child {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (kinds : AddressedNoneOrChiral tree) {slot : Nat}
    {child : LocalizedCumulativeDecoratedTree input carrierFuel}
    (lookup : tree.children[slot]? = some child) :
    AddressedNoneOrChiral child := by
  intro addr node atAddr
  exact kinds (slot :: addr) node (by
    rw [subtreeAt?_cons, lookup, Option.bind_some]
    exact atAddr)

/-- Addressed kind agreement restricts to the actual children at one common slot. -/
theorem addressedSameKind_of_child {treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (same : AddressedSameKind treeL treeR) {slot : Nat}
    {childL childR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (lookupL : treeL.children[slot]? = some childL)
    (lookupR : treeR.children[slot]? = some childR) :
    AddressedSameKind childL childR := by
  intro addr nodeL nodeR atL atR
  exact same (slot :: addr) nodeL nodeR
    (by rw [subtreeAt?_cons, lookupL, Option.bind_some]; exact atL)
    (by rw [subtreeAt?_cons, lookupR, Option.bind_some]; exact atR)

/-! ## From positions to addresses -/

/-- The all-position kind hypothesis is an addressed kind hypothesis. -/
theorem addressedNoneOrChiral_of_positions {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (kinds : ∀ p : Position tree, NoneOrChiral (positionNode p).label) :
    AddressedNoneOrChiral tree := by
  intro addr node atAddr
  have someTrue : (subtreeAt? tree addr).isSome = true := by rw [atAddr]; rfl
  have nodeEq : positionNode (⟨addr, someTrue⟩ : Position tree) = node := by
    have spec := positionNode_spec (⟨addr, someTrue⟩ : Position tree)
    rw [atAddr] at spec
    exact (Option.some.inj spec).symm
  rw [← nodeEq]
  exact kinds ⟨addr, someTrue⟩

/-- The matched-position kind hypothesis is an addressed kind-agreement hypothesis, because
`shapePositionEquiv` preserves the raw sibling-slot address. -/
theorem addressedSameKind_of_positions {treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (hshape : shape treeL = shape treeR)
    (same : ∀ p : Position treeL,
      SameKind (positionNode p).label (positionNode (shapePositionEquiv hshape p)).label) :
    AddressedSameKind treeL treeR := by
  intro addr nodeL nodeR atL atR
  have someL : (subtreeAt? treeL addr).isSome = true := by rw [atL]; rfl
  have nodeLEq : positionNode (⟨addr, someL⟩ : Position treeL) = nodeL := by
    have spec := positionNode_spec (⟨addr, someL⟩ : Position treeL)
    rw [atL] at spec
    exact (Option.some.inj spec).symm
  have imageVal : (shapePositionEquiv hshape (⟨addr, someL⟩ : Position treeL)).val = addr :=
    shapePositionEquiv_val hshape _
  have nodeREq :
      positionNode (shapePositionEquiv hshape (⟨addr, someL⟩ : Position treeL)) = nodeR := by
    have spec := positionNode_spec (shapePositionEquiv hshape (⟨addr, someL⟩ : Position treeL))
    rw [imageVal, atR] at spec
    exact (Option.some.inj spec).symm
  rw [← nodeLEq, ← nodeREq]
  exact same ⟨addr, someL⟩

/-! ## Table alignment from shape and label kinds -/

/-- Child tables of pointwise aligned children are pointwise aligned as tables. -/
theorem forall₂_table_of_forall₂ {stage : LocalizedCumulativeRule45Stage}
    {childrenL childrenR : List (LocalizedCumulativeDecoratedTree input carrierFuel)}
    (pairAligned : List.Forall₂ (fun a b => TableAligned stage
      (table (descriptorObservation stage) a) (table (descriptorObservation stage) b))
      childrenL childrenR) :
    TablesAligned stage
      (childrenL.map (table (descriptorObservation stage)))
      (childrenR.map (table (descriptorObservation stage))) := by
  induction pairAligned with
  | nil => exact List.Forall₂.nil
  | cons head tail ih =>
      rw [List.map_cons, List.map_cons]
      exact List.Forall₂.cons head ih

/-- **Generic table alignment.**  Two decorated trees with the same erased shape, only `none` or
chiral labels at every position of either tree, and the same `none` status at corresponding
positions have aligned descriptor tables. -/
theorem table_forall₂_focusAligned {stage : LocalizedCumulativeRule45Stage}
    {treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (hshape : shape treeL = shape treeR)
    (kindsL : AddressedNoneOrChiral treeL) (kindsR : AddressedNoneOrChiral treeR)
    (sameKind : AddressedSameKind treeL treeR) :
    TableAligned stage
      (table (descriptorObservation stage) treeL)
      (table (descriptorObservation stage) treeR) := by
  have main : ∀ n : Nat,
      ∀ tL : LocalizedCumulativeDecoratedTree input carrierFuel, height tL ≤ n →
        ∀ tR : LocalizedCumulativeDecoratedTree input carrierFuel,
          shape tL = shape tR → AddressedNoneOrChiral tL → AddressedNoneOrChiral tR →
            AddressedSameKind tL tR →
            TableAligned stage
              (table (descriptorObservation stage) tL)
              (table (descriptorObservation stage) tR) := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro k ih tL _bound tR hshapeTK kindsTL kindsTR sameTK
    cases tL with
    | mk sourceL atomicL distL massL labelL childrenL =>
      cases tR with
      | mk sourceR atomicR distR massR labelR childrenR =>
        rw [table_shape_mk sourceL atomicL distL massL labelL childrenL,
          table_shape_mk sourceR atomicR distR massR labelR childrenR] at hshapeTK
        have childrenEq : shapeList childrenL = shapeList childrenR :=
          congrArg LocalizedCumulativeBranchShape.children hshapeTK
        rw [table_shapeList_eq_map, table_shapeList_eq_map] at childrenEq
        have relShapes : List.Forall₂ (fun a b => shape a = shape b) childrenL childrenR :=
          forall₂_of_map_eq shape shape childrenEq
        have rootKindL : NoneOrChiral labelL := by
          have := kindsTL [] ⟨sourceL, atomicL, distL, massL, labelL, childrenL⟩ rfl
          simpa using this
        have rootKindR : NoneOrChiral labelR := by
          have := kindsTR [] ⟨sourceR, atomicR, distR, massR, labelR, childrenR⟩ rfl
          simpa using this
        have rootSame : SameKind labelL labelR := by
          have := sameTK [] ⟨sourceL, atomicL, distL, massL, labelL, childrenL⟩
            ⟨sourceR, atomicR, distR, massR, labelR, childrenR⟩ rfl rfl
          simpa using this
        have rootAligned :
            FocusAligned stage ([], localizedCumulativeRule45Priority stage labelL)
              ([], localizedCumulativeRule45Priority stage labelR) :=
          focusAligned_of_priority (stage := stage) [] rootKindL rootKindR rootSame
        have childPairAligned :
            List.Forall₂ (fun a b => TableAligned stage
              (table (descriptorObservation stage) a) (table (descriptorObservation stage) b))
              childrenL childrenR :=
          forall₂_imp_of_lookup_at childrenL relShapes
            (fun i a b atL atR related =>
              ih (height a) (by
                  have smaller := height_lt_height_of_mem
                    (⟨sourceL, atomicL, distL, massL, labelL, childrenL⟩ :
                      LocalizedCumulativeDecoratedTree input carrierFuel)
                    (List.mem_of_getElem? atL)
                  omega)
                a le_rfl b related
                (addressedNoneOrChiral_of_child kindsTL atL)
                (addressedNoneOrChiral_of_child kindsTR atR)
                (addressedSameKind_of_child sameTK atL atR))
        have childAligned := forall₂_table_of_forall₂ childPairAligned
        have mergedAligned := mergeLocalizedTreeChildTables_forall₂ childAligned
        rw [table_eq_root_merge, table_eq_root_merge]
        exact List.Forall₂.cons (List.Forall₂.cons rootAligned List.Forall₂.nil) mergedAligned
  exact main (height treeL) treeL le_rfl treeR hshape kindsL kindsR sameKind

/-- **Descriptor alignment of matched actual keys.**  Equal erased shape, both actual table
matches at one shared stage, `none`/chiral labels on both trees and matching `none` status at
corresponding positions give aligned descriptor columns of the two actual keys. -/
theorem descriptor_forall₂_of_tableMatch {stage : LocalizedCumulativeRule45Stage}
    {treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel}
    {keyL keyR : input.LocalizedRerootCumulativeRule45Key}
    (hshape : shape treeL = shape treeR)
    (matchL : LocalizedCumulativeTreeTableMatch stage treeL keyL)
    (matchR : LocalizedCumulativeTreeTableMatch stage treeR keyR)
    (kindsL : ∀ p : Position treeL, NoneOrChiral (positionNode p).label)
    (kindsR : ∀ p : Position treeR, NoneOrChiral (positionNode p).label)
    (sameKind : ∀ p : Position treeL,
      SameKind (positionNode p).label (positionNode (shapePositionEquiv hshape p)).label) :
    TableAligned stage keyL.descriptor keyR.descriptor := by
  have tables := table_forall₂_focusAligned (stage := stage) hshape
    (addressedNoneOrChiral_of_positions kindsL) (addressedNoneOrChiral_of_positions kindsR)
    (addressedSameKind_of_positions hshape sameKind)
  have leftEq : keyL.descriptor = table (descriptorObservation stage) treeL := by
    rw [← matchL.2.2.2, tables_descriptor]
    rfl
  have rightEq : keyR.descriptor = table (descriptorObservation stage) treeR := by
    rw [← matchR.2.2.2, tables_descriptor]
    rfl
  rw [leftEq, rightEq]
  exact tables

/-- **Full comparator equality at one shared stage.**  The production cumulative comparator on the
two actual keys equals the rule-major comparator at the cumulative width, under the generic
alignment hypotheses. -/
theorem compareLocalizedRerootCumulativeRule45Keys_eq_ruleMajorDescriptor_of_tableMatch
    (stage : LocalizedCumulativeRule45Stage)
    {treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel}
    {keyL keyR : input.LocalizedRerootCumulativeRule45Key}
    (hshape : shape treeL = shape treeR)
    (matchL : LocalizedCumulativeTreeTableMatch stage treeL keyL)
    (matchR : LocalizedCumulativeTreeTableMatch stage treeR keyR)
    (kindsL : ∀ p : Position treeL, NoneOrChiral (positionNode p).label)
    (kindsR : ∀ p : Position treeR, NoneOrChiral (positionNode p).label)
    (sameKind : ∀ p : Position treeL,
      SameKind (positionNode p).label (positionNode (shapePositionEquiv hshape p)).label) :
    input.compareLocalizedRerootCumulativeRule45Keys keyL keyR =
      compareRuleMajorCumulativeDescriptor input
        (localizedCumulativeRule45Priority stage none).length keyL keyR :=
  SameStageKindComparison.compareLocalizedRerootCumulativeRule45Keys_eq_ruleMajorDescriptor
    input stage
    (descriptor_forall₂_of_tableMatch hshape matchL matchR kindsL kindsR sameKind)

end Generic

section StrictOutcome

/-- **Strict constitutional short-circuit.**  Both comparators open with the *same* constitutional
comparison.  When that comparison is not a tie it decides both results, whatever the descriptor
columns are, so no alignment is needed.  This is what lets the physical endpoint drop any
tie hypothesis: only the tie case has to be routed through the matched-tree algebra. -/
theorem compareLocalizedRerootCumulativeRule45Keys_of_constitutional_ne
    (input : CertifiedLocalizedCIPInput) (width : Nat)
    {left right : input.LocalizedRerootCumulativeRule45Key}
    (notTie : OfficialRuleMajorKey.compare left.constitutional right.constitutional ≠ Ordering.eq) :
    input.compareLocalizedRerootCumulativeRule45Keys left right =
      compareRuleMajorCumulativeDescriptor input width left right := by
  show (Ordering.byKey (fun key => key.constitutional) OfficialRuleMajorKey.compare
        left right).then
      (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        left.descriptor right.descriptor) =
    (Ordering.byKey (fun key => key.constitutional) OfficialRuleMajorKey.compare
        left right).then
      (List.compareLex compare
        ((List.range width).map fun index =>
          OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
            (projectCumulative index left.descriptor)
            (projectCumulative index right.descriptor))
        ((List.range width).map fun _ => Ordering.eq))
  have byKeyEq :
      Ordering.byKey (fun key => key.constitutional) OfficialRuleMajorKey.compare left right =
        OfficialRuleMajorKey.compare left.constitutional right.constitutional := rfl
  rw [byKeyEq, SameStageKindComparison.ordering_then_self_of_ne_eq _ _ notTie,
    SameStageKindComparison.ordering_then_self_of_ne_eq _ _ notTie]

end StrictOutcome

section Physical

variable {reference : LocalizedUniversalReference.Input}










theorem actualSibling_compare_eq_ruleMajorDescriptor_of_tie
    (setup : ActualSlotPhysicalSetup reference)
    {tree : LocalizedCumulativeDecoratedTree reference.certified
      (LocalizedUniversalReference.carrierFuel reference)}
    (realizes : LocalizedCumulativeTreeRealizes reference.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader reference setup.c) tree)
    (reachable : reference.certified.ActualChildReachable setup.tree.source tree.source)
    (p : Position tree)
    {slotL slotR : Nat}
    (boundL : slotL < (positionNode p).children.length)
    (boundR : slotR < (positionNode p).children.length)
    (distinct : slotL ≠ slotR)
    (stage : LocalizedCumulativeRule45Stage)
    (fuelL fuelR : Nat)
    (keyL keyR : reference.certified.LocalizedRerootCumulativeRule45Key)
    (builtL : reference.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? stage
      (ActualReaderPhysicalBranchInverse.dependencyReader reference setup.c) fuelL
      (positionSource (positionChild p slotL boundL)) = some keyL)
    (builtR : reference.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? stage
      (ActualReaderPhysicalBranchInverse.dependencyReader reference setup.c) fuelR
      (positionSource (positionChild p slotR boundR)) = some keyR)
    (constitutionalTie :
      OfficialRuleMajorKey.compare keyL.constitutional keyR.constitutional = .eq) :
    reference.certified.compareLocalizedRerootCumulativeRule45Keys keyL keyR =
      compareRuleMajorCumulativeDescriptor reference.certified
        (localizedCumulativeRule45Priority stage none).length keyL keyR := by
  obtain ⟨tL, tR, hshape, _sourceL, _sourceR, matchL, matchR,
    _realizesL, _realizesR, labelsL, labelsR, sparseL, sparseR,
    noneIff, _chiralIff, _rule4aEq, _markedEq⟩ :=
    exists_actualSiblingPhysicalKind setup realizes reachable p boundL boundR distinct
      stage stage fuelL fuelR keyL keyR builtL builtR constitutionalTie
  refine compareLocalizedRerootCumulativeRule45Keys_eq_ruleMajorDescriptor_of_tableMatch
    (stage := stage) hshape matchL matchR ?_ ?_ noneIff
  · intro pL
    rcases sparseL pL with absent | ⟨descriptor, chiral⟩
    · exact Or.inl ((labelsL pL).trans absent)
    · exact Or.inr ⟨descriptor, (labelsL pL).trans chiral⟩
  · intro pR
    rcases sparseR pR with absent | ⟨descriptor, chiral⟩
    · exact Or.inl ((labelsR pR).trans absent)
    · exact Or.inr ⟨descriptor, (labelsR pR).trans chiral⟩

/-- **Actual physical sibling endpoint (no tie hypothesis).**  The same conclusion for *every*
pair of distinct same-parent siblings at any shared stage: when the constitutional comparison is
strict both comparators short-circuit to that same outcome, and when it ties the matched actual
trees decide.  No constitutional tie, no sorting success, no raw table or label-kind hypothesis is
assumed. -/
theorem actualSibling_compare_eq_ruleMajorDescriptor
    (setup : ActualSlotPhysicalSetup reference)
    {tree : LocalizedCumulativeDecoratedTree reference.certified
      (LocalizedUniversalReference.carrierFuel reference)}
    (realizes : LocalizedCumulativeTreeRealizes reference.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader reference setup.c) tree)
    (reachable : reference.certified.ActualChildReachable setup.tree.source tree.source)
    (p : Position tree)
    {slotL slotR : Nat}
    (boundL : slotL < (positionNode p).children.length)
    (boundR : slotR < (positionNode p).children.length)
    (distinct : slotL ≠ slotR)
    (stage : LocalizedCumulativeRule45Stage)
    (fuelL fuelR : Nat)
    (keyL keyR : reference.certified.LocalizedRerootCumulativeRule45Key)
    (builtL : reference.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? stage
      (ActualReaderPhysicalBranchInverse.dependencyReader reference setup.c) fuelL
      (positionSource (positionChild p slotL boundL)) = some keyL)
    (builtR : reference.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? stage
      (ActualReaderPhysicalBranchInverse.dependencyReader reference setup.c) fuelR
      (positionSource (positionChild p slotR boundR)) = some keyR) :
    reference.certified.compareLocalizedRerootCumulativeRule45Keys keyL keyR =
      compareRuleMajorCumulativeDescriptor reference.certified
        (localizedCumulativeRule45Priority stage none).length keyL keyR := by
  by_cases tie : OfficialRuleMajorKey.compare keyL.constitutional keyR.constitutional = Ordering.eq
  · exact actualSibling_compare_eq_ruleMajorDescriptor_of_tie setup realizes reachable p
      boundL boundR distinct stage fuelL fuelR keyL keyR builtL builtR tie
  · exact compareLocalizedRerootCumulativeRule45Keys_of_constitutional_ne
      reference.certified (localizedCumulativeRule45Priority stage none).length tie

end Physical

end ActualSiblingSortRefinement

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.ActualSiblingSortRefinement.descriptorObservation
assert_kernel_only TetraStereo.OneCenter.ActualSiblingSortRefinement.RowAligned
assert_kernel_only TetraStereo.OneCenter.ActualSiblingSortRefinement.TableAligned
assert_kernel_only TetraStereo.OneCenter.ActualSiblingSortRefinement.TablesAligned
assert_kernel_only TetraStereo.OneCenter.ActualSiblingSortRefinement.forall₂_imp_of_lookup_at
assert_kernel_only TetraStereo.OneCenter.ActualSiblingSortRefinement.forall₂_map
assert_kernel_only TetraStereo.OneCenter.ActualSiblingSortRefinement.forall₂_append
assert_kernel_only TetraStereo.OneCenter.ActualSiblingSortRefinement.forall₂_range'_map
assert_kernel_only TetraStereo.OneCenter.ActualSiblingSortRefinement.forall₂_getD
assert_kernel_only TetraStereo.OneCenter.ActualSiblingSortRefinement.focusAligned_prefix
assert_kernel_only TetraStereo.OneCenter.ActualSiblingSortRefinement.forall₂_prefixLayer
assert_kernel_only TetraStereo.OneCenter.ActualSiblingSortRefinement.forall₂_mergePairs
assert_kernel_only TetraStereo.OneCenter.ActualSiblingSortRefinement.forall₂_mergePairTable
assert_kernel_only TetraStereo.OneCenter.ActualSiblingSortRefinement.foldl_layerCount_eq
assert_kernel_only TetraStereo.OneCenter.ActualSiblingSortRefinement.localizedTreeChildLayerCount_eq
assert_kernel_only TetraStereo.OneCenter.ActualSiblingSortRefinement.mergeLocalizedTreeChildTables_forall₂
assert_kernel_only TetraStereo.OneCenter.ActualSiblingSortRefinement.AddressedNoneOrChiral
assert_kernel_only TetraStereo.OneCenter.ActualSiblingSortRefinement.AddressedSameKind
assert_kernel_only TetraStereo.OneCenter.ActualSiblingSortRefinement.addressedNoneOrChiral_of_child
assert_kernel_only TetraStereo.OneCenter.ActualSiblingSortRefinement.addressedSameKind_of_child
assert_kernel_only TetraStereo.OneCenter.ActualSiblingSortRefinement.addressedNoneOrChiral_of_positions
assert_kernel_only TetraStereo.OneCenter.ActualSiblingSortRefinement.addressedSameKind_of_positions
assert_kernel_only TetraStereo.OneCenter.ActualSiblingSortRefinement.forall₂_table_of_forall₂
assert_kernel_only TetraStereo.OneCenter.ActualSiblingSortRefinement.table_forall₂_focusAligned
assert_kernel_only TetraStereo.OneCenter.ActualSiblingSortRefinement.descriptor_forall₂_of_tableMatch
assert_kernel_only TetraStereo.OneCenter.ActualSiblingSortRefinement.compareLocalizedRerootCumulativeRule45Keys_eq_ruleMajorDescriptor_of_tableMatch
assert_kernel_only TetraStereo.OneCenter.ActualSiblingSortRefinement.compareLocalizedRerootCumulativeRule45Keys_of_constitutional_ne
assert_kernel_only TetraStereo.OneCenter.ActualSiblingSortRefinement.actualSibling_compare_eq_ruleMajorDescriptor_of_tie
assert_kernel_only TetraStereo.OneCenter.ActualSiblingSortRefinement.actualSibling_compare_eq_ruleMajorDescriptor
