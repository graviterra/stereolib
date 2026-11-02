import TetraStereo.OneCenter.LocalizedCumulativeKeyObservableOrder
import Mathlib.Data.List.GetD

set_option autoImplicit false

/-!
# Recovering child layers from a physical-slot prefix merge

`OfficialRuleMajorKey.mergeChildren` and the localized cumulative merges
(`mergeLocalizedRerootDescriptorChildren`, `mergeLocalizedRerootLabelChildren`) place the
`depth`-th sphere of every child beneath a *physical* address prefix equal to the child's position
in the sorted sibling list:

```
mergedLayer depth = children.zipIdx.flatMap fun child =>
  prefixLayer child.1 ((layers child.2).getD depth [])
```

The parent key then exposes `rootLayers ++ mergedLayers`, so a child sphere at child-depth `depth`
sits at parent-depth `depth + rootLayers.length`.

This module proves that the merge is *invertible at every physical slot*: the extraction operator
`stripSlot slot` keeps exactly the entries whose address head is `slot`, removes that head, and
leaves the original child layer untouched (the out-of-range padding default is `[]`).  The
inversion is a pure list identity, proved once for the generic `mergePrefixed` normal form and then
instantiated for the constitutional and cumulative-descriptor merges.

Two consequences are recorded for the cross-cursor Rule 4a ranked-projection argument:

* `stripSlot_getD_mergePrefixed_zero_ne_nil_iff` states that the nonempty slots of the first
  merged sphere are exactly `List.range children.length` whenever every child carries a nonempty
  first layer, giving a way to recover the child count from a node-root layer;
* `child_observable_eq_of_assembled_parent_observable_eq` proves that equality of two assembled
  parent observables forces equality of the child observable profiles at every common slot,
  provided the individual child layers are nonempty (the trailing-empty-layer ambiguity of
  `getD`-recovery is excluded).  `LocalizedKeyLayersNonempty` packages that nonemptiness, and
  `localizedKeyLayersNonempty_of_declarative` discharges it for every independently derived
  cumulative key.

The recursive cross-cursor key induction itself is deliberately *not* proved here; this module
only supplies the slot-inversion and profile-recovery steps it consumes.
-/

namespace TetraStereo.OneCenter

namespace CumulativeAssembly

open CertifiedLocalizedCIPInput

/-! ## The extraction operator -/

/-- Keep the addressed entries whose address begins with `slot`, and remove that leading slot.
Entries with empty addresses (the parent's own root observations) are discarded. -/
def stripSlot {α : Type*} (slot : ℕ) (layer : List (OfficialSparseEntry α)) :
    List (OfficialSparseEntry α) :=
  layer.filterMap fun entry =>
    match entry with
    | ([], _) => none
    | (head :: tail, value) => if head = slot then some (tail, value) else none

@[simp] theorem stripSlot_nil {α : Type*} (slot : ℕ) :
    stripSlot slot ([] : List (OfficialSparseEntry α)) = [] := rfl

/-- Extraction inverts the physical-slot prefix. -/
theorem stripSlot_prefixLayer {α : Type*} (slot : ℕ)
    (layer : List (OfficialSparseEntry α)) :
    stripSlot slot (OfficialRuleMajorKey.prefixLayer slot layer) = layer := by
  unfold stripSlot OfficialRuleMajorKey.prefixLayer
  rw [List.filterMap_map]
  simp only [Function.comp_def]
  have recombined :
      (fun entry : OfficialSparseEntry α => if True then some (entry.1, entry.2) else none) =
        some := by
    funext entry
    simp
  rw [recombined, List.filterMap_some]

/-- A layer prefixed by a different slot contributes nothing to `stripSlot slot`. -/
theorem stripSlot_prefixLayer_of_ne {α : Type*} {slot other : ℕ} (different : other ≠ slot)
    (layer : List (OfficialSparseEntry α)) :
    stripSlot slot (OfficialRuleMajorKey.prefixLayer other layer) = [] := by
  unfold stripSlot OfficialRuleMajorKey.prefixLayer
  rw [List.filterMap_map]
  simp [different]

/-- An append splits the extraction. -/
theorem stripSlot_append {α : Type*} (slot : ℕ)
    (left right : List (OfficialSparseEntry α)) :
    stripSlot slot (left ++ right) = stripSlot slot left ++ stripSlot slot right := by
  unfold stripSlot
  rw [List.filterMap_append]

/-- A flat map passes the extraction through to each batch. -/
theorem stripSlot_flatMap {α β : Type*} (slot : ℕ) (values : List β)
    (batch : β → List (OfficialSparseEntry α)) :
    stripSlot slot (values.flatMap batch) =
      values.flatMap fun value => stripSlot slot (batch value) := by
  unfold stripSlot
  rw [List.filterMap_flatMap]

/-- A layer whose addresses all lack a head (empty addresses) survives no slot. -/
theorem stripSlot_eq_nil_of_headless {α : Type*} {slot : ℕ}
    {layer : List (OfficialSparseEntry α)}
    (headless : ∀ entry ∈ layer, entry.1.head? = none) :
    stripSlot slot layer = [] := by
  unfold stripSlot
  rw [List.filterMap_eq_nil_iff]
  intro entry entryMem
  rcases entry with ⟨address, value⟩
  have empty := headless (address, value) entryMem
  cases address with
  | nil => rfl
  | cons head tail => simp at empty

/-! ## The generic prefixed merge -/

/-- Physical-slot prefix merge of already-projected child layers. This is the shared normal form of
`OfficialRuleMajorKey.mergeChildren` and the localized descriptor and label merges. -/
def mergePrefixed {β α : Type*} (children : List β)
    (layers : β → List (List (OfficialSparseEntry α))) :
    List (List (OfficialSparseEntry α)) :=
  let count := children.foldl (fun longest child => max longest (layers child).length) 0
  (List.range count).map fun depth =>
    children.zipIdx.flatMap fun child =>
      OfficialRuleMajorKey.prefixLayer child.2 ((layers child.1).getD depth [])

/-- The constitutional merge is exactly the generic prefixed merge. -/
theorem mergeChildren_eq_mergePrefixed {V α : Type*}
    (children : List (OfficialRuleMajorKey V))
    (layers : OfficialRuleMajorKey V → List (List (OfficialSparseEntry α))) :
    OfficialRuleMajorKey.mergeChildren children layers = mergePrefixed children layers := by
  unfold OfficialRuleMajorKey.mergeChildren OfficialRuleMajorKey.childLayerCount mergePrefixed
  rfl

/-! ## Indexing bookkeeping -/

/-- `getD` of a mapped range. -/
theorem getD_map_range {γ : Type*} (count depth : ℕ) (f : ℕ → γ) (fallback : γ) :
    ((List.range count).map f).getD depth fallback =
      if depth < count then f depth else fallback := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases inside : depth < count
  · rw [List.getElem?_range inside]
    simp [inside]
  · have absent : (List.range count)[depth]? = none :=
      List.getElem?_eq_none (by simpa using Nat.le_of_not_lt inside)
    rw [absent]
    simp [inside]

/-- Monotonicity of the folded maximum in the accumulator. -/
theorem le_foldl_max {β : Type*} (measure : β → ℕ) :
    ∀ (children : List β) (accumulator : ℕ),
      accumulator ≤ children.foldl (fun longest child => max longest (measure child)) accumulator
  | [], accumulator => Nat.le_refl accumulator
  | head :: tail, accumulator => by
      simp only [List.foldl_cons]
      exact Nat.le_trans (Nat.le_max_left accumulator (measure head))
        (le_foldl_max measure tail (max accumulator (measure head)))

/-- The folded maximum is monotone in its accumulator. -/
theorem foldl_max_mono {β : Type*} (measure : β → ℕ) :
    ∀ (children : List β) {accumulator other : ℕ}, accumulator ≤ other →
      children.foldl (fun longest child => max longest (measure child)) accumulator ≤
        children.foldl (fun longest child => max longest (measure child)) other
  | [], _, _, bound => bound
  | head :: tail, accumulator, other, bound => by
      simp only [List.foldl_cons]
      exact foldl_max_mono measure tail (by omega)

/-- Every member's measure is at most the folded maximum over the list. -/
theorem measure_le_foldl_max {β : Type*} (measure : β → ℕ) :
    ∀ (children : List β) (child : β), child ∈ children →
      measure child ≤ children.foldl (fun longest current => max longest (measure current)) 0
  | [], child, present => by simp at present
  | head :: tail, child, present => by
      rw [List.mem_cons] at present
      rcases present with same | tailPresent
      · subst same
        simp only [List.foldl_cons]
        exact Nat.le_trans (Nat.le_max_right 0 (measure child))
          (le_foldl_max measure tail (max 0 (measure child)))
      · simp only [List.foldl_cons]
        exact Nat.le_trans
          (measure_le_foldl_max measure tail child tailPresent)
          (foldl_max_mono measure tail (Nat.zero_le (measure head)))

/-- A depth below the folded maximum is reached by some child. -/
theorem exists_length_gt_of_lt_foldl_max {β : Type*} (measure : β → ℕ) :
    ∀ (children : List β) (accumulator depth : ℕ),
      depth < children.foldl (fun longest child => max longest (measure child)) accumulator →
        depth < accumulator ∨ ∃ child ∈ children, depth < measure child := by
  intro children
  induction children with
  | nil =>
      intro accumulator depth lower
      simp only [List.foldl_nil] at lower
      exact Or.inl lower
  | cons head tail inductionHypothesis =>
      intro accumulator depth lower
      simp only [List.foldl_cons] at lower
      rcases inductionHypothesis (max accumulator (measure head)) depth lower with
        bounded | found
      · by_cases accumulatorBound : depth < accumulator
        · exact Or.inl accumulatorBound
        · have headBound : depth < measure head := by omega
          exact Or.inr ⟨head, by simp, headBound⟩
      · rcases found with ⟨child, childMem, childBound⟩
        exact Or.inr ⟨child, by simp [childMem], childBound⟩

/-- A depth below the merged layer count is reached by some child layer. -/
theorem exists_length_gt_of_lt_layerCount {β α : Type*} (children : List β)
    (layers : β → List (List (OfficialSparseEntry α))) (depth : ℕ)
    (lower : depth <
      children.foldl (fun longest child => max longest (layers child).length) 0) :
    ∃ child ∈ children, depth < (layers child).length := by
  rcases exists_length_gt_of_lt_foldl_max (fun child => (layers child).length)
      children 0 depth lower with zeroBound | found
  · omega
  · exact found

/-- Reindexing a `zipIdx` correspondence by its starting offset. -/
theorem zipIdx_eq_map_add {β : Type*} (children : List β) (start : ℕ) :
    children.zipIdx start =
      (children.zipIdx).map (Prod.map id fun index => index + start) := by
  rw [List.zipIdx_eq_map_add]
  congr 1
  funext entry
  rcases entry with ⟨value, index⟩
  simp [Prod.map, Nat.add_comm]

/-- Selecting one `zipIdx` position out of a flat map: only the batch belonging to `slot`
survives, and it is the batch of the `slot`-th child (the empty list if there is none). -/
theorem zipIdx_flatMap_select {β γ : Type*} (children : List β) (batch : β → List γ) :
    ∀ slot : ℕ,
      (children.zipIdx.flatMap fun child =>
          if child.2 = slot then batch child.1 else []) =
        Option.rec [] batch children[slot]? := by
  intro slot
  induction slot generalizing children with
  | zero =>
      cases children with
      | nil => rfl
      | cons head tail =>
          rw [List.zipIdx_cons, List.flatMap_cons]
          have tailEmpty :
              (tail.zipIdx (0 + 1)).flatMap
                  (fun child => if child.2 = 0 then batch child.1 else []) = [] := by
            rw [List.flatMap_eq_nil_iff]
            intro child childMem
            have lower := List.le_snd_of_mem_zipIdx childMem
            have different : child.2 ≠ 0 := by omega
            simp [different]
          rw [tailEmpty, List.append_nil]
          simp
  | succ slot inductionHypothesis =>
      cases children with
      | nil => rfl
      | cons head tail =>
          rw [List.zipIdx_cons, List.flatMap_cons]
          have headEmpty : (if (0 : ℕ) = slot + 1 then batch head else []) = [] := by simp
          rw [headEmpty, List.nil_append]
          rw [zipIdx_eq_map_add tail 1, List.flatMap_map]
          have shifted :
              (tail.zipIdx.flatMap fun child =>
                  (if (Prod.map id (fun index => index + 1) child).2 = slot + 1
                    then batch (Prod.map id (fun index => index + 1) child).1
                    else [])) =
                (tail.zipIdx.flatMap fun child =>
                  if child.2 = slot then batch child.1 else []) := by
            apply List.flatMap_congr
            intro child _
            by_cases same : child.2 = slot
            · subst slot
              simp
            · have different : child.2 + 1 ≠ slot + 1 := by omega
              simp only [Prod.map_fst, Prod.map_snd, id_eq]
              rw [if_neg different, if_neg same]
          rw [shifted, inductionHypothesis tail]
          simp [List.getElem?_cons_succ]

/-! ## Inversion of the prefixed merge -/

/-- **Inverse of the physical-slot prefix merge.** Stripping slot `slot` from the merged sphere at
`depth` returns exactly the original child sphere at that depth; a missing child or an out-of-range
depth yields the empty padding layer. -/
theorem stripSlot_getD_mergePrefixed {β α : Type*} (children : List β)
    (layers : β → List (List (OfficialSparseEntry α))) (slot depth : ℕ) :
    stripSlot slot ((mergePrefixed children layers).getD depth []) =
      Option.rec [] (fun child => (layers child).getD depth []) children[slot]? := by
  unfold mergePrefixed
  rw [getD_map_range]
  by_cases inside : depth <
      children.foldl (fun longest child => max longest (layers child).length) 0
  · rw [if_pos inside, stripSlot_flatMap]
    have batch :
        (fun child : β × ℕ =>
            stripSlot slot
              (OfficialRuleMajorKey.prefixLayer child.2 ((layers child.1).getD depth []))) =
          (fun child : β × ℕ =>
            if child.2 = slot then (layers child.1).getD depth [] else []) := by
      funext child
      by_cases same : child.2 = slot
      · rw [if_pos same]
        rw [same]
        exact stripSlot_prefixLayer slot _
      · rw [if_neg same]
        exact stripSlot_prefixLayer_of_ne (by omega) _
    rw [batch]
    exact zipIdx_flatMap_select children (fun child => (layers child).getD depth []) slot
  · rw [if_neg inside]
    cases found : children[slot]? with
    | none => rfl
    | some child =>
        exact (List.getD_eq_default _ _
          (Nat.le_trans (measure_le_foldl_max (fun child => (layers child).length)
            children child (List.mem_of_getElem? found))
            (Nat.le_of_not_lt inside))).symm

/-- Bounded form of the inverse: an existing child slot exposes its exact layer. -/
theorem stripSlot_getD_mergePrefixed_of_lt {β α : Type*} (children : List β)
    (layers : β → List (List (OfficialSparseEntry α))) (slot depth : ℕ)
    (bound : slot < children.length) :
    stripSlot slot ((mergePrefixed children layers).getD depth []) =
      (layers (children[slot]'bound)).getD depth [] := by
  rw [stripSlot_getD_mergePrefixed, List.getElem?_eq_getElem bound]

/-- The first merged sphere has a nonempty slot exactly at the existing child positions, provided
every child carries a nonempty first layer. This recovers the child count from the merged layer. -/
theorem stripSlot_getD_mergePrefixed_zero_ne_nil_iff {β α : Type*} (children : List β)
    (layers : β → List (List (OfficialSparseEntry α))) (slot : ℕ)
    (childNonempty : ∀ child ∈ children, (layers child).getD 0 [] ≠ []) :
    stripSlot slot ((mergePrefixed children layers).getD 0 []) ≠ [] ↔
      slot < children.length := by
  constructor
  · intro nonempty
    by_contra outOfRange
    have absent : children[slot]? = none :=
      List.getElem?_eq_none (by simpa using Nat.le_of_not_lt outOfRange)
    rw [stripSlot_getD_mergePrefixed, absent] at nonempty
    exact nonempty rfl
  · intro bound
    rw [stripSlot_getD_mergePrefixed, List.getElem?_eq_getElem bound]
    exact childNonempty _ (List.getElem_mem bound)

/-- Appending layers leaves layers at and beyond the prefix length to the suffix. -/
theorem stripSlot_getD_append_right {α : Type*}
    (root merged : List (List (OfficialSparseEntry α))) (slot depth : ℕ)
    (bound : root.length ≤ depth) :
    stripSlot slot ((root ++ merged).getD depth []) =
      stripSlot slot (merged.getD (depth - root.length) []) := by
  rw [List.getD_append_right _ _ _ _ bound]

/-- A one-layer root prefix shifts every merged child sphere by exactly one depth. -/
theorem stripSlot_getD_succ_prefix {α : Type*}
    (rootLayers merged : List (List (OfficialSparseEntry α))) (slot depth : ℕ)
    (rootLength : rootLayers.length = 1) :
    stripSlot slot ((rootLayers ++ merged).getD (depth + 1) []) =
      stripSlot slot (merged.getD depth []) := by
  rw [stripSlot_getD_append_right _ _ _ _ (by omega), rootLength]
  simp

/-! ## Constitutional assembly instances -/

/-- The assembled Rule-1a layer at parent-depth `depth + 1` is the merged Rule-1a sphere at
child-depth `depth`. -/
theorem stripSlot_getD_assemble_rule1a {V : Type*} (root : OfficialRuleMajorKey V)
    (children : List (OfficialRuleMajorKey V)) (rootLength : root.rule1a.length = 1)
    (slot depth : ℕ) :
    stripSlot slot ((OfficialRuleMajorKey.assemble root children).rule1a.getD (depth + 1) []) =
      stripSlot slot
        ((OfficialRuleMajorKey.mergeChildren children OfficialRuleMajorKey.rule1a).getD
          depth []) := by
  unfold OfficialRuleMajorKey.assemble
  exact stripSlot_getD_succ_prefix root.rule1a _ slot depth rootLength

/-- The assembled Rule-1b layer at parent-depth `depth + 1` is the merged Rule-1b sphere at
child-depth `depth`. -/
theorem stripSlot_getD_assemble_rule1b {V : Type*} (root : OfficialRuleMajorKey V)
    (children : List (OfficialRuleMajorKey V)) (rootLength : root.rule1b.length = 1)
    (slot depth : ℕ) :
    stripSlot slot ((OfficialRuleMajorKey.assemble root children).rule1b.getD (depth + 1) []) =
      stripSlot slot
        ((OfficialRuleMajorKey.mergeChildren children OfficialRuleMajorKey.rule1b).getD
          depth []) := by
  unfold OfficialRuleMajorKey.assemble
  exact stripSlot_getD_succ_prefix root.rule1b _ slot depth rootLength

/-- The assembled Rule-2 layer at parent-depth `depth + 1` is the merged Rule-2 sphere at
child-depth `depth`. -/
theorem stripSlot_getD_assemble_rule2 {V : Type*} (root : OfficialRuleMajorKey V)
    (children : List (OfficialRuleMajorKey V)) (rootLength : root.rule2.length = 1)
    (slot depth : ℕ) :
    stripSlot slot ((OfficialRuleMajorKey.assemble root children).rule2.getD (depth + 1) []) =
      stripSlot slot
        ((OfficialRuleMajorKey.mergeChildren children OfficialRuleMajorKey.rule2).getD
          depth []) := by
  unfold OfficialRuleMajorKey.assemble
  exact stripSlot_getD_succ_prefix root.rule2 _ slot depth rootLength

/-- Slot inversion on the assembled Rule-1a projection: an existing child slot exposes its exact
Rule-1a sphere at that depth. -/
theorem stripSlot_getD_assemble_rule1a_child {V : Type*} (root : OfficialRuleMajorKey V)
    (children : List (OfficialRuleMajorKey V)) (rootLength : root.rule1a.length = 1)
    (slot depth : ℕ) (bound : slot < children.length) :
    stripSlot slot ((OfficialRuleMajorKey.assemble root children).rule1a.getD (depth + 1) []) =
      (children[slot]'bound).rule1a.getD depth [] := by
  rw [stripSlot_getD_assemble_rule1a root children rootLength slot depth,
    mergeChildren_eq_mergePrefixed, stripSlot_getD_mergePrefixed_of_lt _ _ _ _ bound]

/-- Slot inversion on the assembled Rule-1b projection. -/
theorem stripSlot_getD_assemble_rule1b_child {V : Type*} (root : OfficialRuleMajorKey V)
    (children : List (OfficialRuleMajorKey V)) (rootLength : root.rule1b.length = 1)
    (slot depth : ℕ) (bound : slot < children.length) :
    stripSlot slot ((OfficialRuleMajorKey.assemble root children).rule1b.getD (depth + 1) []) =
      (children[slot]'bound).rule1b.getD depth [] := by
  rw [stripSlot_getD_assemble_rule1b root children rootLength slot depth,
    mergeChildren_eq_mergePrefixed, stripSlot_getD_mergePrefixed_of_lt _ _ _ _ bound]

/-- Slot inversion on the assembled Rule-2 projection. -/
theorem stripSlot_getD_assemble_rule2_child {V : Type*} (root : OfficialRuleMajorKey V)
    (children : List (OfficialRuleMajorKey V)) (rootLength : root.rule2.length = 1)
    (slot depth : ℕ) (bound : slot < children.length) :
    stripSlot slot ((OfficialRuleMajorKey.assemble root children).rule2.getD (depth + 1) []) =
      (children[slot]'bound).rule2.getD depth [] := by
  rw [stripSlot_getD_assemble_rule2 root children rootLength slot depth,
    mergeChildren_eq_mergePrefixed, stripSlot_getD_mergePrefixed_of_lt _ _ _ _ bound]

/-! ## From depthwise layer equality to list equality -/

/-- Two layer lists with nonempty layers are equal as soon as all `getD` readings agree. The
nonemptiness hypothesis removes the trailing-empty-layer ambiguity of `getD`: it is *not* an
equality assumption on the layers themselves. -/
theorem eq_of_forall_getD_eq_of_layers_nonempty {α : Type*}
    {left right : List (List α)}
    (depthwise : ∀ depth : ℕ, left.getD depth [] = right.getD depth [])
    (leftNonempty : ∀ layer ∈ left, layer ≠ [])
    (rightNonempty : ∀ layer ∈ right, layer ≠ []) :
    left = right := by
  have sameLength : left.length = right.length := by
    by_contra different
    rcases Nat.lt_or_gt_of_ne different with shorter | shorter
    · have present : right[left.length]? = some right[left.length] :=
        List.getElem?_eq_getElem shorter
      have reading := depthwise left.length
      rw [List.getD_eq_default _ _ (Nat.le_refl _),
        List.getD_eq_getElem _ _ shorter] at reading
      have empty : right[left.length] = [] := reading.symm
      exact rightNonempty _ (List.getElem_mem shorter) empty
    · have present : left[right.length]? = some left[right.length] :=
        List.getElem?_eq_getElem shorter
      have reading := depthwise right.length
      rw [List.getD_eq_default _ _ (Nat.le_refl _),
        List.getD_eq_getElem _ _ shorter] at reading
      have empty : left[right.length] = [] := reading
      exact leftNonempty _ (List.getElem_mem shorter) empty
  apply List.ext_getElem
  · exact sameLength
  · intro index leftBound rightBound
    have reading := depthwise index
    rwa [List.getD_eq_getElem _ _ leftBound, List.getD_eq_getElem _ _ rightBound] at reading

/-- Every layer of a prefixed merge is nonempty when every child layer is. -/
theorem mergePrefixed_layers_nonempty {β α : Type*} (children : List β)
    (layers : β → List (List (OfficialSparseEntry α)))
    (childNonempty : ∀ child ∈ children, ∀ layer ∈ layers child, layer ≠ []) :
    ∀ layer ∈ mergePrefixed children layers, layer ≠ [] := by
  intro layer layerMem
  unfold mergePrefixed at layerMem
  rw [List.mem_map] at layerMem
  rcases layerMem with ⟨depth, depthMem, rfl⟩
  rw [List.mem_range] at depthMem
  have scaled : depth <
      children.foldl (fun longest child => max longest (layers child).length) 0 := depthMem
  rcases exists_length_gt_of_lt_layerCount children layers depth scaled with
    ⟨child, childMem, childDepth⟩
  have childLayerNonempty : (layers child).getD depth [] ≠ [] := by
    rw [List.getD_eq_getElem _ _ childDepth]
    exact childNonempty child childMem _ (List.getElem_mem childDepth)
  have batchNonempty : ∀ position : ℕ,
      OfficialRuleMajorKey.prefixLayer position ((layers child).getD depth []) ≠ [] := by
    intro position empty
    apply childLayerNonempty
    have mapped : OfficialRuleMajorKey.prefixLayer position ((layers child).getD depth []) =
        ((layers child).getD depth []).map
          (fun entry => (position :: entry.1, entry.2)) := rfl
    rw [mapped, List.map_eq_nil_iff] at empty
    exact empty
  rcases List.mem_iff_getElem?.mp childMem with ⟨position, positionLookup⟩
  have pairMem : (child, position) ∈ children.zipIdx :=
    List.mk_mem_zipIdx_iff_getElem?.mpr positionLookup
  intro empty
  have allEmpty := List.flatMap_eq_nil_iff.mp empty
  exact batchNonempty position (allEmpty (child, position) pairMem)

/-! ## Cumulative-key instances of the prefixed merge -/

/-- The cumulative descriptor merge is the generic prefixed merge with each child's descriptor as
its layer list. -/
theorem mergeDescriptorChildren_eq_mergePrefixed
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    input.mergeLocalizedRerootDescriptorChildren children =
      mergePrefixed children (fun child => child.descriptor) :=
  rfl

/-- The exact-label merge is the generic prefixed merge with each child's label spheres. -/
theorem mergeLabelChildren_eq_mergePrefixed
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    input.mergeLocalizedRerootLabelChildren children =
      mergePrefixed children (fun child => child.labels) :=
  rfl

/-- Extraction inverts the cumulative descriptor merge at every physical slot. -/
theorem stripSlot_getD_mergeDescriptorChildren
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key)
    (slot depth : ℕ) :
    stripSlot slot
        ((input.mergeLocalizedRerootDescriptorChildren children).getD depth []) =
      Option.rec [] (fun child => child.descriptor.getD depth []) children[slot]? := by
  unfold mergeLocalizedRerootDescriptorChildren
  rw [getD_map_range]
  by_cases inside : depth < input.localizedRerootDescriptorChildLayerCount children
  · rw [if_pos inside, stripSlot_flatMap]
    have batch :
        (fun child : input.LocalizedRerootCumulativeRule45Key × ℕ =>
            stripSlot slot
              (OfficialRuleMajorKey.prefixLayer child.2
                (child.1.descriptor.getD depth []))) =
          (fun child : input.LocalizedRerootCumulativeRule45Key × ℕ =>
            if child.2 = slot then child.1.descriptor.getD depth [] else []) := by
      funext child
      by_cases same : child.2 = slot
      · rw [if_pos same, same]
        exact stripSlot_prefixLayer slot _
      · rw [if_neg same]
        exact stripSlot_prefixLayer_of_ne (by omega) _
    rw [batch]
    rw [zipIdx_flatMap_select children (fun child => child.descriptor.getD depth []) slot]
  · rw [if_neg inside]
    cases found : children[slot]? with
    | none => rfl
    | some child =>
        exact (List.getD_eq_default _ _
          (Nat.le_trans
            (measure_le_foldl_max (fun child => child.descriptor.length) children child
              (List.mem_of_getElem? found))
            (Nat.le_of_not_lt inside))).symm

/-- Bounded extraction inverts the cumulative descriptor merge at an existing child slot. -/
theorem stripSlot_getD_mergeDescriptorChildren_of_lt
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key)
    (slot depth : ℕ) (bound : slot < children.length) :
    stripSlot slot
        ((input.mergeLocalizedRerootDescriptorChildren children).getD depth []) =
      (children[slot]'bound).descriptor.getD depth [] := by
  rw [stripSlot_getD_mergeDescriptorChildren input children slot depth,
    List.getElem?_eq_getElem bound]

/-- Extraction inverts the exact-label merge at every physical slot. -/
theorem stripSlot_getD_mergeLabelChildren
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key)
    (slot depth : ℕ) :
    stripSlot slot
        ((input.mergeLocalizedRerootLabelChildren children).getD depth []) =
      Option.rec [] (fun child => child.labels.getD depth []) children[slot]? := by
  unfold mergeLocalizedRerootLabelChildren
  rw [getD_map_range]
  by_cases inside : depth < input.localizedRerootLabelChildLayerCount children
  · rw [if_pos inside, stripSlot_flatMap]
    have batch :
        (fun child : input.LocalizedRerootCumulativeRule45Key × ℕ =>
            stripSlot slot
              (OfficialRuleMajorKey.prefixLayer child.2
                (child.1.labels.getD depth []))) =
          (fun child : input.LocalizedRerootCumulativeRule45Key × ℕ =>
            if child.2 = slot then child.1.labels.getD depth [] else []) := by
      funext child
      by_cases same : child.2 = slot
      · rw [if_pos same, same]
        exact stripSlot_prefixLayer slot _
      · rw [if_neg same]
        exact stripSlot_prefixLayer_of_ne (by omega) _
    rw [batch]
    rw [zipIdx_flatMap_select children (fun child => child.labels.getD depth []) slot]
  · rw [if_neg inside]
    cases found : children[slot]? with
    | none => rfl
    | some child =>
        exact (List.getD_eq_default _ _
          (Nat.le_trans
            (measure_le_foldl_max (fun child => child.labels.length) children child
              (List.mem_of_getElem? found))
            (Nat.le_of_not_lt inside))).symm

/-- Bounded extraction inverts the exact-label merge at an existing child slot. -/
theorem stripSlot_getD_mergeLabelChildren_of_lt
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key)
    (slot depth : ℕ) (bound : slot < children.length) :
    stripSlot slot
        ((input.mergeLocalizedRerootLabelChildren children).getD depth []) =
      (children[slot]'bound).labels.getD depth [] := by
  rw [stripSlot_getD_mergeLabelChildren input children slot depth,
    List.getElem?_eq_getElem bound]

/-- The nonempty slots of the first cumulative descriptor sphere are exactly the child positions,
provided every child has a nonempty first descriptor sphere. -/
theorem stripSlot_getD_mergeDescriptorChildren_zero_ne_nil_iff
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key) (slot : ℕ)
    (childNonempty : ∀ child ∈ children, child.descriptor.getD 0 [] ≠ []) :
    stripSlot slot
        ((input.mergeLocalizedRerootDescriptorChildren children).getD 0 []) ≠ [] ↔
      slot < children.length := by
  rw [mergeDescriptorChildren_eq_mergePrefixed input children]
  exact stripSlot_getD_mergePrefixed_zero_ne_nil_iff children
    (fun child => child.descriptor) slot childNonempty

/-! ## Nonemptiness of constructed key layers -/

/-- The observations of a cumulative key that the comparator can read all have nonempty layers.
This is the only additional fact needed for `getD` inversion to lose no trailing layers. -/
structure LocalizedKeyLayersNonempty
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootCumulativeRule45Key) : Prop where
  /-- Every Rule-1a sphere of the constitutional projection is nonempty. -/
  rule1a : ∀ layer ∈ key.constitutional.rule1a, layer ≠ []
  /-- Every Rule-1b sphere of the constitutional projection is nonempty. -/
  rule1b : ∀ layer ∈ key.constitutional.rule1b, layer ≠ []
  /-- Every Rule-2 sphere of the constitutional projection is nonempty. -/
  rule2 : ∀ layer ∈ key.constitutional.rule2, layer ≠ []
  /-- Every cumulative descriptor sphere is nonempty. -/
  descriptor : ∀ layer ∈ key.descriptor, layer ≠ []
  /-- The cumulative descriptor projection itself is present. -/
  descriptorPresent : key.descriptor ≠ []

/-- A single-sphere layer list carries only nonempty spheres. -/
theorem singleton_layers_nonempty {α : Type*} (entry : OfficialSparseEntry α) :
    ∀ layer ∈ ([ [entry] ] : List (List (OfficialSparseEntry α))), layer ≠ [] := by
  intro layer present
  rw [List.mem_singleton] at present
  cases present
  simp

/-- The Rule-1a layers of an atom-labelled root key are nonempty. -/
theorem rootKey_rule1a_layers_nonempty {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (node : OfficialCIPNode V) (complete : Bool) :
    ∀ layer ∈ (m.officialRuleMajorRootKey node complete).rule1a, layer ≠ [] := by
  have expanded : (m.officialRuleMajorRootKey node complete).rule1a =
      [ [(([], (ofLex (m.officialNodeAtomLabel node)).1))] ] := rfl
  rw [expanded]
  exact singleton_layers_nonempty _

/-- The Rule-1b layers of an atom-labelled root key are nonempty. -/
theorem rootKey_rule1b_layers_nonempty {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (node : OfficialCIPNode V) (complete : Bool) :
    ∀ layer ∈ (m.officialRuleMajorRootKey node complete).rule1b, layer ≠ [] := by
  have expanded : (m.officialRuleMajorRootKey node complete).rule1b =
      [ [(([], node.rule1bRootDistance))] ] := rfl
  rw [expanded]
  exact singleton_layers_nonempty _

/-- The Rule-2 layers of an atom-labelled root key are nonempty. -/
theorem rootKey_rule2_layers_nonempty {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (node : OfficialCIPNode V) (complete : Bool) :
    ∀ layer ∈ (m.officialRuleMajorRootKey node complete).rule2, layer ≠ [] := by
  have expanded : (m.officialRuleMajorRootKey node complete).rule2 =
      [ [(([], (ofLex (m.officialNodeAtomLabel node)).2))] ] := rfl
  rw [expanded]
  exact singleton_layers_nonempty _

/-- Prefixed child merges preserve layerwise nonemptiness for any projection. -/
theorem mergeChildren_projection_layers_nonempty {V α : Type*}
    (children : List (OfficialRuleMajorKey V))
    (layers : OfficialRuleMajorKey V → List (List (OfficialSparseEntry α)))
    (childNonempty : ∀ child ∈ children, ∀ layer ∈ layers child, layer ≠ []) :
    ∀ layer ∈ OfficialRuleMajorKey.mergeChildren children layers, layer ≠ [] := by
  rw [mergeChildren_eq_mergePrefixed]
  exact mergePrefixed_layers_nonempty children layers childNonempty

/-- The cumulative descriptor merge preserves layerwise nonemptiness. -/
theorem mergeDescriptorChildren_layers_nonempty
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key)
    (childNonempty : ∀ child ∈ children, ∀ layer ∈ child.descriptor, layer ≠ []) :
    ∀ layer ∈ input.mergeLocalizedRerootDescriptorChildren children, layer ≠ [] := by
  rw [mergeDescriptorChildren_eq_mergePrefixed input children]
  exact mergePrefixed_layers_nonempty children (fun child => child.descriptor) childNonempty

/-- A terminal cumulative key satisfies `LocalizedKeyLayersNonempty`. -/
theorem localizedKeyLayersNonempty_terminal
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (label : Option LocalizedAuxiliaryLabel) :
    LocalizedKeyLayersNonempty input
      { constitutional := input.moleculeGraph.officialRuleMajorRootKey
          cursor.occurrence.1.node true
        descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
        labels := [[([], label)]]
        rankedLabels := [[([], label)]] } := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact rootKey_rule1a_layers_nonempty _ _ _
  · exact rootKey_rule1b_layers_nonempty _ _ _
  · exact rootKey_rule2_layers_nonempty _ _ _
  · exact singleton_layers_nonempty _
  · simp

/-- A branch cumulative key satisfies `LocalizedKeyLayersNonempty` whenever all its children do. -/
theorem localizedKeyLayersNonempty_branch
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (label : Option LocalizedAuxiliaryLabel)
    (sorted : List input.LocalizedRerootCumulativeRule45Key)
    (childNonempty : ∀ child ∈ sorted, LocalizedKeyLayersNonempty input child) :
    LocalizedKeyLayersNonempty input
      { constitutional := OfficialRuleMajorKey.assemble
          (input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node false)
          (sorted.map fun child => child.constitutional)
        descriptor := [[([], localizedCumulativeRule45Priority stage label)]] ++
          input.mergeLocalizedRerootDescriptorChildren sorted
        labels := [[([], label)]] ++ input.mergeLocalizedRerootLabelChildren sorted
        rankedLabels := [[([], label)]] ++
          input.mergeLocalizedRerootRankedLabelChildren sorted } := by
  have childMajor :
      ∀ (rule : OfficialRuleMajorKey input.Atom → List (List (OfficialSparseEntry ℕ))),
        (∀ child ∈ sorted, ∀ layer ∈ rule child.constitutional, layer ≠ []) →
        ∀ majorChild ∈ sorted.map (fun child => child.constitutional),
          ∀ layer ∈ rule majorChild, layer ≠ [] := by
    intro rule ruleNonempty majorChild majorMem layer inLayer
    rcases List.mem_map.mp majorMem with ⟨child, childMem, same⟩
    cases same
    exact ruleNonempty child childMem layer inLayer
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro layer present
    rw [show (OfficialRuleMajorKey.assemble
        (input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node false)
        (sorted.map fun child => child.constitutional)).rule1a =
      (input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node false).rule1a ++
        OfficialRuleMajorKey.mergeChildren
          (sorted.map fun child => child.constitutional)
          OfficialRuleMajorKey.rule1a from rfl] at present
    rw [List.mem_append] at present
    rcases present with inRoot | inMerged
    · exact rootKey_rule1a_layers_nonempty _ _ _ layer inRoot
    · exact mergeChildren_projection_layers_nonempty _
        OfficialRuleMajorKey.rule1a
        (childMajor OfficialRuleMajorKey.rule1a
          (fun child childMem layer inLayer =>
            (childNonempty child childMem).rule1a layer inLayer))
        layer inMerged
  · intro layer present
    rw [show (OfficialRuleMajorKey.assemble
        (input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node false)
        (sorted.map fun child => child.constitutional)).rule1b =
      (input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node false).rule1b ++
        OfficialRuleMajorKey.mergeChildren
          (sorted.map fun child => child.constitutional)
          OfficialRuleMajorKey.rule1b from rfl] at present
    rw [List.mem_append] at present
    rcases present with inRoot | inMerged
    · exact rootKey_rule1b_layers_nonempty _ _ _ layer inRoot
    · exact mergeChildren_projection_layers_nonempty _
        OfficialRuleMajorKey.rule1b
        (childMajor OfficialRuleMajorKey.rule1b
          (fun child childMem layer inLayer =>
            (childNonempty child childMem).rule1b layer inLayer))
        layer inMerged
  · intro layer present
    rw [show (OfficialRuleMajorKey.assemble
        (input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node false)
        (sorted.map fun child => child.constitutional)).rule2 =
      (input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node false).rule2 ++
        OfficialRuleMajorKey.mergeChildren
          (sorted.map fun child => child.constitutional)
          OfficialRuleMajorKey.rule2 from rfl] at present
    rw [List.mem_append] at present
    rcases present with inRoot | inMerged
    · exact rootKey_rule2_layers_nonempty _ _ _ layer inRoot
    · exact mergeChildren_projection_layers_nonempty _
        OfficialRuleMajorKey.rule2
        (childMajor OfficialRuleMajorKey.rule2
          (fun child childMem layer inLayer =>
            (childNonempty child childMem).rule2 layer inLayer))
        layer inMerged
  · intro layer present
    rw [List.mem_append] at present
    rcases present with inRoot | inMerged
    · exact singleton_layers_nonempty _ layer inRoot
    · exact mergeDescriptorChildren_layers_nonempty input sorted
        (fun child childMem layer inLayer =>
          (childNonempty child childMem).descriptor layer inLayer)
        layer inMerged
  · simp

/-! ## Recovering child observations from an assembled parent -/

/-- Equal first child layers make the child count recoverable from the parent descriptor
projection.  The nonemptiness hypotheses are the first-sphere premises of the merge inversion; no
claim about child equality is assumed. -/
theorem not_lt_length_of_parent_descriptor_eq
    (input : CertifiedLocalizedCIPInput)
    (descriptorRoot : List (List (OfficialSparseEntry (List ℕ))))
    (descriptorRootLength : descriptorRoot.length = 1)
    (left right : List input.LocalizedRerootCumulativeRule45Key)
    (rightFirstNonempty : ∀ child ∈ right, child.descriptor.getD 0 [] ≠ [])
    (parentDescriptor : descriptorRoot ++ input.mergeLocalizedRerootDescriptorChildren left =
      descriptorRoot ++ input.mergeLocalizedRerootDescriptorChildren right) :
    ¬ left.length < right.length := by
  intro shorter
  have merged : input.mergeLocalizedRerootDescriptorChildren left =
      input.mergeLocalizedRerootDescriptorChildren right :=
    List.append_cancel_left parentDescriptor
  have atDepth :
      (descriptorRoot ++ input.mergeLocalizedRerootDescriptorChildren left).getD (0 + 1) [] =
        (descriptorRoot ++ input.mergeLocalizedRerootDescriptorChildren right).getD
          (0 + 1) [] := by
    rw [merged]
  have stripped := congrArg (stripSlot left.length) atDepth
  rw [stripSlot_getD_succ_prefix descriptorRoot _ left.length 0 descriptorRootLength,
    stripSlot_getD_succ_prefix descriptorRoot _ left.length 0 descriptorRootLength] at stripped
  have leftEmpty :
      stripSlot left.length
          ((input.mergeLocalizedRerootDescriptorChildren left).getD 0 []) = [] := by
    rw [stripSlot_getD_mergeDescriptorChildren input left left.length 0]
    rw [List.getElem?_eq_none (Nat.le_refl left.length)]
  have rightPresent :
      stripSlot left.length
          ((input.mergeLocalizedRerootDescriptorChildren right).getD 0 []) ≠ [] := by
    rw [stripSlot_getD_mergeDescriptorChildren input right left.length 0]
    rw [List.getElem?_eq_getElem shorter]
    exact rightFirstNonempty _ (List.getElem_mem shorter)
  rw [leftEmpty] at stripped
  exact rightPresent stripped.symm

/-- **Child-count recovery.** If the two assembled parent descriptor projections agree and both
child lists start with nonempty descriptor spheres, then the child lists have equal length. -/
theorem child_length_eq_of_parent_descriptor_eq
    (input : CertifiedLocalizedCIPInput)
    (descriptorRoot : List (List (OfficialSparseEntry (List ℕ))))
    (descriptorRootLength : descriptorRoot.length = 1)
    (left right : List input.LocalizedRerootCumulativeRule45Key)
    (leftFirstNonempty : ∀ child ∈ left, child.descriptor.getD 0 [] ≠ [])
    (rightFirstNonempty : ∀ child ∈ right, child.descriptor.getD 0 [] ≠ [])
    (parentDescriptor : descriptorRoot ++ input.mergeLocalizedRerootDescriptorChildren left =
      descriptorRoot ++ input.mergeLocalizedRerootDescriptorChildren right) :
    left.length = right.length := by
  have rightLe : right.length ≤ left.length := by
    by_contra notLe
    exact not_lt_length_of_parent_descriptor_eq input descriptorRoot descriptorRootLength
      left right rightFirstNonempty parentDescriptor (Nat.lt_of_not_le notLe)
  have leftLe : left.length ≤ right.length := by
    by_contra notLe
    exact not_lt_length_of_parent_descriptor_eq input descriptorRoot descriptorRootLength
      right left leftFirstNonempty parentDescriptor.symm (Nat.lt_of_not_le notLe)
  exact Nat.le_antisymm leftLe rightLe

/-- **Pointwise child-observable recovery.** Equality of two assembled parent observables forces
equality of the cumulative observable profile of the children in every common physical slot,
provided the two child lists have the same length and their comparison-visible layers are nonempty.
The equality is recovered independently for Rule 1a, Rule 1b, Rule 2 and the cumulative descriptor;
the constitutional source-node and completeness fields never occur. -/
theorem child_observable_eq_of_assembled_parent_observable_eq
    (input : CertifiedLocalizedCIPInput)
    (root : OfficialRuleMajorKey input.Atom)
    (rootRule1a : root.rule1a.length = 1)
    (rootRule1b : root.rule1b.length = 1)
    (rootRule2 : root.rule2.length = 1)
    (descriptorRoot : List (List (OfficialSparseEntry (List ℕ))))
    (descriptorRootLength : descriptorRoot.length = 1)
    (left right : List input.LocalizedRerootCumulativeRule45Key)
    (sameLength : left.length = right.length)
    (leftNonempty : ∀ child ∈ left, LocalizedKeyLayersNonempty input child)
    (rightNonempty : ∀ child ∈ right, LocalizedKeyLayersNonempty input child)
    (leftLabels rightLabels leftRanks rightRanks :
      List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))))
    (parentObservable :
      input.localizedRerootCumulativeRule45Observable
        { constitutional := OfficialRuleMajorKey.assemble root
            (left.map fun child => child.constitutional)
          descriptor := descriptorRoot ++ input.mergeLocalizedRerootDescriptorChildren left
          labels := leftLabels, rankedLabels := leftRanks } =
      input.localizedRerootCumulativeRule45Observable
        { constitutional := OfficialRuleMajorKey.assemble root
            (right.map fun child => child.constitutional)
          descriptor := descriptorRoot ++ input.mergeLocalizedRerootDescriptorChildren right
          labels := rightLabels, rankedLabels := rightRanks }) :
    ∀ (slot : ℕ) (bound : slot < left.length),
      input.localizedRerootCumulativeRule45Observable (left[slot]'bound) =
        input.localizedRerootCumulativeRule45Observable
          (right[slot]'(by omega)) := by
  intro slot bound
  have rightBound : slot < right.length := by omega
  have rule1aParent := congrArg LocalizedCumulativeRule45Observable.rule1a parentObservable
  have rule1bParent := congrArg LocalizedCumulativeRule45Observable.rule1b parentObservable
  have rule2Parent := congrArg LocalizedCumulativeRule45Observable.rule2 parentObservable
  have descriptorParent := congrArg LocalizedCumulativeRule45Observable.descriptor parentObservable
  simp only [localizedRerootCumulativeRule45Observable_rule1a] at rule1aParent
  simp only [localizedRerootCumulativeRule45Observable_rule1b] at rule1bParent
  simp only [localizedRerootCumulativeRule45Observable_rule2] at rule2Parent
  simp only [localizedRerootCumulativeRule45Observable_descriptor] at descriptorParent
  have rule1aEq : (left[slot]'bound).constitutional.rule1a =
      (right[slot]'rightBound).constitutional.rule1a := by
    apply eq_of_forall_getD_eq_of_layers_nonempty
    · intro depth
      have assembled :
          ((OfficialRuleMajorKey.assemble root
              (left.map fun child => child.constitutional)).rule1a.getD (depth + 1) []) =
            ((OfficialRuleMajorKey.assemble root
              (right.map fun child => child.constitutional)).rule1a.getD (depth + 1) []) := by
        rw [rule1aParent]
      have stripped := congrArg (stripSlot slot) assembled
      rw [stripSlot_getD_assemble_rule1a_child root
          (left.map fun child => child.constitutional) rootRule1a slot depth
          (by simpa using bound),
        stripSlot_getD_assemble_rule1a_child root
          (right.map fun child => child.constitutional) rootRule1a slot depth
          (by simpa using rightBound)] at stripped
      simpa [List.getElem_map] using stripped
    · exact (leftNonempty _ (List.getElem_mem bound)).rule1a
    · exact (rightNonempty _ (List.getElem_mem rightBound)).rule1a
  have rule1bEq : (left[slot]'bound).constitutional.rule1b =
      (right[slot]'rightBound).constitutional.rule1b := by
    apply eq_of_forall_getD_eq_of_layers_nonempty
    · intro depth
      have assembled :
          ((OfficialRuleMajorKey.assemble root
              (left.map fun child => child.constitutional)).rule1b.getD (depth + 1) []) =
            ((OfficialRuleMajorKey.assemble root
              (right.map fun child => child.constitutional)).rule1b.getD (depth + 1) []) := by
        rw [rule1bParent]
      have stripped := congrArg (stripSlot slot) assembled
      rw [stripSlot_getD_assemble_rule1b_child root
          (left.map fun child => child.constitutional) rootRule1b slot depth
          (by simpa using bound),
        stripSlot_getD_assemble_rule1b_child root
          (right.map fun child => child.constitutional) rootRule1b slot depth
          (by simpa using rightBound)] at stripped
      simpa [List.getElem_map] using stripped
    · exact (leftNonempty _ (List.getElem_mem bound)).rule1b
    · exact (rightNonempty _ (List.getElem_mem rightBound)).rule1b
  have rule2Eq : (left[slot]'bound).constitutional.rule2 =
      (right[slot]'rightBound).constitutional.rule2 := by
    apply eq_of_forall_getD_eq_of_layers_nonempty
    · intro depth
      have assembled :
          ((OfficialRuleMajorKey.assemble root
              (left.map fun child => child.constitutional)).rule2.getD (depth + 1) []) =
            ((OfficialRuleMajorKey.assemble root
              (right.map fun child => child.constitutional)).rule2.getD (depth + 1) []) := by
        rw [rule2Parent]
      have stripped := congrArg (stripSlot slot) assembled
      rw [stripSlot_getD_assemble_rule2_child root
          (left.map fun child => child.constitutional) rootRule2 slot depth
          (by simpa using bound),
        stripSlot_getD_assemble_rule2_child root
          (right.map fun child => child.constitutional) rootRule2 slot depth
          (by simpa using rightBound)] at stripped
      simpa [List.getElem_map] using stripped
    · exact (leftNonempty _ (List.getElem_mem bound)).rule2
    · exact (rightNonempty _ (List.getElem_mem rightBound)).rule2
  have descriptorEq : (left[slot]'bound).descriptor =
      (right[slot]'rightBound).descriptor := by
    apply eq_of_forall_getD_eq_of_layers_nonempty
    · intro depth
      have assembled :
          ((descriptorRoot ++
              input.mergeLocalizedRerootDescriptorChildren left).getD (depth + 1) []) =
            ((descriptorRoot ++
              input.mergeLocalizedRerootDescriptorChildren right).getD (depth + 1) []) := by
        rw [descriptorParent]
      have stripped := congrArg (stripSlot slot) assembled
      rw [stripSlot_getD_succ_prefix descriptorRoot
          (input.mergeLocalizedRerootDescriptorChildren left) slot depth descriptorRootLength,
        stripSlot_getD_succ_prefix descriptorRoot
          (input.mergeLocalizedRerootDescriptorChildren right) slot depth descriptorRootLength,
        stripSlot_getD_mergeDescriptorChildren_of_lt input left slot depth bound,
        stripSlot_getD_mergeDescriptorChildren_of_lt input right slot depth rightBound]
        at stripped
      exact stripped
    · exact (leftNonempty _ (List.getElem_mem bound)).descriptor
    · exact (rightNonempty _ (List.getElem_mem rightBound)).descriptor
  rw [show input.localizedRerootCumulativeRule45Observable (left[slot]'bound) =
      { rule1a := (left[slot]'bound).constitutional.rule1a,
        rule1b := (left[slot]'bound).constitutional.rule1b,
        rule2 := (left[slot]'bound).constitutional.rule2,
        descriptor := (left[slot]'bound).descriptor } from rfl,
    show input.localizedRerootCumulativeRule45Observable (right[slot]'rightBound) =
      { rule1a := (right[slot]'rightBound).constitutional.rule1a,
        rule1b := (right[slot]'rightBound).constitutional.rule1b,
        rule2 := (right[slot]'rightBound).constitutional.rule2,
        descriptor := (right[slot]'rightBound).descriptor } from rfl,
    rule1aEq, rule1bEq, rule2Eq, descriptorEq]

/-! ## Nonemptiness of declarative derivations -/

/-- Pointwise `LocalizedKeyLayersNonempty` for a derived child list, given the one-step property. -/
theorem localizedKeyLayersNonempty_of_declarative_list
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat)
    (keyNonempty : ∀ (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootCumulativeRule45Key),
      input.DeclarativeLocalizedRerootCumulativeRule45Key stage target view fuel cursor key →
        LocalizedKeyLayersNonempty input key) :
    ∀ (cursors : List (input.LocalizedRerootCursor carrierFuel))
      (keys : List input.LocalizedRerootCumulativeRule45Key),
      input.DeclarativeLocalizedRerootCumulativeRule45KeyList stage target view fuel cursors keys →
        ∀ key ∈ keys, LocalizedKeyLayersNonempty input key := by
  intro cursors
  induction cursors with
  | nil =>
      intro keys derivation targetKey present
      cases derivation
      simp at present
  | cons cursor cursors inductionHypothesis =>
      intro keys derivation targetKey present
      cases derivation with
      | cons head tail =>
          rcases List.mem_cons.mp present with same | inTail
          · rw [same]
            exact keyNonempty _ _ head
          · exact inductionHypothesis _ tail targetKey inTail

/-- Every independently derived cumulative key has nonempty comparison-visible layers. -/
theorem localizedKeyLayersNonempty_of_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootCumulativeRule45Key),
      input.DeclarativeLocalizedRerootCumulativeRule45Key stage target view fuel cursor key →
        LocalizedKeyLayersNonempty input key := by
  intro fuel
  induction fuel with
  | zero =>
      intro cursor key derivation
      cases derivation with
      | terminal frame empty observed =>
          exact localizedKeyLayersNonempty_terminal input stage cursor _
  | succ fuel inductionHypothesis =>
      intro cursor key derivation
      cases derivation with
      | terminal frame empty observed =>
          exact localizedKeyLayersNonempty_terminal input stage cursor _
      | branch frame nonempty observed childDerivations ranking descending =>
          exact localizedKeyLayersNonempty_branch input stage cursor _ _
            (fun child childMem =>
              localizedKeyLayersNonempty_of_declarative_list input stage target view
                fuel inductionHypothesis _ _ childDerivations child
                (ranking.mem_iff.mp childMem))

end CumulativeAssembly

end TetraStereo.OneCenter
