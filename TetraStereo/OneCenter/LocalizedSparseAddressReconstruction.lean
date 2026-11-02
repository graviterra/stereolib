import TetraStereo.OneCenter.LocalizedParametricCumulativeLabels
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Inversion of the actual addressed sparse tables of localized cumulative keys

The localized cumulative builders compile a branch into *parent-slot-addressed* sparse
tables: `OfficialSparseEntry α = List ℕ × α`, where the address is the sequence of final
sibling slots from the root.  Child branches are merged by
`OfficialRuleMajorKey.prefixLayer`/`OfficialRuleMajorKey.mergeChildren` (used directly by
`OfficialRuleMajorKey.assemble`) and by the three cumulative merges
`mergeLocalizedRerootDescriptorChildren`, `mergeLocalizedRerootLabelChildren` and
`mergeLocalizedRerootRankedLabelChildren` of `CertifiedLocalizedCIPInput`.  All four merges
have the same shape: at every sphere depth, each child table's depth-layer is prefixed by
that child's slot and concatenated in slot order.

This module proves that these merges are *invertible on the actual tables*:

* `entriesAtSlot slot` keeps exactly the entries whose address begins with `slot`, and
  `dropAddressHeadLayer` removes that leading slot.  For the slot-indexed merges
  (`mergeChildren`, cumulative `descriptor` and `labels`) the composite
  `dropAddressHeadLayer ∘ entriesAtSlot slot` returns exactly the depth-layer of the child
  that occupies `slot`, for every depth.
* `mergeChildren_getD_eq_flatMap_zipIdx` exposes the merged layer as the concatenation of
  the per-slot prefix blocks in slot order (prefix adjacency).
* `mergeChildren_length` records the merged table's length (`childLayerCount`, the maximum
  child sphere count), which is only the padding length, not any child's own sphere count.
  **No child length is supplied** by the normalized API: `mergePairTable_normalizedChildTable`,
  `mergeChildren_normalizedChildTable`, `mergeDescriptorChildren_normalizedChildTable` and
  `mergeLabelChildren_normalizedChildTable` strip the chosen slot from every actual merged
  sphere and trim the trailing empty padding with `takeWhile nonemptySphere`.  The result is
  the *entire* child table under the explicit nonempty-layer shape condition
  `∀ depth < child.length, child.getD depth [] ≠ []` (F145C derives that condition from the
  actual builder; nothing here claims that the final flattened key retains a child key or a
  length tag).  The padding inverse behind this is `map_getD_range_eq_append`, which
  decomposes the maximum-length read into the child table followed by empty spheres, and
  `takeWhile_getD_range_eq_self`.  The earlier length-tag-indexed theorem
  `mergePairTable_child_reconstruction` is retained only for callers that already hold the
  child's own sphere count.  `nonemptySphere sphere = !sphere.isEmpty` is the executable
  nonempty test; `nonemptySphere_eq_bne` shows it is the usual `sphere != []` whenever the
  entry payload has Boolean equality, and the `..._normalizedChildTable_bne` theorems state
  the normalized reconstruction with the literal `takeWhile (fun sphere => sphere != [])`.
* Root observations have address `[]`, whose head is `none`; slot filtering never selects
  them (`entriesAtSlot_address_ne_nil`), so the root table is separated from every child
  table.  `assemble_rule1a_take` and its siblings recover the root prefix exactly.
* The rank-addressed merge (`mergeLocalizedRerootRankedLabelChildren`) is inverted as a
  *rank population*: filtering a rank recovers the concatenation of the blocks of exactly
  the children that carry that rank.  Unlike slot indices, ranks are intentionally shared by
  comparator-equivalent siblings, so rank-addressed tables are not expected to be injective
  at a rank prefix; the exact recovered object is stated.

The second result concerns the cumulative Rules-4a--5 descriptor reading.  On the five
syntactic label observations `none`, `chiral R`, `chiral S`, `pseudoasymmetric r` and
`pseudoasymmetric s`, the actual
`CertifiedLocalizedCIPInput.localizedCumulativeRule45Priority` is injective for the
`rule5NoRule4bReference` stage, and for the `rule5` stage when the *common* Rule-5 reference
agrees on the two sides while the two own Rule-4b references may differ
(`localizedCumulativeRule45Priority_rule5_commonReference_injective`).  The common
Rule-5 component (together with the Rule-4a and Rule-4c components) alone determines the
label; in particular the fixed-common-reference corollaries
`..._fixedCommonReference_R_injective` and `..._fixedCommonReference_S_injective` allow
different own Rule-4b references.  With the same own reference on both sides, vector
equality is equivalent to label equality (`..._rule5_eq_iff`).

## Scope

`none` is a syntactic "no label was observed at this cursor" value.  It is retained as a
distinct fifth case.  Nothing here asserts that an absent observation means a
nonstereogenic node, and no chemical completeness hypothesis is assumed or concluded.
These are structural theorems about the actual constructors and their actual tables.
-/

/-! ## Address surgery on sparse entries -/

namespace SparseAddress

/-- The leading slot of a parent-slot-addressed observation. -/
def addressHead? {α : Type*} (entry : OfficialSparseEntry α) : Option Nat :=
  entry.1.head?

/-- Remove the leading slot of an addressed observation, keeping the observation itself. -/
def dropAddressHead {α : Type*} (entry : OfficialSparseEntry α) : OfficialSparseEntry α :=
  (entry.1.tail, entry.2)

/-- Remove the leading slot from every entry of one sphere. -/
def dropAddressHeadLayer {α : Type*}
    (layer : List (OfficialSparseEntry α)) : List (OfficialSparseEntry α) :=
  layer.map dropAddressHead

/-- The entries of one sphere whose address begins with `slot`. -/
def entriesAtSlot {α : Type*} (slot : Nat) (layer : List (OfficialSparseEntry α)) :
    List (OfficialSparseEntry α) :=
  layer.filter fun entry => entry.1.head? == some slot

@[simp] theorem addressHead?_eq {α : Type*} (entry : OfficialSparseEntry α) :
    addressHead? entry = entry.1.head? := rfl

theorem addressHead?_of_mem_prefixLayer {α : Type*} {slot : Nat}
    {layer : List (OfficialSparseEntry α)} :
    ∀ entry ∈ OfficialRuleMajorKey.prefixLayer slot layer,
      addressHead? entry = some slot := by
  intro entry present
  obtain ⟨source, _, same⟩ := List.mem_map.mp present
  rw [← same]
  rfl

@[simp] theorem dropAddressHead_prefixLayerEntry {α : Type*} (slot : Nat)
    (entry : OfficialSparseEntry α) :
    dropAddressHead (slot :: entry.1, entry.2) = entry := by
  obtain ⟨address, observation⟩ := entry
  rfl

@[simp] theorem dropAddressHeadLayer_prefixLayer {α : Type*} (slot : Nat) :
    ∀ layer : List (OfficialSparseEntry α),
      dropAddressHeadLayer (OfficialRuleMajorKey.prefixLayer slot layer) = layer
  | [] => rfl
  | entry :: tail => by
      show dropAddressHead (slot :: entry.1, entry.2) ::
          dropAddressHeadLayer (OfficialRuleMajorKey.prefixLayer slot tail) = entry :: tail
      rw [dropAddressHead_prefixLayerEntry, dropAddressHeadLayer_prefixLayer]

/-- Selecting a slot from a single prefix block either keeps the whole block or discards it. -/
theorem entriesAtSlot_prefixLayer {α : Type*} (selected slot : Nat)
    (layer : List (OfficialSparseEntry α)) :
    entriesAtSlot selected (OfficialRuleMajorKey.prefixLayer slot layer) =
      if slot == selected then OfficialRuleMajorKey.prefixLayer slot layer else [] := by
  by_cases same : slot = selected
  · subst selected
    rw [if_pos (by simp)]
    apply List.filter_eq_self.mpr
    intro entry present
    have observed := addressHead?_of_mem_prefixLayer entry present
    simp only [addressHead?_eq] at observed
    rw [observed]
    simp
  · rw [if_neg (by simp [same])]
    apply List.filter_eq_nil_iff.mpr
    intro entry present
    have observed := addressHead?_of_mem_prefixLayer entry present
    simp only [addressHead?_eq] at observed
    rw [observed]
    simp [same]

/-- Filter form of `entriesAtSlot`, used so that the simplification lemmas match
syntactically during the induction below. -/
theorem filter_prefixLayer {α : Type*} (selected slot : Nat)
    (layer : List (OfficialSparseEntry α)) :
    List.filter (fun entry : OfficialSparseEntry α => entry.1.head? == some selected)
        (OfficialRuleMajorKey.prefixLayer slot layer) =
      if slot == selected then OfficialRuleMajorKey.prefixLayer slot layer else [] :=
  entriesAtSlot_prefixLayer selected slot layer

/-- Slot selection distributes across the concatenated per-child blocks of one sphere,
stated with the explicit filter so that it is stable under induction. -/
theorem filter_flatMap_prefixLayer {β γ : Type*} (pairs : List (β × Nat))
    (block : β → List (OfficialSparseEntry γ)) (selected : Nat) :
    List.filter (fun entry : OfficialSparseEntry γ => entry.1.head? == some selected)
        (pairs.flatMap fun pair => OfficialRuleMajorKey.prefixLayer pair.2 (block pair.1)) =
      (pairs.filter fun pair => pair.2 == selected).flatMap
        fun pair => OfficialRuleMajorKey.prefixLayer selected (block pair.1) := by
  induction pairs with
  | nil => rfl
  | cons pair rest inductionHypothesis =>
      rw [List.flatMap_cons, List.filter_append, filter_prefixLayer,
        inductionHypothesis, List.filter_cons]
      by_cases same : pair.2 = selected
      · simp [same]
      · have notSame : ¬((pair.2 == selected) = true) := by simpa using same
        simp [notSame]

/-- Slot selection distributes across the concatenated per-child blocks of one sphere. -/
theorem entriesAtSlot_flatMap_prefixLayer {β γ : Type*} (pairs : List (β × Nat))
    (block : β → List (OfficialSparseEntry γ)) (selected : Nat) :
    entriesAtSlot selected
        (pairs.flatMap fun pair => OfficialRuleMajorKey.prefixLayer pair.2 (block pair.1)) =
      (pairs.filter fun pair => pair.2 == selected).flatMap
        fun pair => OfficialRuleMajorKey.prefixLayer selected (block pair.1) :=
  filter_flatMap_prefixLayer pairs block selected

/-- Entries selected by a slot never carry the empty (root) address. -/
theorem entriesAtSlot_address_ne_nil {α : Type*} {slot : Nat}
    {layer : List (OfficialSparseEntry α)} :
    ∀ entry ∈ entriesAtSlot slot layer, entry.1 ≠ [] := by
  intro entry present empty
  have selected := (List.mem_filter.mp present).2
  have observed : entry.1.head? = some slot := by simpa using selected
  rw [empty] at observed
  simp at observed

/-- Distinct slots select disjoint entries: a slot selection forces the leading slot. -/
theorem entriesAtSlot_disjoint {α : Type*} {layer : List (OfficialSparseEntry α)}
    {leftSlot rightSlot : Nat} (different : leftSlot ≠ rightSlot)
    {entry : OfficialSparseEntry α}
    (selectedLeft : entry ∈ entriesAtSlot leftSlot layer)
    (selectedRight : entry ∈ entriesAtSlot rightSlot layer) : False := by
  have leftHead : entry.1.head? = some leftSlot := by
    simpa using (List.mem_filter.mp selectedLeft).2
  have rightHead : entry.1.head? = some rightSlot := by
    simpa using (List.mem_filter.mp selectedRight).2
  rw [leftHead] at rightHead
  simp only [Option.some.injEq] at rightHead
  exact different rightHead

end SparseAddress

/-! ## A unique-element filter lemma -/

namespace SparseAddress

/-- A `Nodup` list with exactly one element satisfying a boolean predicate filters to that
element. -/
theorem filter_eq_singleton_of_nodup_unique {β : Type*} :
    ∀ (list : List β) (predicate : β → Bool) (chosen : β),
      list.Nodup → chosen ∈ list → predicate chosen = true →
      (∀ candidate ∈ list, predicate candidate = true → candidate = chosen) →
      list.filter predicate = [chosen] := by
  intro list
  induction list with
  | nil =>
      intro predicate chosen _ present _
      exact (List.not_mem_nil present).elim
  | cons head tail inductionHypothesis =>
      intro predicate chosen nodup present satisfies unique
      rw [List.nodup_cons] at nodup
      obtain ⟨headAbsent, tailNodup⟩ := nodup
      rw [List.filter_cons]
      by_cases headSatisfies : predicate head
      · rw [if_pos headSatisfies]
        have headEq : head = chosen := unique head (by simp) headSatisfies
        rw [← headEq]
        have empty : tail.filter predicate = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro candidate candidatePresent candidateSatisfies
          have candidateEq : candidate = head := by
            have observed := unique candidate (by simp [candidatePresent]) candidateSatisfies
            rwa [← headEq] at observed
          subst candidateEq
          exact headAbsent candidatePresent
        rw [empty]
      · rw [if_neg headSatisfies]
        have chosenPresent : chosen ∈ tail := by
          rcases List.mem_cons.mp present with same | rest
          · subst same
            exact absurd satisfies headSatisfies
          · exact rest
        exact inductionHypothesis predicate chosen tailNodup chosenPresent satisfies
          (fun candidate candidatePresent candidateSatisfies =>
            unique candidate (by simp [candidatePresent]) candidateSatisfies)

/-- The index enumeration of a list has no repeated pair. -/
theorem nodup_zipIdx {β : Type*} (values : List β) (start : Nat) :
    (values.zipIdx start).Nodup := by
  induction values generalizing start with
  | nil => simp
  | cons head tail inductionHypothesis =>
      rw [List.zipIdx_cons, List.nodup_cons]
      refine ⟨?_, inductionHypothesis (start + 1)⟩
      intro present
      have bounded := List.le_snd_of_mem_zipIdx present
      omega

/-- In the index enumeration, selecting one index keeps exactly the entry at that index. -/
theorem zipIdx_filter_eq_singleton {β : Type*} (values : List β) (index : Nat)
    (value : β) (atIndex : values[index]? = some value) :
    (values.zipIdx.filter fun pair => pair.2 == index) = [(value, index)] := by
  refine filter_eq_singleton_of_nodup_unique (values.zipIdx 0)
    (fun pair : β × Nat => pair.2 == index)
    (value, index) (nodup_zipIdx values 0) ?_ ?_ ?_
  · exact List.mk_mem_zipIdx_iff_getElem?.mpr atIndex
  · simp
  · rintro ⟨pairValue, pairIndex⟩ present sameIndex
    have observed := List.mk_mem_zipIdx_iff_getElem?.mp present
    have indexEq : pairIndex = index := by simpa using sameIndex
    cases indexEq
    rw [atIndex] at observed
    have valueEq : value = pairValue := by injection observed
    subst valueEq
    rfl

/-! ## Membership and the generic slot-indexed merge -/

theorem mem_entriesAtSlot_iff {α : Type*} {slot : Nat}
    {layer : List (OfficialSparseEntry α)} {entry : OfficialSparseEntry α} :
    entry ∈ entriesAtSlot slot layer ↔ entry ∈ layer ∧ entry.1.head? = some slot := by
  rw [entriesAtSlot, List.mem_filter]
  constructor
  · rintro ⟨present, selected⟩
    exact ⟨present, by simpa using selected⟩
  · rintro ⟨present, head⟩
    exact ⟨present, by simpa using head⟩

/-- The concatenation of the slot-prefixed blocks of `(value, slot)` pairs. -/
def mergePairs {β α : Type*} (pairs : List (β × Nat))
    (block : β → List (OfficialSparseEntry α)) : List (OfficialSparseEntry α) :=
  pairs.flatMap fun pair => OfficialRuleMajorKey.prefixLayer pair.2 (block pair.1)

/-- The sphere table of a slot-indexed merge: `count` spheres, each the concatenation of the
prefixed blocks of all pairs in pair order. -/
def mergePairTable {β α : Type*} (pairs : List (β × Nat))
    (layers : β → List (List (OfficialSparseEntry α))) (count : Nat) :
    List (List (OfficialSparseEntry α)) :=
  (List.range count).map fun depth =>
    mergePairs pairs (fun value => (layers value).getD depth [])

theorem mergePairTable_getD {β α : Type*} (pairs : List (β × Nat))
    (layers : β → List (List (OfficialSparseEntry α))) (count depth : Nat) :
    (mergePairTable pairs layers count).getD depth [] =
      if depth < count then
        mergePairs pairs (fun value => (layers value).getD depth [])
      else [] := by
  show ((List.range count).map
      (fun depth => mergePairs pairs (fun value => (layers value).getD depth []))).getD
        depth [] =
    if depth < count then
      mergePairs pairs (fun value => (layers value).getD depth [])
    else []
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases inRange : depth < count
  · rw [List.getElem?_range inRange, if_pos inRange] ; rfl
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt inRange),
      if_neg inRange] ; rfl

/-- Selecting a slot from the concatenated blocks keeps exactly that pair's block. -/
theorem entriesAtSlot_mergePairs_of_filter_eq {β α : Type*}
    (pairs : List (β × Nat)) (block : β → List (OfficialSparseEntry α))
    (slot : Nat) (chosen : β)
    (filterEq : (pairs.filter fun pair => pair.2 == slot) = [(chosen, slot)]) :
    entriesAtSlot slot (mergePairs pairs block) =
      OfficialRuleMajorKey.prefixLayer slot (block chosen) := by
  show entriesAtSlot slot (pairs.flatMap fun pair =>
      OfficialRuleMajorKey.prefixLayer pair.2 (block pair.1)) =
    OfficialRuleMajorKey.prefixLayer slot (block chosen)
  rw [entriesAtSlot_flatMap_prefixLayer, filterEq]
  simp

theorem dropAddressHeadLayer_entriesAtSlot_mergePairs_of_filter_eq {β α : Type*}
    (pairs : List (β × Nat)) (block : β → List (OfficialSparseEntry α))
    (slot : Nat) (chosen : β)
    (filterEq : (pairs.filter fun pair => pair.2 == slot) = [(chosen, slot)]) :
    dropAddressHeadLayer (entriesAtSlot slot (mergePairs pairs block)) = block chosen := by
  rw [entriesAtSlot_mergePairs_of_filter_eq pairs block slot chosen filterEq,
    dropAddressHeadLayer_prefixLayer]

/-- Slot inversion of a `zipIdx`-addressed merge, at one sphere. -/
theorem dropAddressHeadLayer_entriesAtSlot_mergePairs_zipIdx {β α : Type*}
    (values : List β) (block : β → List (OfficialSparseEntry α))
    (slot : Nat) (chosen : β) (atSlot : values[slot]? = some chosen) :
    dropAddressHeadLayer (entriesAtSlot slot (mergePairs values.zipIdx block)) =
      block chosen :=
  dropAddressHeadLayer_entriesAtSlot_mergePairs_of_filter_eq values.zipIdx block slot chosen
    (zipIdx_filter_eq_singleton values slot chosen atSlot)

/-- Inversion of one sphere of a slot-indexed merge table.  When the requested sphere is beyond
the table's length tag, both sides are empty by the per-child bound. -/
theorem mergePairTable_getD_entriesAtSlot_of_filter_eq {β α : Type*}
    (pairs : List (β × Nat)) (layers : β → List (List (OfficialSparseEntry α)))
    (count depth slot : Nat) (chosen : β)
    (chosenBound : (layers chosen).length ≤ count)
    (filterEq : (pairs.filter fun pair => pair.2 == slot) = [(chosen, slot)]) :
    dropAddressHeadLayer
        (entriesAtSlot slot ((mergePairTable pairs layers count).getD depth [])) =
      (layers chosen).getD depth [] := by
  rw [mergePairTable_getD]
  by_cases inRange : depth < count
  · rw [if_pos inRange]
    exact dropAddressHeadLayer_entriesAtSlot_mergePairs_of_filter_eq pairs
      (fun value => (layers value).getD depth []) slot chosen filterEq
  · rw [if_neg inRange]
    have bound : (layers chosen).length ≤ depth :=
      le_trans chosenBound (Nat.le_of_not_lt inRange)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none bound] ; rfl

/-- Inversion of one sphere of a `zipIdx`-addressed merge table. -/
theorem mergePairTable_getD_entriesAtSlot_zipIdx {β α : Type*}
    (values : List β) (layers : β → List (List (OfficialSparseEntry α)))
    (count depth slot : Nat) (chosen : β)
    (chosenBound : (layers chosen).length ≤ count)
    (atSlot : values[slot]? = some chosen) :
    dropAddressHeadLayer
        (entriesAtSlot slot ((mergePairTable values.zipIdx layers count).getD depth [])) =
      (layers chosen).getD depth [] :=
  mergePairTable_getD_entriesAtSlot_of_filter_eq values.zipIdx layers count depth slot
    chosen chosenBound (zipIdx_filter_eq_singleton values slot chosen atSlot)

/-! ## Normalized reconstruction without a supplied child length

The final flattened key carries no child key and no child sphere count.  The actual merged table
is therefore normalized directly: strip the chosen slot from every actual merged sphere and trim
the trailing empty padding with `takeWhile`.  `nonemptySphere` is the executable nonempty test
`!sphere.isEmpty`; it needs no Boolean-equality instance on the entry payload (on types with
lawful `BEq` it is the usual `fun sphere => sphere != []`).  If every retained child layer is
nonempty -- the explicit shape condition `∀ depth < child.length, child[depth] ≠ []` -- the
normalized table is the entire child table, including its last nonempty sphere, and the child
length is recovered rather than supplied.  Proving that the actual builder retains such layers
is F145C's invariant; this section proves only the generic inverse. -/

/-- Executable nonempty test for one sphere layer, used to trim trailing empty padding. -/
def nonemptySphere {α : Type*} (sphere : List α) : Bool := !sphere.isEmpty

/-- On sphere types with Boolean equality, the executable nonempty test is exactly the
`sphere != []` test. -/
theorem nonemptySphere_eq_bne {α : Type*} [BEq α] (sphere : List α) :
    nonemptySphere sphere = (sphere != []) := by
  cases sphere with
  | nil => rfl
  | cons head tail => rfl

/-- The normalized child slice of a merged table: at each actual merged sphere keep exactly the
entries addressed at `slot`, drop the leading slot, and trim the trailing empty spheres. -/
def normalizedChildTable {α : Type*} (slot : Nat)
    (table : List (List (OfficialSparseEntry α))) : List (List (OfficialSparseEntry α)) :=
  (table.map fun sphere => dropAddressHeadLayer (entriesAtSlot slot sphere)).takeWhile
    nonemptySphere

/-- The normalized child slice is literally the requested `takeWhile (fun sphere => sphere != [])`
of the actual merged layers with the chosen slot stripped. -/
theorem normalizedChildTable_eq_takeWhile_bne {α : Type*} [BEq α] (slot : Nat)
    (table : List (List (OfficialSparseEntry α))) :
    normalizedChildTable slot table =
      (table.map fun sphere => dropAddressHeadLayer (entriesAtSlot slot sphere)).takeWhile
        (fun sphere => sphere != []) := by
  have predicate :
      (fun sphere : List (OfficialSparseEntry α) => sphere != []) = nonemptySphere :=
    funext fun sphere => (nonemptySphere_eq_bne sphere).symm
  rw [predicate]
  rfl

/-- A table of length at most `count`, read at every depth of `range count`, is the table
followed by empty spheres.  This is the padding (maximum length) inverse: all spheres at or
beyond the table's own length are empty. -/
theorem map_getD_range_eq_append {α : Type*} (table : List (List α)) (count : Nat)
    (bound : table.length ≤ count) :
    (List.range count).map (fun depth => table.getD depth []) =
      table ++ (List.range (count - table.length)).map (fun _ => []) := by
  apply List.ext_getElem?
  intro index
  rw [List.getElem?_map]
  by_cases inCount : index < count
  · rw [List.getElem?_range inCount]
    simp only [Option.map_some]
    by_cases inTable : index < table.length
    · rw [List.getElem?_append_left inTable, List.getElem?_eq_getElem inTable,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inTable]
      rfl
    · have tableLe : table.length ≤ index := Nat.le_of_not_lt inTable
      rw [List.getElem?_append_right tableLe]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none tableLe]
      have indexIn : index - table.length < count - table.length := by omega
      rw [List.getElem?_map, List.getElem?_range indexIn]
      rfl
  · have countLe : count ≤ index := Nat.le_of_not_lt inCount
    have appendLength : (table ++ (List.range (count - table.length)).map
        (fun _ => [] : Nat → List α)).length = count := by
      simp [Nat.add_sub_of_le bound]
    rw [List.getElem?_eq_none (by simpa using countLe)]
    rw [List.getElem?_eq_none (by omega)]
    rfl

/-- Trimming a nonempty-sphere table followed by empty spheres returns the table itself. -/
theorem takeWhile_append_of_all_nil {α : Type*} (left right : List (List α))
    (leftNonempty : ∀ sphere ∈ left, sphere ≠ [])
    (rightEmpty : ∀ sphere ∈ right, sphere = []) :
    (left ++ right).takeWhile nonemptySphere = left := by
  induction left with
  | nil =>
      cases right with
      | nil => rfl
      | cons head tail =>
          have headEmpty : head = [] := rightEmpty head (by simp)
          subst headEmpty
          simp [nonemptySphere]
  | cons head tail inductionHypothesis =>
      have headNonempty : head ≠ [] := leftNonempty head (by simp)
      have headTrue : nonemptySphere head = true := by
        obtain ⟨first, rest, rfl⟩ := List.exists_cons_of_ne_nil headNonempty
        rfl
      rw [List.cons_append, List.takeWhile_cons_of_pos headTrue]
      rw [inductionHypothesis
        (fun sphere present => leftNonempty sphere (List.mem_cons_of_mem head present))]

/-- **Normalized padding inverse.**  Reading a table at all depths of `range count` and trimming
the empty spheres yields exactly the table, provided every of its own spheres is nonempty.  No
length of the table is assumed in the conclusion. -/
theorem takeWhile_getD_range_eq_self {α : Type*} (table : List (List α)) (count : Nat)
    (bound : table.length ≤ count)
    (nonempty : ∀ depth, depth < table.length → table.getD depth [] ≠ []) :
    ((List.range count).map (fun depth => table.getD depth [])).takeWhile nonemptySphere =
      table := by
  rw [map_getD_range_eq_append table count bound]
  refine takeWhile_append_of_all_nil table
    ((List.range (count - table.length)).map (fun _ => [])) ?_ ?_
  · intro sphere present
    obtain ⟨index, inTable, rfl⟩ := List.mem_iff_getElem.mp present
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inTable] using
      nonempty index inTable
  · intro sphere present
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp present
    rfl

/-- **Normalized reconstruction of a complete child table.**  Strip the chosen slot from every
actual sphere of the merged table and trim the trailing empty spheres.  This returns the entire
child table, with no supplied child length, under the explicit nonempty-layer shape condition. -/
theorem mergePairTable_normalizedChildTable {β α : Type*}
    (values : List β) (layers : β → List (List (OfficialSparseEntry α)))
    (count slot : Nat) (chosen : β)
    (chosenBound : (layers chosen).length ≤ count)
    (atSlot : values[slot]? = some chosen)
    (nonempty : ∀ depth, depth < (layers chosen).length →
      (layers chosen).getD depth [] ≠ []) :
    normalizedChildTable slot (mergePairTable values.zipIdx layers count) =
      layers chosen := by
  show (((List.range count).map
      (fun depth => mergePairs values.zipIdx
        (fun value => (layers value).getD depth []))).map
        (fun sphere => dropAddressHeadLayer (entriesAtSlot slot sphere))).takeWhile
      nonemptySphere = layers chosen
  rw [List.map_map]
  show ((List.range count).map
      (fun depth => dropAddressHeadLayer (entriesAtSlot slot
        (mergePairs values.zipIdx (fun value => (layers value).getD depth []))))).takeWhile
      nonemptySphere = layers chosen
  rw [List.map_congr_left (l := List.range count)
    (fun (depth : Nat) (_ : depth ∈ List.range count) =>
      dropAddressHeadLayer_entriesAtSlot_mergePairs_of_filter_eq values.zipIdx
        (fun value => (layers value).getD depth []) slot chosen
        (zipIdx_filter_eq_singleton values slot chosen atSlot))]
  show ((List.range count).map (fun depth => (layers chosen).getD depth [])).takeWhile
      nonemptySphere = layers chosen
  exact takeWhile_getD_range_eq_self (layers chosen) count chosenBound nonempty

/-- Literal `takeWhile (fun sphere => sphere != [])` form of the normalized reconstruction,
available when the entry payload has Boolean equality. -/
theorem mergePairTable_normalizedChildTable_bne {β α : Type*} [BEq α]
    (values : List β) (layers : β → List (List (OfficialSparseEntry α)))
    (count slot : Nat) (chosen : β)
    (chosenBound : (layers chosen).length ≤ count)
    (atSlot : values[slot]? = some chosen)
    (nonempty : ∀ depth, depth < (layers chosen).length →
      (layers chosen).getD depth [] ≠ []) :
    ((mergePairTable values.zipIdx layers count).map
        fun sphere => dropAddressHeadLayer (entriesAtSlot slot sphere)).takeWhile
      (fun sphere => sphere != []) = layers chosen := by
  rw [← normalizedChildTable_eq_takeWhile_bne]
  exact mergePairTable_normalizedChildTable values layers count slot chosen chosenBound
    atSlot nonempty

/-- **Reconstruction of a complete child table.**  From the complete merged table, the child's
final sibling slot and the child's own sphere count (its length tag), selecting the slot and
dropping the leading slot at every depth in `range childLength` returns exactly the child table,
including trailing empty spheres.  This version is retained for callers that already hold the
child's sphere count; the length-tag-free API is `mergePairTable_normalizedChildTable`. -/
theorem mergePairTable_child_reconstruction {β α : Type*}
    (values : List β) (layers : β → List (List (OfficialSparseEntry α)))
    (count slot : Nat) (chosen : β)
    (chosenBound : (layers chosen).length ≤ count)
    (atSlot : values[slot]? = some chosen) :
    (List.range (layers chosen).length).map
        (fun depth => dropAddressHeadLayer
          (entriesAtSlot slot
            ((mergePairTable values.zipIdx layers count).getD depth []))) =
      layers chosen := by
  apply List.ext_getElem?
  intro index
  rw [List.getElem?_map]
  by_cases inChild : index < (layers chosen).length
  · rw [List.getElem?_range inChild, List.getElem?_eq_getElem inChild]
    simp only [Option.map_some, Option.some.injEq]
    show dropAddressHeadLayer
        (entriesAtSlot slot ((mergePairTable values.zipIdx layers count).getD index [])) =
      (layers chosen)[index]
    rw [mergePairTable_getD_entriesAtSlot_zipIdx values layers count index slot chosen
      chosenBound atSlot, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem inChild]
    rfl
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_lt inChild),
      List.getElem?_eq_none (by simpa using Nat.le_of_not_lt inChild)] ; rfl

/-! ## The actual sphere-table merge `OfficialRuleMajorKey.mergeChildren` -/

theorem mergeChildren_getD_eq_flatMap_zipIdx {V α : Type*}
    (children : List (OfficialRuleMajorKey V))
    (layers : OfficialRuleMajorKey V → List (List (OfficialSparseEntry α)))
    (depth : Nat) :
    (OfficialRuleMajorKey.mergeChildren children layers).getD depth [] =
      if depth < OfficialRuleMajorKey.childLayerCount children layers then
        children.zipIdx.flatMap fun child =>
          OfficialRuleMajorKey.prefixLayer child.2 ((layers child.1).getD depth [])
      else [] := by
  show (mergePairTable children.zipIdx layers
      (OfficialRuleMajorKey.childLayerCount children layers)).getD depth [] =
    if depth < OfficialRuleMajorKey.childLayerCount children layers then
      children.zipIdx.flatMap fun child =>
        OfficialRuleMajorKey.prefixLayer child.2 ((layers child.1).getD depth [])
    else []
  exact mergePairTable_getD children.zipIdx layers
    (OfficialRuleMajorKey.childLayerCount children layers) depth

theorem mergeChildren_length {V α : Type*}
    (children : List (OfficialRuleMajorKey V))
    (layers : OfficialRuleMajorKey V → List (List (OfficialSparseEntry α))) :
    (OfficialRuleMajorKey.mergeChildren children layers).length =
      OfficialRuleMajorKey.childLayerCount children layers := by
  show (mergePairTable children.zipIdx layers
      (OfficialRuleMajorKey.childLayerCount children layers)).length =
    OfficialRuleMajorKey.childLayerCount children layers
  simp [mergePairTable]

/-- The generic foldl maximum bounds every entry value and is itself monotone in the seed. -/
theorem le_foldl_max {β : Type*} (list : List β) (value : β → Nat) (start : Nat) :
    start ≤ list.foldl (fun longest item => max longest (value item)) start ∧
      ∀ chosen ∈ list,
        value chosen ≤ list.foldl (fun longest item => max longest (value item)) start := by
  induction list generalizing start with
  | nil =>
      refine ⟨Nat.le_refl start, ?_⟩
      intro chosen present
      cases present
  | cons head tail inductionHypothesis =>
      obtain ⟨tailLower, tailValues⟩ := inductionHypothesis (max start (value head))
      refine ⟨?_, ?_⟩
      · exact le_trans (Nat.le_max_left start (value head)) tailLower
      · intro chosen present
        rcases List.mem_cons.mp present with same | tailPresent
        · subst same
          exact le_trans (Nat.le_max_right start (value chosen)) tailLower
        · exact tailValues chosen tailPresent

/-- Every entry value is bounded by a foldl maximum over an arbitrary key type. -/
theorem layers_length_le_foldl_max {β α : Type*}
    (children : List β) (layers : β → List (List (OfficialSparseEntry α)))
    {child : β} (present : child ∈ children) :
    (layers child).length ≤
      children.foldl (fun longest child => max longest (layers child).length) 0 :=
  (le_foldl_max children (fun child => (layers child).length) 0).2 child present

/-- Every child's sphere count is bounded by the merged length tag `childLayerCount`. -/
theorem layers_length_le_childLayerCount {V α : Type*}
    (children : List (OfficialRuleMajorKey V))
    (layers : OfficialRuleMajorKey V → List (List (OfficialSparseEntry α)))
    {child : OfficialRuleMajorKey V} (present : child ∈ children) :
    (layers child).length ≤ OfficialRuleMajorKey.childLayerCount children layers :=
  (le_foldl_max children (fun child => (layers child).length) 0).2 child present

/-- **Inversion of one sphere of `mergeChildren`.**  Selecting the final sibling slot and
dropping that leading slot returns exactly the corresponding child's sphere at the same depth. -/
theorem mergeChildren_getD_entriesAtSlot_dropAddressHeadLayer {V α : Type*}
    (children : List (OfficialRuleMajorKey V))
    (layers : OfficialRuleMajorKey V → List (List (OfficialSparseEntry α)))
    (depth slot : Nat) (child : OfficialRuleMajorKey V)
    (atSlot : children[slot]? = some child) :
    dropAddressHeadLayer
        (entriesAtSlot slot
          ((OfficialRuleMajorKey.mergeChildren children layers).getD depth [])) =
      (layers child).getD depth [] :=
  mergePairTable_getD_entriesAtSlot_zipIdx children layers
    (OfficialRuleMajorKey.childLayerCount children layers) depth slot child
    (layers_length_le_childLayerCount children layers (List.mem_of_getElem? atSlot))
    atSlot

/-- Reconstruction of a complete child table from the `mergeChildren` table. -/
theorem mergeChildren_child_reconstruction {V α : Type*}
    (children : List (OfficialRuleMajorKey V))
    (layers : OfficialRuleMajorKey V → List (List (OfficialSparseEntry α)))
    (slot : Nat) (child : OfficialRuleMajorKey V)
    (atSlot : children[slot]? = some child) :
    (List.range (layers child).length).map
        (fun depth => dropAddressHeadLayer
          (entriesAtSlot slot
            ((OfficialRuleMajorKey.mergeChildren children layers).getD depth []))) =
      layers child :=
  mergePairTable_child_reconstruction children layers
    (OfficialRuleMajorKey.childLayerCount children layers) slot child
    (layers_length_le_childLayerCount children layers (List.mem_of_getElem? atSlot))
    atSlot

/-- **Normalized reconstruction from the actual `mergeChildren` table.**  No child length is
supplied: the slot is stripped from every actual merged sphere and the trailing padding is
trimmed, under the explicit nonempty-layer shape condition. -/
theorem mergeChildren_normalizedChildTable {V α : Type*}
    (children : List (OfficialRuleMajorKey V))
    (layers : OfficialRuleMajorKey V → List (List (OfficialSparseEntry α)))
    (slot : Nat) (child : OfficialRuleMajorKey V)
    (atSlot : children[slot]? = some child)
    (nonempty : ∀ depth, depth < (layers child).length → (layers child).getD depth [] ≠ []) :
    normalizedChildTable slot (OfficialRuleMajorKey.mergeChildren children layers) =
      layers child :=
  mergePairTable_normalizedChildTable children layers
    (OfficialRuleMajorKey.childLayerCount children layers) slot child
    (layers_length_le_childLayerCount children layers (List.mem_of_getElem? atSlot))
    atSlot nonempty

/-- Literal `sphere != []` form of the `mergeChildren` normalized reconstruction. -/
theorem mergeChildren_normalizedChildTable_bne {V α : Type*} [BEq α]
    (children : List (OfficialRuleMajorKey V))
    (layers : OfficialRuleMajorKey V → List (List (OfficialSparseEntry α)))
    (slot : Nat) (child : OfficialRuleMajorKey V)
    (atSlot : children[slot]? = some child)
    (nonempty : ∀ depth, depth < (layers child).length →
      (layers child).getD depth [] ≠ []) :
    ((OfficialRuleMajorKey.mergeChildren children layers).map
        fun sphere => dropAddressHeadLayer (entriesAtSlot slot sphere)).takeWhile
      (fun sphere => sphere != []) = layers child := by
  rw [← normalizedChildTable_eq_takeWhile_bne]
  exact mergeChildren_normalizedChildTable children layers slot child atSlot nonempty

/-! ## Root recovery and child extraction from `assemble` -/

/-- Dropping the root prefix length from an appended table recovers the suffix table. -/
theorem getD_append_length_add {α : Type*} (left right : List α) (depth : Nat)
    (fallback : α) :
    (left ++ right).getD (left.length + depth) fallback = right.getD depth fallback := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (Nat.le_add_right left.length depth),
    Nat.add_sub_cancel_left]

/-- A table with a one-sphere root prefix: dropping that prefix sphere recovers the suffix. -/
theorem getD_append_one_add {α : Type*} (root : List α) (right : List (List α)) (depth : Nat)
    (fallback : List α) :
    ([root] ++ right).getD (1 + depth) fallback = right.getD depth fallback := by
  simpa using getD_append_length_add (left := [root]) (right := right)
    (depth := depth) (fallback := fallback)

@[simp] theorem assemble_rule1a {V : Type*} (root : OfficialRuleMajorKey V)
    (sortedChildren : List (OfficialRuleMajorKey V)) :
    (OfficialRuleMajorKey.assemble root sortedChildren).rule1a =
      root.rule1a ++
        OfficialRuleMajorKey.mergeChildren sortedChildren OfficialRuleMajorKey.rule1a := rfl

@[simp] theorem assemble_rule1b {V : Type*} (root : OfficialRuleMajorKey V)
    (sortedChildren : List (OfficialRuleMajorKey V)) :
    (OfficialRuleMajorKey.assemble root sortedChildren).rule1b =
      root.rule1b ++
        OfficialRuleMajorKey.mergeChildren sortedChildren OfficialRuleMajorKey.rule1b := rfl

@[simp] theorem assemble_rule2 {V : Type*} (root : OfficialRuleMajorKey V)
    (sortedChildren : List (OfficialRuleMajorKey V)) :
    (OfficialRuleMajorKey.assemble root sortedChildren).rule2 =
      root.rule2 ++
        OfficialRuleMajorKey.mergeChildren sortedChildren OfficialRuleMajorKey.rule2 := rfl

@[simp] theorem assemble_sourceNodes {V : Type*} (root : OfficialRuleMajorKey V)
    (sortedChildren : List (OfficialRuleMajorKey V)) :
    (OfficialRuleMajorKey.assemble root sortedChildren).sourceNodes =
      root.sourceNodes ++
        OfficialRuleMajorKey.mergeChildren sortedChildren
          OfficialRuleMajorKey.sourceNodes := rfl

@[simp] theorem assemble_complete {V : Type*} (root : OfficialRuleMajorKey V)
    (sortedChildren : List (OfficialRuleMajorKey V)) :
    (OfficialRuleMajorKey.assemble root sortedChildren).complete =
      sortedChildren.all OfficialRuleMajorKey.complete := rfl

/-- The root prefix of an assembled table is exactly recovered by taking its own length. -/
theorem assemble_rule1a_take {V : Type*} (root : OfficialRuleMajorKey V)
    (sortedChildren : List (OfficialRuleMajorKey V)) :
    (OfficialRuleMajorKey.assemble root sortedChildren).rule1a.take root.rule1a.length =
      root.rule1a := by
  rw [assemble_rule1a, List.take_append_of_le_length (Nat.le_refl root.rule1a.length),
    List.take_length]

theorem assemble_rule1b_take {V : Type*} (root : OfficialRuleMajorKey V)
    (sortedChildren : List (OfficialRuleMajorKey V)) :
    (OfficialRuleMajorKey.assemble root sortedChildren).rule1b.take root.rule1b.length =
      root.rule1b := by
  rw [assemble_rule1b, List.take_append_of_le_length (Nat.le_refl root.rule1b.length),
    List.take_length]

theorem assemble_rule2_take {V : Type*} (root : OfficialRuleMajorKey V)
    (sortedChildren : List (OfficialRuleMajorKey V)) :
    (OfficialRuleMajorKey.assemble root sortedChildren).rule2.take root.rule2.length =
      root.rule2 := by
  rw [assemble_rule2, List.take_append_of_le_length (Nat.le_refl root.rule2.length),
    List.take_length]

theorem assemble_sourceNodes_take {V : Type*} (root : OfficialRuleMajorKey V)
    (sortedChildren : List (OfficialRuleMajorKey V)) :
    (OfficialRuleMajorKey.assemble root sortedChildren).sourceNodes.take
        root.sourceNodes.length = root.sourceNodes := by
  rw [assemble_sourceNodes,
    List.take_append_of_le_length (Nat.le_refl root.sourceNodes.length),
    List.take_length]

/-- Generic inversion of an assembled table: at any depth after the root prefix, filtering the
child's final sibling slot and dropping that slot returns the child's sphere at that depth. -/
theorem assemble_getD_entriesAtSlot_dropAddressHeadLayer {V α : Type*}
    (root : OfficialRuleMajorKey V) (sortedChildren : List (OfficialRuleMajorKey V))
    (table : OfficialRuleMajorKey V → List (List (OfficialSparseEntry α)))
    (depth slot : Nat) (child : OfficialRuleMajorKey V)
    (atSlot : sortedChildren[slot]? = some child) :
    dropAddressHeadLayer
        (entriesAtSlot slot
          ((table root ++ OfficialRuleMajorKey.mergeChildren sortedChildren table).getD
            ((table root).length + depth) [])) =
      (table child).getD depth [] := by
  rw [getD_append_length_add]
  exact mergeChildren_getD_entriesAtSlot_dropAddressHeadLayer sortedChildren table
    depth slot child atSlot

theorem assemble_rule1a_getD_entriesAtSlot_dropAddressHeadLayer {V : Type*}
    (root : OfficialRuleMajorKey V) (sortedChildren : List (OfficialRuleMajorKey V))
    (depth slot : Nat) (child : OfficialRuleMajorKey V)
    (atSlot : sortedChildren[slot]? = some child) :
    dropAddressHeadLayer
        (entriesAtSlot slot
          ((OfficialRuleMajorKey.assemble root sortedChildren).rule1a.getD
            (root.rule1a.length + depth) [])) =
      child.rule1a.getD depth [] := by
  rw [assemble_rule1a]
  exact assemble_getD_entriesAtSlot_dropAddressHeadLayer root sortedChildren
    (fun key => key.rule1a) depth slot child atSlot

theorem assemble_rule1b_getD_entriesAtSlot_dropAddressHeadLayer {V : Type*}
    (root : OfficialRuleMajorKey V) (sortedChildren : List (OfficialRuleMajorKey V))
    (depth slot : Nat) (child : OfficialRuleMajorKey V)
    (atSlot : sortedChildren[slot]? = some child) :
    dropAddressHeadLayer
        (entriesAtSlot slot
          ((OfficialRuleMajorKey.assemble root sortedChildren).rule1b.getD
            (root.rule1b.length + depth) [])) =
      child.rule1b.getD depth [] := by
  rw [assemble_rule1b]
  exact assemble_getD_entriesAtSlot_dropAddressHeadLayer root sortedChildren
    (fun key => key.rule1b) depth slot child atSlot

theorem assemble_rule2_getD_entriesAtSlot_dropAddressHeadLayer {V : Type*}
    (root : OfficialRuleMajorKey V) (sortedChildren : List (OfficialRuleMajorKey V))
    (depth slot : Nat) (child : OfficialRuleMajorKey V)
    (atSlot : sortedChildren[slot]? = some child) :
    dropAddressHeadLayer
        (entriesAtSlot slot
          ((OfficialRuleMajorKey.assemble root sortedChildren).rule2.getD
            (root.rule2.length + depth) [])) =
      child.rule2.getD depth [] := by
  rw [assemble_rule2]
  exact assemble_getD_entriesAtSlot_dropAddressHeadLayer root sortedChildren
    (fun key => key.rule2) depth slot child atSlot

theorem assemble_sourceNodes_getD_entriesAtSlot_dropAddressHeadLayer {V : Type*}
    (root : OfficialRuleMajorKey V) (sortedChildren : List (OfficialRuleMajorKey V))
    (depth slot : Nat) (child : OfficialRuleMajorKey V)
    (atSlot : sortedChildren[slot]? = some child) :
    dropAddressHeadLayer
        (entriesAtSlot slot
          ((OfficialRuleMajorKey.assemble root sortedChildren).sourceNodes.getD
            (root.sourceNodes.length + depth) [])) =
      child.sourceNodes.getD depth [] := by
  rw [assemble_sourceNodes]
  exact assemble_getD_entriesAtSlot_dropAddressHeadLayer root sortedChildren
    (fun key => key.sourceNodes) depth slot child atSlot

/-! ## The actual cumulative descriptor, label and ranked-label merges -/

theorem mergeDescriptorChildren_length
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    (input.mergeLocalizedRerootDescriptorChildren children).length =
      input.localizedRerootDescriptorChildLayerCount children := by
  show (mergePairTable children.zipIdx (fun child => child.descriptor)
      (input.localizedRerootDescriptorChildLayerCount children)).length =
    input.localizedRerootDescriptorChildLayerCount children
  simp [mergePairTable]

theorem mergeLabelChildren_length
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    (input.mergeLocalizedRerootLabelChildren children).length =
      input.localizedRerootLabelChildLayerCount children := by
  show (mergePairTable children.zipIdx (fun child => child.labels)
      (input.localizedRerootLabelChildLayerCount children)).length =
    input.localizedRerootLabelChildLayerCount children
  simp [mergePairTable]

theorem mergeRankedLabelChildren_length
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    (input.mergeLocalizedRerootRankedLabelChildren children).length =
      input.localizedRerootRankedLabelChildLayerCount children := by
  show (mergePairTable (input.localizedRerootRankedChildren children)
      (fun child => child.rankedLabels)
      (input.localizedRerootRankedLabelChildLayerCount children)).length =
    input.localizedRerootRankedLabelChildLayerCount children
  simp [mergePairTable]

/-- Inversion of one descriptor sphere of the actual cumulative descriptor merge. -/
theorem mergeDescriptorChildren_getD_entriesAtSlot_dropAddressHeadLayer
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key)
    (depth slot : Nat) (child : input.LocalizedRerootCumulativeRule45Key)
    (atSlot : children[slot]? = some child) :
    dropAddressHeadLayer
        (entriesAtSlot slot
          ((input.mergeLocalizedRerootDescriptorChildren children).getD depth [])) =
      child.descriptor.getD depth [] :=
  mergePairTable_getD_entriesAtSlot_zipIdx children
    (fun child => child.descriptor)
    (input.localizedRerootDescriptorChildLayerCount children) depth slot child
    (layers_length_le_foldl_max children (fun child => child.descriptor)
      (List.mem_of_getElem? atSlot))
    atSlot

/-- Reconstruction of a complete child descriptor table from the actual cumulative merge. -/
theorem mergeDescriptorChildren_child_reconstruction
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key)
    (slot : Nat) (child : input.LocalizedRerootCumulativeRule45Key)
    (atSlot : children[slot]? = some child) :
    (List.range child.descriptor.length).map
        (fun depth => dropAddressHeadLayer
          (entriesAtSlot slot
            ((input.mergeLocalizedRerootDescriptorChildren children).getD depth []))) =
      child.descriptor :=
  mergePairTable_child_reconstruction children (fun child => child.descriptor)
    (input.localizedRerootDescriptorChildLayerCount children) slot child
    (layers_length_le_foldl_max children (fun child => child.descriptor)
      (List.mem_of_getElem? atSlot))
    atSlot

/-- **Normalized reconstruction from the actual cumulative descriptor merge.**  No descriptor
length is supplied; the explicit nonempty-layer condition is the only shape assumption. -/
theorem mergeDescriptorChildren_normalizedChildTable
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key)
    (slot : Nat) (child : input.LocalizedRerootCumulativeRule45Key)
    (atSlot : children[slot]? = some child)
    (nonempty : ∀ depth, depth < child.descriptor.length →
      child.descriptor.getD depth [] ≠ []) :
    normalizedChildTable slot (input.mergeLocalizedRerootDescriptorChildren children) =
      child.descriptor :=
  mergePairTable_normalizedChildTable children (fun child => child.descriptor)
    (input.localizedRerootDescriptorChildLayerCount children) slot child
    (layers_length_le_foldl_max children (fun child => child.descriptor)
      (List.mem_of_getElem? atSlot)) atSlot nonempty

/-- Literal `sphere != []` form of the descriptor-merge normalized reconstruction. -/
theorem mergeDescriptorChildren_normalizedChildTable_bne
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key)
    (slot : Nat) (child : input.LocalizedRerootCumulativeRule45Key)
    (atSlot : children[slot]? = some child)
    (nonempty : ∀ depth, depth < child.descriptor.length →
      child.descriptor.getD depth [] ≠ []) :
    ((input.mergeLocalizedRerootDescriptorChildren children).map
        fun sphere => dropAddressHeadLayer (entriesAtSlot slot sphere)).takeWhile
      (fun sphere => sphere != []) = child.descriptor := by
  rw [← normalizedChildTable_eq_takeWhile_bne]
  exact mergeDescriptorChildren_normalizedChildTable input children slot child atSlot nonempty

/-- Inversion of one exact-label sphere of the actual cumulative label merge. -/
theorem mergeLabelChildren_getD_entriesAtSlot_dropAddressHeadLayer
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key)
    (depth slot : Nat) (child : input.LocalizedRerootCumulativeRule45Key)
    (atSlot : children[slot]? = some child) :
    dropAddressHeadLayer
        (entriesAtSlot slot
          ((input.mergeLocalizedRerootLabelChildren children).getD depth [])) =
      child.labels.getD depth [] :=
  mergePairTable_getD_entriesAtSlot_zipIdx children
    (fun child => child.labels)
    (input.localizedRerootLabelChildLayerCount children) depth slot child
    (layers_length_le_foldl_max children (fun child => child.labels)
      (List.mem_of_getElem? atSlot))
    atSlot

/-- Reconstruction of a complete child exact-label table from the actual cumulative merge. -/
theorem mergeLabelChildren_child_reconstruction
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key)
    (slot : Nat) (child : input.LocalizedRerootCumulativeRule45Key)
    (atSlot : children[slot]? = some child) :
    (List.range child.labels.length).map
        (fun depth => dropAddressHeadLayer
          (entriesAtSlot slot
            ((input.mergeLocalizedRerootLabelChildren children).getD depth []))) =
      child.labels :=
  mergePairTable_child_reconstruction children (fun child => child.labels)
    (input.localizedRerootLabelChildLayerCount children) slot child
    (layers_length_le_foldl_max children (fun child => child.labels)
      (List.mem_of_getElem? atSlot))
    atSlot

/-- **Normalized reconstruction from the actual cumulative exact-label merge.**  No label-table
length is supplied; the explicit nonempty-layer condition is the only shape assumption. -/
theorem mergeLabelChildren_normalizedChildTable
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key)
    (slot : Nat) (child : input.LocalizedRerootCumulativeRule45Key)
    (atSlot : children[slot]? = some child)
    (nonempty : ∀ depth, depth < child.labels.length →
      child.labels.getD depth [] ≠ []) :
    normalizedChildTable slot (input.mergeLocalizedRerootLabelChildren children) =
      child.labels :=
  mergePairTable_normalizedChildTable children (fun child => child.labels)
    (input.localizedRerootLabelChildLayerCount children) slot child
    (layers_length_le_foldl_max children (fun child => child.labels)
      (List.mem_of_getElem? atSlot)) atSlot nonempty

/-- Literal `sphere != []` form of the exact-label-merge normalized reconstruction. -/
theorem mergeLabelChildren_normalizedChildTable_bne
    [BEq (Option CertifiedLocalizedCIPInput.LocalizedAuxiliaryLabel)]
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key)
    (slot : Nat) (child : input.LocalizedRerootCumulativeRule45Key)
    (atSlot : children[slot]? = some child)
    (nonempty : ∀ depth, depth < child.labels.length →
      child.labels.getD depth [] ≠ []) :
    ((input.mergeLocalizedRerootLabelChildren children).map
        fun sphere => dropAddressHeadLayer (entriesAtSlot slot sphere)).takeWhile
      (fun sphere => sphere != []) = child.labels := by
  rw [← normalizedChildTable_eq_takeWhile_bne]
  exact mergeLabelChildren_normalizedChildTable input children slot child atSlot nonempty

/-! ## The rank-addressed label merge -/

/-- Every ranked child lies in the child list it was ranked from. -/
theorem mem_localizedRerootRankedChildTail (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    ∀ (previous : input.LocalizedRerootCumulativeRule45Key) (rank : Nat)
      (pair : input.LocalizedRerootCumulativeRule45Key × Nat),
      pair ∈ input.localizedRerootRankedChildTail previous rank children →
        pair.1 ∈ children := by
  induction children with
  | nil =>
      intro previous rank pair present
      simp [CertifiedLocalizedCIPInput.localizedRerootRankedChildTail] at present
  | cons child children inductionHypothesis =>
      intro previous rank pair present
      simp only [CertifiedLocalizedCIPInput.localizedRerootRankedChildTail,
        List.mem_cons] at present
      rcases present with same | tailPresent
      · subst same
        simp
      · exact List.mem_cons_of_mem _
          (inductionHypothesis child _ pair tailPresent)

/-- Every ranked child lies in the child list it was ranked from. -/
theorem mem_localizedRerootRankedChildren (input : CertifiedLocalizedCIPInput) :
    ∀ (children : List input.LocalizedRerootCumulativeRule45Key)
      (pair : input.LocalizedRerootCumulativeRule45Key × Nat),
      pair ∈ input.localizedRerootRankedChildren children → pair.1 ∈ children := by
  intro children
  induction children with
  | nil =>
      intro pair present
      simp [CertifiedLocalizedCIPInput.localizedRerootRankedChildren] at present
  | cons child children inductionHypothesis =>
      intro pair present
      simp only [CertifiedLocalizedCIPInput.localizedRerootRankedChildren,
        List.mem_cons] at present
      rcases present with same | tailPresent
      · subst same
        simp
      · exact List.mem_cons_of_mem _
          (mem_localizedRerootRankedChildTail input children child 0 pair tailPresent)

/-- **Rank population inversion.**  Unlike a final sibling slot, a hierarchy-equivalence rank is
deliberately shared by comparator-equivalent siblings, so filtering a rank returns exactly the
concatenated blocks of all children carrying that rank, in ranked child order. -/
theorem mergeRankedLabelChildren_getD_entriesAtSlot
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key)
    (depth rank : Nat) :
    entriesAtSlot rank
        ((input.mergeLocalizedRerootRankedLabelChildren children).getD depth []) =
      ((input.localizedRerootRankedChildren children).filter
        fun pair => pair.2 == rank).flatMap
        fun pair => OfficialRuleMajorKey.prefixLayer rank
          (pair.1.rankedLabels.getD depth []) := by
  have tableEq :
      input.mergeLocalizedRerootRankedLabelChildren children =
        mergePairTable (input.localizedRerootRankedChildren children)
          (fun child => child.rankedLabels)
          (input.localizedRerootRankedLabelChildLayerCount children) := rfl
  rw [tableEq, mergePairTable_getD]
  by_cases inRange : depth < input.localizedRerootRankedLabelChildLayerCount children
  · rw [if_pos inRange]
    exact entriesAtSlot_flatMap_prefixLayer (input.localizedRerootRankedChildren children)
      (fun child => child.rankedLabels.getD depth []) rank
  · rw [if_neg inRange]
    have blocksEmpty : ∀ pair ∈ (input.localizedRerootRankedChildren children).filter
        (fun pair => pair.2 == rank),
        OfficialRuleMajorKey.prefixLayer rank
          (pair.1.rankedLabels.getD depth []) = [] := by
      intro pair pairPresent
      have rankedPresent : pair ∈ input.localizedRerootRankedChildren children :=
        (List.mem_filter.mp pairPresent).1
      have childPresent : pair.1 ∈ children :=
        mem_localizedRerootRankedChildren input children pair rankedPresent
      have childBound : (pair.1.rankedLabels).length ≤
          input.localizedRerootRankedLabelChildLayerCount children :=
        layers_length_le_foldl_max children (fun child => child.rankedLabels)
          childPresent
      have outOfRange : (pair.1.rankedLabels).length ≤ depth :=
        le_trans childBound (Nat.le_of_not_lt inRange)
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none outOfRange]
      rfl
    rw [List.flatMap_eq_nil_iff.mpr blocksEmpty] ; rfl

/-! ## The exact builder table shapes: one root sphere followed by the child merge -/

theorem descriptorTable_getD_entriesAtSlot_dropAddressHeadLayer
    (input : CertifiedLocalizedCIPInput) (rootPriority : List Nat)
    (children : List input.LocalizedRerootCumulativeRule45Key)
    (depth slot : Nat) (child : input.LocalizedRerootCumulativeRule45Key)
    (atSlot : children[slot]? = some child) :
    dropAddressHeadLayer
        (entriesAtSlot slot
          (([[([], rootPriority)]] ++
            input.mergeLocalizedRerootDescriptorChildren children).getD
              (1 + depth) [])) =
      child.descriptor.getD depth [] := by
  rw [getD_append_one_add]
  exact mergeDescriptorChildren_getD_entriesAtSlot_dropAddressHeadLayer
    input children depth slot child atSlot

theorem labelTable_getD_entriesAtSlot_dropAddressHeadLayer
    (input : CertifiedLocalizedCIPInput)
    (rootLabel : Option CertifiedLocalizedCIPInput.LocalizedAuxiliaryLabel)
    (children : List input.LocalizedRerootCumulativeRule45Key)
    (depth slot : Nat) (child : input.LocalizedRerootCumulativeRule45Key)
    (atSlot : children[slot]? = some child) :
    dropAddressHeadLayer
        (entriesAtSlot slot
          (([[([], rootLabel)]] ++
            input.mergeLocalizedRerootLabelChildren children).getD
              (1 + depth) [])) =
      child.labels.getD depth [] := by
  rw [getD_append_one_add]
  exact mergeLabelChildren_getD_entriesAtSlot_dropAddressHeadLayer
    input children depth slot child atSlot

theorem rankedLabelTable_getD_entriesAtSlot
    (input : CertifiedLocalizedCIPInput)
    (rootLabel : Option CertifiedLocalizedCIPInput.LocalizedAuxiliaryLabel)
    (children : List input.LocalizedRerootCumulativeRule45Key)
    (depth rank : Nat) :
    entriesAtSlot rank
        (([[([], rootLabel)]] ++
          input.mergeLocalizedRerootRankedLabelChildren children).getD
            (1 + depth) []) =
      ((input.localizedRerootRankedChildren children).filter
        fun pair => pair.2 == rank).flatMap
        fun pair => OfficialRuleMajorKey.prefixLayer rank
          (pair.1.rankedLabels.getD depth []) := by
  rw [getD_append_one_add]
  exact mergeRankedLabelChildren_getD_entriesAtSlot input children depth rank

theorem descriptorTable_root_take
    (input : CertifiedLocalizedCIPInput) (rootPriority : List Nat)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    ([[([], rootPriority)]] ++
        input.mergeLocalizedRerootDescriptorChildren children).take 1 =
      [[([], rootPriority)]] := by
  rfl

theorem labelTable_root_take
    (input : CertifiedLocalizedCIPInput)
    (rootLabel : Option CertifiedLocalizedCIPInput.LocalizedAuxiliaryLabel)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    ([[([], rootLabel)]] ++
        input.mergeLocalizedRerootLabelChildren children).take 1 =
      [[([], rootLabel)]] := by
  rfl

theorem rankedLabelTable_root_take
    (input : CertifiedLocalizedCIPInput)
    (rootLabel : Option CertifiedLocalizedCIPInput.LocalizedAuxiliaryLabel)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    ([[([], rootLabel)]] ++
        input.mergeLocalizedRerootRankedLabelChildren children).take 1 =
      [[([], rootLabel)]] := by
  rfl

/-! ## Kernel-authority guards for the structural API -/

assert_kernel_only addressHead?
assert_kernel_only dropAddressHead
assert_kernel_only dropAddressHeadLayer
assert_kernel_only entriesAtSlot
assert_kernel_only addressHead?_eq
assert_kernel_only addressHead?_of_mem_prefixLayer
assert_kernel_only dropAddressHead_prefixLayerEntry
assert_kernel_only dropAddressHeadLayer_prefixLayer
assert_kernel_only entriesAtSlot_prefixLayer
assert_kernel_only filter_prefixLayer
assert_kernel_only filter_flatMap_prefixLayer
assert_kernel_only entriesAtSlot_flatMap_prefixLayer
assert_kernel_only entriesAtSlot_address_ne_nil
assert_kernel_only entriesAtSlot_disjoint
assert_kernel_only filter_eq_singleton_of_nodup_unique
assert_kernel_only nodup_zipIdx
assert_kernel_only zipIdx_filter_eq_singleton
assert_kernel_only mem_entriesAtSlot_iff
assert_kernel_only mergePairs
assert_kernel_only mergePairTable
assert_kernel_only mergePairTable_getD
assert_kernel_only entriesAtSlot_mergePairs_of_filter_eq
assert_kernel_only dropAddressHeadLayer_entriesAtSlot_mergePairs_of_filter_eq
assert_kernel_only dropAddressHeadLayer_entriesAtSlot_mergePairs_zipIdx
assert_kernel_only mergePairTable_getD_entriesAtSlot_of_filter_eq
assert_kernel_only mergePairTable_getD_entriesAtSlot_zipIdx
assert_kernel_only nonemptySphere
assert_kernel_only nonemptySphere_eq_bne
assert_kernel_only normalizedChildTable
assert_kernel_only normalizedChildTable_eq_takeWhile_bne
assert_kernel_only map_getD_range_eq_append
assert_kernel_only takeWhile_append_of_all_nil
assert_kernel_only takeWhile_getD_range_eq_self
assert_kernel_only mergePairTable_normalizedChildTable
assert_kernel_only mergePairTable_normalizedChildTable_bne
assert_kernel_only mergePairTable_child_reconstruction
assert_kernel_only mergeChildren_getD_eq_flatMap_zipIdx
assert_kernel_only mergeChildren_length
assert_kernel_only le_foldl_max
assert_kernel_only layers_length_le_foldl_max
assert_kernel_only layers_length_le_childLayerCount
assert_kernel_only mergeChildren_getD_entriesAtSlot_dropAddressHeadLayer
assert_kernel_only mergeChildren_child_reconstruction
assert_kernel_only mergeChildren_normalizedChildTable
assert_kernel_only mergeChildren_normalizedChildTable_bne
assert_kernel_only getD_append_length_add
assert_kernel_only getD_append_one_add
assert_kernel_only assemble_rule1a
assert_kernel_only assemble_rule1b
assert_kernel_only assemble_rule2
assert_kernel_only assemble_sourceNodes
assert_kernel_only assemble_complete
assert_kernel_only assemble_rule1a_take
assert_kernel_only assemble_rule1b_take
assert_kernel_only assemble_rule2_take
assert_kernel_only assemble_sourceNodes_take
assert_kernel_only assemble_getD_entriesAtSlot_dropAddressHeadLayer
assert_kernel_only assemble_rule1a_getD_entriesAtSlot_dropAddressHeadLayer
assert_kernel_only assemble_rule1b_getD_entriesAtSlot_dropAddressHeadLayer
assert_kernel_only assemble_rule2_getD_entriesAtSlot_dropAddressHeadLayer
assert_kernel_only assemble_sourceNodes_getD_entriesAtSlot_dropAddressHeadLayer
assert_kernel_only mergeDescriptorChildren_length
assert_kernel_only mergeLabelChildren_length
assert_kernel_only mergeRankedLabelChildren_length
assert_kernel_only mergeDescriptorChildren_getD_entriesAtSlot_dropAddressHeadLayer
assert_kernel_only mergeDescriptorChildren_child_reconstruction
assert_kernel_only mergeDescriptorChildren_normalizedChildTable
assert_kernel_only mergeDescriptorChildren_normalizedChildTable_bne
assert_kernel_only mergeLabelChildren_getD_entriesAtSlot_dropAddressHeadLayer
assert_kernel_only mergeLabelChildren_child_reconstruction
assert_kernel_only mergeLabelChildren_normalizedChildTable
assert_kernel_only mergeLabelChildren_normalizedChildTable_bne
assert_kernel_only mem_localizedRerootRankedChildTail
assert_kernel_only mem_localizedRerootRankedChildren
assert_kernel_only mergeRankedLabelChildren_getD_entriesAtSlot
assert_kernel_only descriptorTable_getD_entriesAtSlot_dropAddressHeadLayer
assert_kernel_only labelTable_getD_entriesAtSlot_dropAddressHeadLayer
assert_kernel_only rankedLabelTable_getD_entriesAtSlot
assert_kernel_only descriptorTable_root_take
assert_kernel_only labelTable_root_take
assert_kernel_only rankedLabelTable_root_take

end SparseAddress

/-! ## Injectivity of the cumulative Rules-4a--5 priority vectors -/

namespace CertifiedLocalizedCIPInput

/-- The Rule-4a component detects absence of a label. -/
theorem eq_none_of_rule4aPriority_eq_zero
    (label : Option LocalizedAuxiliaryLabel)
    (zero : localizedRule4aPriority label = 0) : label = none := by
  cases label with
  | none => rfl
  | some value =>
      rcases value with descriptor | pseudo
      · cases descriptor <;> simp [localizedRule4aPriority] at zero
      · cases pseudo <;> simp [localizedRule4aPriority] at zero

/-- The Rule-4a component detects the lowercase (pseudoasymmetric) family. -/
theorem exists_pseudo_of_rule4aPriority_eq_one
    (label : Option LocalizedAuxiliaryLabel)
    (one : localizedRule4aPriority label = 1) :
    ∃ pseudo : PseudoRS, label = some (.pseudoasymmetric pseudo) := by
  cases label with
  | none => simp [localizedRule4aPriority] at one
  | some value =>
      rcases value with descriptor | pseudo
      · cases descriptor <;> simp [localizedRule4aPriority] at one
      · cases pseudo
        · exact ⟨.r, rfl⟩
        · exact ⟨.s, rfl⟩

/-- The Rule-4a component detects the uppercase (chiral) family. -/
theorem exists_chiral_of_rule4aPriority_eq_two
    (label : Option LocalizedAuxiliaryLabel)
    (two : localizedRule4aPriority label = 2) :
    ∃ descriptor : RS, label = some (.chiral descriptor) := by
  cases label with
  | none => simp [localizedRule4aPriority] at two
  | some value =>
      rcases value with descriptor | pseudo
      · exact ⟨descriptor, rfl⟩
      · cases pseudo <;> simp [localizedRule4aPriority] at two

/-- The Rule-4c component injects the two lowercase descriptors. -/
theorem localizedRule4cPriority_pseudo_injective (left right : PseudoRS)
    (same : localizedRule4cPriority (some (.pseudoasymmetric left)) =
      localizedRule4cPriority (some (.pseudoasymmetric right))) :
    left = right := by
  cases left <;> cases right <;> simp [localizedRule4cPriority] at same ⊢

/-- Under any Rule-4b reference, the Rule-4b component injects the two uppercase descriptors. -/
theorem localizedRule4bPriority_chiral_injective (reference left right : RS)
    (same : localizedRule4bPriority reference (some (.chiral left)) =
      localizedRule4bPriority reference (some (.chiral right))) :
    left = right := by
  cases reference <;> cases left <;> cases right <;>
    simp [localizedRule4bPriority] at same ⊢

/-- Under any common Rule-5 reference, the Rule-5 component injects the two uppercase
descriptors. -/
theorem localizedRule5Priority_chiral_injective (reference left right : RS)
    (same : localizedRule5Priority reference (some (.chiral left)) =
      localizedRule5Priority reference (some (.chiral right))) :
    left = right := by
  cases reference <;> cases left <;> cases right <;>
    simp [localizedRule5Priority] at same ⊢

/-! Concrete component extraction from the two actual cumulative vector shapes.  These are
definitional evaluations of `List.getD` at literal indices and literal-length vectors; they keep
the injectivity proofs independent of the simplifier's numeral treatment. -/

theorem cumulativePriority_getD_zero_three (first second third : Nat) :
    ([first, second, third] : List Nat).getD 0 0 = first := rfl

theorem cumulativePriority_getD_one_three (first second third : Nat) :
    ([first, second, third] : List Nat).getD 1 0 = second := rfl

theorem cumulativePriority_getD_two_three (first second third : Nat) :
    ([first, second, third] : List Nat).getD 2 0 = third := rfl

theorem cumulativePriority_getD_zero_four (first second third fourth : Nat) :
    ([first, second, third, fourth] : List Nat).getD 0 0 = first := rfl

theorem cumulativePriority_getD_one_four (first second third fourth : Nat) :
    ([first, second, third, fourth] : List Nat).getD 1 0 = second := rfl

theorem cumulativePriority_getD_two_four (first second third fourth : Nat) :
    ([first, second, third, fourth] : List Nat).getD 2 0 = third := rfl

theorem cumulativePriority_getD_three_four (first second third fourth : Nat) :
    ([first, second, third, fourth] : List Nat).getD 3 0 = fourth := rfl

/-- **Five-case injectivity without a Rule-4b reference.**  On `none`, `chiral R`, `chiral S`,
`pseudoasymmetric r` and `pseudoasymmetric s`, the actual cumulative vector of the
`rule5NoRule4bReference` stage determines the label for every Rule-5 reference. -/
theorem localizedCumulativeRule45Priority_rule5NoRule4bReference_injective
    (reference : RS) (left right : Option LocalizedAuxiliaryLabel)
    (same : localizedCumulativeRule45Priority (.rule5NoRule4bReference reference) left =
      localizedCumulativeRule45Priority (.rule5NoRule4bReference reference) right) :
    left = right := by
  have component0 : localizedRule4aPriority left = localizedRule4aPriority right := by
    have := congrArg (fun vector : List Nat => vector.getD 0 0) same
    simpa [localizedCumulativeRule45Priority, cumulativePriority_getD_zero_three,
      cumulativePriority_getD_one_three, cumulativePriority_getD_two_three,
      cumulativePriority_getD_zero_four, cumulativePriority_getD_one_four,
      cumulativePriority_getD_two_four] using this
  cases left with
  | none =>
      have rightZero : localizedRule4aPriority right = 0 := by
        rw [← component0]
        rfl
      exact (eq_none_of_rule4aPriority_eq_zero right rightZero).symm
  | some leftValue =>
      rcases leftValue with leftDescriptor | leftPseudo
      · have rightTwo : localizedRule4aPriority right = 2 := by
          rw [← component0]
          rfl
        obtain ⟨rightDescriptor, rightEq⟩ :=
          exists_chiral_of_rule4aPriority_eq_two right rightTwo
        rw [rightEq] at same ⊢
        have chiralSame :
            localizedRule5Priority reference (some (.chiral leftDescriptor)) =
              localizedRule5Priority reference (some (.chiral rightDescriptor)) := by
          have := congrArg (fun vector : List Nat => vector.getD 2 0) same
          simpa [localizedCumulativeRule45Priority, cumulativePriority_getD_zero_three,
        cumulativePriority_getD_one_three, cumulativePriority_getD_two_three,
        cumulativePriority_getD_zero_four, cumulativePriority_getD_one_four,
        cumulativePriority_getD_two_four] using this
        rw [localizedRule5Priority_chiral_injective reference leftDescriptor
          rightDescriptor chiralSame]
      · have rightOne : localizedRule4aPriority right = 1 := by
          rw [← component0]
          rfl
        obtain ⟨rightPseudo, rightEq⟩ :=
          exists_pseudo_of_rule4aPriority_eq_one right rightOne
        rw [rightEq] at same ⊢
        have pseudoSame :
            localizedRule4cPriority (some (.pseudoasymmetric leftPseudo)) =
              localizedRule4cPriority (some (.pseudoasymmetric rightPseudo)) := by
          have := congrArg (fun vector : List Nat => vector.getD 1 0) same
          simpa [localizedCumulativeRule45Priority, cumulativePriority_getD_zero_three,
        cumulativePriority_getD_one_three, cumulativePriority_getD_two_three,
        cumulativePriority_getD_zero_four, cumulativePriority_getD_one_four,
        cumulativePriority_getD_two_four] using this
        rw [localizedRule4cPriority_pseudo_injective leftPseudo rightPseudo pseudoSame]

/-- **Five-case injectivity with an own Rule-4b reference.**  The `rule5` vector determines the
label for *any* pair of own Rule-4b reference and common Rule-5 reference.  In particular no
agreement between the two references is needed. -/
theorem localizedCumulativeRule45Priority_rule5_injective
    (ownReference rule5Reference : RS)
    (left right : Option LocalizedAuxiliaryLabel)
    (same : localizedCumulativeRule45Priority (.rule5 ownReference rule5Reference) left =
      localizedCumulativeRule45Priority (.rule5 ownReference rule5Reference) right) :
    left = right := by
  have component0 : localizedRule4aPriority left = localizedRule4aPriority right := by
    have := congrArg (fun vector : List Nat => vector.getD 0 0) same
    simpa [localizedCumulativeRule45Priority, cumulativePriority_getD_zero_three,
      cumulativePriority_getD_one_three, cumulativePriority_getD_two_three,
      cumulativePriority_getD_zero_four, cumulativePriority_getD_one_four,
      cumulativePriority_getD_two_four] using this
  cases left with
  | none =>
      have rightZero : localizedRule4aPriority right = 0 := by
        rw [← component0]
        rfl
      exact (eq_none_of_rule4aPriority_eq_zero right rightZero).symm
  | some leftValue =>
      rcases leftValue with leftDescriptor | leftPseudo
      · have rightTwo : localizedRule4aPriority right = 2 := by
          rw [← component0]
          rfl
        obtain ⟨rightDescriptor, rightEq⟩ :=
          exists_chiral_of_rule4aPriority_eq_two right rightTwo
        rw [rightEq] at same ⊢
        have chiralSame :
            localizedRule4bPriority ownReference (some (.chiral leftDescriptor)) =
              localizedRule4bPriority ownReference (some (.chiral rightDescriptor)) := by
          have := congrArg (fun vector : List Nat => vector.getD 1 0) same
          simpa [localizedCumulativeRule45Priority, cumulativePriority_getD_zero_three,
        cumulativePriority_getD_one_three, cumulativePriority_getD_two_three,
        cumulativePriority_getD_zero_four, cumulativePriority_getD_one_four,
        cumulativePriority_getD_two_four] using this
        rw [localizedRule4bPriority_chiral_injective ownReference leftDescriptor
          rightDescriptor chiralSame]
      · have rightOne : localizedRule4aPriority right = 1 := by
          rw [← component0]
          rfl
        obtain ⟨rightPseudo, rightEq⟩ :=
          exists_pseudo_of_rule4aPriority_eq_one right rightOne
        rw [rightEq] at same ⊢
        have pseudoSame :
            localizedRule4cPriority (some (.pseudoasymmetric leftPseudo)) =
              localizedRule4cPriority (some (.pseudoasymmetric rightPseudo)) := by
          have := congrArg (fun vector : List Nat => vector.getD 2 0) same
          simpa [localizedCumulativeRule45Priority, cumulativePriority_getD_zero_three,
        cumulativePriority_getD_one_three, cumulativePriority_getD_two_three,
        cumulativePriority_getD_zero_four, cumulativePriority_getD_one_four,
        cumulativePriority_getD_two_four] using this
        rw [localizedRule4cPriority_pseudo_injective leftPseudo rightPseudo pseudoSame]

/-- **Five-case injectivity with a fixed common Rule-5 reference and possibly different own
Rule-4b references.**  The two compared stages may use different own Rule-4b references; only
the common Rule-5 reference must agree.  The common component (Rule 5, index 3), together with
the Rule-4a and Rule-4c components, already determines the label on all five cases; the own
Rule-4b components are irrelevant to the determination. -/
theorem localizedCumulativeRule45Priority_rule5_commonReference_injective
    (ownLeft ownRight commonReference : RS)
    (left right : Option LocalizedAuxiliaryLabel)
    (same : localizedCumulativeRule45Priority (.rule5 ownLeft commonReference) left =
      localizedCumulativeRule45Priority (.rule5 ownRight commonReference) right) :
    left = right := by
  have component0 : localizedRule4aPriority left = localizedRule4aPriority right := by
    have := congrArg (fun vector : List Nat => vector.getD 0 0) same
    simpa [localizedCumulativeRule45Priority, cumulativePriority_getD_zero_three,
      cumulativePriority_getD_one_three, cumulativePriority_getD_two_three,
      cumulativePriority_getD_zero_four, cumulativePriority_getD_one_four,
      cumulativePriority_getD_two_four, cumulativePriority_getD_three_four] using this
  cases left with
  | none =>
      have rightZero : localizedRule4aPriority right = 0 := by
        rw [← component0]
        rfl
      exact (eq_none_of_rule4aPriority_eq_zero right rightZero).symm
  | some leftValue =>
      rcases leftValue with leftDescriptor | leftPseudo
      · have rightTwo : localizedRule4aPriority right = 2 := by
          rw [← component0]
          rfl
        obtain ⟨rightDescriptor, rightEq⟩ :=
          exists_chiral_of_rule4aPriority_eq_two right rightTwo
        rw [rightEq] at same ⊢
        have chiralSame :
            localizedRule5Priority commonReference (some (.chiral leftDescriptor)) =
              localizedRule5Priority commonReference (some (.chiral rightDescriptor)) := by
          have := congrArg (fun vector : List Nat => vector.getD 3 0) same
          simpa [localizedCumulativeRule45Priority, cumulativePriority_getD_zero_three,
            cumulativePriority_getD_one_three, cumulativePriority_getD_two_three,
            cumulativePriority_getD_zero_four, cumulativePriority_getD_one_four,
            cumulativePriority_getD_two_four, cumulativePriority_getD_three_four] using this
        rw [localizedRule5Priority_chiral_injective commonReference leftDescriptor
          rightDescriptor chiralSame]
      · have rightOne : localizedRule4aPriority right = 1 := by
          rw [← component0]
          rfl
        obtain ⟨rightPseudo, rightEq⟩ :=
          exists_pseudo_of_rule4aPriority_eq_one right rightOne
        rw [rightEq] at same ⊢
        have pseudoSame :
            localizedRule4cPriority (some (.pseudoasymmetric leftPseudo)) =
              localizedRule4cPriority (some (.pseudoasymmetric rightPseudo)) := by
          have := congrArg (fun vector : List Nat => vector.getD 2 0) same
          simpa [localizedCumulativeRule45Priority, cumulativePriority_getD_zero_three,
            cumulativePriority_getD_one_three, cumulativePriority_getD_two_three,
            cumulativePriority_getD_zero_four, cumulativePriority_getD_one_four,
            cumulativePriority_getD_two_four, cumulativePriority_getD_three_four] using this
        rw [localizedRule4cPriority_pseudo_injective leftPseudo rightPseudo pseudoSame]

/-- Fixed-`R` common Rule-5 reference, with the two own Rule-4b references allowed to differ. -/
theorem localizedCumulativeRule45Priority_rule5_fixedCommonReference_R_injective
    (ownLeft ownRight : RS) (left right : Option LocalizedAuxiliaryLabel)
    (same : localizedCumulativeRule45Priority (.rule5 ownLeft RS.R) left =
      localizedCumulativeRule45Priority (.rule5 ownRight RS.R) right) :
    left = right :=
  localizedCumulativeRule45Priority_rule5_commonReference_injective ownLeft ownRight RS.R
    left right same

/-- Fixed-`S` common Rule-5 reference, with the two own Rule-4b references allowed to differ. -/
theorem localizedCumulativeRule45Priority_rule5_fixedCommonReference_S_injective
    (ownLeft ownRight : RS) (left right : Option LocalizedAuxiliaryLabel)
    (same : localizedCumulativeRule45Priority (.rule5 ownLeft RS.S) left =
      localizedCumulativeRule45Priority (.rule5 ownRight RS.S) right) :
    left = right :=
  localizedCumulativeRule45Priority_rule5_commonReference_injective ownLeft ownRight RS.S
    left right same

/-- Equality of the `rule5NoRule4bReference` cumulative vectors is equivalent to label
equality. -/
theorem localizedCumulativeRule45Priority_rule5NoRule4bReference_eq_iff
    (reference : RS) (left right : Option LocalizedAuxiliaryLabel) :
    (localizedCumulativeRule45Priority (.rule5NoRule4bReference reference) left =
      localizedCumulativeRule45Priority (.rule5NoRule4bReference reference) right) ↔
        left = right :=
  ⟨localizedCumulativeRule45Priority_rule5NoRule4bReference_injective reference left right,
    fun same => congrArg
      (localizedCumulativeRule45Priority (.rule5NoRule4bReference reference)) same⟩

/-- Equality of the `rule5` cumulative vectors is equivalent to label equality. -/
theorem localizedCumulativeRule45Priority_rule5_eq_iff
    (ownReference rule5Reference : RS) (left right : Option LocalizedAuxiliaryLabel) :
    (localizedCumulativeRule45Priority (.rule5 ownReference rule5Reference) left =
      localizedCumulativeRule45Priority (.rule5 ownReference rule5Reference) right) ↔
        left = right :=
  ⟨localizedCumulativeRule45Priority_rule5_injective ownReference rule5Reference left right,
    fun same => congrArg
      (localizedCumulativeRule45Priority (.rule5 ownReference rule5Reference)) same⟩

/-- Fixing the common Rule-5 reference to `R` still determines the label for every own Rule-4b
reference, including own references different from `R`. -/
theorem localizedCumulativeRule45Priority_rule5_fixedRule5Reference_injective
    (ownReference : RS) (left right : Option LocalizedAuxiliaryLabel)
    (same : localizedCumulativeRule45Priority (.rule5 ownReference RS.R) left =
      localizedCumulativeRule45Priority (.rule5 ownReference RS.R) right) :
    left = right :=
  localizedCumulativeRule45Priority_rule5_injective ownReference RS.R left right same

/-- Fixed-`R` equivalence form of the five-case determination. -/
theorem localizedCumulativeRule45Priority_rule5_fixedRule5Reference_eq_iff
    (ownReference : RS) (left right : Option LocalizedAuxiliaryLabel) :
    (localizedCumulativeRule45Priority (.rule5 ownReference RS.R) left =
      localizedCumulativeRule45Priority (.rule5 ownReference RS.R) right) ↔
        left = right :=
  ⟨localizedCumulativeRule45Priority_rule5_fixedRule5Reference_injective ownReference left right,
    fun same => congrArg
      (localizedCumulativeRule45Priority (.rule5 ownReference RS.R)) same⟩

assert_kernel_only cumulativePriority_getD_zero_three
assert_kernel_only cumulativePriority_getD_one_three
assert_kernel_only cumulativePriority_getD_two_three
assert_kernel_only cumulativePriority_getD_zero_four
assert_kernel_only cumulativePriority_getD_one_four
assert_kernel_only cumulativePriority_getD_two_four
assert_kernel_only cumulativePriority_getD_three_four
assert_kernel_only eq_none_of_rule4aPriority_eq_zero
assert_kernel_only exists_pseudo_of_rule4aPriority_eq_one
assert_kernel_only exists_chiral_of_rule4aPriority_eq_two
assert_kernel_only localizedRule4cPriority_pseudo_injective
assert_kernel_only localizedRule4bPriority_chiral_injective
assert_kernel_only localizedRule5Priority_chiral_injective
assert_kernel_only localizedCumulativeRule45Priority_rule5NoRule4bReference_injective
assert_kernel_only localizedCumulativeRule45Priority_rule5_injective
assert_kernel_only localizedCumulativeRule45Priority_rule5_commonReference_injective
assert_kernel_only localizedCumulativeRule45Priority_rule5_fixedCommonReference_R_injective
assert_kernel_only localizedCumulativeRule45Priority_rule5_fixedCommonReference_S_injective
assert_kernel_only localizedCumulativeRule45Priority_rule5NoRule4bReference_eq_iff
assert_kernel_only localizedCumulativeRule45Priority_rule5_eq_iff
assert_kernel_only localizedCumulativeRule45Priority_rule5_fixedRule5Reference_injective
assert_kernel_only localizedCumulativeRule45Priority_rule5_fixedRule5Reference_eq_iff

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
