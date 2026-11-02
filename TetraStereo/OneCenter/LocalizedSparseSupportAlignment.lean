import TetraStereo.OneCenter.LocalizedSparsePhysicalFirstDifference

set_option autoImplicit false

namespace TetraStereo.OneCenter

open DeclarativeCIP

namespace SparseSupportAlignment

open SparsePhysicalFirstDifference



































/-! ## Addresses in a table -/

/-- An entry of `table` in sphere `depth` carries the address `position`. -/
def AddressAtDepth (table : List (List (OfficialSparseEntry ℕ))) (depth : ℕ)
    (position : List ℕ) : Prop :=
  ∃ entry, entry ∈ table.getD depth [] ∧ entry.1 = position

/-- Some entry of `table` carries the address `position`. -/
def HasAddress (table : List (List (OfficialSparseEntry ℕ))) (position : List ℕ) : Prop :=
  ∃ depth, AddressAtDepth table depth position

theorem addressAtDepth_iff_exists (table : List (List (OfficialSparseEntry ℕ))) (depth : ℕ)
    (position : List ℕ) :
    AddressAtDepth table depth position ↔
      ∃ entry, entry ∈ table.getD depth [] ∧ entry.1 = position :=
  Iff.rfl

/-- The support statement used by the physical first-difference module, phrased with the named
predicate. -/
theorem hasAddress_iff_exists (table : List (List (OfficialSparseEntry ℕ))) (position : List ℕ) :
    HasAddress table position ↔
      ∃ depth entry, entry ∈ table.getD depth [] ∧ entry.1 = position :=
  Iff.rfl

/-- A member of the row at `depth` is only possible below the layer count. -/
theorem mem_getD_imp_lt_length {table : List (List (OfficialSparseEntry ℕ))} {depth : ℕ}
    {entry : OfficialSparseEntry ℕ} (present : entry ∈ table.getD depth []) :
    depth < table.length := by
  induction table generalizing depth with
  | nil => simp at present
  | cons head tail inductionHypothesis =>
      cases depth with
      | zero => simp
      | succ depth =>
          rw [List.getD_cons_succ] at present
          have tailBound : depth < tail.length := inductionHypothesis present
          simp only [List.length_cons]
          omega

/-- Exact row depths make the length of an address determine its sphere. -/
theorem addressAtDepth_length {table : List (List (OfficialSparseEntry ℕ))} {depth : ℕ}
    {position : List ℕ} (depthExact : RowsAtDepth 0 table)
    (present : AddressAtDepth table depth position) : position.length = depth := by
  obtain ⟨entry, entryMem, entryAt⟩ := present
  rw [← entryAt]
  simpa using depthExact depth entry entryMem

/-! ## Unique strict enumerations -/

/-- The strict executed address order as a proposition. -/
def AddressBefore (left right : List ℕ) : Prop :=
  AddressCompare left right = Ordering.lt

theorem AddressCompare_antisymm {left right : List ℕ}
    (before : AddressCompare left right = Ordering.lt)
    (after : AddressCompare right left = Ordering.lt) : left = right := by
  have swapped := AddressCompare_swap left right
  rw [after, before] at swapped
  exact Ordering.noConfusion swapped

/-- Two strictly increasing address lists with the same members are equal. -/
theorem eq_of_pairwise_AddressBefore_of_mem_iff {left right : List (List ℕ)}
    (leftSorted : left.Pairwise AddressBefore)
    (rightSorted : right.Pairwise AddressBefore)
    (sameMem : ∀ position, position ∈ left ↔ position ∈ right) : left = right := by
  have leftNodup : left.Nodup :=
    List.nodup_iff_pairwise_ne.mpr
      (leftSorted.imp (fun {a b} compared => ne_of_AddressCompare_lt compared))
  have rightNodup : right.Nodup :=
    List.nodup_iff_pairwise_ne.mpr
      (rightSorted.imp (fun {a b} compared => ne_of_AddressCompare_lt compared))
  have permuted : List.Perm left right :=
    (List.perm_ext_iff_of_nodup leftNodup rightNodup).mpr sameMem
  exact List.Perm.eq_of_pairwise (l₁ := left) (l₂ := right) (le := AddressBefore)
    (fun a b _ _ before after => AddressCompare_antisymm before after)
    leftSorted rightSorted permuted

/-! ## Support equality descends to each sphere -/

/-- With exact row depths, equal global address support is equal address support in every fixed
sphere: the length of an address pins down its sphere. -/
theorem addressAtDepth_iff_of_hasAddress_iff
    {left right : List (List (OfficialSparseEntry ℕ))}
    (depthLeft : RowsAtDepth 0 left) (depthRight : RowsAtDepth 0 right)
    (support : ∀ position, HasAddress left position ↔ HasAddress right position)
    (depth : ℕ) (position : List ℕ) :
    AddressAtDepth left depth position ↔ AddressAtDepth right depth position := by
  constructor
  · intro present
    have positionLength : position.length = depth := addressAtDepth_length depthLeft present
    obtain ⟨entry, entryMem, entryAt⟩ := present
    obtain ⟨rightDepth, rightEntry, rightMem, rightAt⟩ :=
      (support position).mp ⟨depth, entry, entryMem, entryAt⟩
    have rightLength : rightEntry.1.length = rightDepth := by
      simpa using depthRight rightDepth rightEntry rightMem
    have depthEq : rightDepth = depth := by
      rw [← rightLength, rightAt, positionLength]
    rw [depthEq] at rightMem
    exact ⟨rightEntry, rightMem, rightAt⟩
  · intro present
    have positionLength : position.length = depth := addressAtDepth_length depthRight present
    obtain ⟨entry, entryMem, entryAt⟩ := present
    obtain ⟨leftDepth, leftEntry, leftMem, leftAt⟩ :=
      (support position).mpr ⟨depth, entry, entryMem, entryAt⟩
    have leftLength : leftEntry.1.length = leftDepth := by
      simpa using depthLeft leftDepth leftEntry leftMem
    have depthEq : leftDepth = depth := by
      rw [← leftLength, leftAt, positionLength]
    rw [depthEq] at leftMem
    exact ⟨leftEntry, leftMem, leftAt⟩

/-! ## Rows with the same addresses are equal -/

/-- Strictly increasing rows with the same addresses are equal, hence have the same cardinality. -/
theorem rowAddresses_eq
    {left right : List (List (OfficialSparseEntry ℕ))}
    (wellFormedLeft : SparseTableWellFormed left)
    (wellFormedRight : SparseTableWellFormed right)
    (support : ∀ position, HasAddress left position ↔ HasAddress right position)
    (depth : ℕ) :
    (left.getD depth []).map Prod.fst = (right.getD depth []).map Prod.fst := by
  have leftSorted : ((left.getD depth []).map Prod.fst).Pairwise AddressBefore :=
    List.Pairwise.map Prod.fst (fun _ _ before => before) (wellFormedLeft.increasing depth)
  have rightSorted : ((right.getD depth []).map Prod.fst).Pairwise AddressBefore :=
    List.Pairwise.map Prod.fst (fun _ _ before => before) (wellFormedRight.increasing depth)
  refine eq_of_pairwise_AddressBefore_of_mem_iff leftSorted rightSorted ?_
  intro position
  rw [List.mem_map, List.mem_map]
  exact addressAtDepth_iff_of_hasAddress_iff wellFormedLeft.depthExact
    wellFormedRight.depthExact support depth position

/-- Equal support and well-formedness give equal layer counts.  Exact depth is not enough here:
inhabitation of every sphere below the layer count is what exposes each layer index in the
support. -/
theorem length_le_of_hasAddress_iff
    {left right : List (List (OfficialSparseEntry ℕ))}
    (wellFormedLeft : SparseTableWellFormed left)
    (wellFormedRight : SparseTableWellFormed right)
    (support : ∀ position, HasAddress left position ↔ HasAddress right position) :
    left.length ≤ right.length := by
  by_contra notLe
  have rightBelow : right.length < left.length := Nat.lt_of_not_ge notLe
  have rowNonempty : left.getD right.length [] ≠ [] :=
    wellFormedLeft.nonempty right.length rightBelow
  obtain ⟨entry, entryMem⟩ :=
    List.exists_mem_of_ne_nil _ rowNonempty
  have entryLength : entry.1.length = right.length := by
    simpa using wellFormedLeft.depthExact right.length entry entryMem
  obtain ⟨rightDepth, rightEntry, rightMem, rightAt⟩ :=
    (support entry.1).mp ⟨right.length, entry, entryMem, rfl⟩
  have rightEntryLength : rightEntry.1.length = rightDepth := by
    simpa using wellFormedRight.depthExact rightDepth rightEntry rightMem
  have depthEq : rightDepth = right.length := by
    rw [← rightEntryLength, rightAt, entryLength]
  have below : rightDepth < right.length := mem_getD_imp_lt_length rightMem
  rw [depthEq] at below
  exact absurd below (Nat.lt_irrefl _)

theorem length_eq_of_hasAddress_iff
    {left right : List (List (OfficialSparseEntry ℕ))}
    (wellFormedLeft : SparseTableWellFormed left)
    (wellFormedRight : SparseTableWellFormed right)
    (support : ∀ position, HasAddress left position ↔ HasAddress right position) :
    left.length = right.length :=
  Nat.le_antisymm
    (length_le_of_hasAddress_iff wellFormedLeft wellFormedRight support)
    (length_le_of_hasAddress_iff wellFormedRight wellFormedLeft
      (fun position => (support position).symm))

theorem cardinality_rows_eq_of_hasAddress_iff
    {left right : List (List (OfficialSparseEntry ℕ))}
    (wellFormedLeft : SparseTableWellFormed left)
    (wellFormedRight : SparseTableWellFormed right)
    (support : ∀ position, HasAddress left position ↔ HasAddress right position)
    (depth : ℕ) :
    (left.getD depth []).length = (right.getD depth []).length := by
  simpa using congrArg List.length
    (rowAddresses_eq wellFormedLeft wellFormedRight support depth)

/-- Equal per-sphere address rows produce equal flattened address sequences.  The observation
types of the two tables may differ: only the addresses are inspected. -/
theorem flattenAddresses_eq_of_rows {α β : Type*}
    {left : List (List (OfficialSparseEntry α))}
    {right : List (List (OfficialSparseEntry β))}
    (lengthEq : left.length = right.length)
    (rows : ∀ depth, (left.getD depth []).map Prod.fst =
      (right.getD depth []).map Prod.fst) :
    left.flatten.map Prod.fst = right.flatten.map Prod.fst := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons head tail => simp at lengthEq
  | cons head tail inductionHypothesis =>
      cases right with
      | nil => simp at lengthEq
      | cons rightHead rightTail =>
          have headEq : head.map Prod.fst = rightHead.map Prod.fst := by
            simpa using rows 0
          have tailRows : ∀ depth,
              (tail.getD depth []).map Prod.fst =
                (rightTail.getD depth []).map Prod.fst := by
            intro depth
            simpa using rows (depth + 1)
          have tailLength : tail.length = rightTail.length := by simpa using lengthEq
          rw [List.flatten_cons, List.flatten_cons, List.map_append, List.map_append,
            headEq, inductionHypothesis tailLength tailRows]

theorem flattenAddresses_eq_of_hasAddress_iff
    {left right : List (List (OfficialSparseEntry ℕ))}
    (wellFormedLeft : SparseTableWellFormed left)
    (wellFormedRight : SparseTableWellFormed right)
    (support : ∀ position, HasAddress left position ↔ HasAddress right position) :
    left.flatten.map Prod.fst = right.flatten.map Prod.fst :=
  flattenAddresses_eq_of_rows
    (length_eq_of_hasAddress_iff wellFormedLeft wellFormedRight support)
    (fun depth => rowAddresses_eq wellFormedLeft wellFormedRight support depth)

/-! ## The alignment record -/

/-- The three structural facts consumed by
`compareSparseLayers_eq_compareLex_commonSupport`: equal layer count, equal sphere cardinalities,
and equal flattened address sequences. -/
structure SparseAlignment {α : Type*}
    (left right : List (List (OfficialSparseEntry α))) : Prop where
  lengthEq : left.length = right.length
  cardinality : ∀ depth, (left.getD depth []).length = (right.getD depth []).length
  sameAddresses : left.flatten.map Prod.fst = right.flatten.map Prod.fst

/-- Equal support of two well-formed tables yields the full common alignment. -/
theorem alignment_of_wellFormed_sameSupport
    {left right : List (List (OfficialSparseEntry ℕ))}
    (wellFormedLeft : SparseTableWellFormed left)
    (wellFormedRight : SparseTableWellFormed right)
    (support : ∀ position, HasAddress left position ↔ HasAddress right position) :
    SparseAlignment left right := by
  have lengthEq : left.length = right.length :=
    length_eq_of_hasAddress_iff wellFormedLeft wellFormedRight support
  refine ⟨lengthEq, ?_, ?_⟩
  · intro depth
    exact cardinality_rows_eq_of_hasAddress_iff wellFormedLeft wellFormedRight support depth
  · exact flattenAddresses_eq_of_hasAddress_iff wellFormedLeft wellFormedRight support

/-- A Rule-1a tie between well-formed, strictly positive tables yields the full common
alignment.  All three structural facts are derived; the only inputs are the tie itself, the two
well-formedness certificates, and positivity (needed by the physical first-difference module to
recover support from the tie). -/
theorem alignment_of_compareSparseLayers_eq
    {left right : List (List (OfficialSparseEntry ℕ))}
    (wellFormedLeft : SparseTableWellFormed left)
    (wellFormedRight : SparseTableWellFormed right)
    (positiveLeft : TablePositive left) (positiveRight : TablePositive right)
    (tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      left right = Ordering.eq) :
    SparseAlignment left right :=
  alignment_of_wellFormed_sameSupport wellFormedLeft wellFormedRight
    (sameSupport_of_compareSparseLayers_eq wellFormedLeft wellFormedRight
      positiveLeft positiveRight tied)

/-! ## Any scalar comparator on the derived alignment -/

/-- The generic common-support comparison, consuming the derived alignment.  The comparator is
arbitrary: no positivity, zero filling, or direction is assumed. -/
theorem compareSparseLayers_eq_compareLex_of_alignment {α : Type*}
    (compareObservation : α → α → Ordering)
    {left right : List (List (OfficialSparseEntry α))}
    (alignment : SparseAlignment left right) :
    OfficialRuleMajorKey.compareSparseLayers compareObservation left right =
      List.compareLex compareObservation
        (left.flatten.map Prod.snd) (right.flatten.map Prod.snd) :=
  compareSparseLayers_eq_compareLex_commonSupport compareObservation
    alignment.lengthEq alignment.cardinality alignment.sameAddresses

/-- After a Rule-1a tie, *any* scalar comparator — including the reversed Rule-1b distance
comparator and a larger-senior mass comparator — compares the two tables by the pointwise
comparison of their flattened observations along the common address schedule. -/
theorem compareSparseLayers_eq_compareLex_commonSupport_of_tie
    {left right : List (List (OfficialSparseEntry ℕ))}
    (wellFormedLeft : SparseTableWellFormed left)
    (wellFormedRight : SparseTableWellFormed right)
    (positiveLeft : TablePositive left) (positiveRight : TablePositive right)
    (tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      left right = Ordering.eq)
    (compareObservation : ℕ → ℕ → Ordering) :
    OfficialRuleMajorKey.compareSparseLayers compareObservation left right =
      List.compareLex compareObservation
        (left.flatten.map Prod.snd) (right.flatten.map Prod.snd) :=
  compareSparseLayers_eq_compareLex_of_alignment compareObservation
    (alignment_of_compareSparseLayers_eq wellFormedLeft wellFormedRight
      positiveLeft positiveRight tied)

/-- The layer counts agree after a Rule-1a tie. -/
theorem layerCount_eq_of_compareSparseLayers_eq
    {left right : List (List (OfficialSparseEntry ℕ))}
    (wellFormedLeft : SparseTableWellFormed left)
    (wellFormedRight : SparseTableWellFormed right)
    (positiveLeft : TablePositive left) (positiveRight : TablePositive right)
    (tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      left right = Ordering.eq) :
    left.length = right.length :=
  (alignment_of_compareSparseLayers_eq wellFormedLeft wellFormedRight
    positiveLeft positiveRight tied).lengthEq

/-- Every sphere has the same cardinality on both sides after a Rule-1a tie. -/
theorem layerCardinality_eq_of_compareSparseLayers_eq
    {left right : List (List (OfficialSparseEntry ℕ))}
    (wellFormedLeft : SparseTableWellFormed left)
    (wellFormedRight : SparseTableWellFormed right)
    (positiveLeft : TablePositive left) (positiveRight : TablePositive right)
    (tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      left right = Ordering.eq)
    (depth : ℕ) :
    (left.getD depth []).length = (right.getD depth []).length :=
  (alignment_of_compareSparseLayers_eq wellFormedLeft wellFormedRight
    positiveLeft positiveRight tied).cardinality depth

/-- The flattened address sequences coincide after a Rule-1a tie. -/
theorem flattenedAddresses_eq_of_compareSparseLayers_eq
    {left right : List (List (OfficialSparseEntry ℕ))}
    (wellFormedLeft : SparseTableWellFormed left)
    (wellFormedRight : SparseTableWellFormed right)
    (positiveLeft : TablePositive left) (positiveRight : TablePositive right)
    (tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      left right = Ordering.eq) :
    left.flatten.map Prod.fst = right.flatten.map Prod.fst :=
  (alignment_of_compareSparseLayers_eq wellFormedLeft wellFormedRight
    positiveLeft positiveRight tied).sameAddresses

/-! ## Transport to later observation tables

A Rule-1b distance table or a mass table uses the same addresses as the Rule-1a table of the same
tree, but its observations live in a possibly different type.  `SameAddressRows` records that a
table reproduces a reference table's sphere addresses; the alignment then transports. -/

/-- A table has the same address rows and layer count as a reference table. -/
structure SameAddressRows {α : Type*}
    (table : List (List (OfficialSparseEntry α)))
    (reference : List (List (OfficialSparseEntry ℕ))) : Prop where
  lengthEq : table.length = reference.length
  rows : ∀ depth, (table.getD depth []).map Prod.fst =
    (reference.getD depth []).map Prod.fst

/-- Transport the alignment along tables with the reference address rows. -/
theorem SparseAlignment.ofSameAddressRows {α : Type*}
    {left right : List (List (OfficialSparseEntry α))}
    {referenceLeft referenceRight : List (List (OfficialSparseEntry ℕ))}
    (alignment : SparseAlignment referenceLeft referenceRight)
    (leftRows : SameAddressRows left referenceLeft)
    (rightRows : SameAddressRows right referenceRight) :
    SparseAlignment left right := by
  have leftFlat : left.flatten.map Prod.fst = referenceLeft.flatten.map Prod.fst :=
    flattenAddresses_eq_of_rows (left := left) (right := referenceLeft)
      leftRows.lengthEq leftRows.rows
  have rightFlat : right.flatten.map Prod.fst = referenceRight.flatten.map Prod.fst :=
    flattenAddresses_eq_of_rows (left := right) (right := referenceRight)
      rightRows.lengthEq rightRows.rows
  refine ⟨?_, ?_, ?_⟩
  · exact leftRows.lengthEq.trans (alignment.lengthEq.trans rightRows.lengthEq.symm)
  · intro depth
    have leftLength : (left.getD depth []).length =
        (referenceLeft.getD depth []).length := by
      simpa using congrArg List.length (leftRows.rows depth)
    have rightLength : (right.getD depth []).length =
        (referenceRight.getD depth []).length := by
      simpa using congrArg List.length (rightRows.rows depth)
    exact leftLength.trans ((alignment.cardinality depth).trans rightLength.symm)
  · exact leftFlat.trans (alignment.sameAddresses.trans rightFlat.symm)

/-- Any scalar comparison of later tables whose address rows agree with a common reference
alignment is a pointwise comparison of their flattened observations. -/
theorem compareSparseLayers_eq_compareLex_of_sameAddressRows {α : Type*}
    (compareObservation : α → α → Ordering)
    {left right : List (List (OfficialSparseEntry α))}
    {referenceLeft referenceRight : List (List (OfficialSparseEntry ℕ))}
    (alignment : SparseAlignment referenceLeft referenceRight)
    (leftRows : SameAddressRows left referenceLeft)
    (rightRows : SameAddressRows right referenceRight) :
    OfficialRuleMajorKey.compareSparseLayers compareObservation left right =
      List.compareLex compareObservation
        (left.flatten.map Prod.snd) (right.flatten.map Prod.snd) :=
  compareSparseLayers_eq_compareLex_of_alignment compareObservation
    (SparseAlignment.ofSameAddressRows alignment leftRows rightRows)

/-- The full Rule-1a-to-later-table route: a Rule-1a tie produces the reference alignment, and any
later pair of tables (distance, mass, or other observations) with the same address rows compares
pointwise on the common schedule, with no assumption on the later comparator. -/
theorem compareSparseLayers_eq_compareLex_of_agreesWithRule1a {α : Type*}
    {rule1aLeft rule1aRight : List (List (OfficialSparseEntry ℕ))}
    (wellFormedLeft : SparseTableWellFormed rule1aLeft)
    (wellFormedRight : SparseTableWellFormed rule1aRight)
    (positiveLeft : TablePositive rule1aLeft)
    (positiveRight : TablePositive rule1aRight)
    (tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      rule1aLeft rule1aRight = Ordering.eq)
    {left right : List (List (OfficialSparseEntry α))}
    (leftRows : SameAddressRows left rule1aLeft)
    (rightRows : SameAddressRows right rule1aRight)
    (compareObservation : α → α → Ordering) :
    OfficialRuleMajorKey.compareSparseLayers compareObservation left right =
      List.compareLex compareObservation
        (left.flatten.map Prod.snd) (right.flatten.map Prod.snd) :=
  compareSparseLayers_eq_compareLex_of_sameAddressRows compareObservation
    (alignment_of_compareSparseLayers_eq wellFormedLeft wellFormedRight
      positiveLeft positiveRight tied) leftRows rightRows

end SparseSupportAlignment

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.SparseSupportAlignment.AddressAtDepth
assert_kernel_only TetraStereo.OneCenter.SparseSupportAlignment.HasAddress
assert_kernel_only TetraStereo.OneCenter.SparseSupportAlignment.addressAtDepth_iff_exists
assert_kernel_only TetraStereo.OneCenter.SparseSupportAlignment.hasAddress_iff_exists
assert_kernel_only TetraStereo.OneCenter.SparseSupportAlignment.mem_getD_imp_lt_length
assert_kernel_only TetraStereo.OneCenter.SparseSupportAlignment.addressAtDepth_length
assert_kernel_only TetraStereo.OneCenter.SparseSupportAlignment.AddressBefore
assert_kernel_only TetraStereo.OneCenter.SparseSupportAlignment.AddressCompare_antisymm
assert_kernel_only TetraStereo.OneCenter.SparseSupportAlignment.eq_of_pairwise_AddressBefore_of_mem_iff
assert_kernel_only TetraStereo.OneCenter.SparseSupportAlignment.addressAtDepth_iff_of_hasAddress_iff
assert_kernel_only TetraStereo.OneCenter.SparseSupportAlignment.rowAddresses_eq
assert_kernel_only TetraStereo.OneCenter.SparseSupportAlignment.length_le_of_hasAddress_iff
assert_kernel_only TetraStereo.OneCenter.SparseSupportAlignment.length_eq_of_hasAddress_iff
assert_kernel_only TetraStereo.OneCenter.SparseSupportAlignment.cardinality_rows_eq_of_hasAddress_iff
assert_kernel_only TetraStereo.OneCenter.SparseSupportAlignment.flattenAddresses_eq_of_rows
assert_kernel_only TetraStereo.OneCenter.SparseSupportAlignment.flattenAddresses_eq_of_hasAddress_iff
assert_kernel_only TetraStereo.OneCenter.SparseSupportAlignment.SparseAlignment
assert_kernel_only TetraStereo.OneCenter.SparseSupportAlignment.alignment_of_wellFormed_sameSupport
assert_kernel_only TetraStereo.OneCenter.SparseSupportAlignment.alignment_of_compareSparseLayers_eq
assert_kernel_only TetraStereo.OneCenter.SparseSupportAlignment.compareSparseLayers_eq_compareLex_of_alignment
assert_kernel_only TetraStereo.OneCenter.SparseSupportAlignment.compareSparseLayers_eq_compareLex_commonSupport_of_tie
assert_kernel_only TetraStereo.OneCenter.SparseSupportAlignment.layerCount_eq_of_compareSparseLayers_eq
assert_kernel_only TetraStereo.OneCenter.SparseSupportAlignment.layerCardinality_eq_of_compareSparseLayers_eq
assert_kernel_only TetraStereo.OneCenter.SparseSupportAlignment.flattenedAddresses_eq_of_compareSparseLayers_eq
assert_kernel_only TetraStereo.OneCenter.SparseSupportAlignment.SameAddressRows
assert_kernel_only TetraStereo.OneCenter.SparseSupportAlignment.SparseAlignment.ofSameAddressRows
assert_kernel_only TetraStereo.OneCenter.SparseSupportAlignment.compareSparseLayers_eq_compareLex_of_sameAddressRows
assert_kernel_only TetraStereo.OneCenter.SparseSupportAlignment.compareSparseLayers_eq_compareLex_of_agreesWithRule1a
