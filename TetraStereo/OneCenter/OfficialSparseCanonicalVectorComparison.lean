import TetraStereo.OneCenter.LocalizedSparseSupportAlignment
import TetraStereo.OneCenter.DeclarativeCIPCanonicalOrder
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace OfficialSparseCanonicalVectorComparison

open DeclarativeCIP
open Certificate.CanonicalSphereKey

/-!
# Signed comparison of rule-major sparse keys against canonical vector keys

`OfficialRuleMajorKey.compare` compares three exhaustive sparse addressed projections in the
normative rule order (Rule 1a, then Rule 1b, then Rule 2).  `Certificate.CanonicalSphereKey`
compares a vector of three sphere-major keys of optional signed observations.

This module proves the complete three-rule signed correspondence between the two orders.  The
bridge is the priority-oriented *encoded observation*: at every relative address, the observation
of a rule is read on the Rule-1a address support of the same key, and an address absent from that
support reads `⊥`.  Present observations are cast through `DeclarativeCIP.priorityValue`, so Rule 1a
and Rule 2 are larger-first while Rule 1b is smaller-distance-first.

The Rule-1a comparison is handled by the sparse first-difference algebra of
`LocalizedSparsePhysicalFirstDifference`, using positivity of the Rule-1a observations only.  Once
Rule 1a ties, the address support is shared, and the later columns reduce to a pointwise comparison
of their observations along that common support (`LocalizedSparseSupportAlignment`).  The first
difference is then read in the canonical shortlex address order, which is proved (not assumed) to
coincide with the sphere-major hierarchy address order of the declarative specification.
-/

noncomputable section

open scoped Classical

universe u

variable {V : Type u}

/-! ## Columns and encoded observations -/

/-- The sparse addressed table that carries one constitutional rule of a rule-major key. -/
def column (key : OfficialRuleMajorKey V) :
    ConstitutionalRule → List (List (OfficialSparseEntry ℕ))
  | .rule1aAtomicNumber => key.rule1a
  | .rule1bDuplicateNodeProximity => key.rule1b
  | .rule2AtomicMass => key.rule2

@[simp] theorem column_rule1a (key : OfficialRuleMajorKey V) :
    column key .rule1aAtomicNumber = key.rule1a := rfl

@[simp] theorem column_rule1b (key : OfficialRuleMajorKey V) :
    column key .rule1bDuplicateNodeProximity = key.rule1b := rfl

@[simp] theorem column_rule2 (key : OfficialRuleMajorKey V) :
    column key .rule2AtomicMass = key.rule2 := rfl

/-- The priority-oriented signed observation of one rule at a relative address.  The address
support is the Rule-1a support of the same key; an absent address reads `⊥`, never an integer
zero. -/
def encodedObservation (key : OfficialRuleMajorKey V) (rule : ConstitutionalRule)
    (path : List ℕ) : WithBot ℤ :=
  if SparseSupportAlignment.HasAddress key.rule1a path then
    ((priorityValue rule
      (SparsePhysicalFirstDifference.tableValue (column key rule) path) : ℤ) : WithBot ℤ)
  else ⊥

/-- Signed comparison of optional observations. -/
def compareObservation : WithBot ℤ → WithBot ℤ → Ordering :=
  compare

theorem compareObservation_eq_iff (left right : WithBot ℤ) :
    compareObservation left right = Ordering.eq ↔ left = right :=
  compare_eq_iff_eq

theorem compareObservation_eq_lt_iff (left right : WithBot ℤ) :
    compareObservation left right = Ordering.lt ↔ left < right :=
  compare_lt_iff_lt

theorem compareObservation_eq_gt_iff (left right : WithBot ℤ) :
    compareObservation left right = Ordering.gt ↔ right < left :=
  compare_gt_iff_gt

/-! ## Reading encoded observations -/

theorem encodedObservation_rule1a_of_has (key : OfficialRuleMajorKey V) {path : List ℕ}
    (present : SparseSupportAlignment.HasAddress key.rule1a path) :
    encodedObservation key .rule1aAtomicNumber path =
      ((SparsePhysicalFirstDifference.tableValue key.rule1a path : ℤ) : WithBot ℤ) := by
  unfold encodedObservation
  rw [if_pos present, column_rule1a]
  rfl

theorem encodedObservation_rule1b_of_has (key : OfficialRuleMajorKey V) {path : List ℕ}
    (present : SparseSupportAlignment.HasAddress key.rule1a path) :
    encodedObservation key .rule1bDuplicateNodeProximity path =
      ((-(SparsePhysicalFirstDifference.tableValue key.rule1b path : ℤ) : ℤ) : WithBot ℤ) := by
  unfold encodedObservation
  rw [if_pos present, column_rule1b]
  rfl

theorem encodedObservation_rule2_of_has (key : OfficialRuleMajorKey V) {path : List ℕ}
    (present : SparseSupportAlignment.HasAddress key.rule1a path) :
    encodedObservation key .rule2AtomicMass path =
      ((SparsePhysicalFirstDifference.tableValue key.rule2 path : ℤ) : WithBot ℤ) := by
  unfold encodedObservation
  rw [if_pos present, column_rule2]
  rfl

theorem encodedObservation_of_not_has (key : OfficialRuleMajorKey V) (rule : ConstitutionalRule)
    {path : List ℕ} (absent : ¬ SparseSupportAlignment.HasAddress key.rule1a path) :
    encodedObservation key rule path = ⊥ := by
  unfold encodedObservation
  rw [if_neg absent]

theorem encodedObservation_rule1a_of_not_has (key : OfficialRuleMajorKey V) {path : List ℕ}
    (absent : ¬ SparseSupportAlignment.HasAddress key.rule1a path) :
    encodedObservation key .rule1aAtomicNumber path = ⊥ :=
  encodedObservation_of_not_has key _ absent

theorem encodedObservation_rule1b_of_not_has (key : OfficialRuleMajorKey V) {path : List ℕ}
    (absent : ¬ SparseSupportAlignment.HasAddress key.rule1a path) :
    encodedObservation key .rule1bDuplicateNodeProximity path = ⊥ :=
  encodedObservation_of_not_has key _ absent

theorem encodedObservation_rule2_of_not_has (key : OfficialRuleMajorKey V) {path : List ℕ}
    (absent : ¬ SparseSupportAlignment.HasAddress key.rule1a path) :
    encodedObservation key .rule2AtomicMass path = ⊥ :=
  encodedObservation_of_not_has key _ absent

/-! ## Address membership in a table -/

theorem hasAddress_iff_exists_mem_map (table : List (List (OfficialSparseEntry ℕ)))
    (path : List ℕ) :
    SparseSupportAlignment.HasAddress table path ↔
      ∃ depth, path ∈ (table.getD depth []).map Prod.fst := by
  constructor
  · rintro ⟨depth, entry, present, addressEq⟩
    exact ⟨depth, List.mem_map.mpr ⟨entry, present, addressEq⟩⟩
  · rintro ⟨depth, present⟩
    obtain ⟨entry, entryPresent, addressEq⟩ := List.mem_map.mp present
    exact ⟨depth, entry, entryPresent, addressEq⟩

/-- Tables with the same address rows carry the same addresses. -/
theorem hasAddress_iff_of_sameAddressRows {table reference : List (List (OfficialSparseEntry ℕ))}
    (rows : SparseSupportAlignment.SameAddressRows table reference) (path : List ℕ) :
    SparseSupportAlignment.HasAddress table path ↔
      SparseSupportAlignment.HasAddress reference path := by
  rw [hasAddress_iff_exists_mem_map, hasAddress_iff_exists_mem_map]
  exact exists_congr fun depth => by rw [rows.rows depth]

/-- A table with no entry at an address reads zero there. -/
theorem tableValue_eq_zero_of_not_hasAddress {table : List (List (OfficialSparseEntry ℕ))}
    {path : List ℕ} (absent : ¬ SparseSupportAlignment.HasAddress table path) :
    SparsePhysicalFirstDifference.tableValue table path = 0 := by
  refine SparsePhysicalFirstDifference.tableValue_eq_zero_of_absent table path ?_
  intro depth entry present addressEq
  exact absent ⟨depth, entry, present, addressEq⟩

/-- For a well-formed, strictly positive Rule-1a table, a positive reading is exactly a present
address. -/
theorem tableValue_pos_iff_hasAddress {table : List (List (OfficialSparseEntry ℕ))}
    (wellFormed : SparsePhysicalFirstDifference.SparseTableWellFormed table)
    (positive : SparsePhysicalFirstDifference.TablePositive table) (path : List ℕ) :
    0 < SparsePhysicalFirstDifference.tableValue table path ↔
      SparseSupportAlignment.HasAddress table path := by
  constructor
  · intro nonzero
    unfold SparsePhysicalFirstDifference.tableValue at nonzero
    obtain ⟨entry, present, addressEq⟩ :=
      SparsePhysicalFirstDifference.exists_mem_of_rowValueAt_ne_zero
        (table.getD path.length []) path (by omega)
    exact ⟨path.length, entry, present, addressEq⟩
  · rintro ⟨depth, entry, present, addressEq⟩
    have lengthEq : entry.1.length = depth := by
      simpa using wellFormed.depthExact depth entry present
    unfold SparsePhysicalFirstDifference.tableValue
    rw [← addressEq, lengthEq]
    exact SparsePhysicalFirstDifference.rowValueAt_pos_of_mem _ _
      (fun other otherMem => positive depth other otherMem) ⟨entry, present, rfl⟩

/-! ## Reading a well-formed row and table at its own addresses -/

theorem rowValueAt_eq_snd_of_mem {row : List (OfficialSparseEntry ℕ)}
    (sorted : row.Pairwise fun left right =>
      SparsePhysicalFirstDifference.AddressCompare left.1 right.1 = Ordering.lt)
    {entry : OfficialSparseEntry ℕ} (present : entry ∈ row) :
    SparsePhysicalFirstDifference.rowValueAt row entry.1 = entry.2 := by
  induction row with
  | nil => cases present
  | cons head tail inductionHypothesis =>
      rcases List.mem_cons.mp present with rfl | later
      · simp
      · have headBefore : SparsePhysicalFirstDifference.AddressCompare head.1 entry.1 =
            Ordering.lt := (List.pairwise_cons.mp sorted).1 entry later
        have headNe : head.1 ≠ entry.1 := by
          intro equal
          rw [equal, SparsePhysicalFirstDifference.AddressCompare_refl] at headBefore
          exact Ordering.noConfusion headBefore
        rw [SparsePhysicalFirstDifference.rowValueAt_cons_of_ne head tail entry.1 headNe]
        exact inductionHypothesis (List.pairwise_cons.mp sorted).2 later

theorem tableValue_eq_snd_of_mem_getD {table : List (List (OfficialSparseEntry ℕ))}
    (depthExact : SparsePhysicalFirstDifference.RowsAtDepth 0 table)
    (increasing : SparsePhysicalFirstDifference.RowsIncreasing table)
    {depth : ℕ} {entry : OfficialSparseEntry ℕ} (present : entry ∈ table.getD depth []) :
    SparsePhysicalFirstDifference.tableValue table entry.1 = entry.2 := by
  have lengthEq : entry.1.length = depth := by
    simpa using depthExact depth entry present
  unfold SparsePhysicalFirstDifference.tableValue
  rw [lengthEq]
  exact rowValueAt_eq_snd_of_mem (increasing depth) present

/-- The flattened address sequence of a well-formed table is strictly sphere-major ordered. -/
theorem flatten_addresses_pairwise {table : List (List (OfficialSparseEntry ℕ))} :
    ∀ {offset : ℕ}, SparsePhysicalFirstDifference.RowsAtDepth offset table →
      SparsePhysicalFirstDifference.RowsIncreasing table →
      (table.flatten.map Prod.fst).Pairwise HierarchyAddressBefore := by
  intro offset
  induction table generalizing offset with
  | nil =>
      intro depthExact increasing
      simp
  | cons head tail inductionHypothesis =>
      intro depthExact increasing
      rw [List.flatten_cons, List.map_append, List.pairwise_append]
      have tailDepthExact : SparsePhysicalFirstDifference.RowsAtDepth (offset + 1) tail :=
        SparsePhysicalFirstDifference.RowsAtDepth.tail depthExact
      have tailIncreasing : SparsePhysicalFirstDifference.RowsIncreasing tail :=
        SparsePhysicalFirstDifference.RowsIncreasing.tail increasing
      refine ⟨?_, ?_, ?_⟩
      · exact SparsePhysicalFirstDifference.pairwise_map_fst_of_row head
          (SparsePhysicalFirstDifference.RowsAtDepth.head depthExact) (increasing 0)
      · exact inductionHypothesis tailDepthExact tailIncreasing
      · intro leftPosition leftPresent rightPosition rightPresent
        obtain ⟨leftEntry, leftEntryMem, leftAt⟩ := List.mem_map.mp leftPresent
        obtain ⟨rightEntry, rightEntryMem, rightAt⟩ := List.mem_map.mp rightPresent
        have leftLength : leftEntry.1.length = offset :=
          SparsePhysicalFirstDifference.RowsAtDepth.head depthExact leftEntry leftEntryMem
        obtain ⟨rightRow, rightRowMem, rightEntryInRow⟩ := List.mem_flatten.mp rightEntryMem
        obtain ⟨rightDepth, rightRowLookup⟩ := List.mem_iff_getElem?.mp rightRowMem
        have rightRowEq : tail.getD rightDepth [] = rightRow := by
          rw [List.getD_eq_getElem?_getD, rightRowLookup]
          rfl
        have inTailRow : rightEntry ∈ tail.getD rightDepth [] := by
          rw [rightRowEq]
          exact rightEntryInRow
        have rightLength : rightEntry.1.length = offset + 1 + rightDepth :=
          tailDepthExact rightDepth rightEntry inTailRow
        rw [← leftAt, ← rightAt]
        exact SparsePhysicalFirstDifference.hierarchyAddressBefore_of_length_lt (by
          rw [leftLength, rightLength]
          omega)

/-- The flattened observations of a well-formed table are the table read at the flattened
addresses. -/
theorem flatten_snd_eq_map_tableValue {table : List (List (OfficialSparseEntry ℕ))}
    (depthExact : SparsePhysicalFirstDifference.RowsAtDepth 0 table)
    (increasing : SparsePhysicalFirstDifference.RowsIncreasing table) :
    table.flatten.map Prod.snd =
      (table.flatten.map Prod.fst).map (SparsePhysicalFirstDifference.tableValue table) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro entry present
  obtain ⟨row, rowMem, entryMem⟩ := List.mem_flatten.mp present
  obtain ⟨depth, rowLookup⟩ := List.mem_iff_getElem?.mp rowMem
  have rowEq : table.getD depth [] = row := by
    rw [List.getD_eq_getElem?_getD, rowLookup]
    rfl
  rw [← rowEq] at entryMem
  exact (tableValue_eq_snd_of_mem_getD depthExact increasing entryMem).symm

/-- The address of an entry of any sphere occurs in the flattened address sequence. -/
theorem mem_flatten_map_fst_of_getD {table : List (List (OfficialSparseEntry ℕ))}
    {depth : ℕ} {entry : OfficialSparseEntry ℕ} (present : entry ∈ table.getD depth []) :
    entry.1 ∈ table.flatten.map Prod.fst := by
  have rowInTable : table.getD depth [] ∈ table := by
    cases lookup : table[depth]? with
    | some row =>
        rw [List.getD_eq_getElem?_getD, lookup]
        exact List.mem_iff_getElem?.mpr ⟨depth, lookup⟩
    | none =>
        have empty : table.getD depth [] = [] := by
          rw [List.getD_eq_getElem?_getD, lookup]
          rfl
        have inNil : entry ∈ ([] : List (OfficialSparseEntry ℕ)) := by
          rw [← empty]
          exact present
        exact False.elim (List.not_mem_nil inNil)
  exact List.mem_map.mpr ⟨entry, List.mem_flatten.mpr ⟨table.getD depth [], rowInTable, present⟩, rfl⟩

/-! ## First differences of encoded observations -/

/-- Path-level first difference under the canonical shortlex address order. -/
def PathFirstDifference (left right : List ℕ → WithBot ℤ) : Ordering → Prop
  | Ordering.eq => ∀ path, left path = right path
  | Ordering.lt =>
      ∃ path, left path < right path ∧
        ∀ earlier, Certificate.CanonicalSphereKey.AddressBefore earlier path →
          left earlier = right earlier
  | Ordering.gt =>
      ∃ path, right path < left path ∧
        ∀ earlier, Certificate.CanonicalSphereKey.AddressBefore earlier path →
          left earlier = right earlier

/-- The canonical shortlex address order and the sphere-major hierarchy address order coincide.
This is proved, not definitional. -/
theorem addressBefore_iff_hierarchyAddressBefore (earlier later : List ℕ) :
    Certificate.CanonicalSphereKey.AddressBefore earlier later ↔
      HierarchyAddressBefore earlier later := by
  unfold Certificate.CanonicalSphereKey.AddressBefore HierarchyAddressBefore HierarchyAddressKey
  show (earlier.length < later.length ∨
      (earlier.length = later.length ∧ List.Lex (· < ·) earlier later)) ↔
    List.Lex (· < ·) (earlier.length :: earlier) (later.length :: later)
  rw [SparsePhysicalFirstDifference.listLex_cons_cons_iff]

/-- A first difference of signed observations over the hierarchy address order is exactly a
path-level first difference over the canonical shortlex address order. -/
theorem firstDifferenceOutcome_iff_pathFirstDifference
    (left right : List ℕ → WithBot ℤ) (outcome : Ordering) :
    FirstDifferenceOutcome
        (fun path result => compareObservation (left path) (right path) = result) outcome ↔
      PathFirstDifference left right outcome := by
  cases outcome with
  | eq =>
      change (∀ path, compareObservation (left path) (right path) = Ordering.eq) ↔
        (∀ path, left path = right path)
      exact forall_congr' fun path => compareObservation_eq_iff _ _
  | lt =>
      change (∃ path, compareObservation (left path) (right path) = Ordering.lt ∧
          ∀ earlier, HierarchyAddressBefore earlier path →
            compareObservation (left earlier) (right earlier) = Ordering.eq) ↔
        (∃ path, left path < right path ∧
          ∀ earlier, Certificate.CanonicalSphereKey.AddressBefore earlier path →
            left earlier = right earlier)
      constructor
      · rintro ⟨path, decided, earlierTied⟩
        exact ⟨path, (compareObservation_eq_lt_iff _ _).1 decided,
          fun earlier before => (compareObservation_eq_iff _ _).1
            (earlierTied earlier ((addressBefore_iff_hierarchyAddressBefore earlier path).mp before))⟩
      · rintro ⟨path, decided, earlierTied⟩
        exact ⟨path, (compareObservation_eq_lt_iff _ _).2 decided,
          fun earlier before => (compareObservation_eq_iff _ _).2
            (earlierTied earlier ((addressBefore_iff_hierarchyAddressBefore earlier path).mpr before))⟩
  | gt =>
      change (∃ path, compareObservation (left path) (right path) = Ordering.gt ∧
          ∀ earlier, HierarchyAddressBefore earlier path →
            compareObservation (left earlier) (right earlier) = Ordering.eq) ↔
        (∃ path, right path < left path ∧
          ∀ earlier, Certificate.CanonicalSphereKey.AddressBefore earlier path →
            left earlier = right earlier)
      constructor
      · rintro ⟨path, decided, earlierTied⟩
        exact ⟨path, (compareObservation_eq_gt_iff _ _).1 decided,
          fun earlier before => (compareObservation_eq_iff _ _).1
            (earlierTied earlier ((addressBefore_iff_hierarchyAddressBefore earlier path).mp before))⟩
      · rintro ⟨path, decided, earlierTied⟩
        exact ⟨path, (compareObservation_eq_gt_iff _ _).2 decided,
          fun earlier before => (compareObservation_eq_iff _ _).2
            (earlierTied earlier ((addressBefore_iff_hierarchyAddressBefore earlier path).mpr before))⟩

/-! ## Relational characterisations of the natural outcomes -/

theorem descendingNatOutcome_eq_iff {left right : ℕ} :
    DescendingNatOutcome left right Ordering.eq ↔ left = right := by
  constructor
  · intro observed
    cases observed with
    | eq equal => exact equal
  · intro equal
    subst equal
    exact DescendingNatOutcome.eq rfl

theorem descendingNatOutcome_lt_iff {left right : ℕ} :
    DescendingNatOutcome left right Ordering.lt ↔ left < right := by
  constructor
  · intro observed
    cases observed with
    | lt lower => exact lower
  · intro lower
    exact DescendingNatOutcome.lt lower

theorem descendingNatOutcome_gt_iff {left right : ℕ} :
    DescendingNatOutcome left right Ordering.gt ↔ right < left := by
  constructor
  · intro observed
    cases observed with
    | gt higher => exact higher
  · intro higher
    exact DescendingNatOutcome.gt higher

/-! ## The structural predicate and the readback representation -/

/-- Structural well-formedness of one rule-major key for the signed canonical bridge.  All three
columns are well-formed; only Rule 1a is required to be strictly positive, and the later columns
must reproduce the Rule-1a address rows. -/
structure WellFormedRuleMajorKey (key : OfficialRuleMajorKey V) : Prop where
  wellFormed1a : SparsePhysicalFirstDifference.SparseTableWellFormed key.rule1a
  wellFormed1b : SparsePhysicalFirstDifference.SparseTableWellFormed key.rule1b
  wellFormed2 : SparsePhysicalFirstDifference.SparseTableWellFormed key.rule2
  positive1a : SparsePhysicalFirstDifference.TablePositive key.rule1a
  rows1b : SparseSupportAlignment.SameAddressRows key.rule1b key.rule1a
  rows2 : SparseSupportAlignment.SameAddressRows key.rule2 key.rule1a

/-- Pointwise, all-path readback of a rule-major key by a three-component canonical vector key at
one common layout `W, D`. -/
def Represents (W D : ℕ) (vector : List (Certificate.CanonicalSphereKey.Key ℤ))
    (key : OfficialRuleMajorKey V) : Prop :=
  ∀ r < 3, ∀ path,
    Certificate.CanonicalSphereKey.pathObservationOf W D (vector.getD r []) path =
      encodedObservation key (DeclarativeCIP.ruleOfIndex r) path

theorem compareRule1b_zero_zero :
    OfficialRuleMajorKey.compareRule1b 0 0 = Ordering.eq := by
  simpa [OfficialRuleMajorKey.compareRule1b] using
    SparsePhysicalFirstDifference.compareNat_zero_zero

/-! ## Signed pointwise correspondence per rule -/

/-- Rule 1a.  Rule 1a positivity is what makes the optional readback agree with the positive
natural first difference: a present observation is positive and hence strictly above absence. -/
theorem compareObservation_rule1a_iff
    {left right : OfficialRuleMajorKey V}
    (leftWellFormed : SparsePhysicalFirstDifference.SparseTableWellFormed left.rule1a)
    (rightWellFormed : SparsePhysicalFirstDifference.SparseTableWellFormed right.rule1a)
    (leftPositive : SparsePhysicalFirstDifference.TablePositive left.rule1a)
    (rightPositive : SparsePhysicalFirstDifference.TablePositive right.rule1a)
    (path : List ℕ) (outcome : Ordering) :
    compareObservation (encodedObservation left .rule1aAtomicNumber path)
        (encodedObservation right .rule1aAtomicNumber path) = outcome ↔
      DescendingNatOutcome (SparsePhysicalFirstDifference.tableValue left.rule1a path)
        (SparsePhysicalFirstDifference.tableValue right.rule1a path) outcome := by
  have leftPositiveAt := tableValue_pos_iff_hasAddress leftWellFormed leftPositive path
  have rightPositiveAt := tableValue_pos_iff_hasAddress rightWellFormed rightPositive path
  by_cases leftPresent : SparseSupportAlignment.HasAddress left.rule1a path
  · by_cases rightPresent : SparseSupportAlignment.HasAddress right.rule1a path
    · rw [encodedObservation_rule1a_of_has left leftPresent,
        encodedObservation_rule1a_of_has right rightPresent]
      cases outcome with
      | eq =>
          rw [compareObservation_eq_iff, WithBot.coe_eq_coe, descendingNatOutcome_eq_iff]
          constructor <;> intro h <;> omega
      | lt =>
          rw [compareObservation_eq_lt_iff, WithBot.coe_lt_coe, descendingNatOutcome_lt_iff]
          constructor <;> intro h <;> omega
      | gt =>
          rw [compareObservation_eq_gt_iff, WithBot.coe_lt_coe, descendingNatOutcome_gt_iff]
          constructor <;> intro h <;> omega
    · have leftValuePositive : 0 < SparsePhysicalFirstDifference.tableValue left.rule1a path :=
        leftPositiveAt.2 leftPresent
      have rightValueZero : SparsePhysicalFirstDifference.tableValue right.rule1a path = 0 :=
        tableValue_eq_zero_of_not_hasAddress rightPresent
      rw [encodedObservation_rule1a_of_has left leftPresent,
        encodedObservation_of_not_has right .rule1aAtomicNumber rightPresent, rightValueZero]
      cases outcome with
      | eq =>
          rw [compareObservation_eq_iff, descendingNatOutcome_eq_iff]
          constructor
          · intro h; exact absurd h (by simp)
          · intro h; exact absurd h (by omega)
      | lt =>
          rw [compareObservation_eq_lt_iff, descendingNatOutcome_lt_iff]
          constructor
          · intro h; exact absurd h (by simp)
          · intro h; exact absurd h (by omega)
      | gt =>
          rw [compareObservation_eq_gt_iff, descendingNatOutcome_gt_iff]
          constructor
          · intro _; exact leftValuePositive
          · intro _; simp
  · by_cases rightPresent : SparseSupportAlignment.HasAddress right.rule1a path
    · have rightValuePositive : 0 < SparsePhysicalFirstDifference.tableValue right.rule1a path :=
        rightPositiveAt.2 rightPresent
      have leftValueZero : SparsePhysicalFirstDifference.tableValue left.rule1a path = 0 :=
        tableValue_eq_zero_of_not_hasAddress leftPresent
      rw [encodedObservation_of_not_has left .rule1aAtomicNumber leftPresent, leftValueZero,
        encodedObservation_rule1a_of_has right rightPresent]
      cases outcome with
      | eq =>
          rw [compareObservation_eq_iff, descendingNatOutcome_eq_iff]
          constructor
          · intro h; exact absurd h.symm (by simp)
          · intro h; exact absurd h (by omega)
      | lt =>
          rw [compareObservation_eq_lt_iff, descendingNatOutcome_lt_iff]
          constructor
          · intro _; exact rightValuePositive
          · intro _; simp
      | gt =>
          rw [compareObservation_eq_gt_iff, descendingNatOutcome_gt_iff]
          constructor
          · intro h; exact absurd h (by simp)
          · intro h; exact absurd h (by omega)
    · have leftValueZero : SparsePhysicalFirstDifference.tableValue left.rule1a path = 0 :=
        tableValue_eq_zero_of_not_hasAddress leftPresent
      have rightValueZero : SparsePhysicalFirstDifference.tableValue right.rule1a path = 0 :=
        tableValue_eq_zero_of_not_hasAddress rightPresent
      rw [encodedObservation_of_not_has left .rule1aAtomicNumber leftPresent,
        encodedObservation_of_not_has right .rule1aAtomicNumber rightPresent,
        leftValueZero, rightValueZero]
      cases outcome with
      | eq => rw [compareObservation_eq_iff, descendingNatOutcome_eq_iff]; simp
      | lt => rw [compareObservation_eq_lt_iff, descendingNatOutcome_lt_iff]; simp
      | gt => rw [compareObservation_eq_gt_iff, descendingNatOutcome_gt_iff]; simp

/-- Rule 1b.  Guarded by the Rule-1a tie: on the shared support the negative distance readback
agrees with the reversed natural comparator. -/
theorem compareObservation_rule1b_iff
    {left right : OfficialRuleMajorKey V}
    (leftRows : SparseSupportAlignment.SameAddressRows left.rule1b left.rule1a)
    (rightRows : SparseSupportAlignment.SameAddressRows right.rule1b right.rule1a)
    (support : ∀ path, SparseSupportAlignment.HasAddress left.rule1a path ↔
      SparseSupportAlignment.HasAddress right.rule1a path)
    (path : List ℕ) (outcome : Ordering) :
    compareObservation (encodedObservation left .rule1bDuplicateNodeProximity path)
        (encodedObservation right .rule1bDuplicateNodeProximity path) = outcome ↔
      OfficialRuleMajorKey.compareRule1b
        (SparsePhysicalFirstDifference.tableValue left.rule1b path)
        (SparsePhysicalFirstDifference.tableValue right.rule1b path) = outcome := by
  have hcompare : ∀ result, OfficialRuleMajorKey.compareRule1b
        (SparsePhysicalFirstDifference.tableValue left.rule1b path)
        (SparsePhysicalFirstDifference.tableValue right.rule1b path) = result ↔
      DescendingNatOutcome (SparsePhysicalFirstDifference.tableValue right.rule1b path)
        (SparsePhysicalFirstDifference.tableValue left.rule1b path) result :=
    fun result => SparsePhysicalFirstDifference.compareNat_iff_descendingNatOutcome _ _ result
  by_cases leftPresent : SparseSupportAlignment.HasAddress left.rule1a path
  · have rightPresent : SparseSupportAlignment.HasAddress right.rule1a path :=
      (support path).1 leftPresent
    rw [encodedObservation_rule1b_of_has left leftPresent,
      encodedObservation_rule1b_of_has right rightPresent, hcompare]
    cases outcome with
    | eq =>
        rw [compareObservation_eq_iff, WithBot.coe_eq_coe, descendingNatOutcome_eq_iff]
        constructor <;> intro h <;> omega
    | lt =>
        rw [compareObservation_eq_lt_iff, WithBot.coe_lt_coe, descendingNatOutcome_lt_iff]
        constructor <;> intro h <;> omega
    | gt =>
        rw [compareObservation_eq_gt_iff, WithBot.coe_lt_coe, descendingNatOutcome_gt_iff]
        constructor <;> intro h <;> omega
  · have rightAbsent : ¬ SparseSupportAlignment.HasAddress right.rule1a path :=
      fun present => leftPresent ((support path).2 present)
    have leftLateAbsent : ¬ SparseSupportAlignment.HasAddress left.rule1b path :=
      fun present => leftPresent ((hasAddress_iff_of_sameAddressRows leftRows path).mp present)
    have rightLateAbsent : ¬ SparseSupportAlignment.HasAddress right.rule1b path :=
      fun present => rightAbsent ((hasAddress_iff_of_sameAddressRows rightRows path).mp present)
    rw [encodedObservation_of_not_has left .rule1bDuplicateNodeProximity leftPresent,
      encodedObservation_of_not_has right .rule1bDuplicateNodeProximity rightAbsent, hcompare,
      tableValue_eq_zero_of_not_hasAddress leftLateAbsent,
      tableValue_eq_zero_of_not_hasAddress rightLateAbsent]
    cases outcome with
    | eq => rw [compareObservation_eq_iff, descendingNatOutcome_eq_iff]; simp
    | lt => rw [compareObservation_eq_lt_iff, descendingNatOutcome_lt_iff]; simp
    | gt => rw [compareObservation_eq_gt_iff, descendingNatOutcome_gt_iff]; simp

/-- Rule 2.  Guarded by the Rule-1a tie: on the shared support the positive mass readback agrees
with the descending natural comparator. -/
theorem compareObservation_rule2_iff
    {left right : OfficialRuleMajorKey V}
    (leftRows : SparseSupportAlignment.SameAddressRows left.rule2 left.rule1a)
    (rightRows : SparseSupportAlignment.SameAddressRows right.rule2 right.rule1a)
    (support : ∀ path, SparseSupportAlignment.HasAddress left.rule1a path ↔
      SparseSupportAlignment.HasAddress right.rule1a path)
    (path : List ℕ) (outcome : Ordering) :
    compareObservation (encodedObservation left .rule2AtomicMass path)
        (encodedObservation right .rule2AtomicMass path) = outcome ↔
      OfficialRuleMajorKey.compareNat
        (SparsePhysicalFirstDifference.tableValue left.rule2 path)
        (SparsePhysicalFirstDifference.tableValue right.rule2 path) = outcome := by
  have hcompare : ∀ result, OfficialRuleMajorKey.compareNat
        (SparsePhysicalFirstDifference.tableValue left.rule2 path)
        (SparsePhysicalFirstDifference.tableValue right.rule2 path) = result ↔
      DescendingNatOutcome (SparsePhysicalFirstDifference.tableValue left.rule2 path)
        (SparsePhysicalFirstDifference.tableValue right.rule2 path) result :=
    fun result => SparsePhysicalFirstDifference.compareNat_iff_descendingNatOutcome _ _ result
  by_cases leftPresent : SparseSupportAlignment.HasAddress left.rule1a path
  · have rightPresent : SparseSupportAlignment.HasAddress right.rule1a path :=
      (support path).1 leftPresent
    rw [encodedObservation_rule2_of_has left leftPresent,
      encodedObservation_rule2_of_has right rightPresent, hcompare]
    cases outcome with
    | eq =>
        rw [compareObservation_eq_iff, WithBot.coe_eq_coe, descendingNatOutcome_eq_iff]
        constructor <;> intro h <;> omega
    | lt =>
        rw [compareObservation_eq_lt_iff, WithBot.coe_lt_coe, descendingNatOutcome_lt_iff]
        constructor <;> intro h <;> omega
    | gt =>
        rw [compareObservation_eq_gt_iff, WithBot.coe_lt_coe, descendingNatOutcome_gt_iff]
        constructor <;> intro h <;> omega
  · have rightAbsent : ¬ SparseSupportAlignment.HasAddress right.rule1a path :=
      fun present => leftPresent ((support path).2 present)
    have leftLateAbsent : ¬ SparseSupportAlignment.HasAddress left.rule2 path :=
      fun present => leftPresent ((hasAddress_iff_of_sameAddressRows leftRows path).mp present)
    have rightLateAbsent : ¬ SparseSupportAlignment.HasAddress right.rule2 path :=
      fun present => rightAbsent ((hasAddress_iff_of_sameAddressRows rightRows path).mp present)
    rw [encodedObservation_of_not_has left .rule2AtomicMass leftPresent,
      encodedObservation_of_not_has right .rule2AtomicMass rightAbsent, hcompare,
      tableValue_eq_zero_of_not_hasAddress leftLateAbsent,
      tableValue_eq_zero_of_not_hasAddress rightLateAbsent]
    cases outcome with
    | eq => rw [compareObservation_eq_iff, descendingNatOutcome_eq_iff]; simp
    | lt => rw [compareObservation_eq_lt_iff, descendingNatOutcome_lt_iff]; simp
    | gt => rw [compareObservation_eq_gt_iff, descendingNatOutcome_gt_iff]; simp

/-! ## Later columns on the shared address schedule -/

/-- After a Rule-1a tie, any scalar comparator of two later tables that share the Rule-1a address
rows is the independent relational first difference of the pointwise comparisons over the common
sphere-major address schedule. -/
theorem later_compareSparseLayers_eq_firstDifference
    (compareLate : ℕ → ℕ → Ordering) (compareLateZero : compareLate 0 0 = Ordering.eq)
    {left right : OfficialRuleMajorKey V}
    (leftRule1aWellFormed : SparsePhysicalFirstDifference.SparseTableWellFormed left.rule1a)
    (rightRule1aWellFormed : SparsePhysicalFirstDifference.SparseTableWellFormed right.rule1a)
    (leftRule1aPositive : SparsePhysicalFirstDifference.TablePositive left.rule1a)
    (rightRule1aPositive : SparsePhysicalFirstDifference.TablePositive right.rule1a)
    (tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      left.rule1a right.rule1a = Ordering.eq)
    {leftLate rightLate : List (List (OfficialSparseEntry ℕ))}
    (leftRows : SparseSupportAlignment.SameAddressRows leftLate left.rule1a)
    (rightRows : SparseSupportAlignment.SameAddressRows rightLate right.rule1a)
    (leftLateWellFormed : SparsePhysicalFirstDifference.SparseTableWellFormed leftLate)
    (rightLateWellFormed : SparsePhysicalFirstDifference.SparseTableWellFormed rightLate)
    (outcome : Ordering) :
    OfficialRuleMajorKey.compareSparseLayers compareLate leftLate rightLate = outcome ↔
      FirstDifferenceOutcome
        (fun position result =>
          compareLate (SparsePhysicalFirstDifference.tableValue leftLate position)
            (SparsePhysicalFirstDifference.tableValue rightLate position) = result)
        outcome := by
  have alignment : SparseSupportAlignment.SparseAlignment left.rule1a right.rule1a :=
    SparseSupportAlignment.alignment_of_compareSparseLayers_eq
      leftRule1aWellFormed rightRule1aWellFormed
      leftRule1aPositive rightRule1aPositive tied
  have lateAlignment : SparseSupportAlignment.SparseAlignment leftLate rightLate :=
    SparseSupportAlignment.SparseAlignment.ofSameAddressRows alignment leftRows rightRows
  rw [SparseSupportAlignment.compareSparseLayers_eq_compareLex_of_alignment compareLate lateAlignment]
  rw [flatten_snd_eq_map_tableValue leftLateWellFormed.depthExact leftLateWellFormed.increasing,
    flatten_snd_eq_map_tableValue rightLateWellFormed.depthExact rightLateWellFormed.increasing]
  rw [← lateAlignment.sameAddresses]
  exact DeclarativeCIP.compareLex_map_iff_firstDifference compareLate
    (fun position => SparsePhysicalFirstDifference.tableValue leftLate position)
    (fun position => SparsePhysicalFirstDifference.tableValue rightLate position)
    (leftLate.flatten.map Prod.fst)
    (flatten_addresses_pairwise leftLateWellFormed.depthExact leftLateWellFormed.increasing)
    (fun position absent => by
      have leftAbsent : ¬ SparseSupportAlignment.HasAddress leftLate position := by
        rintro ⟨depth, entry, present, addressEq⟩
        exact absent (by rw [← addressEq]; exact mem_flatten_map_fst_of_getD present)
      have rightAbsent : ¬ SparseSupportAlignment.HasAddress rightLate position := by
        rintro ⟨depth, entry, present, addressEq⟩
        exact absent (by
          rw [← addressEq, lateAlignment.sameAddresses]
          exact mem_flatten_map_fst_of_getD present)
      change compareLate (SparsePhysicalFirstDifference.tableValue leftLate position)
        (SparsePhysicalFirstDifference.tableValue rightLate position) = Ordering.eq
      rw [tableValue_eq_zero_of_not_hasAddress leftAbsent,
        tableValue_eq_zero_of_not_hasAddress rightAbsent, compareLateZero])
    outcome

/-! ## Path-level first differences per rule -/

/-- Rule 1a's executed comparison is exactly the path-level first difference of its signed
observations. -/
theorem rule1a_pathFirstDifference_iff
    {left right : OfficialRuleMajorKey V}
    (leftWellFormed : WellFormedRuleMajorKey left)
    (rightWellFormed : WellFormedRuleMajorKey right)
    (outcome : Ordering) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        left.rule1a right.rule1a = outcome ↔
      PathFirstDifference
        (encodedObservation left .rule1aAtomicNumber)
        (encodedObservation right .rule1aAtomicNumber) outcome := by
  rw [SparsePhysicalFirstDifference.compareSparseLayers_eq_firstDifference
    leftWellFormed.wellFormed1a rightWellFormed.wellFormed1a
    leftWellFormed.positive1a rightWellFormed.positive1a outcome]
  exact (FirstDifferenceOutcome.congr (fun position result =>
    (compareObservation_rule1a_iff leftWellFormed.wellFormed1a rightWellFormed.wellFormed1a
      leftWellFormed.positive1a rightWellFormed.positive1a position result).symm)
    outcome).trans (firstDifferenceOutcome_iff_pathFirstDifference _ _ outcome)

/-- Rule 1b's executed comparison, guarded by the Rule-1a tie, is exactly the path-level first
difference of its signed observations. -/
theorem rule1b_pathFirstDifference_iff
    {left right : OfficialRuleMajorKey V}
    (leftWellFormed : WellFormedRuleMajorKey left)
    (rightWellFormed : WellFormedRuleMajorKey right)
    (tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      left.rule1a right.rule1a = Ordering.eq)
    (outcome : Ordering) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b
        left.rule1b right.rule1b = outcome ↔
      PathFirstDifference
        (encodedObservation left .rule1bDuplicateNodeProximity)
        (encodedObservation right .rule1bDuplicateNodeProximity) outcome := by
  have support : ∀ path, SparseSupportAlignment.HasAddress left.rule1a path ↔
      SparseSupportAlignment.HasAddress right.rule1a path :=
    SparsePhysicalFirstDifference.sameSupport_of_compareSparseLayers_eq
      leftWellFormed.wellFormed1a rightWellFormed.wellFormed1a
      leftWellFormed.positive1a rightWellFormed.positive1a tied
  exact (later_compareSparseLayers_eq_firstDifference OfficialRuleMajorKey.compareRule1b
      compareRule1b_zero_zero leftWellFormed.wellFormed1a rightWellFormed.wellFormed1a
      leftWellFormed.positive1a rightWellFormed.positive1a tied
      leftWellFormed.rows1b rightWellFormed.rows1b
      leftWellFormed.wellFormed1b rightWellFormed.wellFormed1b outcome).trans
    ((FirstDifferenceOutcome.congr (fun position result =>
      (compareObservation_rule1b_iff leftWellFormed.rows1b rightWellFormed.rows1b
        support position result).symm) outcome).trans
      (firstDifferenceOutcome_iff_pathFirstDifference _ _ outcome))

/-- Rule 2's executed comparison, guarded by the Rule-1a tie, is exactly the path-level first
difference of its signed observations. -/
theorem rule2_pathFirstDifference_iff
    {left right : OfficialRuleMajorKey V}
    (leftWellFormed : WellFormedRuleMajorKey left)
    (rightWellFormed : WellFormedRuleMajorKey right)
    (tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      left.rule1a right.rule1a = Ordering.eq)
    (outcome : Ordering) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        left.rule2 right.rule2 = outcome ↔
      PathFirstDifference
        (encodedObservation left .rule2AtomicMass)
        (encodedObservation right .rule2AtomicMass) outcome := by
  have support : ∀ path, SparseSupportAlignment.HasAddress left.rule1a path ↔
      SparseSupportAlignment.HasAddress right.rule1a path :=
    SparsePhysicalFirstDifference.sameSupport_of_compareSparseLayers_eq
      leftWellFormed.wellFormed1a rightWellFormed.wellFormed1a
      leftWellFormed.positive1a rightWellFormed.positive1a tied
  exact (later_compareSparseLayers_eq_firstDifference OfficialRuleMajorKey.compareNat
      SparsePhysicalFirstDifference.compareNat_zero_zero
      leftWellFormed.wellFormed1a rightWellFormed.wellFormed1a
      leftWellFormed.positive1a rightWellFormed.positive1a tied
      leftWellFormed.rows2 rightWellFormed.rows2
      leftWellFormed.wellFormed2 rightWellFormed.wellFormed2 outcome).trans
    ((FirstDifferenceOutcome.congr (fun position result =>
      (compareObservation_rule2_iff leftWellFormed.rows2 rightWellFormed.rows2
        support position result).symm) outcome).trans
      (firstDifferenceOutcome_iff_pathFirstDifference _ _ outcome))

/-! ## List comparison versus the list order

The `compare` selected at a list type is core's lexicographic `List.compareLex`.  The list order
used by the canonical vector keys is Mathlib's `List.Lex (· < ·)`.  The following bridge identifies
them level by level, starting from the `WithBot ℤ` observations. -/

/-- A cons/cons list comparison is a head comparison, or equal heads and a tail comparison. -/
theorem listLex_cons_cons_iff {α : Type*} [LinearOrder α] {a b : α} {l₁ l₂ : List α} :
    (a :: l₁ : List α) < b :: l₂ ↔ a < b ∨ a = b ∧ l₁ < l₂ := by
  constructor
  · intro h
    have h' : List.Lex (· < ·) (a :: l₁) (b :: l₂) := h
    match h' with
    | .rel headBefore => exact Or.inl headBefore
    | .cons tailBefore => exact Or.inr ⟨rfl, tailBefore⟩
  · rintro (headBefore | ⟨rfl, tailBefore⟩)
    · exact List.Lex.rel headBefore
    · exact List.Lex.cons tailBefore

/-- Equal heads can be cancelled from a list comparison. -/
theorem listLex_cons_cons_same {α : Type*} [LinearOrder α] {a : α} {l₁ l₂ : List α} :
    (a :: l₁ : List α) < a :: l₂ ↔ l₁ < l₂ := by
  constructor
  · intro h
    have h' : List.Lex (· < ·) (a :: l₁) (a :: l₂) := h
    match h' with
    | .rel headBefore => exact absurd headBefore (lt_irrefl a)
    | .cons tailBefore => exact tailBefore
  · intro h
    exact List.Lex.cons h

/-- Lexicographic list comparison is the list order when the scalar comparator agrees with the
scalar order in all three outcomes. -/
theorem listCompareLex_iff_lex {α : Type*} [LinearOrder α] {cmp : α → α → Ordering}
    (cmpEq : ∀ a b : α, cmp a b = Ordering.eq ↔ a = b)
    (cmpLt : ∀ a b : α, cmp a b = Ordering.lt ↔ a < b)
    (cmpGt : ∀ a b : α, cmp a b = Ordering.gt ↔ b < a) (l₁ l₂ : List α) :
    (List.compareLex cmp l₁ l₂ = Ordering.lt ↔ l₁ < l₂) ∧
      (List.compareLex cmp l₁ l₂ = Ordering.gt ↔ l₂ < l₁) ∧
        (List.compareLex cmp l₁ l₂ = Ordering.eq ↔ l₁ = l₂) := by
  induction l₁ generalizing l₂ with
  | nil =>
      cases l₂ with
      | nil =>
          rw [List.compareLex_nil_nil]
          refine ⟨?_, ?_, ?_⟩
          · constructor
            · intro h; cases h
            · intro h; cases h
          · constructor
            · intro h; cases h
            · intro h; cases h
          · constructor
            · intro _; rfl
            · intro _; rfl
      | cons b l₂ =>
          rw [List.compareLex_nil_cons]
          refine ⟨?_, ?_, ?_⟩
          · constructor
            · intro _; exact List.Lex.nil
            · intro _; rfl
          · constructor
            · intro h; cases h
            · intro h; cases h
          · constructor
            · intro h; cases h
            · intro h; cases h
  | cons a l₁ ih =>
      cases l₂ with
      | nil =>
          rw [List.compareLex_cons_nil]
          refine ⟨?_, ?_, ?_⟩
          · constructor
            · intro h; cases h
            · intro h; cases h
          · constructor
            · intro _; exact List.Lex.nil
            · intro _; rfl
          · constructor
            · intro h; cases h
            · intro h; cases h
      | cons b l₂ =>
          cases h : cmp a b with
          | lt =>
              have headBefore : a < b := (cmpLt a b).mp h
              rw [List.compareLex_cons_cons, h, Ordering.lt_then]
              refine ⟨?_, ?_, ?_⟩
              · constructor
                · intro _; exact List.Lex.rel headBefore
                · intro _; rfl
              · constructor
                · intro hc; cases hc
                · intro hlex
                  rcases listLex_cons_cons_iff.mp hlex with headAfter | ⟨headsEqual, _⟩
                  · exact absurd headAfter (not_lt_of_ge (le_of_lt headBefore))
                  · exact absurd headsEqual.symm (ne_of_lt headBefore)
              · constructor
                · intro hc; cases hc
                · intro he
                  have headsEqual : a = b := ((List.cons.injEq a l₁ b l₂).mp he).1
                  exact absurd headsEqual (ne_of_lt headBefore)
          | gt =>
              have headAfter : b < a := (cmpGt a b).mp h
              rw [List.compareLex_cons_cons, h, Ordering.gt_then]
              refine ⟨?_, ?_, ?_⟩
              · constructor
                · intro hc; cases hc
                · intro hlex
                  rcases listLex_cons_cons_iff.mp hlex with headBefore | ⟨headsEqual, _⟩
                  · exact absurd headBefore (not_lt_of_ge (le_of_lt headAfter))
                  · exact absurd headsEqual.symm (ne_of_lt headAfter)
              · constructor
                · intro _; exact List.Lex.rel headAfter
                · intro _; rfl
              · constructor
                · intro hc; cases hc
                · intro he
                  have headsEqual : a = b := ((List.cons.injEq a l₁ b l₂).mp he).1
                  exact absurd headsEqual.symm (ne_of_lt headAfter)
          | eq =>
              have headsEqual : a = b := (cmpEq a b).mp h
              subst headsEqual
              rw [List.compareLex_cons_cons, h, Ordering.eq_then]
              refine ⟨?_, ?_, ?_⟩
              · rw [listLex_cons_cons_same]
                exact (ih l₂).1
              · rw [listLex_cons_cons_same]
                exact (ih l₂).2.1
              · rw [List.cons_inj_right]
                exact (ih l₂).2.2

/-! ### Comparison levels of the canonical vector key -/

theorem withBotCompare_eq_iff (left right : WithBot ℤ) :
    compare left right = Ordering.eq ↔ left = right :=
  compare_eq_iff_eq

theorem withBotCompare_lt_iff (left right : WithBot ℤ) :
    compare left right = Ordering.lt ↔ left < right :=
  compare_lt_iff_lt

theorem withBotCompare_gt_iff (left right : WithBot ℤ) :
    compare left right = Ordering.gt ↔ right < left :=
  compare_gt_iff_gt

theorem levelCompare_eq_iff (left right : Certificate.CanonicalSphereKey.Level ℤ) :
    compare left right = Ordering.eq ↔ left = right :=
  (listCompareLex_iff_lex (cmp := compare) (fun a b => withBotCompare_eq_iff a b)
    (fun a b => withBotCompare_lt_iff a b) (fun a b => withBotCompare_gt_iff a b)
    left right).2.2

theorem levelCompare_lt_iff (left right : Certificate.CanonicalSphereKey.Level ℤ) :
    compare left right = Ordering.lt ↔ left < right :=
  (listCompareLex_iff_lex (cmp := compare) (fun a b => withBotCompare_eq_iff a b)
    (fun a b => withBotCompare_lt_iff a b) (fun a b => withBotCompare_gt_iff a b)
    left right).1

theorem levelCompare_gt_iff (left right : Certificate.CanonicalSphereKey.Level ℤ) :
    compare left right = Ordering.gt ↔ right < left :=
  (listCompareLex_iff_lex (cmp := compare) (fun a b => withBotCompare_eq_iff a b)
    (fun a b => withBotCompare_lt_iff a b) (fun a b => withBotCompare_gt_iff a b)
    left right).2.1

theorem keyCompare_eq_iff (left right : Certificate.CanonicalSphereKey.Key ℤ) :
    compare left right = Ordering.eq ↔ left = right :=
  (listCompareLex_iff_lex (cmp := compare) (fun a b => levelCompare_eq_iff a b)
    (fun a b => levelCompare_lt_iff a b) (fun a b => levelCompare_gt_iff a b)
    left right).2.2

theorem keyCompare_lt_iff (left right : Certificate.CanonicalSphereKey.Key ℤ) :
    compare left right = Ordering.lt ↔ left < right :=
  (listCompareLex_iff_lex (cmp := compare) (fun a b => levelCompare_eq_iff a b)
    (fun a b => levelCompare_lt_iff a b) (fun a b => levelCompare_gt_iff a b)
    left right).1

theorem keyCompare_gt_iff (left right : Certificate.CanonicalSphereKey.Key ℤ) :
    compare left right = Ordering.gt ↔ right < left :=
  (listCompareLex_iff_lex (cmp := compare) (fun a b => levelCompare_eq_iff a b)
    (fun a b => levelCompare_lt_iff a b) (fun a b => levelCompare_gt_iff a b)
    left right).2.1

theorem vectorCompare_eq_iff (left right : List (Certificate.CanonicalSphereKey.Key ℤ)) :
    compare left right = Ordering.eq ↔ left = right :=
  (listCompareLex_iff_lex (cmp := compare) (fun a b => keyCompare_eq_iff a b)
    (fun a b => keyCompare_lt_iff a b) (fun a b => keyCompare_gt_iff a b)
    left right).2.2

theorem vectorCompare_lt_iff (left right : List (Certificate.CanonicalSphereKey.Key ℤ)) :
    compare left right = Ordering.lt ↔ left < right :=
  (listCompareLex_iff_lex (cmp := compare) (fun a b => keyCompare_eq_iff a b)
    (fun a b => keyCompare_lt_iff a b) (fun a b => keyCompare_gt_iff a b)
    left right).1

theorem vectorCompare_gt_iff (left right : List (Certificate.CanonicalSphereKey.Key ℤ)) :
    compare left right = Ordering.gt ↔ right < left :=
  (listCompareLex_iff_lex (cmp := compare) (fun a b => keyCompare_eq_iff a b)
    (fun a b => keyCompare_lt_iff a b) (fun a b => keyCompare_gt_iff a b)
    left right).2.1

/-- The list-level form of "the comparison never prefers the right key". -/
theorem vectorCompare_ne_lt_iff_le (left right : List (Certificate.CanonicalSphereKey.Key ℤ)) :
    compare left right ≠ Ordering.lt ↔ right ≤ left := by
  constructor
  · intro notLt
    cases hlt : compare left right with
    | lt => exact absurd hlt notLt
    | eq => exact le_of_eq ((vectorCompare_eq_iff left right).mp hlt).symm
    | gt => exact le_of_lt ((vectorCompare_gt_iff left right).mp hlt)
  · intro rightLe leftLt
    exact not_le_of_gt ((vectorCompare_lt_iff left right).mp leftLt) rightLe

/-! ## The full signed comparison theorem -/

/-- **Three-rule signed canonical-vector correspondence.**  The executed rule-major sparse
comparison of two structurally well-formed keys is the standard comparison of any two common-layout
canonical vector keys that read the same signed observations on every path. -/
theorem compare_eq_compare_vector
    {left right : OfficialRuleMajorKey V}
    (leftWellFormed : WellFormedRuleMajorKey left)
    (rightWellFormed : WellFormedRuleMajorKey right)
    {W D : ℕ} {leftVector rightVector : List (Certificate.CanonicalSphereKey.Key ℤ)}
    (leftShaped : Certificate.CanonicalSphereKey.VectorWellShaped 3 W D leftVector)
    (rightShaped : Certificate.CanonicalSphereKey.VectorWellShaped 3 W D rightVector)
    (leftRepresents : Represents W D leftVector left)
    (rightRepresents : Represents W D rightVector right) :
    OfficialRuleMajorKey.compare left right = compare leftVector rightVector := by
  change (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        left.rule1a right.rule1a).then
      ((OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b
          left.rule1b right.rule1b).then
        (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
          left.rule2 right.rule2)) = compare leftVector rightVector
  cases hRule1a : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      left.rule1a right.rule1a with
  | lt =>
      change Ordering.lt = compare leftVector rightVector
      obtain ⟨path, decisive, earlierTied⟩ :=
        (rule1a_pathFirstDifference_iff leftWellFormed rightWellFormed Ordering.lt).1 hRule1a
      symm
      rw [vectorCompare_lt_iff]
      refine (Certificate.CanonicalSphereKey.vector_lt_iff_pathObservation
        leftShaped rightShaped).2 ⟨0, by omega, path, ?_, ?_, ?_⟩
      · rw [leftRepresents 0 (by omega) path, rightRepresents 0 (by omega) path]
        exact decisive
      · intro r' hr' path'
        omega
      · intro earlier earlierBefore
        rw [leftRepresents 0 (by omega) earlier, rightRepresents 0 (by omega) earlier]
        exact earlierTied earlier earlierBefore
  | gt =>
      change Ordering.gt = compare leftVector rightVector
      obtain ⟨path, decisive, earlierTied⟩ :=
        (rule1a_pathFirstDifference_iff leftWellFormed rightWellFormed Ordering.gt).1 hRule1a
      symm
      rw [vectorCompare_gt_iff]
      refine (Certificate.CanonicalSphereKey.vector_lt_iff_pathObservation
        rightShaped leftShaped).2 ⟨0, by omega, path, ?_, ?_, ?_⟩
      · rw [rightRepresents 0 (by omega) path, leftRepresents 0 (by omega) path]
        exact decisive
      · intro r' hr' path'
        omega
      · intro earlier earlierBefore
        rw [rightRepresents 0 (by omega) earlier, leftRepresents 0 (by omega) earlier]
        exact (earlierTied earlier earlierBefore).symm
  | eq =>
      change (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b
            left.rule1b right.rule1b).then
          (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
            left.rule2 right.rule2) = compare leftVector rightVector
      have tied0 : ∀ path, Certificate.CanonicalSphereKey.pathObservationOf W D
            (leftVector.getD 0 []) path =
          Certificate.CanonicalSphereKey.pathObservationOf W D
            (rightVector.getD 0 []) path := by
        intro path
        rw [leftRepresents 0 (by omega) path, rightRepresents 0 (by omega) path]
        exact (rule1a_pathFirstDifference_iff leftWellFormed rightWellFormed
          Ordering.eq).1 hRule1a path
      cases hRule1b : OfficialRuleMajorKey.compareSparseLayers
          OfficialRuleMajorKey.compareRule1b left.rule1b right.rule1b with
      | lt =>
          change Ordering.lt = compare leftVector rightVector
          obtain ⟨path, decisive, earlierTied⟩ :=
            (rule1b_pathFirstDifference_iff leftWellFormed rightWellFormed hRule1a
              Ordering.lt).1 hRule1b
          symm
          rw [vectorCompare_lt_iff]
          refine (Certificate.CanonicalSphereKey.vector_lt_iff_pathObservation
            leftShaped rightShaped).2 ⟨1, by omega, path, ?_, ?_, ?_⟩
          · rw [leftRepresents 1 (by omega) path, rightRepresents 1 (by omega) path]
            exact decisive
          · intro r' hr' path'
            rcases (show r' = 0 by omega) with rfl
            exact tied0 path'
          · intro earlier earlierBefore
            rw [leftRepresents 1 (by omega) earlier, rightRepresents 1 (by omega) earlier]
            exact earlierTied earlier earlierBefore
      | gt =>
          change Ordering.gt = compare leftVector rightVector
          obtain ⟨path, decisive, earlierTied⟩ :=
            (rule1b_pathFirstDifference_iff leftWellFormed rightWellFormed hRule1a
              Ordering.gt).1 hRule1b
          symm
          rw [vectorCompare_gt_iff]
          refine (Certificate.CanonicalSphereKey.vector_lt_iff_pathObservation
            rightShaped leftShaped).2 ⟨1, by omega, path, ?_, ?_, ?_⟩
          · rw [rightRepresents 1 (by omega) path, leftRepresents 1 (by omega) path]
            exact decisive
          · intro r' hr' path'
            rcases (show r' = 0 by omega) with rfl
            exact (tied0 path').symm
          · intro earlier earlierBefore
            rw [rightRepresents 1 (by omega) earlier, leftRepresents 1 (by omega) earlier]
            exact (earlierTied earlier earlierBefore).symm
      | eq =>
          change (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
              left.rule2 right.rule2) = compare leftVector rightVector
          have tied1 : ∀ path, Certificate.CanonicalSphereKey.pathObservationOf W D
                (leftVector.getD 1 []) path =
              Certificate.CanonicalSphereKey.pathObservationOf W D
                (rightVector.getD 1 []) path := by
            intro path
            rw [leftRepresents 1 (by omega) path, rightRepresents 1 (by omega) path]
            exact (rule1b_pathFirstDifference_iff leftWellFormed rightWellFormed
              hRule1a Ordering.eq).1 hRule1b path
          cases hRule2 : OfficialRuleMajorKey.compareSparseLayers
              OfficialRuleMajorKey.compareNat left.rule2 right.rule2 with
          | lt =>
              change Ordering.lt = compare leftVector rightVector
              obtain ⟨path, decisive, earlierTied⟩ :=
                (rule2_pathFirstDifference_iff leftWellFormed rightWellFormed hRule1a
                  Ordering.lt).1 hRule2
              symm
              rw [vectorCompare_lt_iff]
              refine (Certificate.CanonicalSphereKey.vector_lt_iff_pathObservation
                leftShaped rightShaped).2 ⟨2, by omega, path, ?_, ?_, ?_⟩
              · rw [leftRepresents 2 (by omega) path, rightRepresents 2 (by omega) path]
                exact decisive
              · intro r' hr' path'
                rcases (show r' = 0 ∨ r' = 1 by omega) with rfl | rfl
                · exact tied0 path'
                · exact tied1 path'
              · intro earlier earlierBefore
                rw [leftRepresents 2 (by omega) earlier, rightRepresents 2 (by omega) earlier]
                exact earlierTied earlier earlierBefore
          | gt =>
              change Ordering.gt = compare leftVector rightVector
              obtain ⟨path, decisive, earlierTied⟩ :=
                (rule2_pathFirstDifference_iff leftWellFormed rightWellFormed hRule1a
                  Ordering.gt).1 hRule2
              symm
              rw [vectorCompare_gt_iff]
              refine (Certificate.CanonicalSphereKey.vector_lt_iff_pathObservation
                rightShaped leftShaped).2 ⟨2, by omega, path, ?_, ?_, ?_⟩
              · rw [rightRepresents 2 (by omega) path, leftRepresents 2 (by omega) path]
                exact decisive
              · intro r' hr' path'
                rcases (show r' = 0 ∨ r' = 1 by omega) with rfl | rfl
                · exact (tied0 path').symm
                · exact (tied1 path').symm
              · intro earlier earlierBefore
                rw [rightRepresents 2 (by omega) earlier, leftRepresents 2 (by omega) earlier]
                exact (earlierTied earlier earlierBefore).symm
          | eq =>
              symm
              rw [vectorCompare_eq_iff]
              refine (Certificate.CanonicalSphereKey.vector_eq_iff_pathObservation
                leftShaped rightShaped).2 ?_
              intro r hr path
              rcases (show r = 0 ∨ r = 1 ∨ r = 2 by omega) with rfl | rfl | rfl
              · exact tied0 path
              · exact tied1 path
              · rw [leftRepresents 2 (by omega) path, rightRepresents 2 (by omega) path]
                exact (rule2_pathFirstDifference_iff leftWellFormed rightWellFormed
                  hRule1a Ordering.eq).1 hRule2 path

/-! ## Explicit outcome endpoints and the descending corollary -/

theorem compare_eq_iff_vector_eq
    {left right : OfficialRuleMajorKey V}
    (leftWellFormed : WellFormedRuleMajorKey left)
    (rightWellFormed : WellFormedRuleMajorKey right)
    {W D : ℕ} {leftVector rightVector : List (Certificate.CanonicalSphereKey.Key ℤ)}
    (leftShaped : Certificate.CanonicalSphereKey.VectorWellShaped 3 W D leftVector)
    (rightShaped : Certificate.CanonicalSphereKey.VectorWellShaped 3 W D rightVector)
    (leftRepresents : Represents W D leftVector left)
    (rightRepresents : Represents W D rightVector right) :
    OfficialRuleMajorKey.compare left right = Ordering.eq ↔ leftVector = rightVector := by
  rw [compare_eq_compare_vector leftWellFormed rightWellFormed leftShaped rightShaped
    leftRepresents rightRepresents]
  exact vectorCompare_eq_iff _ _

theorem compare_lt_iff_vector_lt
    {left right : OfficialRuleMajorKey V}
    (leftWellFormed : WellFormedRuleMajorKey left)
    (rightWellFormed : WellFormedRuleMajorKey right)
    {W D : ℕ} {leftVector rightVector : List (Certificate.CanonicalSphereKey.Key ℤ)}
    (leftShaped : Certificate.CanonicalSphereKey.VectorWellShaped 3 W D leftVector)
    (rightShaped : Certificate.CanonicalSphereKey.VectorWellShaped 3 W D rightVector)
    (leftRepresents : Represents W D leftVector left)
    (rightRepresents : Represents W D rightVector right) :
    OfficialRuleMajorKey.compare left right = Ordering.lt ↔ leftVector < rightVector := by
  rw [compare_eq_compare_vector leftWellFormed rightWellFormed leftShaped rightShaped
    leftRepresents rightRepresents]
  exact vectorCompare_lt_iff _ _

theorem compare_gt_iff_vector_gt
    {left right : OfficialRuleMajorKey V}
    (leftWellFormed : WellFormedRuleMajorKey left)
    (rightWellFormed : WellFormedRuleMajorKey right)
    {W D : ℕ} {leftVector rightVector : List (Certificate.CanonicalSphereKey.Key ℤ)}
    (leftShaped : Certificate.CanonicalSphereKey.VectorWellShaped 3 W D leftVector)
    (rightShaped : Certificate.CanonicalSphereKey.VectorWellShaped 3 W D rightVector)
    (leftRepresents : Represents W D leftVector left)
    (rightRepresents : Represents W D rightVector right) :
    OfficialRuleMajorKey.compare left right = Ordering.gt ↔ rightVector < leftVector := by
  rw [compare_eq_compare_vector leftWellFormed rightWellFormed leftShaped rightShaped
    leftRepresents rightRepresents]
  exact vectorCompare_gt_iff _ _

/-- Descending corollary: the executed comparison never prefers the right key exactly when the
right vector is at most the left vector. -/
theorem compare_ne_lt_iff_rightVector_le
    {left right : OfficialRuleMajorKey V}
    (leftWellFormed : WellFormedRuleMajorKey left)
    (rightWellFormed : WellFormedRuleMajorKey right)
    {W D : ℕ} {leftVector rightVector : List (Certificate.CanonicalSphereKey.Key ℤ)}
    (leftShaped : Certificate.CanonicalSphereKey.VectorWellShaped 3 W D leftVector)
    (rightShaped : Certificate.CanonicalSphereKey.VectorWellShaped 3 W D rightVector)
    (leftRepresents : Represents W D leftVector left)
    (rightRepresents : Represents W D rightVector right) :
    OfficialRuleMajorKey.compare left right ≠ Ordering.lt ↔ rightVector ≤ leftVector := by
  rw [compare_eq_compare_vector leftWellFormed rightWellFormed leftShaped rightShaped
    leftRepresents rightRepresents]
  exact vectorCompare_ne_lt_iff_le _ _

end

end OfficialSparseCanonicalVectorComparison

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.column
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.column_rule1a
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.column_rule1b
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.column_rule2
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.encodedObservation
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.compareObservation
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.compareObservation_eq_iff
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.compareObservation_eq_lt_iff
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.compareObservation_eq_gt_iff
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.encodedObservation_rule1a_of_has
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.encodedObservation_rule1b_of_has
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.encodedObservation_rule2_of_has
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.encodedObservation_of_not_has
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.encodedObservation_rule1a_of_not_has
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.encodedObservation_rule1b_of_not_has
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.encodedObservation_rule2_of_not_has
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.hasAddress_iff_exists_mem_map
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.hasAddress_iff_of_sameAddressRows
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.tableValue_eq_zero_of_not_hasAddress
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.tableValue_pos_iff_hasAddress
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.rowValueAt_eq_snd_of_mem
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.tableValue_eq_snd_of_mem_getD
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.flatten_addresses_pairwise
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.flatten_snd_eq_map_tableValue
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.mem_flatten_map_fst_of_getD
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.PathFirstDifference
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.addressBefore_iff_hierarchyAddressBefore
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.firstDifferenceOutcome_iff_pathFirstDifference
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.descendingNatOutcome_eq_iff
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.descendingNatOutcome_lt_iff
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.descendingNatOutcome_gt_iff
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.WellFormedRuleMajorKey
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.Represents
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.compareRule1b_zero_zero
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.compareObservation_rule1a_iff
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.compareObservation_rule1b_iff
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.compareObservation_rule2_iff
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.later_compareSparseLayers_eq_firstDifference
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.rule1a_pathFirstDifference_iff
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.rule1b_pathFirstDifference_iff
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.rule2_pathFirstDifference_iff
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.listLex_cons_cons_iff
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.listLex_cons_cons_same
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.listCompareLex_iff_lex
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.withBotCompare_eq_iff
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.withBotCompare_lt_iff
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.withBotCompare_gt_iff
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.levelCompare_eq_iff
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.levelCompare_lt_iff
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.levelCompare_gt_iff
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.keyCompare_eq_iff
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.keyCompare_lt_iff
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.keyCompare_gt_iff
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.vectorCompare_eq_iff
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.vectorCompare_lt_iff
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.vectorCompare_gt_iff
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.vectorCompare_ne_lt_iff_le
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.compare_eq_compare_vector
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.compare_eq_iff_vector_eq
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.compare_lt_iff_vector_lt
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.compare_gt_iff_vector_gt
assert_kernel_only TetraStereo.OneCenter.OfficialSparseCanonicalVectorComparison.compare_ne_lt_iff_rightVector_le
