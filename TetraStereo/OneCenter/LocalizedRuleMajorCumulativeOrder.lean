import TetraStereo.OneCenter.LocalizedActualMolecularEvidenceRefinement
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Lawful rule-major comparison and sorting for cumulative descriptors

The cumulative descriptor comparison is the existing rule-major comparison from
`LocalizedActualMolecularEvidenceRefinement`.  This module proves its general comparator laws,
strict prefix stability as further rule columns are appended, and the basic ordering and
permutation properties of the existing insertion sort.  None of these results assumes a desired
descriptor outcome or restricts the auxiliary labels.
-/

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

variable (input : CertifiedLocalizedCIPInput)

/-- The comparisons of each complete cumulative descriptor column, in rule order. -/
def ruleMajorCumulativeColumnOutcomes (width : Nat)
    (left right : input.LocalizedRerootCumulativeRule45Key) : List Ordering :=
  (List.range width).map fun index =>
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (projectCumulative index left.descriptor)
      (projectCumulative index right.descriptor)

/-- Every cumulative column of one key, in rule order. -/
def ruleMajorCumulativeColumns (width : Nat)
    (key : input.LocalizedRerootCumulativeRule45Key) :
    List (List (List (OfficialSparseEntry Nat))) :=
  (List.range width).map fun index => projectCumulative index key.descriptor

/-- Compare complete cumulative columns directly, one whole rule column at a time. -/
def compareRuleMajorCumulativeColumnTables (width : Nat)
    (left right : input.LocalizedRerootCumulativeRule45Key) : Ordering :=
  List.compareLex (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat)
    (input.ruleMajorCumulativeColumns width left)
    (input.ruleMajorCumulativeColumns width right)

/-- With constitutionally tied keys, the rule-major comparison is exactly the lexicographic
comparison of the complete projected columns. -/
theorem compareRuleMajorCumulativeDescriptor_of_constitutional_eq
    (width : Nat) (left right : input.LocalizedRerootCumulativeRule45Key)
    (constitutionalTie : OfficialRuleMajorKey.compare left.constitutional
      right.constitutional = Ordering.eq) :
    input.compareRuleMajorCumulativeDescriptor width left right =
      List.compareLex compare (input.ruleMajorCumulativeColumnOutcomes width left right)
        (List.replicate width Ordering.eq) := by
  simp [compareRuleMajorCumulativeDescriptor, ruleMajorCumulativeColumnOutcomes,
    projectCumulative, compareLex, Ordering.byKey, constitutionalTie]

private theorem compareLex_append_of_length_eq {α : Type*}
    (cmp : α → α → Ordering) : ∀ left right leftTail rightTail,
    left.length = right.length →
    List.compareLex cmp (left ++ leftTail) (right ++ rightTail) =
      (List.compareLex cmp left right).then (List.compareLex cmp leftTail rightTail)
  | [], [], leftTail, rightTail, _ => rfl
  | leftHead :: left, rightHead :: right, leftTail, rightTail, lengths => by
      simp only [List.length_cons, Nat.succ.injEq] at lengths
      simp only [List.cons_append, List.compareLex]
      cases headCmp : cmp leftHead rightHead with
      | lt => simp
      | gt => simp
      | eq =>
          simpa [headCmp] using
            compareLex_append_of_length_eq cmp left right leftTail rightTail lengths

private theorem compareLex_append_preserves_lt {α : Type*}
    (cmp : α → α → Ordering) (left right leftTail rightTail : List α)
    (samePrefixLength : left.length = right.length)
    (prefixResult : List.compareLex cmp left right = Ordering.lt) :
    List.compareLex cmp (left ++ leftTail) (right ++ rightTail) = Ordering.lt := by
  rw [compareLex_append_of_length_eq cmp left right leftTail rightTail samePrefixLength]
  simp [prefixResult]

private theorem compareLex_append_preserves_gt {α : Type*}
    (cmp : α → α → Ordering) (left right leftTail rightTail : List α)
    (samePrefixLength : left.length = right.length)
    (prefixResult : List.compareLex cmp left right = Ordering.gt) :
    List.compareLex cmp (left ++ leftTail) (right ++ rightTail) = Ordering.gt := by
  rw [compareLex_append_of_length_eq cmp left right leftTail rightTail samePrefixLength]
  simp [prefixResult]

private theorem orderingCompare_eq_right (outcome : Ordering) :
    compare outcome Ordering.eq = outcome := by
  cases outcome <;> rfl

private theorem compareLex_compare_zipWith_eq {α : Type*}
    (cmp : α → α → Ordering) : ∀ left right,
    left.length = right.length →
    List.compareLex compare (List.zipWith cmp left right)
        (List.replicate left.length Ordering.eq) = List.compareLex cmp left right
  | [], [], _ => rfl
  | leftHead :: left, rightHead :: right, lengths => by
      simp only [List.length_cons, Nat.succ.injEq] at lengths
      simp only [List.length_cons, List.replicate_succ, List.zipWith_cons_cons]
      cases headCmp : cmp leftHead rightHead with
      | lt => simp [List.compareLex, headCmp, orderingCompare_eq_right]
      | gt => simp [List.compareLex, headCmp, orderingCompare_eq_right]
      | eq =>
          simp only [List.compareLex, headCmp, orderingCompare_eq_right]
          exact compareLex_compare_zipWith_eq cmp left right lengths

private theorem ruleMajorCumulativeColumnOutcomes_eq_zip (width : Nat)
    (left right : input.LocalizedRerootCumulativeRule45Key) :
    input.ruleMajorCumulativeColumnOutcomes width left right =
      List.zipWith
        (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat)
        (input.ruleMajorCumulativeColumns width left)
        (input.ruleMajorCumulativeColumns width right) := by
  unfold ruleMajorCumulativeColumnOutcomes ruleMajorCumulativeColumns
  rw [List.zipWith_map, List.zipWith_self]

private theorem range_eq_replicate_orderingEq (width : Nat) :
    (List.range width).map (fun _ => Ordering.eq) = List.replicate width Ordering.eq := by
  simp

/-- The ordering-list encoding in the existing comparator is the ordinary lexicographic order on
the projected whole-rule columns. -/
theorem compareRuleMajorCumulativeColumnOutcomes_eq_columnTables (width : Nat)
    (left right : input.LocalizedRerootCumulativeRule45Key) :
    List.compareLex compare (input.ruleMajorCumulativeColumnOutcomes width left right)
      (List.replicate width Ordering.eq) =
        input.compareRuleMajorCumulativeColumnTables width left right := by
  rw [ruleMajorCumulativeColumnOutcomes_eq_zip]
  simpa [ruleMajorCumulativeColumns, compareRuleMajorCumulativeColumnTables] using
    compareLex_compare_zipWith_eq
    (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat)
    (input.ruleMajorCumulativeColumns width left)
    (input.ruleMajorCumulativeColumns width right) (by simp [ruleMajorCumulativeColumns])

/-- The existing comparator is definitionally equivalent in meaning to a lexicographic
constitutional-then-whole-column order. -/
theorem compareRuleMajorCumulativeDescriptor_eq_lexColumns (width : Nat)
    (left right : input.LocalizedRerootCumulativeRule45Key) :
    input.compareRuleMajorCumulativeDescriptor width left right =
      compareLex
        (Ordering.byKey (fun key => key.constitutional) OfficialRuleMajorKey.compare)
        (input.compareRuleMajorCumulativeColumnTables width) left right := by
  unfold compareRuleMajorCumulativeDescriptor
  congr 1
  funext leftKey rightKey
  rw [range_eq_replicate_orderingEq]
  exact compareRuleMajorCumulativeColumnOutcomes_eq_columnTables input width leftKey rightKey

/-- Function-level form of the lexicographic characterization. -/
theorem compareRuleMajorCumulativeDescriptor_eq_lexColumnsFunction (width : Nat) :
    input.compareRuleMajorCumulativeDescriptor width =
      compareLex
        (Ordering.byKey (fun key => key.constitutional) OfficialRuleMajorKey.compare)
        (input.compareRuleMajorCumulativeColumnTables width) := by
  funext left right
  exact compareRuleMajorCumulativeDescriptor_eq_lexColumns input width left right

private theorem ruleMajorCumulativeColumnOutcomes_add (width extra : Nat)
    (left right : input.LocalizedRerootCumulativeRule45Key) :
    input.ruleMajorCumulativeColumnOutcomes (width + extra) left right =
      input.ruleMajorCumulativeColumnOutcomes width left right ++
        (List.range extra).map fun offset =>
          OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
            (projectCumulative (width + offset) left.descriptor)
            (projectCumulative (width + offset) right.descriptor) := by
  unfold ruleMajorCumulativeColumnOutcomes
  rw [List.range_add, List.map_append]
  simp only [List.map_map, Function.comp_def]

private theorem ruleMajorCumulativeColumnComparison_prefix_lt (width extra : Nat)
    (left right : input.LocalizedRerootCumulativeRule45Key)
    (prefixResult : List.compareLex compare
      (input.ruleMajorCumulativeColumnOutcomes width left right)
      (List.replicate width Ordering.eq) = Ordering.lt) :
    List.compareLex compare
      (input.ruleMajorCumulativeColumnOutcomes (width + extra) left right)
      (List.replicate (width + extra) Ordering.eq) = Ordering.lt := by
  rw [ruleMajorCumulativeColumnOutcomes_add, List.replicate_add]
  apply compareLex_append_preserves_lt
  · simp [ruleMajorCumulativeColumnOutcomes]
  · exact prefixResult

private theorem ruleMajorCumulativeColumnComparison_prefix_gt (width extra : Nat)
    (left right : input.LocalizedRerootCumulativeRule45Key)
    (prefixResult : List.compareLex compare
      (input.ruleMajorCumulativeColumnOutcomes width left right)
      (List.replicate width Ordering.eq) = Ordering.gt) :
    List.compareLex compare
      (input.ruleMajorCumulativeColumnOutcomes (width + extra) left right)
      (List.replicate (width + extra) Ordering.eq) = Ordering.gt := by
  rw [ruleMajorCumulativeColumnOutcomes_add, List.replicate_add]
  apply compareLex_append_preserves_gt
  · simp [ruleMajorCumulativeColumnOutcomes]
  · exact prefixResult

/-- A strict comparison decided by the first `width` cumulative columns is unchanged when any
number of later columns are included. -/
theorem compareRuleMajorCumulativeDescriptor_prefix_preserves
    (width extra : Nat) (left right : input.LocalizedRerootCumulativeRule45Key)
    (strict : input.compareRuleMajorCumulativeDescriptor width left right = Ordering.lt) :
    input.compareRuleMajorCumulativeDescriptor (width + extra) left right = Ordering.lt := by
  unfold compareRuleMajorCumulativeDescriptor at strict ⊢
  simp only [compareLex, Ordering.byKey] at strict ⊢
  cases constitutional : OfficialRuleMajorKey.compare left.constitutional right.constitutional with
  | lt => simp [constitutional] at strict ⊢
  | gt => simp [constitutional] at strict
  | eq =>
      have columnStrict :
          List.compareLex compare (input.ruleMajorCumulativeColumnOutcomes width left right)
            (List.replicate width Ordering.eq) = Ordering.lt := by
        simpa [ruleMajorCumulativeColumnOutcomes, projectCumulative, constitutional,
          Ordering.byKey] using strict
      simpa [ruleMajorCumulativeColumnOutcomes, projectCumulative, constitutional,
        Ordering.byKey] using
          ruleMajorCumulativeColumnComparison_prefix_lt input width extra left right columnStrict

/-- The symmetric strict prefix-stability result. -/
theorem compareRuleMajorCumulativeDescriptor_prefix_preserves_gt
    (width extra : Nat) (left right : input.LocalizedRerootCumulativeRule45Key)
    (strict : input.compareRuleMajorCumulativeDescriptor width left right = Ordering.gt) :
    input.compareRuleMajorCumulativeDescriptor (width + extra) left right = Ordering.gt := by
  unfold compareRuleMajorCumulativeDescriptor at strict ⊢
  simp only [compareLex, Ordering.byKey] at strict ⊢
  cases constitutional : OfficialRuleMajorKey.compare left.constitutional right.constitutional with
  | lt => simp [constitutional] at strict
  | gt => simp [constitutional] at strict ⊢
  | eq =>
      have columnStrict :
          List.compareLex compare (input.ruleMajorCumulativeColumnOutcomes width left right)
            (List.replicate width Ordering.eq) = Ordering.gt := by
        simpa [ruleMajorCumulativeColumnOutcomes, projectCumulative, constitutional,
          Ordering.byKey] using strict
      simpa [ruleMajorCumulativeColumnOutcomes, projectCumulative, constitutional,
        Ordering.byKey] using
          ruleMajorCumulativeColumnComparison_prefix_gt input width extra left right columnStrict

/-- The cumulative rule-major comparator is transitive for every finite width. -/
theorem compareRuleMajorCumulativeDescriptor_transCmp (width : Nat) :
    Std.TransCmp (input.compareRuleMajorCumulativeDescriptor width) := by
  letI : Std.TransCmp
      (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat) := by
    letI : Std.TransCmp OfficialRuleMajorKey.compareNat := by
      unfold OfficialRuleMajorKey.compareNat
      infer_instance
    unfold OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareSparseLayer
      OfficialRuleMajorKey.compareSparseEntry
    infer_instance
  letI : Std.TransCmp (@OfficialRuleMajorKey.compare input.Atom) :=
    OfficialRuleMajorKey.compare_transCmp
  letI : Std.TransCmp (input.compareRuleMajorCumulativeColumnTables width) := by
    letI : Std.TransCmp
        (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat) := by
      letI : Std.TransCmp OfficialRuleMajorKey.compareNat := by
        unfold OfficialRuleMajorKey.compareNat
        infer_instance
      unfold OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareSparseLayer
        OfficialRuleMajorKey.compareSparseEntry
      infer_instance
    refine { eq_swap := ?_, isLE_trans := ?_ }
    · intro left right
      unfold compareRuleMajorCumulativeColumnTables
      exact Std.OrientedCmp.eq_swap
    · intro left middle right leftLeMiddle middleLeRight
      unfold compareRuleMajorCumulativeColumnTables at leftLeMiddle middleLeRight ⊢
      exact Std.TransCmp.isLE_trans leftLeMiddle middleLeRight
  rw [compareRuleMajorCumulativeDescriptor_eq_lexColumnsFunction]
  infer_instance

/-- Reversing the arguments reverses every strict comparison in the cumulative rule-major order. -/
theorem compareRuleMajorCumulativeDescriptor_orientedCmp (width : Nat) :
    Std.OrientedCmp (input.compareRuleMajorCumulativeDescriptor width) := by
  haveI : Std.OrientedCmp
      (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat) := by
    haveI : Std.OrientedCmp OfficialRuleMajorKey.compareNat := by
      unfold OfficialRuleMajorKey.compareNat
      infer_instance
    unfold OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareSparseLayer
      OfficialRuleMajorKey.compareSparseEntry
    infer_instance
  haveI : Std.OrientedCmp OfficialRuleMajorKey.compareNat := by
    unfold OfficialRuleMajorKey.compareNat
    infer_instance
  haveI : Std.OrientedCmp OfficialRuleMajorKey.compareRule1b := by
    unfold OfficialRuleMajorKey.compareRule1b
    infer_instance
  haveI : Std.OrientedCmp (@OfficialRuleMajorKey.compare input.Atom) := by
    unfold OfficialRuleMajorKey.compare OfficialRuleMajorKey.compareSparseLayers
      OfficialRuleMajorKey.compareSparseLayer OfficialRuleMajorKey.compareSparseEntry
    infer_instance
  haveI : Std.OrientedCmp (input.compareRuleMajorCumulativeColumnTables width) := by
    haveI : Std.OrientedCmp
        (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat) := by
      haveI : Std.OrientedCmp OfficialRuleMajorKey.compareNat := by
        unfold OfficialRuleMajorKey.compareNat
        infer_instance
      unfold OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareSparseLayer
        OfficialRuleMajorKey.compareSparseEntry
      infer_instance
    refine ⟨?_⟩
    intro left right
    unfold compareRuleMajorCumulativeColumnTables
    exact Std.OrientedCmp.eq_swap
  rw [compareRuleMajorCumulativeDescriptor_eq_lexColumnsFunction]
  infer_instance

/-- The exact descending-order invariant for a list of cumulative descriptor keys. -/
def RuleMajorCumulativeKeysDescending (width : Nat)
    (keys : List input.LocalizedRerootCumulativeRule45Key) : Prop :=
  keys.Pairwise fun left right =>
    input.compareRuleMajorCumulativeDescriptor width left right ≠ Ordering.lt

/-- Generic insertion sort preserves permutation, independently of comparator laws. -/
theorem insertKeyBy_perm {α : Type*} (cmp : α → α → Ordering) (key : α) :
    ∀ keys, (insertKeyBy cmp key keys).Perm (key :: keys)
  | [] => List.Perm.refl _
  | head :: tail => by
      unfold insertKeyBy
      cases comparison : cmp key head with
      | eq => exact List.Perm.refl _
      | gt => exact List.Perm.refl _
      | lt =>
          exact (List.Perm.cons head (insertKeyBy_perm cmp key tail)).trans
            (List.Perm.swap key head tail)

/-- Generic recursive insertion sort preserves the order and contents of its input list. -/
theorem sortKeysBy_perm {α : Type*} (cmp : α → α → Ordering) :
    ∀ keys, (sortKeysBy cmp keys).Perm keys
  | [] => List.Perm.refl []
  | key :: keys =>
      (insertKeyBy_perm cmp key (sortKeysBy cmp keys)).trans
        (List.Perm.cons key (sortKeysBy_perm cmp keys))

/-- Insertion into a descending list preserves its ordering when the comparator is transitive and
oriented. -/
theorem insertKeyBy_descending {α : Type*} (cmp : α → α → Ordering)
    [Std.TransCmp cmp] [Std.OrientedCmp cmp] (key : α) :
    ∀ keys, (keys.Pairwise fun left right => cmp left right ≠ Ordering.lt) →
      ((insertKeyBy cmp key keys).Pairwise fun left right => cmp left right ≠ Ordering.lt)
  | [], _ => by simp [insertKeyBy]
  | head :: tail, sorted => by
      have headOverTail : ∀ observed ∈ tail, cmp head observed ≠ Ordering.lt :=
        (List.pairwise_cons.mp sorted).1
      have tailSorted : tail.Pairwise (fun left right => cmp left right ≠ Ordering.lt) :=
        (List.pairwise_cons.mp sorted).2
      unfold insertKeyBy
      cases comparison : cmp key head with
      | gt =>
          rw [List.pairwise_cons]
          constructor
          · intro observed present
            rcases List.mem_cons.mp present with same | tailPresent
            · subst observed
              simp [comparison]
            · exact Std.TransCmp.ge_trans (by simp [comparison])
                (headOverTail observed tailPresent)
          · exact sorted
      | eq =>
          rw [List.pairwise_cons]
          constructor
          · intro observed present
            rcases List.mem_cons.mp present with same | tailPresent
            · subst observed
              simp [comparison]
            · exact Std.TransCmp.ge_trans (by simp [comparison])
                (headOverTail observed tailPresent)
          · exact sorted
      | lt =>
          have insertedSorted := insertKeyBy_descending cmp key tail tailSorted
          rw [List.pairwise_cons]
          constructor
          · intro observed present
            have permutation := insertKeyBy_perm cmp key tail
            have sourcePresent : observed ∈ key :: tail :=
              (permutation.mem_iff).mp present
            rcases List.mem_cons.mp sourcePresent with same | tailPresent
            · subst observed
              have reverse : cmp head key = Ordering.gt := by
                rw [Std.OrientedCmp.gt_iff_lt]
                exact comparison
              simp [reverse]
            · exact headOverTail observed tailPresent
          · exact insertedSorted

/-- Sorting cumulative descriptor keys produces descending rule-major order. -/
theorem sortKeysBy_ruleMajorCumulative_descending (width : Nat) :
    ∀ keys,
      input.RuleMajorCumulativeKeysDescending width (sortKeysBy
        (input.compareRuleMajorCumulativeDescriptor width) keys)
  | [] => by simp [sortKeysBy, RuleMajorCumulativeKeysDescending]
  | key :: keys => by
      letI : Std.TransCmp (input.compareRuleMajorCumulativeDescriptor width) :=
        input.compareRuleMajorCumulativeDescriptor_transCmp width
      letI : Std.OrientedCmp (input.compareRuleMajorCumulativeDescriptor width) :=
        input.compareRuleMajorCumulativeDescriptor_orientedCmp width
      exact insertKeyBy_descending (input.compareRuleMajorCumulativeDescriptor width) key
        (sortKeysBy (input.compareRuleMajorCumulativeDescriptor width) keys)
        (sortKeysBy_ruleMajorCumulative_descending width keys)

/-- Sorting cumulative descriptor keys preserves the exact child multiset. -/
theorem sortKeysBy_ruleMajorCumulative_perm (width : Nat) :
    ∀ keys, (sortKeysBy (input.compareRuleMajorCumulativeDescriptor width) keys).Perm keys
  | [] => List.Perm.refl []
  | key :: keys =>
      (insertKeyBy_perm (input.compareRuleMajorCumulativeDescriptor width) key
        (sortKeysBy (input.compareRuleMajorCumulativeDescriptor width) keys)).trans
        (List.Perm.cons key
          (sortKeysBy_ruleMajorCumulative_perm width keys))

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareRuleMajorCumulativeDescriptor_of_constitutional_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareRuleMajorCumulativeColumnOutcomes_eq_columnTables
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareRuleMajorCumulativeDescriptor_eq_lexColumns
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareRuleMajorCumulativeDescriptor_eq_lexColumnsFunction
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareRuleMajorCumulativeDescriptor_prefix_preserves
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareRuleMajorCumulativeDescriptor_prefix_preserves_gt
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareRuleMajorCumulativeDescriptor_transCmp
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareRuleMajorCumulativeDescriptor_orientedCmp
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.insertKeyBy_perm
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.sortKeysBy_perm
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.insertKeyBy_descending
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.sortKeysBy_ruleMajorCumulative_descending
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.sortKeysBy_ruleMajorCumulative_perm
