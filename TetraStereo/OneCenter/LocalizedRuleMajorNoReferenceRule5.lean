import TetraStereo.OneCenter.LocalizedRuleMajorRule5Relabel
import TetraStereo.OneCenter.LocalizedEmptyRule4bReferenceDecoding
import TetraStereo.OneCenter.LocalizedRuleMajorCumulativeTrace
import TetraStereo.OneCenter.LocalizedRankedProjectionTransport
import TetraStereo.OneCenter.LocalizedSparseAddressReconstruction
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The no-Rule-4b-reference Rule-5 stage retains the Rule-4c `r/s` column and appends a
Rule-5 bit.  For a successful no-reference trace whose visited observations contain no uppercase
chiral label, that bit is zero at every visited node.  The stage-5 whole-rule build is therefore
the exact zero-lift of the stage-4c-no-reference build.  The trace-local premise is intentional:
an arbitrary callback may return chiral labels at unrelated cursors. -/

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

open OfficialRuleMajorKey
open CompilerProjectionFidelity
open SparseAddress

variable (input : CertifiedLocalizedCIPInput)
variable {carrierFuel : Nat}

/-- Every vector in a no-reference Rule-4c key has exactly its retained 4a and 4c columns. -/
def Stage4cNoReferenceShaped
    (key : input.LocalizedRerootCumulativeRule45Key) : Prop :=
  ∀ layer ∈ key.descriptor, ∀ entry ∈ layer, entry.2.length = 2

/-- Chiral-freeness of observations visited by the actual recursive expansion at one cursor.
The predicate follows only children returned by the production reroot enumerator, and so makes no
claim about unrelated cursors accepted by the callback's type. -/
def RuleMajorReadChiralFreeBelow
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel) :
    Nat → input.LocalizedRerootCursor carrierFuel → Prop
  | 0, cursor => ∀ descriptor : RS, read cursor ≠ some (.chiral descriptor)
  | fuel + 1, cursor =>
      (∀ descriptor : RS, read cursor ≠ some (.chiral descriptor)) ∧
        match input.localizedRerootChildren? cursor with
        | none => True
        | some children =>
            ∀ child, child ∈ children → RuleMajorReadChiralFreeBelow read fuel child

private theorem read_priority_noReference_lift
    (reference : RS) (label : Option LocalizedAuxiliaryLabel)
    (free : ∀ descriptor : RS, label ≠ some (.chiral descriptor)) :
    localizedCumulativeRule45Priority (.rule5NoRule4bReference reference) label =
      rule5Lift false (localizedCumulativeRule45Priority .rule4cNoReference label) := by
  cases label with
  | none => rfl
  | some label =>
      cases label with
      | chiral descriptor => exact (free descriptor rfl).elim
      | pseudoasymmetric descriptor => cases descriptor <;> rfl

private theorem compareLex_map_rel_noref {α β : Type*}
    (cmpα : α → α → Ordering) (cmpβ : β → β → Ordering) (f : α → β) :
    ∀ xs ys : List α,
      (∀ x ∈ xs, ∀ y ∈ ys, cmpβ (f x) (f y) = cmpα x y) →
      List.compareLex cmpβ (xs.map f) (ys.map f) = List.compareLex cmpα xs ys
  | [], [], _ => rfl
  | [], _ :: _, _ => rfl
  | _ :: _, [], _ => rfl
  | x :: xs, y :: ys, related => by
      simp only [List.map_cons, List.compareLex]
      rw [related x List.mem_cons_self y List.mem_cons_self,
        compareLex_map_rel_noref cmpα cmpβ f xs ys
          (fun a ha b hb => related a (List.mem_cons_of_mem x ha)
            b (List.mem_cons_of_mem y hb))]

private theorem compareLex_append_one_noref :
    ∀ (left right : List Nat) (x y : Nat), left.length = right.length →
      List.compareLex compareNat (left ++ [x]) (right ++ [y]) =
        (List.compareLex compareNat left right).then (compareNat x y)
  | [], [], x, y, _ => by
      simp only [List.nil_append, List.compareLex]
      cases compareNat x y <;> rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | a :: left, b :: right, x, y, h => by
      simp only [List.cons_append, List.compareLex]
      rw [compareLex_append_one_noref left right x y (by simpa using h)]
      cases compareNat a b <;> simp [Ordering.then]

private theorem compareRule5LiftPriority_noref (same : Bool)
    (left right : List Nat) (leftShape : left.length = 2)
    (rightShape : right.length = 2) :
    compareLocalizedCumulativeRule45Priority (rule5Lift same left)
        (rule5Lift same right) =
      compareLocalizedCumulativeRule45Priority left right := by
  have leftBit : rule5Bit same left = 0 := by
    cases left with
    | nil => simp at leftShape
    | cons a tail => cases tail with
      | nil => simp at leftShape
      | cons b tail => cases tail with
        | nil => rfl
        | cons c tail => simp at leftShape
  have rightBit : rule5Bit same right = 0 := by
    cases right with
    | nil => simp at rightShape
    | cons a tail => cases tail with
      | nil => simp at rightShape
      | cons b tail => cases tail with
        | nil => rfl
        | cons c tail => simp at rightShape
  unfold compareLocalizedCumulativeRule45Priority rule5Lift
  rw [show left ++ [rule5Bit same left] = left ++ [0] by rw [leftBit],
    show right ++ [rule5Bit same right] = right ++ [0] by rw [rightBit],
    compareLex_append_one_noref left right 0 0 (by omega)]
  cases result : List.compareLex compareNat left right with
  | lt => rfl
  | gt => rfl
  | eq =>
      have sameValues : left = right :=
        (list_compareLex_eq_eq_iff compareNat compareNat_self
          (fun a b eq => (compareNat_eq_eq_iff a b).1 eq) left right).1 result
      subst right
      simp [compareNat_self]

private theorem compareRule5LiftSparseEntry_noref (same : Bool)
    (left right : OfficialSparseEntry (List Nat))
    (leftShape : left.2.length = 2) (rightShape : right.2.length = 2) :
    compareSparseEntry compareLocalizedCumulativeRule45Priority
        (left.1, rule5Lift same left.2) (right.1, rule5Lift same right.2) =
      compareSparseEntry compareLocalizedCumulativeRule45Priority left right := by
  unfold compareSparseEntry
  simp only [compareLex, Ordering.byKey]
  rw [compareRule5LiftPriority_noref same left.2 right.2 leftShape rightShape]

private theorem compareRule5LiftSparseLayer_noref (same : Bool)
    (left right : List (OfficialSparseEntry (List Nat)))
    (leftShape : ∀ entry ∈ left, entry.2.length = 2)
    (rightShape : ∀ entry ∈ right, entry.2.length = 2) :
    compareSparseLayer compareLocalizedCumulativeRule45Priority
        (rule5LiftLayer same left) (rule5LiftLayer same right) =
      compareSparseLayer compareLocalizedCumulativeRule45Priority left right := by
  unfold compareSparseLayer rule5LiftLayer
  exact compareLex_map_rel_noref _ _ _ left right
    (fun first firstMem second secondMem =>
      compareRule5LiftSparseEntry_noref same first second
        (leftShape first firstMem) (rightShape second secondMem))

private theorem compareRule5LiftSparseLayers_noref (same : Bool)
    (left right : List (List (OfficialSparseEntry (List Nat))))
    (leftShape : ∀ layer ∈ left, ∀ entry ∈ layer, entry.2.length = 2)
    (rightShape : ∀ layer ∈ right, ∀ entry ∈ layer, entry.2.length = 2) :
    compareSparseLayers compareLocalizedCumulativeRule45Priority
        (left.map (rule5LiftLayer same)) (right.map (rule5LiftLayer same)) =
      compareSparseLayers compareLocalizedCumulativeRule45Priority left right := by
  unfold compareSparseLayers
  exact compareLex_map_rel_noref _ _ _ left right
    (fun first firstMem second secondMem =>
      compareRule5LiftSparseLayer_noref same first second
        (fun entry entryMem => leftShape first firstMem entry entryMem)
        (fun entry entryMem => rightShape second secondMem entry entryMem))

private theorem compareRule5LiftKey_localized_noref (same : Bool)
    (left right : input.LocalizedRerootCumulativeRule45Key)
    (leftShape : input.Stage4cNoReferenceShaped left)
    (rightShape : input.Stage4cNoReferenceShaped right) :
    input.compareLocalizedRerootCumulativeRule45Keys
        (input.rule5LiftKey same left) (input.rule5LiftKey same right) =
      input.compareLocalizedRerootCumulativeRule45Keys left right := by
  unfold compareLocalizedRerootCumulativeRule45Keys
  simp only [compareLex, Ordering.byKey, rule5LiftKey]
  rw [compareRule5LiftSparseLayers_noref same _ _ leftShape rightShape]

private theorem compareNat_sound_noref (left right : Nat)
    (equal : compareNat left right = Ordering.eq) : left = right :=
  (compareNat_eq_eq_iff left right).1 equal

private theorem sparseNatTables_compare_eq_iff_noref
    (left right : List (List (OfficialSparseEntry Nat))) :
    compareSparseLayers compareNat left right = Ordering.eq ↔ left = right :=
  compareSparseLayers_eq_eq_iff compareNat compareNat_self
    compareNat_sound_noref left right

private theorem compareRuleMajorColumnTables_eq_iff_noref (width : Nat)
    (left right : input.LocalizedRerootCumulativeRule45Key) :
    input.compareRuleMajorCumulativeColumnTables width left right = Ordering.eq ↔
      input.ruleMajorCumulativeColumns width left =
        input.ruleMajorCumulativeColumns width right := by
  unfold compareRuleMajorCumulativeColumnTables
  exact list_compareLex_eq_eq_iff
    (compareSparseLayers compareNat)
    (fun table => compareSparseLayers_self compareNat compareNat_self table)
    (fun first second => (sparseNatTables_compare_eq_iff_noref first second).1)
    (input.ruleMajorCumulativeColumns width left)
    (input.ruleMajorCumulativeColumns width right)

private theorem projectRule5LiftKey_column_noref (same : Bool)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (shaped : input.Stage4cNoReferenceShaped key)
    (index : Nat) (beforeRule5 : index < 2) :
    projectCumulative index (input.rule5LiftKey same key).descriptor =
      projectCumulative index key.descriptor := by
  have getD_before_append {values : List Nat} (added fallback : Nat)
      (bound : index < values.length) :
      (values ++ [added]).getD index fallback = values.getD index fallback := by
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left bound]
  unfold projectCumulative
  change ((key.descriptor.map (rule5LiftLayer same)).map
      (List.map fun entry => (entry.1, entry.2.getD index 0))) =
    key.descriptor.map (List.map fun entry => (entry.1, entry.2.getD index 0))
  rw [List.map_map]
  apply List.map_congr_left
  intro layer layerMem
  change (rule5LiftLayer same layer).map
      (fun entry => (entry.1, entry.2.getD index 0)) =
    layer.map (fun entry => (entry.1, entry.2.getD index 0))
  unfold rule5LiftLayer
  rw [List.map_map]
  apply List.map_congr_left
  intro entry entryMem
  have entryShape : entry.2.length = 2 := shaped layer layerMem entry entryMem
  have indexBound : index < entry.2.length := by omega
  have observation :
      (entry.2 ++ [rule5Bit same entry.2]).getD index 0 = entry.2.getD index 0 :=
    getD_before_append (rule5Bit same entry.2) 0 indexBound
  simpa [rule5Lift, Function.comp_apply] using
    congrArg (fun value : Nat => (entry.1, value)) observation

private theorem ruleMajorColumns2_rule5LiftKey_noref (same : Bool)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (shaped : input.Stage4cNoReferenceShaped key) :
    input.ruleMajorCumulativeColumns 2 (input.rule5LiftKey same key) =
      input.ruleMajorCumulativeColumns 2 key := by
  unfold ruleMajorCumulativeColumns
  apply List.map_congr_left
  intro index inRange
  exact projectRule5LiftKey_column_noref input same key shaped index
    (List.mem_range.mp inRange)

private theorem natVector_eq_of_two_getD_noref
    (left right : List Nat) (leftShape : left.length = 2)
    (rightShape : right.length = 2)
    (first : left.getD 0 0 = right.getD 0 0)
    (second : left.getD 1 0 = right.getD 1 0) : left = right := by
  have representation (values : List Nat) (shape : values.length = 2) :
      values = [values.getD 0 0, values.getD 1 0] := by
    cases values with
    | nil => simp at shape
    | cons head tail =>
        cases tail with
        | nil => simp at shape
        | cons next tail =>
            cases tail with
            | nil => simp [List.getD]
            | cons extra rest => simp at shape
  rw [representation left leftShape, representation right rightShape, first, second]

private theorem layer_eq_of_two_projections_noref
    (left right : List (OfficialSparseEntry (List Nat)))
    (leftShape : ∀ entry ∈ left, entry.2.length = 2)
    (rightShape : ∀ entry ∈ right, entry.2.length = 2)
    (first : left.map (fun entry => (entry.1, entry.2.getD 0 0)) =
      right.map (fun entry => (entry.1, entry.2.getD 0 0)))
    (second : left.map (fun entry => (entry.1, entry.2.getD 1 0)) =
      right.map (fun entry => (entry.1, entry.2.getD 1 0))) : left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons entry tail => simp at first
  | cons entry tail ih =>
      cases right with
      | nil => simp at first
      | cons other rest =>
          simp only [List.map_cons, List.cons.injEq] at first second
          rcases Prod.mk.inj first.1 with ⟨addressEq, value0Eq⟩
          rcases Prod.mk.inj second.1 with ⟨_, value1Eq⟩
          have valueEq := natVector_eq_of_two_getD_noref entry.2 other.2
            (leftShape entry List.mem_cons_self)
            (rightShape other List.mem_cons_self) value0Eq value1Eq
          have headEq : entry = other := by
            cases entry with
            | mk entryAddress entryValues =>
              cases other with
              | mk otherAddress otherValues =>
                simp only [Prod.mk.injEq]
                exact ⟨addressEq, valueEq⟩
          have tailEq := ih rest
            (fun inner present => leftShape inner (List.mem_cons_of_mem entry present))
            (fun inner present => rightShape inner (List.mem_cons_of_mem other present))
            first.2 second.2
          simp [headEq, tailEq]

private theorem descriptor_eq_of_two_projected_columns_noref
    (left right : List (List (OfficialSparseEntry (List Nat))))
    (leftShape : ∀ layer ∈ left, ∀ entry ∈ layer, entry.2.length = 2)
    (rightShape : ∀ layer ∈ right, ∀ entry ∈ layer, entry.2.length = 2)
    (first : projectCumulative 0 left = projectCumulative 0 right)
    (second : projectCumulative 1 left = projectCumulative 1 right) : left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons layer tail => simp [projectCumulative] at first
  | cons layer tail ih =>
      cases right with
      | nil => simp [projectCumulative] at first
      | cons other rest =>
          simp only [projectCumulative, List.map_cons, List.cons.injEq] at first second
          have headEq := layer_eq_of_two_projections_noref layer other
            (fun entry present => leftShape layer List.mem_cons_self entry present)
            (fun entry present => rightShape other List.mem_cons_self entry present)
            first.1 second.1
          have tailEq := ih rest
            (fun inner member entry entryMem =>
              leftShape inner (List.mem_cons_of_mem layer member) entry entryMem)
            (fun inner member entry entryMem =>
              rightShape inner (List.mem_cons_of_mem other member) entry entryMem)
            first.2 second.2
          simp [headEq, tailEq]

private theorem compareRuleMajorCumulativeDescriptor_rule5LiftKey_noref
    (same : Bool) (left right : input.LocalizedRerootCumulativeRule45Key)
    (leftShape : input.Stage4cNoReferenceShaped left)
    (rightShape : input.Stage4cNoReferenceShaped right) :
    input.compareRuleMajorCumulativeDescriptor 3
        (input.rule5LiftKey same left) (input.rule5LiftKey same right) =
      input.compareRuleMajorCumulativeDescriptor 2 left right := by
  have leftColumns := ruleMajorColumns2_rule5LiftKey_noref input same left leftShape
  have rightColumns := ruleMajorColumns2_rule5LiftKey_noref input same right rightShape
  have prefixCompare :
      input.compareRuleMajorCumulativeDescriptor 2
          (input.rule5LiftKey same left) (input.rule5LiftKey same right) =
        input.compareRuleMajorCumulativeDescriptor 2 left right := by
    rw [input.compareRuleMajorCumulativeDescriptor_eq_lexColumns,
      input.compareRuleMajorCumulativeDescriptor_eq_lexColumns]
    simp only [compareLex, Ordering.byKey]
    unfold compareRuleMajorCumulativeColumnTables
    change (left.constitutional.compare right.constitutional).then
        (List.compareLex (compareSparseLayers compareNat)
          (input.ruleMajorCumulativeColumns 2 (input.rule5LiftKey same left))
          (input.ruleMajorCumulativeColumns 2 (input.rule5LiftKey same right))) =
      (left.constitutional.compare right.constitutional).then
        (List.compareLex (compareSparseLayers compareNat)
          (input.ruleMajorCumulativeColumns 2 left)
          (input.ruleMajorCumulativeColumns 2 right))
    rw [leftColumns, rightColumns]
  cases baseComparison : input.compareRuleMajorCumulativeDescriptor 2 left right with
  | lt =>
      have liftedPrefix : input.compareRuleMajorCumulativeDescriptor 2
          (input.rule5LiftKey same left) (input.rule5LiftKey same right) = Ordering.lt := by
        rw [prefixCompare, baseComparison]
      have full := input.compareRuleMajorCumulativeDescriptor_prefix_preserves 2 1
        (input.rule5LiftKey same left) (input.rule5LiftKey same right) liftedPrefix
      simpa using full
  | gt =>
      have liftedPrefix : input.compareRuleMajorCumulativeDescriptor 2
          (input.rule5LiftKey same left) (input.rule5LiftKey same right) = Ordering.gt := by
        rw [prefixCompare, baseComparison]
      have full := input.compareRuleMajorCumulativeDescriptor_prefix_preserves_gt 2 1
        (input.rule5LiftKey same left) (input.rule5LiftKey same right) liftedPrefix
      simpa using full
  | eq =>
      have decomposed :
          OfficialRuleMajorKey.compare left.constitutional right.constitutional = Ordering.eq ∧
            input.compareRuleMajorCumulativeColumnTables 2 left right = Ordering.eq := by
        rw [input.compareRuleMajorCumulativeDescriptor_eq_lexColumns] at baseComparison
        simp only [compareLex, Ordering.byKey] at baseComparison
        cases comparison : OfficialRuleMajorKey.compare left.constitutional right.constitutional with
        | lt => simp [comparison] at baseComparison
        | gt => simp [comparison] at baseComparison
        | eq =>
            have columns : input.compareRuleMajorCumulativeColumnTables 2 left right = Ordering.eq := by
              simpa [comparison, Ordering.then] using baseComparison
            exact ⟨rfl, columns⟩
      rcases decomposed with ⟨constitutionalEq, columnsEq⟩
      have columnsEqual : input.ruleMajorCumulativeColumns 2 left =
          input.ruleMajorCumulativeColumns 2 right :=
        (compareRuleMajorColumnTables_eq_iff_noref input 2 left right).1 columnsEq
      have firstColumn := List.cons.inj columnsEqual |>.1
      have tailColumns := List.cons.inj columnsEqual |>.2
      have secondColumn := List.cons.inj tailColumns |>.1
      have descriptorEq := descriptor_eq_of_two_projected_columns_noref
        left.descriptor right.descriptor leftShape rightShape firstColumn secondColumn
      have liftedDescriptorEq : (input.rule5LiftKey same left).descriptor =
          (input.rule5LiftKey same right).descriptor := by
        simp only [rule5LiftKey]
        rw [descriptorEq]
      have liftedColumnsEq : input.ruleMajorCumulativeColumns 3
          (input.rule5LiftKey same left) = input.ruleMajorCumulativeColumns 3
            (input.rule5LiftKey same right) := by
        simp [ruleMajorCumulativeColumns, liftedDescriptorEq]
      rw [input.compareRuleMajorCumulativeDescriptor_eq_lexColumns]
      simp only [compareLex, Ordering.byKey]
      have liftedConstitutionalEq : OfficialRuleMajorKey.compare
          (input.rule5LiftKey same left).constitutional
          (input.rule5LiftKey same right).constitutional = Ordering.eq := by
        simpa [rule5LiftKey] using constitutionalEq
      have liftedColumnEq : input.compareRuleMajorCumulativeColumnTables 3
          (input.rule5LiftKey same left) (input.rule5LiftKey same right) = Ordering.eq :=
        (compareRuleMajorColumnTables_eq_iff_noref input 3
          (input.rule5LiftKey same left) (input.rule5LiftKey same right)).2 liftedColumnsEq
      rw [liftedConstitutionalEq]
      rw [liftedColumnEq]
      rfl

private theorem localizedRankedChildTail_rule5LiftKey_noref (same : Bool)
    (previous : input.LocalizedRerootCumulativeRule45Key)
    (previousShape : input.Stage4cNoReferenceShaped previous) (rank : Nat) :
    ∀ keys : List input.LocalizedRerootCumulativeRule45Key,
      (∀ key ∈ keys, input.Stage4cNoReferenceShaped key) →
      input.localizedRerootRankedChildTail (input.rule5LiftKey same previous) rank
          (keys.map (input.rule5LiftKey same)) =
        (input.localizedRerootRankedChildTail previous rank keys).map
          (Prod.map (input.rule5LiftKey same) id)
  | [], _ => rfl
  | child :: tail, shaped => by
      have childShape := shaped child List.mem_cons_self
      have comparison := compareRule5LiftKey_localized_noref input same child previous
        childShape previousShape
      change input.localizedRerootRankedChildTail (input.rule5LiftKey same previous) rank
          (input.rule5LiftKey same child :: List.map (input.rule5LiftKey same) tail) =
        List.map (Prod.map (input.rule5LiftKey same) id)
          (input.localizedRerootRankedChildTail previous rank (child :: tail))
      rw [input.localizedRerootRankedChildTail_cons
          (input.rule5LiftKey same previous) (input.rule5LiftKey same child) rank
          (List.map (input.rule5LiftKey same) tail),
        input.localizedRerootRankedChildTail_cons previous child rank tail]
      simp only [List.map_cons, comparison, Prod.map, id]
      rw [localizedRankedChildTail_rule5LiftKey_noref same child childShape _ tail
        (fun key member => shaped key (List.mem_cons_of_mem child member))]

private theorem localizedRankedChildren_rule5LiftKey_noref (same : Bool) :
    ∀ keys : List input.LocalizedRerootCumulativeRule45Key,
      (∀ key ∈ keys, input.Stage4cNoReferenceShaped key) →
      input.localizedRerootRankedChildren (keys.map (input.rule5LiftKey same)) =
        (input.localizedRerootRankedChildren keys).map
          (Prod.map (input.rule5LiftKey same) id)
  | [], _ => rfl
  | key :: tail, shaped => by
      have keyShape := shaped key List.mem_cons_self
      have tailShape : ∀ child ∈ tail, input.Stage4cNoReferenceShaped child :=
        fun child member => shaped child (List.mem_cons_of_mem key member)
      change input.localizedRerootRankedChildren
          (input.rule5LiftKey same key :: List.map (input.rule5LiftKey same) tail) =
        List.map (Prod.map (input.rule5LiftKey same) id)
          (input.localizedRerootRankedChildren (key :: tail))
      rw [localizedRerootRankedChildren_cons input (input.rule5LiftKey same key)
          (List.map (input.rule5LiftKey same) tail),
        localizedRerootRankedChildren_cons input key tail]
      simp only [List.map_cons, Prod.map, id]
      rw [localizedRankedChildTail_rule5LiftKey_noref input same key keyShape 0 tail tailShape]

private theorem mergeRankedLabel_rule5LiftKey_noref (same : Bool)
    (keys : List input.LocalizedRerootCumulativeRule45Key)
    (shaped : ∀ key ∈ keys, input.Stage4cNoReferenceShaped key) :
    input.mergeLocalizedRerootRankedLabelChildren (keys.map (input.rule5LiftKey same)) =
      input.mergeLocalizedRerootRankedLabelChildren keys := by
  unfold mergeLocalizedRerootRankedLabelChildren
  have countEq :
      input.localizedRerootRankedLabelChildLayerCount (keys.map (input.rule5LiftKey same)) =
        input.localizedRerootRankedLabelChildLayerCount keys := by
    simp [localizedRerootRankedLabelChildLayerCount, List.foldl_map, rule5LiftKey]
  rw [countEq]
  rw [localizedRankedChildren_rule5LiftKey_noref input same keys shaped]
  apply List.map_congr_left
  intro depth depthMem
  rw [List.flatMap_map]
  apply List.flatMap_congr
  intro child childMem
  rfl

private theorem mem_of_mapM_ruleMajor_some
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) :
    ∀ (cursors : List (input.LocalizedRerootCursor carrierFuel))
      (keys : List input.LocalizedRerootCumulativeRule45Key),
      cursors.mapM (input.buildRuleMajorCumulativeWithRead? stage read fuel) = some keys →
      ∀ key, key ∈ keys →
        ∃ cursor, cursor ∈ cursors ∧
          input.buildRuleMajorCumulativeWithRead? stage read fuel cursor = some key
  | [], keys, computed, key, present => by
      simp at computed
      subst keys
      simp at present
  | cursor :: cursors, keys, computed, key, present => by
      rw [List.mapM_cons] at computed
      cases headComputed : input.buildRuleMajorCumulativeWithRead? stage read fuel cursor with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : cursors.mapM
              (input.buildRuleMajorCumulativeWithRead? stage read fuel) with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst keys
              rcases List.mem_cons.mp present with headPresent | tailPresent
              · subst key
                exact ⟨cursor, by simp, headComputed⟩
              · obtain ⟨source, sourcePresent, sourceComputed⟩ :=
                  mem_of_mapM_ruleMajor_some input stage read fuel cursors tail
                    tailComputed key tailPresent
                exact ⟨source, List.mem_cons_of_mem cursor sourcePresent, sourceComputed⟩

private theorem exists_mem_getD_noref {α : Type*}
    {layers : List (List α)} {depth : Nat} {entry : α}
    (present : entry ∈ layers.getD depth []) :
    ∃ layer, layer ∈ layers ∧ entry ∈ layer := by
  rw [List.getD_eq_getElem?_getD] at present
  cases looked : layers[depth]? with
  | none => rw [looked] at present; simp at present
  | some layer =>
      rw [looked] at present
      exact ⟨layer, List.mem_of_getElem? looked, present⟩

private theorem mem_fst_zipIdx_noref {α : Type*} (item : α × Nat) :
    ∀ (values : List α) (start : Nat), item ∈ values.zipIdx start → item.1 ∈ values
  | [], _, present => by simp at present
  | value :: values, start, present => by
      rw [List.zipIdx_cons] at present
      rcases List.mem_cons.mp present with head | tail
      · subst item
        simp
      · exact List.mem_cons_of_mem value
          (mem_fst_zipIdx_noref item values (start + 1) tail)

private theorem mapM_some_source_key
    {α β : Type*} (f : α → Option β) :
    ∀ (sources : List α) (results : List β), sources.mapM f = some results →
      ∀ source, source ∈ sources →
        ∃ result, result ∈ results ∧ f source = some result
  | [], results, computed, source, present => by
      simp at present
  | source :: sources, results, computed, source', present => by
      rw [List.mapM_cons] at computed
      cases head : f source with
      | none => simp [head] at computed
      | some result =>
          cases tail : sources.mapM f with
          | none => simp [head, tail] at computed
          | some rest =>
              simp [head, tail] at computed
              subst results
              rcases List.mem_cons.mp present with same | later
              · subst source'
                exact ⟨result, by simp, head⟩
              · obtain ⟨next, nextMem, nextComputed⟩ :=
                  mapM_some_source_key f sources rest tail source' later
                exact ⟨next, by simp [nextMem], nextComputed⟩

private theorem noReferenceStepChildLabelsChiralFree
    (input : CertifiedLocalizedCIPInput)
    {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (label : Option LocalizedAuxiliaryLabel)
    (children : List input.LocalizedRerootCumulativeRule45Key)
    (child : input.LocalizedRerootCumulativeRule45Key)
    (childMem : child ∈ children)
    (parentFree : LocalizedLabelLayersChiralFree
      (localizedCumulativeRule45StepKey input .rule4cNoReference
        cursor label children).labels) :
    LocalizedLabelLayersChiralFree child.labels := by
  have freeLabels : LocalizedLabelLayersChiralFree
      ([[([], label)]] ++ input.mergeLocalizedRerootLabelChildren children) := by
    simpa [localizedCumulativeRule45StepKey] using parentFree
  obtain ⟨slot, atSlot⟩ := List.mem_iff_getElem?.mp childMem
  intro childLayer childLayerMem entry entryMem descriptor chiral
  obtain ⟨depth, depthLookup⟩ := List.mem_iff_getElem?.mp childLayerMem
  have childLayerGetD : child.labels.getD depth [] = childLayer := by
    rw [List.getD_eq_getElem?_getD, depthLookup]
    rfl
  have projected := TetraStereo.OneCenter.SparseAddress.labelTable_getD_entriesAtSlot_dropAddressHeadLayer
    input label children depth slot child atSlot
  have entryProjected : entry ∈ dropAddressHeadLayer
      (entriesAtSlot slot
        (([[([], label)]] ++ input.mergeLocalizedRerootLabelChildren children).getD
          (1 + depth) [])) := by
    rw [projected, childLayerGetD]
    exact entryMem
  change entry ∈ (entriesAtSlot slot
      (([[([], label)]] ++ input.mergeLocalizedRerootLabelChildren children).getD
        (1 + depth) [])).map dropAddressHead at entryProjected
  obtain ⟨parentEntry, parentEntryMem, droppedEq⟩ := List.mem_map.mp entryProjected
  have parentEntryInSphere : parentEntry ∈
      ([[([], label)]] ++ input.mergeLocalizedRerootLabelChildren children).getD
        (1 + depth) [] :=
    (mem_entriesAtSlot_iff).mp parentEntryMem |>.1
  obtain ⟨parentLayer, parentLayerMem, parentEntryMem⟩ :=
    exists_mem_getD_noref parentEntryInSphere
  have parentChiralFree := freeLabels parentLayer parentLayerMem
    parentEntry parentEntryMem descriptor
  have sameValue : parentEntry.2 = entry.2 := by
    have valueEq := congrArg Prod.snd droppedEq
    simpa [dropAddressHead] using valueEq
  exact parentChiralFree (sameValue.trans chiral)

private theorem noReferenceShape_ruleMajorBuilder
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel) :
    ∀ fuel (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootCumulativeRule45Key),
      input.buildRuleMajorCumulativeWithRead? .rule4cNoReference read fuel cursor =
        some key → input.Stage4cNoReferenceShaped key := by
  intro fuel
  induction fuel with
  | zero =>
      intro cursor key computed
      unfold buildRuleMajorCumulativeWithRead? at computed
      cases childrenEq : input.localizedRerootChildren? cursor with
      | none => simp [childrenEq] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenEq, terminal] at computed
            subst key
            intro layer layerMem entry entryMem
            simp only [List.mem_singleton] at layerMem
            subst layer
            simp only [List.mem_singleton] at entryMem
            subst entry
            rfl
          · simp [childrenEq, terminal] at computed
  | succ fuel ih =>
      intro cursor key computed
      unfold buildRuleMajorCumulativeWithRead? at computed
      cases childrenEq : input.localizedRerootChildren? cursor with
      | none => simp [childrenEq] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenEq, terminal] at computed
            subst key
            intro layer layerMem entry entryMem
            simp only [List.mem_singleton] at layerMem
            subst layer
            simp only [List.mem_singleton] at entryMem
            subst entry
            rfl
          · cases keysEq : children.mapM
                (input.buildRuleMajorCumulativeWithRead? .rule4cNoReference read fuel) with
            | none => simp [childrenEq, terminal, keysEq] at computed
            | some keys =>
                simp [childrenEq, terminal, keysEq] at computed
                subst key
                have keyShape : ∀ child ∈ keys, input.Stage4cNoReferenceShaped child := by
                  intro child present
                  obtain ⟨childCursor, _, childComputed⟩ :=
                  mem_of_mapM_ruleMajor_some input .rule4cNoReference read
                      fuel children keys keysEq child present
                  exact ih childCursor child childComputed
                have sortedPerm :
                    input.sortRuleMajorCumulativeKeys .rule4cNoReference keys |>.Perm keys := by
                  simpa [sortRuleMajorCumulativeKeys, ruleMajorStageWidth] using
                    input.sortKeysBy_ruleMajorCumulative_perm 2 keys
                have sortedShape : ∀ child ∈
                    input.sortRuleMajorCumulativeKeys .rule4cNoReference keys,
                    input.Stage4cNoReferenceShaped child := fun child present =>
                  keyShape child (sortedPerm.mem_iff.1 present)
                intro layer layerMem entry entryMem
                simp only [List.cons_append,
                  List.nil_append, List.mem_cons] at layerMem
                rcases layerMem with rootLayer | childLayer
                · subst layer
                  simp only [List.mem_singleton] at entryMem
                  subst entry
                  simp [localizedCumulativeRule45Priority]
                · unfold mergeLocalizedRerootDescriptorChildren at childLayer
                  simp only [List.mem_map, List.mem_range] at childLayer
                  obtain ⟨depth, _, rfl⟩ := childLayer
                  rw [List.mem_flatMap] at entryMem
                  obtain ⟨child, childPresent, entryMem⟩ := entryMem
                  unfold prefixLayer at entryMem
                  rw [List.mem_map] at entryMem
                  obtain ⟨entry', entryMem, rfl⟩ := entryMem
                  obtain ⟨childLayer, childLayerMem, childEntryMem⟩ :=
                    exists_mem_getD_noref entryMem
                  exact sortedShape child.1
                    (mem_fst_zipIdx_noref child _ 0 childPresent)
                    childLayer childLayerMem entry' childEntryMem

private theorem noReferenceBuildReadChiralFreeBelow
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel) :
    ∀ fuel (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : input.LocalizedRerootCumulativeRule45Key),
      input.buildRuleMajorCumulativeWithRead? .rule4cNoReference read fuel cursor =
        some key →
      LocalizedLabelLayersChiralFree key.labels →
      input.RuleMajorReadChiralFreeBelow read fuel cursor := by
  intro fuel
  induction fuel with
  | zero =>
      intro cursor key computed labelsFree
      unfold buildRuleMajorCumulativeWithRead? at computed
      cases childrenEq : input.localizedRerootChildren? cursor with
      | none => simp [childrenEq] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenEq, terminal] at computed
            subst key
            have rootFree : ∀ descriptor : RS,
                read cursor ≠ some (.chiral descriptor) := by
              intro descriptor chiral
              have freeRoot := labelsFree [([], read cursor)] (by simp)
                ([], read cursor) (by simp) descriptor
              exact freeRoot chiral
            exact rootFree
          · simp [childrenEq, terminal] at computed
  | succ fuel ih =>
      intro cursor key computed labelsFree
      unfold buildRuleMajorCumulativeWithRead? at computed
      cases childrenEq : input.localizedRerootChildren? cursor with
      | none => simp [childrenEq] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenEq, terminal] at computed
            subst key
            have rootFree : ∀ descriptor : RS,
                read cursor ≠ some (.chiral descriptor) := by
              intro descriptor chiral
              have freeRoot := labelsFree [([], read cursor)] (by simp)
                ([], read cursor) (by simp) descriptor
              exact freeRoot chiral
            refine ⟨rootFree, ?_⟩
            simp [childrenEq, terminal]
          · cases childKeysComputed : children.mapM
                (input.buildRuleMajorCumulativeWithRead? .rule4cNoReference read fuel) with
            | none => simp [childrenEq, terminal, childKeysComputed] at computed
            | some childKeys =>
                simp [childrenEq, terminal, childKeysComputed] at computed
                subst key
                let sortedKeys := input.sortRuleMajorCumulativeKeys
                  .rule4cNoReference childKeys
                have sortedPerm : sortedKeys.Perm childKeys := by
                  simpa [sortedKeys, sortRuleMajorCumulativeKeys, ruleMajorStageWidth] using
                    input.sortKeysBy_ruleMajorCumulative_perm 2 childKeys
                have sortedLabelsFree : ∀ child ∈ sortedKeys,
                    LocalizedLabelLayersChiralFree child.labels := by
                  intro child childMem
                  exact noReferenceStepChildLabelsChiralFree input cursor (read cursor)
                    sortedKeys child childMem labelsFree
                have childFree : ∀ child ∈ children,
                    input.RuleMajorReadChiralFreeBelow read fuel child := by
                  intro child childMem
                  obtain ⟨childKey, childKeyMem, childComputed⟩ :=
                    mapM_some_source_key
                      (input.buildRuleMajorCumulativeWithRead? .rule4cNoReference read fuel)
                      children childKeys childKeysComputed child childMem
                  have childSortedMem : childKey ∈ sortedKeys :=
                    sortedPerm.mem_iff.mpr childKeyMem
                  exact ih child childKey childComputed
                    (sortedLabelsFree childKey childSortedMem)
                have rootFree : ∀ descriptor : RS,
                    read cursor ≠ some (.chiral descriptor) := by
                  intro descriptor chiral
                  have freeRoot := labelsFree [([], read cursor)] (by simp)
                    ([], read cursor) (by simp) descriptor
                  exact freeRoot chiral
                unfold RuleMajorReadChiralFreeBelow
                rw [childrenEq]
                exact ⟨rootFree, childFree⟩

private theorem rule5Lift_ruleMajorInsert_noref (same : Bool)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (keyShape : input.Stage4cNoReferenceShaped key) :
    ∀ keys : List input.LocalizedRerootCumulativeRule45Key,
      (∀ child ∈ keys, input.Stage4cNoReferenceShaped child) →
      insertKeyBy (input.compareRuleMajorCumulativeDescriptor 3)
          (input.rule5LiftKey same key) (keys.map (input.rule5LiftKey same)) =
        (insertKeyBy (input.compareRuleMajorCumulativeDescriptor 2) key keys).map
          (input.rule5LiftKey same)
  | [], _ => rfl
  | head :: tail, shaped => by
      have headShape := shaped head List.mem_cons_self
      have comparison := compareRuleMajorCumulativeDescriptor_rule5LiftKey_noref
        input same key head keyShape headShape
      simp only [List.map_cons, insertKeyBy, comparison]
      cases input.compareRuleMajorCumulativeDescriptor 2 key head <;>
        simp [rule5Lift_ruleMajorInsert_noref same key keyShape tail
          (fun child member => shaped child (List.mem_cons_of_mem head member))]

private theorem sortRuleMajorRule5LiftKey_noref (same : Bool) :
    ∀ keys : List input.LocalizedRerootCumulativeRule45Key,
      (∀ child ∈ keys, input.Stage4cNoReferenceShaped child) →
      sortKeysBy (input.compareRuleMajorCumulativeDescriptor 3)
          (keys.map (input.rule5LiftKey same)) =
        (sortKeysBy (input.compareRuleMajorCumulativeDescriptor 2) keys).map
          (input.rule5LiftKey same)
  | [], _ => rfl
  | key :: tail, shaped => by
      have keyShape := shaped key List.mem_cons_self
      have tailShape : ∀ child ∈ tail, input.Stage4cNoReferenceShaped child :=
        fun child member => shaped child (List.mem_cons_of_mem key member)
      have sortedTailShape : ∀ child ∈
          sortKeysBy (input.compareRuleMajorCumulativeDescriptor 2) tail,
          input.Stage4cNoReferenceShaped child := fun child member =>
        tailShape child ((input.sortKeysBy_ruleMajorCumulative_perm 2 tail).mem_iff.1 member)
      simp only [List.map_cons, sortKeysBy]
      rw [sortRuleMajorRule5LiftKey_noref same tail tailShape,
        rule5Lift_ruleMajorInsert_noref input same key keyShape
          (sortKeysBy (input.compareRuleMajorCumulativeDescriptor 2) tail) sortedTailShape]

theorem sortRuleMajorCumulativeKeys_rule5NoReferenceLift (same : Bool)
    (probe : RS) (keys : List input.LocalizedRerootCumulativeRule45Key)
    (shaped : ∀ key ∈ keys, input.Stage4cNoReferenceShaped key) :
    input.sortRuleMajorCumulativeKeys (.rule5NoRule4bReference probe)
        (keys.map (input.rule5LiftKey same)) =
      (input.sortRuleMajorCumulativeKeys .rule4cNoReference keys).map
        (input.rule5LiftKey same) := by
  change sortKeysBy (input.compareRuleMajorCumulativeDescriptor 3)
      (keys.map (input.rule5LiftKey same)) = _
  change _ = (sortKeysBy (input.compareRuleMajorCumulativeDescriptor 2) keys).map
    (input.rule5LiftKey same)
  exact sortRuleMajorRule5LiftKey_noref input same keys shaped

private theorem mapM_map_option_noref {α β γ : Type*}
    (f : α → Option β) (g : α → Option γ) (h : β → γ) :
    ∀ values : List α, (∀ value ∈ values, g value = (f value).map h) →
      values.mapM g = (values.mapM f).map (List.map h)
  | [], _ => rfl
  | value :: values, agree => by
      rw [List.mapM_cons, List.mapM_cons, agree value List.mem_cons_self,
        mapM_map_option_noref f g h values
          (fun inner present => agree inner (List.mem_cons_of_mem value present))]
      cases f value <;> cases values.mapM f <;> rfl

theorem buildRuleMajorCumulativeWithRead?_rule5NoReference_of_chiralFreeBelow
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (probe : RS)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel) :
    ∀ fuel (cursor : input.LocalizedRerootCursor carrierFuel),
      input.RuleMajorReadChiralFreeBelow read fuel cursor →
      input.buildRuleMajorCumulativeWithRead?
          (.rule5NoRule4bReference probe) read fuel cursor =
        (input.buildRuleMajorCumulativeWithRead? .rule4cNoReference read fuel cursor).map
          (input.rule5LiftKey false)
  | 0, cursor => by
      intro free
      unfold buildRuleMajorCumulativeWithRead?
      cases childrenEq : input.localizedRerootChildren? cursor with
      | none => rfl
      | some children =>
          by_cases terminal : children = []
          · have rootFree := free
            simp only [Option.bind_eq_bind, Option.bind_some, if_pos terminal]
            simp [localizedCumulativeRule45TerminalKey, rule5LiftKey, rule5LiftLayer,
              rule5Lift, rule5Bit, read_priority_noReference_lift probe (read cursor) rootFree]
          · simp [terminal]
  | fuel + 1, cursor => by
      intro free
      have rootFree := free.1
      unfold buildRuleMajorCumulativeWithRead?
      cases childrenEq : input.localizedRerootChildren? cursor with
      | none => rfl
      | some children =>
          by_cases terminal : children = []
          · simp only [Option.bind_eq_bind, Option.bind_some, if_pos terminal]
            simp [localizedCumulativeRule45TerminalKey, rule5LiftKey, rule5LiftLayer,
              rule5Lift, rule5Bit, read_priority_noReference_lift probe (read cursor) rootFree]
          · have childFree : ∀ child ∈ children,
                input.RuleMajorReadChiralFreeBelow read fuel child := by
              simpa [childrenEq] using free.2
            simp only [Option.bind_eq_bind, Option.bind_some, if_neg terminal]
            rw [mapM_map_option_noref
              (input.buildRuleMajorCumulativeWithRead? .rule4cNoReference read fuel)
              (input.buildRuleMajorCumulativeWithRead?
                (.rule5NoRule4bReference probe) read fuel)
              (input.rule5LiftKey false) children (by
                intro child present
                exact buildRuleMajorCumulativeWithRead?_rule5NoReference_of_chiralFreeBelow
                  input probe read fuel child (childFree child present))]
            cases baseKeys : children.mapM
                (input.buildRuleMajorCumulativeWithRead? .rule4cNoReference read fuel) with
            | none => rfl
            | some childKeys =>
                have childShape : ∀ child ∈ childKeys,
                    input.Stage4cNoReferenceShaped child := by
                  intro child present
                  obtain ⟨childCursor, _, computed⟩ :=
                  mem_of_mapM_ruleMajor_some input .rule4cNoReference read
                      fuel children childKeys baseKeys child present
                  exact noReferenceShape_ruleMajorBuilder input read fuel childCursor child computed
                have sortedPerm :
                    input.sortRuleMajorCumulativeKeys .rule4cNoReference childKeys |>.Perm childKeys := by
                  simpa [sortRuleMajorCumulativeKeys, ruleMajorStageWidth] using
                    input.sortKeysBy_ruleMajorCumulative_perm 2 childKeys
                have sortedShape : ∀ child ∈
                    input.sortRuleMajorCumulativeKeys .rule4cNoReference childKeys,
                    input.Stage4cNoReferenceShaped child := fun child present =>
                  childShape child (sortedPerm.mem_iff.1 present)
                simp only [Option.map_some, Option.bind_some, Option.some.injEq]
                rw [sortRuleMajorCumulativeKeys_rule5NoReferenceLift input false probe
                  childKeys childShape]
                simp only [localizedCumulativeRule45StepKey, rule5LiftKey]
                rw [input.mergeDescriptor_rule5LiftKey,
                  input.mergeLabel_rule5LiftKey,
                  mergeRankedLabel_rule5LiftKey_noref input false
                    (input.sortRuleMajorCumulativeKeys .rule4cNoReference childKeys)
                    sortedShape]
                simp only [List.map_map, List.map_append, List.map_cons, List.map_nil,
                  rule5LiftLayer, read_priority_noReference_lift probe (read cursor) rootFree]
                rfl

/-- A successful no-reference 4c key whose exact observations are chiral-free supplies the
trace-local premise automatically.  This connects the exact Rule-5 lift to a condition stated on
the produced whole-rule key, rather than on the reader at unrelated cursors. -/
theorem buildRuleMajorCumulativeWithRead?_rule5NoReference_of_keyChiralFree
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (probe : RS)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (computed : input.buildRuleMajorCumulativeWithRead? .rule4cNoReference
      read fuel cursor = some key)
    (labelsFree : LocalizedLabelLayersChiralFree key.labels) :
    input.buildRuleMajorCumulativeWithRead?
        (.rule5NoRule4bReference probe) read fuel cursor =
      (input.buildRuleMajorCumulativeWithRead? .rule4cNoReference read fuel cursor).map
        (input.rule5LiftKey false) := by
  exact buildRuleMajorCumulativeWithRead?_rule5NoReference_of_chiralFreeBelow
    input probe read fuel cursor
    (noReferenceBuildReadChiralFreeBelow input read fuel cursor key computed labelsFree)

/-- On a successful no-reference 4c key with chiral-free labels, the Rule-5 cumulative build is
independent of the candidate used to instantiate the no-Rule-4b-reference stage. -/
theorem buildRuleMajorCumulativeWithRead?_rule5NoReference_same_for_allReferences_of_keyChiralFree
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (leftReference rightReference : RS)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (computed : input.buildRuleMajorCumulativeWithRead? .rule4cNoReference
      read fuel cursor = some key)
    (labelsFree : LocalizedLabelLayersChiralFree key.labels) :
    input.buildRuleMajorCumulativeWithRead?
        (.rule5NoRule4bReference leftReference) read fuel cursor =
      input.buildRuleMajorCumulativeWithRead?
        (.rule5NoRule4bReference rightReference) read fuel cursor := by
  rw [buildRuleMajorCumulativeWithRead?_rule5NoReference_of_keyChiralFree
      input leftReference read fuel cursor key computed labelsFree,
    buildRuleMajorCumulativeWithRead?_rule5NoReference_of_keyChiralFree
      input rightReference read fuel cursor key computed labelsFree]

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.Stage4cNoReferenceShaped
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorReadChiralFreeBelow
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.sortRuleMajorCumulativeKeys_rule5NoReferenceLift
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCumulativeWithRead?_rule5NoReference_of_chiralFreeBelow
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCumulativeWithRead?_rule5NoReference_of_keyChiralFree
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCumulativeWithRead?_rule5NoReference_same_for_allReferences_of_keyChiralFree
