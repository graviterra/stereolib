import TetraStereo.OneCenter.LocalizedActualRecursiveSortTrace
import TetraStereo.OneCenter.LocalizedRuleMajorCumulativeTrace
import TetraStereo.OneCenter.LocalizedActualRule4aTableBridge
import TetraStereo.OneCenter.LocalizedRuleMajorCumulativeBuilder
import TetraStereo.OneCenter.LocalizedRuleMajorCumulativeOrder
import TetraStereo.OneCenter.LocalizedParametricCumulativeLabels
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The old recursive Rule-4a builder sorts by its node-major cumulative comparator, while the new
whole-rule builder sorts by the Rule-4a column over the full descriptor table. Successful traces
give actual table matches for both builders. The Rule-4a table bridge identifies the old descriptor
comparison with its scalar column, which is exactly the width-one projection compared by the new
builder. We use that derived comparator equality only for keys actually produced by a successful
Rule-4a build. -/

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

open OfficialRuleMajorKey
open LocalizedCumulativeDecoratedTree

private theorem mapM_same_values_agreement {α β : Type*}
    (left right : α → Option β) :
    ∀ (values : List α), (∀ value ∈ values, left value = right value) →
      values.mapM left = values.mapM right
  | [], _ => rfl
  | value :: values, agree => by
      rw [List.mapM_cons, List.mapM_cons, agree value List.mem_cons_self,
        mapM_same_values_agreement left right values
          (fun item present => agree item (List.mem_cons_of_mem value present))]

private theorem mapM_some_source_of_member {α β : Type*}
    (build : α → Option β) :
    ∀ (sources : List α) (results : List β), sources.mapM build = some results →
      ∀ result, result ∈ results → ∃ source, source ∈ sources ∧ build source = some result
  | [], results, computed, result, present => by
      simp at computed
      subst results
      simp at present
  | source :: sources, results, computed, result, present => by
      rw [List.mapM_cons] at computed
      cases head : build source with
      | none => simp [head] at computed
      | some value =>
          cases tail : sources.mapM build with
          | none => simp [head, tail] at computed
          | some rest =>
              simp [head, tail] at computed
              subst results
              rcases List.mem_cons.mp present with here | there
              · subst result
                exact ⟨source, by simp, head⟩
              · obtain ⟨witness, witnessMem, witnessBuilt⟩ :=
                  mapM_some_source_of_member build sources rest tail result there
                exact ⟨witness, List.mem_cons_of_mem source witnessMem, witnessBuilt⟩

private theorem insertKeyBy_eq_of_memberComparison {α : Type*}
    (leftCompare rightCompare : α → α → Ordering) (key : α) :
    ∀ keys, (∀ other, other ∈ keys → leftCompare key other = rightCompare key other) →
      insertKeyBy leftCompare key keys = insertKeyBy rightCompare key keys
  | [], _ => rfl
  | head :: tail, agree => by
      have headAgree := agree head List.mem_cons_self
      have tailAgree : ∀ other, other ∈ tail →
          leftCompare key other = rightCompare key other := by
        intro other present
        exact agree other (List.mem_cons_of_mem head present)
      unfold insertKeyBy
      rw [headAgree]
      cases comparison : rightCompare key head with
      | lt =>
          exact congrArg (fun rest => head :: rest)
            (insertKeyBy_eq_of_memberComparison leftCompare rightCompare key tail tailAgree)
      | eq => rfl
      | gt => rfl

private theorem sortKeysBy_eq_of_memberComparison {α : Type*}
    (leftCompare rightCompare : α → α → Ordering) :
    ∀ keys, (∀ left, left ∈ keys → ∀ right, right ∈ keys →
        leftCompare left right = rightCompare left right) →
      sortKeysBy leftCompare keys = sortKeysBy rightCompare keys
  | [], _ => rfl
  | key :: tail, agree => by
      have tailAgree : ∀ left, left ∈ tail → ∀ right, right ∈ tail →
          leftCompare left right = rightCompare left right := by
        intro left leftMem right rightMem
        exact agree left (List.mem_cons_of_mem key leftMem)
          right (List.mem_cons_of_mem key rightMem)
      simp only [sortKeysBy]
      rw [sortKeysBy_eq_of_memberComparison leftCompare rightCompare tail tailAgree]
      apply insertKeyBy_eq_of_memberComparison leftCompare rightCompare key
      intro other present
      exact agree key List.mem_cons_self other
        ((sortKeysBy_perm rightCompare tail).mem_iff.mp present |> List.mem_cons_of_mem key)

private theorem insertLocalized_eq_insertKeyBy
    (input : CertifiedLocalizedCIPInput)
    (key : input.LocalizedRerootCumulativeRule45Key) :
    ∀ keys : List input.LocalizedRerootCumulativeRule45Key,
      input.insertLocalizedRerootCumulativeRule45Key key keys =
        insertKeyBy input.compareLocalizedRerootCumulativeRule45Keys key keys := by
  intro keys
  induction keys with
  | nil => rfl
  | cons head tail ih =>
      cases comparison : input.compareLocalizedRerootCumulativeRule45Keys key head with
      | lt =>
          simp only [insertLocalizedRerootCumulativeRule45Key, insertKeyBy, comparison]
          exact congrArg (fun rest => head :: rest) ih
      | eq => simp [insertLocalizedRerootCumulativeRule45Key, insertKeyBy, comparison]
      | gt => simp [insertLocalizedRerootCumulativeRule45Key, insertKeyBy, comparison]

private theorem sortLocalized_eq_sortKeysBy (input : CertifiedLocalizedCIPInput) :
    ∀ keys : List input.LocalizedRerootCumulativeRule45Key,
      input.sortLocalizedRerootCumulativeRule45Keys keys =
        sortKeysBy input.compareLocalizedRerootCumulativeRule45Keys keys
  | [] => rfl
  | key :: keys => by
      change input.insertLocalizedRerootCumulativeRule45Key key
          (input.sortLocalizedRerootCumulativeRule45Keys keys) =
        insertKeyBy input.compareLocalizedRerootCumulativeRule45Keys key
          (sortKeysBy input.compareLocalizedRerootCumulativeRule45Keys keys)
      rw [insertLocalized_eq_insertKeyBy input key,
        sortLocalized_eq_sortKeysBy input keys]

private theorem scalar4a_eq_projectZero
    {input : CertifiedLocalizedCIPInput}
    (key : input.LocalizedRerootCumulativeRule45Key) :
    Rule4aTableBridge.scalar4a key = projectCumulative 0 key.descriptor := by
  unfold Rule4aTableBridge.scalar4a Rule4aTableBridge.sparseEntryMap projectCumulative
  apply List.map_congr_left
  intro layer _
  apply List.map_congr_left
  intro entry _
  cases entry.2 <;> rfl

private theorem compareRule4aOld_eq_ruleMajor_one_of_tableMatches
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {leftTree rightTree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {left right : input.LocalizedRerootCumulativeRule45Key}
    (leftMatch : LocalizedCumulativeTreeTableMatch .rule4a leftTree left)
    (rightMatch : LocalizedCumulativeTreeTableMatch .rule4a rightTree right) :
    input.compareLocalizedRerootCumulativeRule45Keys left right =
      input.compareRuleMajorCumulativeDescriptor 1 left right := by
  have columnComparison : input.compareRuleMajorCumulativeColumnTables 1 left right =
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (Rule4aTableBridge.scalar4a left) (Rule4aTableBridge.scalar4a right) := by
    unfold compareRuleMajorCumulativeColumnTables ruleMajorCumulativeColumns
    simp only [List.range_one, List.map_cons, List.map_nil,
      List.compareLex_cons_cons, List.compareLex_nil_nil]
    rw [← scalar4a_eq_projectZero left, ← scalar4a_eq_projectZero right]
    cases comparison : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (Rule4aTableBridge.scalar4a left) (Rule4aTableBridge.scalar4a right) <;>
      simp [Ordering.then]
  rw [input.compareRuleMajorCumulativeDescriptor_eq_lexColumnsFunction]
  simp only [compareLocalizedRerootCumulativeRule45Keys, compareLex, Ordering.byKey]
  rw [Rule4aTableBridge.compare_descriptor_eq_scalar leftMatch rightMatch, columnComparison]

private theorem sortRule4aOld_eq_ruleMajor
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (children : List (input.LocalizedRerootCursor carrierFuel))
    (keys : List input.LocalizedRerootCumulativeRule45Key)
    (oldComputed : children.mapM
      (input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a read fuel) = some keys)
    (newComputed : children.mapM
      (input.buildRuleMajorCumulativeWithRead? .rule4a read fuel) = some keys) :
    input.sortLocalizedRerootCumulativeRule45Keys keys =
      input.sortRuleMajorCumulativeKeys .rule4a keys := by
  have comparatorAgreement : ∀ left, left ∈ keys → ∀ right, right ∈ keys →
      input.compareLocalizedRerootCumulativeRule45Keys left right =
        input.compareRuleMajorCumulativeDescriptor 1 left right := by
    intro left leftMem right rightMem
    obtain ⟨leftCursor, _, leftBuilt⟩ := mapM_some_source_of_member
      (input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a read fuel)
      children keys oldComputed left leftMem
    obtain ⟨rightCursor, _, rightBuilt⟩ := mapM_some_source_of_member
      (input.buildRuleMajorCumulativeWithRead? .rule4a read fuel)
      children keys newComputed right rightMem
    obtain ⟨leftTree, _, leftTrace⟩ :=
      exists_trace_of_buildWithRead input .rule4a read fuel leftCursor left leftBuilt
    obtain ⟨rightTree, _, rightTrace⟩ :=
      exists_ruleMajorTrace_of_buildWithRead input .rule4a read fuel rightCursor right rightBuilt
    exact compareRule4aOld_eq_ruleMajor_one_of_tableMatches
      (LocalizedActualRecursiveSortTrace.fullMatch_of_trace leftTrace).tableMatch
      (LocalizedRuleMajorSortTrace.fullMatch_of_trace rightTrace).tableMatch
  have widthOne : ruleMajorStageWidth .rule4a = 1 := rfl
  rw [sortLocalized_eq_sortKeysBy input keys]
  unfold sortRuleMajorCumulativeKeys
  rw [widthOne]
  exact sortKeysBy_eq_of_memberComparison
    input.compareLocalizedRerootCumulativeRule45Keys
    (input.compareRuleMajorCumulativeDescriptor 1) keys comparatorAgreement

/-- Exact equality of the old and whole-rule Rule-4a builders for every reader, fuel and cursor.
The proof follows the actual child `mapM`s and establishes sort agreement from table matches
carried by successful old and new traces. -/
theorem buildRuleMajorCumulativeWithRead?_rule4a_eq_localized
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel) :
    ∀ fuel cursor,
      input.buildRuleMajorCumulativeWithRead? .rule4a read fuel cursor =
        input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a read fuel cursor
  | 0, cursor => by
      unfold buildRuleMajorCumulativeWithRead?
        buildLocalizedRerootCumulativeRule45KeyWithRead?
      cases input.localizedRerootChildren? cursor <;> simp
  | fuel + 1, cursor => by
      unfold buildRuleMajorCumulativeWithRead?
        buildLocalizedRerootCumulativeRule45KeyWithRead?
      cases childrenEq : input.localizedRerootChildren? cursor with
      | none => rfl
      | some children =>
          by_cases terminal : children = []
          · simp [terminal]
          · have mapEq : children.mapM
                (input.buildRuleMajorCumulativeWithRead? .rule4a read fuel) =
              children.mapM
                (input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a read fuel) :=
                mapM_same_values_agreement
                  (input.buildRuleMajorCumulativeWithRead? .rule4a read fuel)
                  (input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a read fuel)
                  children (fun child _ => buildRuleMajorCumulativeWithRead?_rule4a_eq_localized
                    input read fuel child)
            cases oldChildren : children.mapM
                (input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a read fuel) with
            | none =>
                simp [terminal, mapEq, oldChildren]
            | some keys =>
                have newChildren : children.mapM
                    (input.buildRuleMajorCumulativeWithRead? .rule4a read fuel) = some keys := by
                  exact mapEq.trans oldChildren
                have sorting : input.sortLocalizedRerootCumulativeRule45Keys keys =
                    input.sortRuleMajorCumulativeKeys .rule4a keys :=
                  sortRule4aOld_eq_ruleMajor input read fuel children keys oldChildren newChildren
                simp [terminal, mapEq, oldChildren, sorting]

/-- The executable whole-rule Rule-4a builder also agrees with the existing production builder
when its reader is the production restricted dependency reader. This combines the executable
child-enumerator refinement, the arbitrary-reader Rule-4a agreement above, and the established
specialization theorem for the old builder. -/
theorem buildRuleMajorCumulativeWithReadExec?_rule4a_eq_localizedDependencyLabel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ fuel (cursor : input.LocalizedRerootCursor carrierFuel),
      input.buildRuleMajorCumulativeWithReadExec? .rule4a
          (fun cursor => input.localizedDependencyLabel target view cursor) fuel cursor =
        input.buildLocalizedRerootCumulativeRule45Key? .rule4a target view fuel cursor := by
  intro fuel cursor
  calc
    input.buildRuleMajorCumulativeWithReadExec? .rule4a
        (fun cursor => input.localizedDependencyLabel target view cursor) fuel cursor =
      input.buildRuleMajorCumulativeWithRead? .rule4a
        (fun cursor => input.localizedDependencyLabel target view cursor) fuel cursor :=
      input.buildRuleMajorCumulativeWithReadExec_eq .rule4a
        (fun cursor => input.localizedDependencyLabel target view cursor) fuel cursor
    _ = input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
          (fun cursor => input.localizedDependencyLabel target view cursor) fuel cursor :=
      input.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized
        (fun cursor => input.localizedDependencyLabel target view cursor) fuel cursor
    _ = input.buildLocalizedRerootCumulativeRule45Key? .rule4a target view fuel cursor :=
      input.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
        .rule4a target view fuel cursor

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCumulativeWithReadExec?_rule4a_eq_localizedDependencyLabel
