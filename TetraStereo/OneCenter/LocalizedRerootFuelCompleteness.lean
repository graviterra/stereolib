import TetraStereo.OneCenter.LocalizedRerootCompoundRule45Exact

set_option autoImplicit false

namespace TetraStereo.OneCenter










namespace CertifiedLocalizedCIPInput

/-- Address-only adjacency in one final-center occurrence tree. -/
def LocalizedCarrierTreeAdjacent
    (input : CertifiedLocalizedCIPInput)
    (first second : input.LocalizedCIPOccurrenceFrame) : Prop :=
  first.root = second.root ∧
    ((first.address.length + 1 = second.address.length ∧
        first.address = second.address.dropLast) ∨
      (second.address.length + 1 = first.address.length ∧
        second.address = first.address.dropLast))

/-- Carrier-neighbor membership is exactly carrier membership plus tree adjacency. -/
theorem mem_localizedRerootNeighborFrames_iff
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (source frame : input.LocalizedCIPOccurrenceFrame) :
    frame ∈ input.localizedRerootNeighborFrames (fuel := fuel) source ↔
      frame ∈ input.localizedOccurrences fuel ∧
        input.LocalizedCarrierTreeAdjacent frame source := by
  simp only [localizedRerootNeighborFrames, localizedCarrierParentFrames,
    localizedCarrierOutwardChildFrames, List.mem_append, List.mem_filter,
    Bool.and_eq_true, beq_iff_eq, LocalizedCarrierTreeAdjacent]
  aesop

/-- Tree-neighbor membership is symmetric when the source itself belongs to the carrier. -/
theorem mem_localizedRerootNeighborFrames_symm
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (source : input.LocalizedCIPOccurrence fuel)
    (frame : input.LocalizedCIPOccurrenceFrame)
    (present : frame ∈ input.localizedRerootNeighborFrames
      (fuel := fuel) source.1) :
    source.1 ∈ input.localizedRerootNeighborFrames (fuel := fuel) frame := by
  have characterized :=
    (input.mem_localizedRerootNeighborFrames_iff source.1 frame).mp present
  apply (input.mem_localizedRerootNeighborFrames_iff frame source.1).mpr
  refine ⟨source.2, ?_⟩
  rcases characterized.2 with ⟨sameRoot, parent | child⟩
  · exact ⟨sameRoot.symm, Or.inr ⟨parent.1, parent.2⟩⟩
  · exact ⟨sameRoot.symm, Or.inl ⟨child.1, child.2⟩⟩

/-- A reroot cursor is path-valid when its incoming coordinate is absent or is the tree neighbor
from which the cursor was reached. -/
def LocalizedRerootCursorValid
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) : Prop :=
  match cursor.previous? with
  | none => True
  | some previous =>
      cursor.occurrence.1 ∈ input.localizedRerootNeighborFrames
        (fuel := fuel) previous.1

/-- Intended children are uncut tree neighbors. -/
theorem mem_localizedRerootNeighborFrames_of_mem_intended
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (frame : input.LocalizedCIPOccurrenceFrame)
    (present : frame ∈ input.intendedLocalizedRerootChildFrames cursor) :
    frame ∈ input.localizedRerootNeighborFrames
      (fuel := fuel) cursor.occurrence.1 := by
  unfold intendedLocalizedRerootChildFrames at present
  split at present
  · simp at present
  · split at present
    · exact present
    · exact List.mem_of_mem_filter present

/-- The cut excludes the incoming root-relative address. -/
theorem address_ne_previous_of_mem_intended
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (previous : input.LocalizedCIPOccurrence fuel)
    (previousEq : cursor.previous? = some previous)
    (frame : input.LocalizedCIPOccurrenceFrame)
    (present : frame ∈ input.intendedLocalizedRerootChildFrames cursor) :
    frame.address ≠ previous.1.address := by
  unfold intendedLocalizedRerootChildFrames at present
  rw [previousEq] at present
  by_cases duplicate : cursor.occurrence.1.node.isDuplicateLeaf = true
  · simp [duplicate] at present
  · have cut : frame ∈ input.localizedRerootNeighborFrames
        (fuel := fuel) cursor.occurrence.1 ∧
        frame.address ≠ previous.1.address := by
      simpa [duplicate] using present
    exact cut.2

/-- Every emitted child cursor is path-valid. -/
theorem localizedRerootChild_valid
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor child : input.LocalizedRerootCursor fuel)
    (children : List (input.LocalizedRerootCursor fuel))
    (derived : input.DeclarativeLocalizedRerootChildren cursor children)
    (present : child ∈ children) :
    input.LocalizedRerootCursorValid child := by
  have intended : child.occurrence.1 ∈
      input.intendedLocalizedRerootChildFrames cursor := by
    rw [← derived.1]
    exact List.mem_map.mpr ⟨child, present, rfl⟩
  have previous := derived.2 child present
  unfold LocalizedRerootCursorValid
  rw [previous]
  change child.occurrence.1 ∈ input.localizedRerootNeighborFrames
    (fuel := fuel) cursor.occurrence.1
  exact input.mem_localizedRerootNeighborFrames_of_mem_intended cursor
    child.occurrence.1 intended




def localizedRerootCursorBudget
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) : Nat :=
  match cursor.previous? with
  | none => cursor.occurrence.1.address.length + (fuel + 1)
  | some previous =>
      if previous.1.address.length < cursor.occurrence.1.address.length then
        cursor.occurrence.1.remaining
      else
        cursor.occurrence.1.address.length + (fuel + 1)

/-- Every cursor budget is bounded by twice the common carrier depth. -/
theorem localizedRerootCursorBudget_le_twice
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    input.localizedRerootCursorBudget cursor ≤ 2 * (fuel + 1) := by
  have graded := input.localizedCIPOccurrence_depthGrade cursor.occurrence
  unfold localizedRerootCursorBudget
  split
  · omega
  · split <;> omega


theorem localizedRerootChild_budget_lt
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor child : input.LocalizedRerootCursor fuel)
    (children : List (input.LocalizedRerootCursor fuel))
    (cursorValid : input.LocalizedRerootCursorValid cursor)
    (derived : input.DeclarativeLocalizedRerootChildren cursor children)
    (present : child ∈ children) :
    input.localizedRerootCursorBudget child <
      input.localizedRerootCursorBudget cursor := by
  have childIntended : child.occurrence.1 ∈
      input.intendedLocalizedRerootChildFrames cursor := by
    rw [← derived.1]
    exact List.mem_map.mpr ⟨child, present, rfl⟩
  have childNeighbor := input.mem_localizedRerootNeighborFrames_of_mem_intended
    cursor child.occurrence.1 childIntended
  have childAdjacent :=
    (input.mem_localizedRerootNeighborFrames_iff
      cursor.occurrence.1 child.occurrence.1).mp childNeighbor |>.2
  have childPrevious := derived.2 child present
  have cursorGrade := input.localizedCIPOccurrence_depthGrade cursor.occurrence
  have childGrade := input.localizedCIPOccurrence_depthGrade child.occurrence
  unfold localizedRerootCursorBudget
  rw [childPrevious]
  cases previousEq : cursor.previous? with
  | none =>
      change (if cursor.occurrence.1.address.length <
          child.occurrence.1.address.length then child.occurrence.1.remaining
        else child.occurrence.1.address.length + (fuel + 1)) <
        cursor.occurrence.1.address.length + (fuel + 1)
      rcases childAdjacent with ⟨_sameRoot, childParent | childOutward⟩
      · have notDescending : ¬ cursor.occurrence.1.address.length <
            child.occurrence.1.address.length := by omega
        rw [if_neg notDescending]
        omega
      · have descending : cursor.occurrence.1.address.length <
            child.occurrence.1.address.length := by omega
        rw [if_pos descending]
        omega
  | some previous =>
      unfold LocalizedRerootCursorValid at cursorValid
      rw [previousEq] at cursorValid
      change cursor.occurrence.1 ∈ input.localizedRerootNeighborFrames
        (fuel := fuel) previous.1 at cursorValid
      have currentAdjacent : input.LocalizedCarrierTreeAdjacent
          cursor.occurrence.1 previous.1 := by
        exact (input.mem_localizedRerootNeighborFrames_iff
          previous.1 cursor.occurrence.1).mp cursorValid |>.2
      change (if cursor.occurrence.1.address.length <
          child.occurrence.1.address.length then child.occurrence.1.remaining
        else child.occurrence.1.address.length + (fuel + 1)) <
        (if previous.1.address.length < cursor.occurrence.1.address.length then
          cursor.occurrence.1.remaining
        else cursor.occurrence.1.address.length + (fuel + 1))
      rcases currentAdjacent with ⟨_sameRoot, currentParent | currentOutward⟩
      · have notDescendingCurrent : ¬ previous.1.address.length <
            cursor.occurrence.1.address.length := by omega
        rw [if_neg notDescendingCurrent]
        rcases childAdjacent with ⟨_sameChildRoot, childParent | childOutward⟩
        · have notDescendingChild : ¬ cursor.occurrence.1.address.length <
              child.occurrence.1.address.length := by omega
          rw [if_neg notDescendingChild]
          omega
        · have descendingChild : cursor.occurrence.1.address.length <
              child.occurrence.1.address.length := by omega
          rw [if_pos descendingChild]
          omega
      · have descendingCurrent : previous.1.address.length <
            cursor.occurrence.1.address.length := by omega
        rw [if_pos descendingCurrent]
        rcases childAdjacent with ⟨_sameChildRoot, childParent | childOutward⟩
        · have sameParentAddress :
              child.occurrence.1.address = previous.1.address := by
            exact childParent.2.trans currentOutward.2.symm
          exact (input.address_ne_previous_of_mem_intended cursor previous
            previousEq child.occurrence.1 childIntended sameParentAddress).elim
        · have descendingChild : cursor.occurrence.1.address.length <
              child.occurrence.1.address.length := by omega
          rw [if_pos descendingChild]
          omega

private theorem exists_mapM_buildLocalizedRerootCumulativeRule45Key?_of_forall
    (input : CertifiedLocalizedCIPInput) {carrierFuel evaluationFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ cursors : List (input.LocalizedRerootCursor carrierFuel),
      (∀ cursor ∈ cursors, ∃ key,
        input.buildLocalizedRerootCumulativeRule45Key?
          stage target view evaluationFuel cursor = some key) →
      ∃ keys, cursors.mapM
        (input.buildLocalizedRerootCumulativeRule45Key?
          stage target view evaluationFuel) = some keys
  | [], _ => ⟨[], rfl⟩
  | cursor :: cursors, complete => by
      obtain ⟨key, keyComputed⟩ := complete cursor (by simp)
      obtain ⟨keys, keysComputed⟩ :=
        input.exists_mapM_buildLocalizedRerootCumulativeRule45Key?_of_forall
          stage target view cursors (fun child present =>
            complete child (by simp [present]))
      exact ⟨key :: keys, by simp [keyComputed, keysComputed]⟩

/-- Evaluation succeeds whenever its structural fuel covers the strictly decreasing cursor
budget.  No chemical label assumption is needed: missing dependency labels are represented by
`none` inside the key, while structural truncation is impossible under the bound. -/
theorem exists_buildLocalizedRerootCumulativeRule45Key?_of_budget_le
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ evaluationFuel (cursor : input.LocalizedRerootCursor carrierFuel),
      input.LocalizedRerootCursorValid cursor →
      input.localizedRerootCursorBudget cursor ≤ evaluationFuel →
      ∃ key, input.buildLocalizedRerootCumulativeRule45Key?
        stage target view evaluationFuel cursor = some key
  | 0, cursor, valid, covered => by
      obtain ⟨children, childrenComputed⟩ := input.exists_localizedRerootChildren cursor
      have childrenDerived := input.localizedRerootChildren?_sound
        cursor children childrenComputed
      by_cases empty : children = []
      · let label := input.localizedDependencyLabel target view cursor
        refine ⟨
          { constitutional := input.moleculeGraph.officialRuleMajorRootKey
              cursor.occurrence.1.node true
            descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
            labels := [[([], label)]]
            rankedLabels := [[([], label)]] }, ?_⟩
        simp [buildLocalizedRerootCumulativeRule45Key?, childrenComputed, empty, label]
      · obtain ⟨child, present⟩ := List.exists_mem_of_ne_nil children empty
        have decreases := input.localizedRerootChild_budget_lt
          cursor child children valid childrenDerived present
        omega
  | evaluationFuel + 1, cursor, valid, covered => by
      obtain ⟨children, childrenComputed⟩ := input.exists_localizedRerootChildren cursor
      have childrenDerived := input.localizedRerootChildren?_sound
        cursor children childrenComputed
      by_cases empty : children = []
      · let label := input.localizedDependencyLabel target view cursor
        refine ⟨
          { constitutional := input.moleculeGraph.officialRuleMajorRootKey
              cursor.occurrence.1.node true
            descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
            labels := [[([], label)]]
            rankedLabels := [[([], label)]] }, ?_⟩
        simp [buildLocalizedRerootCumulativeRule45Key?, childrenComputed, empty, label]
      · have childComplete : ∀ child ∈ children, ∃ key,
            input.buildLocalizedRerootCumulativeRule45Key?
              stage target view evaluationFuel child = some key := by
          intro child present
          have childValid := input.localizedRerootChild_valid
            cursor child children childrenDerived present
          have decreases := input.localizedRerootChild_budget_lt
            cursor child children valid childrenDerived present
          apply input.exists_buildLocalizedRerootCumulativeRule45Key?_of_budget_le
            stage target view evaluationFuel child childValid
          omega
        obtain ⟨childKeys, childKeysComputed⟩ :=
          input.exists_mapM_buildLocalizedRerootCumulativeRule45Key?_of_forall
            stage target view children childComplete
        let label := input.localizedDependencyLabel target view cursor
        let sorted := input.sortLocalizedRerootCumulativeRule45Keys childKeys
        refine ⟨
          { constitutional := OfficialRuleMajorKey.assemble
              (input.moleculeGraph.officialRuleMajorRootKey
                cursor.occurrence.1.node false)
              (sorted.map fun child => child.constitutional)
            descriptor := [[([], localizedCumulativeRule45Priority stage label)]] ++
              input.mergeLocalizedRerootDescriptorChildren sorted
            labels := [[([], label)]] ++
              input.mergeLocalizedRerootLabelChildren sorted
            rankedLabels := [[([], label)]] ++
              input.mergeLocalizedRerootRankedLabelChildren sorted }, ?_⟩
        simp [buildLocalizedRerootCumulativeRule45Key?, childrenComputed, empty,
          childKeysComputed, label, sorted]

/-- Twice the carrier depth is sufficient for every path-valid reroot cursor. -/
theorem exists_buildLocalizedRerootCumulativeRule45Key?_at_twice
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor) :
    ∃ key, input.buildLocalizedRerootCumulativeRule45Key?
      stage target view (2 * (carrierFuel + 1)) cursor = some key := by
  apply input.exists_buildLocalizedRerootCumulativeRule45Key?_of_budget_le
    stage target view (2 * (carrierFuel + 1)) cursor valid
  exact input.localizedRerootCursorBudget_le_twice cursor

/-! ## Totality of the nonrecursive compound layers -/

/-- Every one-reference Rule-4b/4c reading succeeds at the proved reroot bound. -/
theorem exists_buildLocalizedRerootRule4bcReading?_at_twice
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    (reference : Option RS) :
    ∃ reading, input.buildLocalizedRerootRule4bcReading? target view
      (2 * (carrierFuel + 1)) cursor reference = some reading := by
  cases reference with
  | none =>
      obtain ⟨rule4bKey, rule4bComputed⟩ :=
        input.exists_buildLocalizedRerootCumulativeRule45Key?_at_twice
          .rule4a target view cursor valid
      obtain ⟨rule4cKey, rule4cComputed⟩ :=
        input.exists_buildLocalizedRerootCumulativeRule45Key?_at_twice
          .rule4cNoReference target view cursor valid
      exact ⟨
        { reference? := none
          rule4bKey := rule4bKey
          rule4cKey := rule4cKey },
        by simp [buildLocalizedRerootRule4bcReading?, rule4bComputed, rule4cComputed]⟩
  | some reference =>
      obtain ⟨rule4bKey, rule4bComputed⟩ :=
        input.exists_buildLocalizedRerootCumulativeRule45Key?_at_twice
          (.rule4b reference) target view cursor valid
      obtain ⟨rule4cKey, rule4cComputed⟩ :=
        input.exists_buildLocalizedRerootCumulativeRule45Key?_at_twice
          (.rule4c reference) target view cursor valid
      exact ⟨
        { reference? := some reference
          rule4bKey := rule4bKey
          rule4cKey := rule4cKey },
        by simp [buildLocalizedRerootRule4bcReading?, rule4bComputed, rule4cComputed]⟩

/-- Every finite normative Rule-4b/4c alternative list succeeds at the proved bound. -/
theorem exists_buildLocalizedRerootRule4bcReadings?_at_twice
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor) :
    ∀ references : List (Option RS),
      ∃ readings, input.buildLocalizedRerootRule4bcReadings? target view
        (2 * (carrierFuel + 1)) cursor references = some readings
  | [] => ⟨[], rfl⟩
  | reference :: references => by
      obtain ⟨reading, readingComputed⟩ :=
        input.exists_buildLocalizedRerootRule4bcReading?_at_twice
          target view cursor valid reference
      obtain ⟨readings, readingsComputed⟩ :=
        input.exists_buildLocalizedRerootRule4bcReadings?_at_twice
          target view cursor valid references
      exact ⟨reading :: readings,
        by simp [buildLocalizedRerootRule4bcReadings?, readingComputed, readingsComputed]⟩

/-- The complete no/one/two-reference Rule-4b/4c key is total at the proved bound. -/
theorem exists_buildLocalizedRerootCompoundRule4bcKey?_at_twice
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor) :
    ∃ key, input.buildLocalizedRerootCompoundRule4bcKey? target view
      (2 * (carrierFuel + 1)) cursor = some key := by
  obtain ⟨rule4aKey, rule4aComputed⟩ :=
    input.exists_buildLocalizedRerootCumulativeRule45Key?_at_twice
      .rule4a target view cursor valid
  let references := localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels
  let alternatives := localizedRule4bcReferenceAlternatives references
  obtain ⟨readings, readingsComputed⟩ :=
    input.exists_buildLocalizedRerootRule4bcReadings?_at_twice
      target view cursor valid alternatives
  exact ⟨
    { rule4aKey := rule4aKey
      references := references
      referenceCountPriority := constitutionalRule4bReferenceCountPriority references
      readings := readings },
    by simp [buildLocalizedRerootCompoundRule4bcKey?, rule4aComputed,
      references, alternatives, readingsComputed]⟩

/-- Both common-reference Rule-5 readings are total at the proved bound. -/
theorem exists_buildLocalizedRerootRule5Reading?_at_twice
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    (prior : input.LocalizedRerootRule4bcReading) :
    ∃ reading, input.buildLocalizedRerootRule5Reading? target view
      (2 * (carrierFuel + 1)) cursor prior = some reading := by
  obtain ⟨commonR, commonRComputed⟩ :=
    input.exists_buildLocalizedRerootCumulativeRule45Key?_at_twice
      (localizedRule5StageFor prior.reference? .R) target view cursor valid
  obtain ⟨commonS, commonSComputed⟩ :=
    input.exists_buildLocalizedRerootCumulativeRule45Key?_at_twice
      (localizedRule5StageFor prior.reference? .S) target view cursor valid
  exact ⟨{ prior := prior, commonR := commonR, commonS := commonS },
    by simp [buildLocalizedRerootRule5Reading?, commonRComputed, commonSComputed]⟩

/-- Every finite normative Rule-5 reading list is total at the proved bound. -/
theorem exists_buildLocalizedRerootRule5Readings?_at_twice
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor) :
    ∀ priors : List input.LocalizedRerootRule4bcReading,
      ∃ readings, input.buildLocalizedRerootRule5Readings? target view
        (2 * (carrierFuel + 1)) cursor priors = some readings
  | [] => ⟨[], rfl⟩
  | prior :: priors => by
      obtain ⟨reading, readingComputed⟩ :=
        input.exists_buildLocalizedRerootRule5Reading?_at_twice
          target view cursor valid prior
      obtain ⟨readings, readingsComputed⟩ :=
        input.exists_buildLocalizedRerootRule5Readings?_at_twice
          target view cursor valid priors
      exact ⟨reading :: readings,
        by simp [buildLocalizedRerootRule5Readings?, readingComputed, readingsComputed]⟩

/-- The complete compound through-Rule-5 key is total at the evaluator's stated bound. -/
theorem exists_buildLocalizedRerootCompoundRule45Key?_at_twice
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor) :
    ∃ key, input.buildLocalizedRerootCompoundRule45Key? target view
      (2 * (carrierFuel + 1)) cursor = some key := by
  obtain ⟨prior, priorComputed⟩ :=
    input.exists_buildLocalizedRerootCompoundRule4bcKey?_at_twice
      target view cursor valid
  obtain ⟨readings, readingsComputed⟩ :=
    input.exists_buildLocalizedRerootRule5Readings?_at_twice
      target view cursor valid prior.readings
  exact ⟨{ prior := prior, rule5Readings := readings }, by
    simp [buildLocalizedRerootCompoundRule45Key?, priorComputed, readingsComputed]⟩

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
