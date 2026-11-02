import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceCompoundRule45

set_option autoImplicit false

namespace TetraStereo.OneCenter










namespace AuthoritativeChemicalInput

open CertifiedLocalizedCIPInput

/-- Address-only adjacency in one final-center occurrence tree. -/
def AromaticCanonicalCarrierTreeAdjacent
    (source : AuthoritativeChemicalInput)
    (first second : source.AromaticCanonicalOccurrenceFrame) : Prop :=
  first.root = second.root ∧
    ((first.address.length + 1 = second.address.length ∧
        first.address = second.address.dropLast) ∨
      (second.address.length + 1 = first.address.length ∧
        second.address = first.address.dropLast))

/-- Carrier-neighbor membership is exactly carrier membership plus tree adjacency. -/
theorem mem_aromaticCanonicalRerootNeighborFrames_iff
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (sourceFrame frame : source.AromaticCanonicalOccurrenceFrame) :
    frame ∈ source.aromaticCanonicalRerootNeighborFrames (fuel := fuel) sourceFrame ↔
      frame ∈ source.aromaticCanonicalOccurrences fuel ∧
        source.AromaticCanonicalCarrierTreeAdjacent frame sourceFrame := by
  simp only [aromaticCanonicalRerootNeighborFrames, aromaticCanonicalCarrierParentFrames,
    aromaticCanonicalCarrierOutwardChildFrames, List.mem_append, List.mem_filter,
    Bool.and_eq_true, beq_iff_eq, AromaticCanonicalCarrierTreeAdjacent]
  aesop

/-- Tree-neighbor membership is symmetric when the source itself belongs to the carrier. -/
theorem mem_aromaticCanonicalRerootNeighborFrames_symm
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (sourceOccurrence : source.AromaticCanonicalOccurrence fuel)
    (frame : source.AromaticCanonicalOccurrenceFrame)
    (present : frame ∈ source.aromaticCanonicalRerootNeighborFrames
      (fuel := fuel) sourceOccurrence.1) :
    sourceOccurrence.1 ∈ source.aromaticCanonicalRerootNeighborFrames
      (fuel := fuel) frame := by
  have characterized :=
    (source.mem_aromaticCanonicalRerootNeighborFrames_iff
      sourceOccurrence.1 frame).mp present
  apply (source.mem_aromaticCanonicalRerootNeighborFrames_iff
    frame sourceOccurrence.1).mpr
  refine ⟨sourceOccurrence.2, ?_⟩
  rcases characterized.2 with ⟨sameRoot, parent | child⟩
  · exact ⟨sameRoot.symm, Or.inr ⟨parent.1, parent.2⟩⟩
  · exact ⟨sameRoot.symm, Or.inl ⟨child.1, child.2⟩⟩

/-- A reroot cursor is path-valid when its incoming coordinate is absent or is the tree neighbor
from which the cursor was reached. -/
def AromaticCanonicalRerootCursorValid
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (cursor : source.AromaticCanonicalRerootCursor fuel) : Prop :=
  match cursor.previous? with
  | none => True
  | some previous =>
      cursor.occurrence.1 ∈ source.aromaticCanonicalRerootNeighborFrames
        (fuel := fuel) previous.1

/-- Intended children are uncut tree neighbors. -/
theorem mem_aromaticCanonicalRerootNeighborFrames_of_mem_intended
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (cursor : source.AromaticCanonicalRerootCursor fuel)
    (frame : source.AromaticCanonicalOccurrenceFrame)
    (present : frame ∈ source.intendedAromaticCanonicalRerootChildFrames cursor) :
    frame ∈ source.aromaticCanonicalRerootNeighborFrames
      (fuel := fuel) cursor.occurrence.1 := by
  unfold intendedAromaticCanonicalRerootChildFrames at present
  split at present
  · simp at present
  · split at present
    · exact present
    · exact List.mem_of_mem_filter present

/-- The cut excludes the incoming root-relative address. -/
theorem address_ne_previous_of_mem_aromaticCanonicalIntended
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (cursor : source.AromaticCanonicalRerootCursor fuel)
    (previous : source.AromaticCanonicalOccurrence fuel)
    (previousEq : cursor.previous? = some previous)
    (frame : source.AromaticCanonicalOccurrenceFrame)
    (present : frame ∈ source.intendedAromaticCanonicalRerootChildFrames cursor) :
    frame.address ≠ previous.1.address := by
  unfold intendedAromaticCanonicalRerootChildFrames at present
  rw [previousEq] at present
  by_cases duplicate : cursor.occurrence.1.node.isDuplicateLeaf = true
  · simp [duplicate] at present
  · have cut : frame ∈ source.aromaticCanonicalRerootNeighborFrames
        (fuel := fuel) cursor.occurrence.1 ∧
        frame.address ≠ previous.1.address := by
      simpa [duplicate] using present
    exact cut.2

/-- Every emitted child cursor is path-valid. -/
theorem aromaticCanonicalRerootChild_valid
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (cursor child : source.AromaticCanonicalRerootCursor fuel)
    (children : List (source.AromaticCanonicalRerootCursor fuel))
    (derived : source.DeclarativeAromaticCanonicalRerootChildren cursor children)
    (present : child ∈ children) :
    source.AromaticCanonicalRerootCursorValid child := by
  have intended : child.occurrence.1 ∈
      source.intendedAromaticCanonicalRerootChildFrames cursor := by
    rw [← derived.1]
    exact List.mem_map.mpr ⟨child, present, rfl⟩
  have previous := derived.2 child present
  unfold AromaticCanonicalRerootCursorValid
  rw [previous]
  change child.occurrence.1 ∈ source.aromaticCanonicalRerootNeighborFrames
    (fuel := fuel) cursor.occurrence.1
  exact source.mem_aromaticCanonicalRerootNeighborFrames_of_mem_intended cursor
    child.occurrence.1 intended




def aromaticCanonicalRerootCursorBudget
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (cursor : source.AromaticCanonicalRerootCursor fuel) : Nat :=
  match cursor.previous? with
  | none => cursor.occurrence.1.address.length + (fuel + 1)
  | some previous =>
      if previous.1.address.length < cursor.occurrence.1.address.length then
        cursor.occurrence.1.remaining
      else
        cursor.occurrence.1.address.length + (fuel + 1)

/-- Every cursor budget is bounded by twice the common carrier depth. -/
theorem aromaticCanonicalRerootCursorBudget_le_twice
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (cursor : source.AromaticCanonicalRerootCursor fuel) :
    source.aromaticCanonicalRerootCursorBudget cursor ≤ 2 * (fuel + 1) := by
  have graded := source.aromaticCanonicalOccurrence_depthGrade cursor.occurrence
  unfold aromaticCanonicalRerootCursorBudget
  split
  · omega
  · split <;> omega


theorem aromaticCanonicalRerootChild_budget_lt
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (cursor child : source.AromaticCanonicalRerootCursor fuel)
    (children : List (source.AromaticCanonicalRerootCursor fuel))
    (cursorValid : source.AromaticCanonicalRerootCursorValid cursor)
    (derived : source.DeclarativeAromaticCanonicalRerootChildren cursor children)
    (present : child ∈ children) :
    source.aromaticCanonicalRerootCursorBudget child <
      source.aromaticCanonicalRerootCursorBudget cursor := by
  have childIntended : child.occurrence.1 ∈
      source.intendedAromaticCanonicalRerootChildFrames cursor := by
    rw [← derived.1]
    exact List.mem_map.mpr ⟨child, present, rfl⟩
  have childNeighbor := source.mem_aromaticCanonicalRerootNeighborFrames_of_mem_intended
    cursor child.occurrence.1 childIntended
  have childAdjacent :=
    (source.mem_aromaticCanonicalRerootNeighborFrames_iff
      cursor.occurrence.1 child.occurrence.1).mp childNeighbor |>.2
  have childPrevious := derived.2 child present
  have cursorGrade := source.aromaticCanonicalOccurrence_depthGrade cursor.occurrence
  have childGrade := source.aromaticCanonicalOccurrence_depthGrade child.occurrence
  unfold aromaticCanonicalRerootCursorBudget
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
      unfold AromaticCanonicalRerootCursorValid at cursorValid
      rw [previousEq] at cursorValid
      change cursor.occurrence.1 ∈ source.aromaticCanonicalRerootNeighborFrames
        (fuel := fuel) previous.1 at cursorValid
      have currentAdjacent : source.AromaticCanonicalCarrierTreeAdjacent
          cursor.occurrence.1 previous.1 := by
        exact (source.mem_aromaticCanonicalRerootNeighborFrames_iff
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
          exact (source.address_ne_previous_of_mem_aromaticCanonicalIntended cursor previous
            previousEq child.occurrence.1 childIntended sameParentAddress).elim
        · have descendingChild : cursor.occurrence.1.address.length <
              child.occurrence.1.address.length := by omega
          rw [if_pos descendingChild]
          omega

private theorem exists_mapM_buildAromaticCanonicalCumulativeRule45Key?_of_forall
    (source : AuthoritativeChemicalInput) {carrierFuel evaluationFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) :
    ∀ cursors : List (source.AromaticCanonicalRerootCursor carrierFuel),
      (∀ cursor ∈ cursors, ∃ key,
        source.buildAromaticCanonicalCumulativeRule45Key?
          stage target view evaluationFuel cursor = some key) →
      ∃ keys, cursors.mapM
        (source.buildAromaticCanonicalCumulativeRule45Key?
          stage target view evaluationFuel) = some keys
  | [], _ => ⟨[], rfl⟩
  | cursor :: cursors, complete => by
      obtain ⟨key, keyComputed⟩ := complete cursor (by simp)
      obtain ⟨keys, keysComputed⟩ :=
        source.exists_mapM_buildAromaticCanonicalCumulativeRule45Key?_of_forall
          stage target view cursors (fun child present =>
            complete child (by simp [present]))
      exact ⟨key :: keys, by simp [keyComputed, keysComputed]⟩

/-- Evaluation succeeds whenever its structural fuel covers the strictly decreasing cursor
budget.  No chemical label assumption is needed: missing dependency labels are represented by
`none` inside the key, while structural truncation is impossible under the bound. -/
theorem exists_buildAromaticCanonicalCumulativeRule45Key?_of_budget_le
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) :
    ∀ evaluationFuel (cursor : source.AromaticCanonicalRerootCursor carrierFuel),
      source.AromaticCanonicalRerootCursorValid cursor →
      source.aromaticCanonicalRerootCursorBudget cursor ≤ evaluationFuel →
      ∃ key, source.buildAromaticCanonicalCumulativeRule45Key?
        stage target view evaluationFuel cursor = some key
  | 0, cursor, valid, covered => by
      let children := source.aromaticCanonicalRerootChildren cursor
      have childrenComputed : source.aromaticCanonicalRerootChildren? cursor =
          some children := rfl
      have childrenDerived := source.aromaticCanonicalRerootChildren?_sound
        cursor children childrenComputed
      by_cases empty : children = []
      · let label := source.aromaticCanonicalDependencyLabel target view cursor
        refine ⟨
          { constitutional := MoleculeGraph.exactOfficialRuleMajorRootKey
              cursor.occurrence.1.node true
            descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
            labels := [[([], label)]]
            rankedLabels := [[([], label)]] }, ?_⟩
        simp [buildAromaticCanonicalCumulativeRule45Key?, childrenComputed, empty, label]
      · obtain ⟨child, present⟩ := List.exists_mem_of_ne_nil children empty
        have decreases := source.aromaticCanonicalRerootChild_budget_lt
          cursor child children valid childrenDerived present
        omega
  | evaluationFuel + 1, cursor, valid, covered => by
      let children := source.aromaticCanonicalRerootChildren cursor
      have childrenComputed : source.aromaticCanonicalRerootChildren? cursor =
          some children := rfl
      have childrenDerived := source.aromaticCanonicalRerootChildren?_sound
        cursor children childrenComputed
      by_cases empty : children = []
      · let label := source.aromaticCanonicalDependencyLabel target view cursor
        refine ⟨
          { constitutional := MoleculeGraph.exactOfficialRuleMajorRootKey
              cursor.occurrence.1.node true
            descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
            labels := [[([], label)]]
            rankedLabels := [[([], label)]] }, ?_⟩
        simp [buildAromaticCanonicalCumulativeRule45Key?, childrenComputed, empty, label]
      · have childComplete : ∀ child ∈ children, ∃ key,
            source.buildAromaticCanonicalCumulativeRule45Key?
              stage target view evaluationFuel child = some key := by
          intro child present
          have childValid := source.aromaticCanonicalRerootChild_valid
            cursor child children childrenDerived present
          have decreases := source.aromaticCanonicalRerootChild_budget_lt
            cursor child children valid childrenDerived present
          apply source.exists_buildAromaticCanonicalCumulativeRule45Key?_of_budget_le
            stage target view evaluationFuel child childValid
          omega
        obtain ⟨childKeys, childKeysComputed⟩ :=
          source.exists_mapM_buildAromaticCanonicalCumulativeRule45Key?_of_forall
            stage target view children childComplete
        let label := source.aromaticCanonicalDependencyLabel target view cursor
        let compare := source.compareAromaticCanonicalCumulativeRule45Keys
        let sorted := sortAromaticCanonicalCumulativeRule45Keys compare childKeys
        refine ⟨
          { constitutional := ExactOfficialRuleMajorKey.assemble
              (MoleculeGraph.exactOfficialRuleMajorRootKey
                cursor.occurrence.1.node false)
              (sorted.map fun child => child.constitutional)
            descriptor := [[([], localizedCumulativeRule45Priority stage label)]] ++
              mergeAromaticCanonicalDescriptorChildren sorted
            labels := [[([], label)]] ++
              mergeAromaticCanonicalLabelChildren sorted
            rankedLabels := [[([], label)]] ++
              mergeAromaticCanonicalRankedLabelChildren compare sorted }, ?_⟩
        simp [buildAromaticCanonicalCumulativeRule45Key?, childrenComputed, empty,
          childKeysComputed, label, compare, sorted]

/-- Twice the carrier depth is sufficient for every path-valid reroot cursor. -/
theorem exists_buildAromaticCanonicalCumulativeRule45Key?_at_twice
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (valid : source.AromaticCanonicalRerootCursorValid cursor) :
    ∃ key, source.buildAromaticCanonicalCumulativeRule45Key?
      stage target view (2 * (carrierFuel + 1)) cursor = some key := by
  apply source.exists_buildAromaticCanonicalCumulativeRule45Key?_of_budget_le
    stage target view (2 * (carrierFuel + 1)) cursor valid
  exact source.aromaticCanonicalRerootCursorBudget_le_twice cursor

/-! ## Totality of the nonrecursive compound layers -/

/-- Every one-reference Rule-4b/4c reading succeeds at the proved reroot bound. -/
theorem exists_buildAromaticCanonicalRerootRule4bcReading?_at_twice
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (valid : source.AromaticCanonicalRerootCursorValid cursor)
    (reference : Option RS) :
    ∃ reading, source.buildAromaticCanonicalRerootRule4bcReading? target view
      (2 * (carrierFuel + 1)) cursor reference = some reading := by
  cases reference with
  | none =>
      obtain ⟨rule4bKey, rule4bComputed⟩ :=
        source.exists_buildAromaticCanonicalCumulativeRule45Key?_at_twice
          .rule4a target view cursor valid
      obtain ⟨rule4cKey, rule4cComputed⟩ :=
        source.exists_buildAromaticCanonicalCumulativeRule45Key?_at_twice
          .rule4cNoReference target view cursor valid
      exact ⟨
        { reference? := none
          rule4bKey := rule4bKey
          rule4cKey := rule4cKey },
        by simp [buildAromaticCanonicalRerootRule4bcReading?, rule4bComputed, rule4cComputed]⟩
  | some reference =>
      obtain ⟨rule4bKey, rule4bComputed⟩ :=
        source.exists_buildAromaticCanonicalCumulativeRule45Key?_at_twice
          (.rule4b reference) target view cursor valid
      obtain ⟨rule4cKey, rule4cComputed⟩ :=
        source.exists_buildAromaticCanonicalCumulativeRule45Key?_at_twice
          (.rule4c reference) target view cursor valid
      exact ⟨
        { reference? := some reference
          rule4bKey := rule4bKey
          rule4cKey := rule4cKey },
        by simp [buildAromaticCanonicalRerootRule4bcReading?, rule4bComputed, rule4cComputed]⟩

/-- Every finite normative Rule-4b/4c alternative list succeeds at the proved bound. -/
theorem exists_buildAromaticCanonicalRerootRule4bcReadings?_at_twice
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (valid : source.AromaticCanonicalRerootCursorValid cursor) :
    ∀ references : List (Option RS),
      ∃ readings, source.buildAromaticCanonicalRerootRule4bcReadings? target view
        (2 * (carrierFuel + 1)) cursor references = some readings
  | [] => ⟨[], rfl⟩
  | reference :: references => by
      obtain ⟨reading, readingComputed⟩ :=
        source.exists_buildAromaticCanonicalRerootRule4bcReading?_at_twice
          target view cursor valid reference
      obtain ⟨readings, readingsComputed⟩ :=
        source.exists_buildAromaticCanonicalRerootRule4bcReadings?_at_twice
          target view cursor valid references
      exact ⟨reading :: readings,
        by simp [buildAromaticCanonicalRerootRule4bcReadings?, readingComputed, readingsComputed]⟩

/-- The complete no/one/two-reference Rule-4b/4c key is total at the proved bound. -/
theorem exists_buildAromaticCanonicalRerootCompoundRule4bcKey?_at_twice
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (valid : source.AromaticCanonicalRerootCursorValid cursor) :
    ∃ key, source.buildAromaticCanonicalRerootCompoundRule4bcKey? target view
      (2 * (carrierFuel + 1)) cursor = some key := by
  obtain ⟨rule4aKey, rule4aComputed⟩ :=
    source.exists_buildAromaticCanonicalCumulativeRule45Key?_at_twice
      .rule4a target view cursor valid
  let references := localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels
  let alternatives := aromaticCanonicalRule4bcReferenceAlternatives references
  obtain ⟨readings, readingsComputed⟩ :=
    source.exists_buildAromaticCanonicalRerootRule4bcReadings?_at_twice
      target view cursor valid alternatives
  exact ⟨
    { rule4aKey := rule4aKey
      references := references
      referenceCountPriority := constitutionalRule4bReferenceCountPriority references
      readings := readings },
    by simp [buildAromaticCanonicalRerootCompoundRule4bcKey?, rule4aComputed,
      references, alternatives, readingsComputed]⟩

/-- Both common-reference Rule-5 readings are total at the proved bound. -/
theorem exists_buildAromaticCanonicalRerootRule5Reading?_at_twice
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (valid : source.AromaticCanonicalRerootCursorValid cursor)
    (prior : source.AromaticCanonicalRerootRule4bcReading) :
    ∃ reading, source.buildAromaticCanonicalRerootRule5Reading? target view
      (2 * (carrierFuel + 1)) cursor prior = some reading := by
  obtain ⟨commonR, commonRComputed⟩ :=
    source.exists_buildAromaticCanonicalCumulativeRule45Key?_at_twice
      (aromaticCanonicalRule5StageFor prior.reference? .R) target view cursor valid
  obtain ⟨commonS, commonSComputed⟩ :=
    source.exists_buildAromaticCanonicalCumulativeRule45Key?_at_twice
      (aromaticCanonicalRule5StageFor prior.reference? .S) target view cursor valid
  exact ⟨{ prior := prior, commonR := commonR, commonS := commonS },
    by simp [buildAromaticCanonicalRerootRule5Reading?, commonRComputed, commonSComputed]⟩

/-- Every finite normative Rule-5 reading list is total at the proved bound. -/
theorem exists_buildAromaticCanonicalRerootRule5Readings?_at_twice
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (valid : source.AromaticCanonicalRerootCursorValid cursor) :
    ∀ priors : List source.AromaticCanonicalRerootRule4bcReading,
      ∃ readings, source.buildAromaticCanonicalRerootRule5Readings? target view
        (2 * (carrierFuel + 1)) cursor priors = some readings
  | [] => ⟨[], rfl⟩
  | prior :: priors => by
      obtain ⟨reading, readingComputed⟩ :=
        source.exists_buildAromaticCanonicalRerootRule5Reading?_at_twice
          target view cursor valid prior
      obtain ⟨readings, readingsComputed⟩ :=
        source.exists_buildAromaticCanonicalRerootRule5Readings?_at_twice
          target view cursor valid priors
      exact ⟨reading :: readings,
        by simp [buildAromaticCanonicalRerootRule5Readings?, readingComputed, readingsComputed]⟩

/-- The complete compound through-Rule-5 key is total at the evaluator's stated bound. -/
theorem exists_buildAromaticCanonicalRerootCompoundRule45Key?_at_twice
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (valid : source.AromaticCanonicalRerootCursorValid cursor) :
    ∃ key, source.buildAromaticCanonicalRerootCompoundRule45Key? target view
      (2 * (carrierFuel + 1)) cursor = some key := by
  obtain ⟨prior, priorComputed⟩ :=
    source.exists_buildAromaticCanonicalRerootCompoundRule4bcKey?_at_twice
      target view cursor valid
  obtain ⟨readings, readingsComputed⟩ :=
    source.exists_buildAromaticCanonicalRerootRule5Readings?_at_twice
      target view cursor valid prior.readings
  exact ⟨{ prior := prior, rule5Readings := readings }, by
    simp [buildAromaticCanonicalRerootCompoundRule45Key?, priorComputed, readingsComputed]⟩

end AuthoritativeChemicalInput

end TetraStereo.OneCenter
