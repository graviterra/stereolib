import TetraStereo.OneCenter.ProductionCIPRule6BranchingCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter.ProductionCIPRule6BranchingCompleteness

/-!
# Initial Rule-6 order from a lawful total key

Structural branching support already proves that every comparison used by the fail-closed initial
sort returns.  This module proves the next semantic fact: that literal option-valued sort is the
ordinary stable insertion sort of the independently lawful occurrence key.  Consequently its
output is pairwise nonincreasing and its adjacent traversal cannot contain an `lt` result.
-/

open RawMolecule
open ProductionCIPRerootComparatorLaws
open ProductionCIPOccurrenceDescriptorComparatorLaws
open ProductionCIPDescriptorBranchingCompleteness
open ProductionCIPRule6BranchingCompleteness
open DeclarativeCIP.ProductionOccurrenceRules456

namespace DescriptorBranchingRule6CIPFrame

/-- A total cursor lookup used only to state the lawful-key sorting relation.  All production
positions in this module are below four, so the phantom fallback is never observed. -/
def initialCursorAt
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (_frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (position : Nat) : CanonicalRerootCursor :=
  roots.getD position { node := mol.canonicalPhantom node.atom 0 }

/-- The independently lawful unary-key comparison pulled back to ligand positions. -/
def initialPositionComparator
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (left right : Nat) : Ordering :=
  let api := failClosedOccurrenceOrderingAPI mol state fuel
  api.compare (api.build (frame.initialCursorAt left))
    (api.build (frame.initialCursorAt right))

/-- Senior-or-equal relation induced by the lawful unary occurrence key. -/
def InitialPositionGE
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (left right : Nat) : Prop :=
  frame.initialPositionComparator left right ≠ Ordering.lt

instance initialPositionGE_decidable
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots) :
    DecidableRel frame.InitialPositionGE := by
  intro left right
  unfold InitialPositionGE
  infer_instance

theorem initialPositionComparator_transCmp
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots) :
    Std.TransCmp frame.initialPositionComparator := by
  let api := failClosedOccurrenceOrderingAPI mol state fuel
  letI := api.lawful
  exact
    { eq_swap := by
        exact Std.OrientedCmp.eq_swap (cmp := api.compare)
      isLE_trans := by
        intro left middle right leftMiddle middleRight
        exact Std.TransCmp.isLE_trans (cmp := api.compare) leftMiddle middleRight }

theorem initialPositionGE_total
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots) :
    Std.Total frame.InitialPositionGE := by
  letI := frame.initialPositionComparator_transCmp
  constructor
  intro left right
  by_cases relation : frame.initialPositionComparator left right = Ordering.lt
  · exact Or.inr (by
      unfold InitialPositionGE
      rw [Std.OrientedCmp.eq_swap (cmp := frame.initialPositionComparator)
        (a := right) (b := left)]
      simp [relation])
  · exact Or.inl relation

theorem initialPositionGE_trans
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots) :
    IsTrans Nat frame.InitialPositionGE := by
  letI := frame.initialPositionComparator_transCmp
  constructor
  intro left middle right leftMiddle middleRight
  exact Std.TransCmp.ge_trans leftMiddle middleRight

/-- Below the exact four-root bound, the total lookup is the literal production cursor lookup. -/
theorem roots_getElem?_eq_initialCursorAt
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (position : Nat) (position_lt : position < 4) :
    roots[position]? = some (frame.initialCursorAt position) := by
  have bound : position < roots.length := by simpa [frame.roots_length] using position_lt
  rw [List.getElem?_eq_getElem bound]
  congr 1
  simpa [initialCursorAt] using
    (List.getElem_eq_getD (l := roots) (i := position)
      ({ node := mol.canonicalPhantom node.atom 0 } : CanonicalRerootCursor))

/-- Every successful production position comparison factors through the independently lawful
unary key, and structural branching support supplies the success equation. -/
theorem compare_initial_positions_factors
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    {left right : Nat} (left_lt : left < 4) (right_lt : right < 4) :
    ∃ decision,
      compareRule6InitialPositions? (mol := mol) state fuel roots left right = some decision ∧
      frame.initialPositionComparator left right = decision.ordering := by
  rcases frame.compare_initial_positions_exists
      (frame.positionInFrame_of_lt_four left left_lt)
      (frame.positionInFrame_of_lt_four right right_lt) with ⟨decision, decisionEq⟩
  have leftEq := frame.roots_getElem?_eq_initialCursorAt left left_lt
  have rightEq := frame.roots_getElem?_eq_initialCursorAt right right_lt
  have occurrenceEq :
      compareOccurrenceBranches? mol state fuel (frame.initialCursorAt left)
          (frame.initialCursorAt right) = some decision := by
    simpa [compareRule6InitialPositions?, leftEq, rightEq] using decisionEq
  let api := failClosedOccurrenceOrderingAPI mol state fuel
  exact ⟨decision, decisionEq, api.factor _ _ decision occurrenceEq⟩

/-- Rank lookup followed by the production comparator is exactly the lawful unary-key comparison
at the two resolved sorted positions. -/
theorem compare_initial_ranks_eq_comparator
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    {sorted : List Nat}
    (sorted_lt : ∀ position, position ∈ sorted → position < 4)
    {leftRank rightRank : Nat} (left_bound : leftRank < sorted.length)
    (right_bound : rightRank < sorted.length) :
    compareRule6InitialRanks? (mol := mol) state fuel roots sorted leftRank rightRank =
      some (frame.initialPositionComparator sorted[leftRank] sorted[rightRank]) := by
  have left_lt : sorted[leftRank] < 4 :=
    sorted_lt sorted[leftRank] (List.getElem_mem left_bound)
  have right_lt : sorted[rightRank] < 4 :=
    sorted_lt sorted[rightRank] (List.getElem_mem right_bound)
  rcases frame.compare_initial_positions_factors left_lt right_lt with
    ⟨decision, decisionEq, factor⟩
  simp [compareRule6InitialRanks?, List.getElem?_eq_getElem left_bound,
    List.getElem?_eq_getElem right_bound, decisionEq, factor]

/-- Defined composition of two position-key comparisons is their direct endpoint comparison. -/
theorem initialPositionComparator_compose
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    {left middle right : Nat} {composed : Ordering}
    (composition : composeOrdering?
      (frame.initialPositionComparator left middle)
      (frame.initialPositionComparator middle right) = some composed) :
    frame.initialPositionComparator left right = composed := by
  letI := frame.initialPositionComparator_transCmp
  cases leftMiddleEq : frame.initialPositionComparator left middle <;>
    cases middleRightEq : frame.initialPositionComparator middle right <;>
    simp [composeOrdering?, leftMiddleEq, middleRightEq] at composition <;>
    subst composed
  · exact Std.TransCmp.lt_trans leftMiddleEq middleRightEq
  · exact Std.TransCmp.lt_of_lt_of_eq leftMiddleEq middleRightEq
  · exact Std.TransCmp.lt_of_eq_of_lt leftMiddleEq middleRightEq
  · exact Std.TransCmp.eq_trans leftMiddleEq middleRightEq
  · exact Std.TransCmp.gt_of_eq_of_gt leftMiddleEq middleRightEq
  · exact Std.TransCmp.gt_of_gt_of_eq leftMiddleEq middleRightEq
  · exact Std.TransCmp.gt_trans leftMiddleEq middleRightEq

@[simp] theorem initialPositionComparator_self
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (position : Nat) :
    frame.initialPositionComparator position position = Ordering.eq := by
  letI := frame.initialPositionComparator_transCmp
  exact Std.ReflCmp.compare_self

theorem initialPositionComparator_swap
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (left right : Nat) :
    frame.initialPositionComparator right left =
      (frame.initialPositionComparator left right).swap := by
  letI := frame.initialPositionComparator_transCmp
  exact Std.OrientedCmp.eq_swap

/-- A nonincreasing two-edge key chain is tied exactly when both edges are tied; otherwise its
endpoint is strictly senior. -/
theorem initialPositionComparator_chain_two
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    {left middle right : Nat}
    (leftMiddle_not_lt :
      frame.initialPositionComparator left middle ≠ Ordering.lt)
    (middleRight_not_lt :
      frame.initialPositionComparator middle right ≠ Ordering.lt) :
    frame.initialPositionComparator left right =
      if frame.initialPositionComparator left middle = Ordering.eq ∧
          frame.initialPositionComparator middle right = Ordering.eq then
        Ordering.eq else Ordering.gt := by
  cases leftMiddleEq : frame.initialPositionComparator left middle with
  | lt => exact (leftMiddle_not_lt leftMiddleEq).elim
  | eq =>
      cases middleRightEq : frame.initialPositionComparator middle right with
      | lt => exact (middleRight_not_lt middleRightEq).elim
      | eq =>
          simpa [leftMiddleEq, middleRightEq, composeOrdering?] using
            (frame.initialPositionComparator_compose
              (left := left) (middle := middle) (right := right)
              (composed := Ordering.eq) (by simp [leftMiddleEq, middleRightEq, composeOrdering?]))
      | gt =>
          simpa [leftMiddleEq, middleRightEq, composeOrdering?] using
            (frame.initialPositionComparator_compose
              (left := left) (middle := middle) (right := right)
              (composed := Ordering.gt) (by simp [leftMiddleEq, middleRightEq, composeOrdering?]))
  | gt =>
      cases middleRightEq : frame.initialPositionComparator middle right with
      | lt => exact (middleRight_not_lt middleRightEq).elim
      | eq =>
          simpa [leftMiddleEq, middleRightEq, composeOrdering?] using
            (frame.initialPositionComparator_compose
              (left := left) (middle := middle) (right := right)
              (composed := Ordering.gt) (by simp [leftMiddleEq, middleRightEq, composeOrdering?]))
      | gt =>
          simpa [leftMiddleEq, middleRightEq, composeOrdering?] using
            (frame.initialPositionComparator_compose
              (left := left) (middle := middle) (right := right)
              (composed := Ordering.gt) (by simp [leftMiddleEq, middleRightEq, composeOrdering?]))

/-- The literal fail-closed insertion is exactly lawful-key ordered insertion on positions from
the exact four-position frame. -/
theorem insert_initial_eq_orderedInsert
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (candidate : Nat) (candidate_lt : candidate < 4) :
    ∀ input, (∀ position, position ∈ input → position < 4) →
      insertRule6InitialPosition? (mol := mol) state fuel roots candidate input =
        some (input.orderedInsert frame.InitialPositionGE candidate)
  | [], _ => rfl
  | head :: tail, input_lt => by
      have head_lt : head < 4 := input_lt head (by simp)
      have tail_lt : ∀ position, position ∈ tail → position < 4 := by
        intro position member
        exact input_lt position (by simp [member])
      rcases frame.compare_initial_positions_factors candidate_lt head_lt with
        ⟨decision, decisionEq, factor⟩
      by_cases senior : frame.InitialPositionGE candidate head
      · have not_lt : decision.ordering ≠ Ordering.lt := by
          simpa [InitialPositionGE, factor] using senior
        simp [insertRule6InitialPosition?, decisionEq, not_lt, List.orderedInsert, senior]
      · have is_lt : decision.ordering = Ordering.lt := by
          unfold InitialPositionGE at senior
          rw [factor] at senior
          cases orderingEq : decision.ordering <;> simp_all
        have deeper := frame.insert_initial_eq_orderedInsert candidate candidate_lt tail tail_lt
        simp [insertRule6InitialPosition?, decisionEq, is_lt, deeper,
          List.orderedInsert, senior]

/-- The exact production initial sort is ordinary stable insertion sort of the lawful occurrence
key on every list of exact four-frame positions. -/
theorem sort_initial_eq_insertionSort
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots) :
    ∀ input, (∀ position, position ∈ input → position < 4) →
      sortRule6InitialPositions? (mol := mol) state fuel roots input =
        some (input.insertionSort frame.InitialPositionGE)
  | [], _ => rfl
  | position :: positions, input_lt => by
      have position_lt : position < 4 := input_lt position (by simp)
      have positions_lt : ∀ candidate, candidate ∈ positions → candidate < 4 := by
        intro candidate member
        exact input_lt candidate (by simp [member])
      have tailEq := frame.sort_initial_eq_insertionSort positions positions_lt
      have insertEq := frame.insert_initial_eq_orderedInsert position position_lt
        (positions.insertionSort frame.InitialPositionGE) (by
          intro candidate member
          exact positions_lt candidate ((List.mem_insertionSort _).mp member))
      rw [List.insertionSort_cons]
      simp [sortRule6InitialPositions?, tailEq, insertEq]

/-- Every successful exact production initial sort is pairwise nonincreasing in the lawful unary
occurrence key. -/
theorem sort_initial_pairwise
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    {input sorted : List Nat}
    (input_lt : ∀ position, position ∈ input → position < 4)
    (sortedEq : sortRule6InitialPositions? (mol := mol) state fuel roots input = some sorted) :
    sorted.Pairwise frame.InitialPositionGE := by
  have modelEq := frame.sort_initial_eq_insertionSort input input_lt
  have sorted_eq : sorted = input.insertionSort frame.InitialPositionGE :=
    Option.some.inj (sortedEq.symm.trans modelEq)
  subst sorted
  letI := frame.initialPositionGE_total
  letI := frame.initialPositionGE_trans
  exact List.pairwise_insertionSort frame.InitialPositionGE input

/-- The adjacent traversal of a pairwise lawful-key order contains no junior-before-senior
(`lt`) comparison. -/
theorem initial_adjacent_not_lt_of_pairwise
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    {input : List Nat} {adjacent : List (Option Ordering)}
    (input_lt : ∀ position, position ∈ input → position < 4)
    (ordered : input.Pairwise frame.InitialPositionGE)
    (derived : Rule6InitialAdjacentDerivation (mol := mol) state fuel roots input adjacent) :
    some Ordering.lt ∉ adjacent := by
  induction derived with
  | nil => simp
  | singleton position => simp
  | cons left right remaining decision deeper evaluation tail inductionHypothesis =>
      have left_lt : left < 4 := input_lt left (by simp)
      have right_lt : right < 4 := input_lt right (by simp)
      have tail_lt : ∀ position, position ∈ right :: remaining → position < 4 := by
        intro position member
        exact input_lt position (by simp at member ⊢; exact Or.inr member)
      have tailOrdered : (right :: remaining).Pairwise frame.InitialPositionGE := ordered.of_cons
      rcases frame.compare_initial_positions_factors left_lt right_lt with
        ⟨actual, actualEq, factor⟩
      have actual_eq : actual = decision :=
        Option.some.inj (actualEq.symm.trans evaluation.production_eq)
      subst actual
      have decision_not_lt : decision.ordering ≠ Ordering.lt := by
        have headRelation : frame.InitialPositionGE left right :=
          (List.pairwise_cons.mp ordered).1 right (by simp)
        simpa [InitialPositionGE, factor] using headRelation
      have deeper_not_lt := inductionHypothesis tail_lt tailOrdered
      intro member
      simp only [List.mem_cons, Option.some.injEq] at member
      rcases member with headEq | tailMember
      · exact decision_not_lt headEq.symm
      · exact deeper_not_lt tailMember

/-- Structural four-position support supplies an initial order and adjacent comparison list whose
sort is lawful-key ordered and whose adjacency list contains only equality or strict-seniority. -/
theorem initial_four_position_ordered_exists
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots) :
    ∃ sorted adjacent,
      SortRule6InitialDerivation (mol := mol) state fuel roots (List.range 4) sorted ∧
      Rule6InitialAdjacentDerivation (mol := mol) state fuel roots sorted adjacent ∧
      sorted.Pairwise frame.InitialPositionGE ∧
      some Ordering.lt ∉ adjacent := by
  rcases frame.initial_four_position_partition_exists with
    ⟨sorted, adjacent, sortedEq, adjacentEq⟩
  let sorting := sortRule6InitialDerivation_of_production state fuel roots
    (List.range 4) sorted sortedEq
  let comparisons := rule6InitialAdjacentDerivation_of_production state fuel roots
    sorted adjacent adjacentEq
  have range_lt : ∀ position, position ∈ List.range 4 → position < 4 := by
    intro position member
    exact List.mem_range.mp member
  have ordered := frame.sort_initial_pairwise range_lt sortedEq
  have sorted_lt : ∀ position, position ∈ sorted → position < 4 := by
    intro position member
    exact List.mem_range.mp (sorting.perm.mem_iff.mp member)
  exact ⟨sorted, adjacent, sorting, comparisons, ordered,
    frame.initial_adjacent_not_lt_of_pairwise sorted_lt ordered comparisons⟩

/-- The pairwise lawful-key invariant determines all sixteen directed comparisons from the three
adjacent labels. Thus the executable complete-partition check is not an extra success assumption on
a structurally supported four-ligand frame. -/
theorem initial_four_position_complete_partition_exists
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots) :
    ∃ sorted adjacent,
      SortRule6InitialDerivation (mol := mol) state fuel roots (List.range 4) sorted ∧
      Rule6InitialAdjacentDerivation (mol := mol) state fuel roots sorted adjacent ∧
      some Ordering.lt ∉ adjacent ∧
      Nonempty (Rule6InitialCompletePartitionCertificate (mol := mol) state fuel roots
        sorted adjacent) := by
  rcases frame.initial_four_position_ordered_exists with
    ⟨sorted, adjacent, sorting, comparisons, _ordered, adjacent_not_lt⟩
  have sorted_length : sorted.length = 4 := by
    simpa using sorting.perm.length_eq
  rcases List.length_eq_four.mp sorted_length with ⟨a, b, c, d, rfl⟩
  have sorted_lt : ∀ position, position ∈ [a, b, c, d] → position < 4 := by
    intro position member
    exact List.mem_range.mp (sorting.perm.mem_iff.mp member)
  have a_lt : a < 4 := sorted_lt a (by simp)
  have b_lt : b < 4 := sorted_lt b (by simp)
  have c_lt : c < 4 := sorted_lt c (by simp)
  have d_lt : d < 4 := sorted_lt d (by simp)
  rcases frame.compare_initial_positions_factors a_lt b_lt with
    ⟨ab, abEq, abFactor⟩
  rcases frame.compare_initial_positions_factors b_lt c_lt with
    ⟨bc, bcEq, bcFactor⟩
  rcases frame.compare_initial_positions_factors c_lt d_lt with
    ⟨cd, cdEq, cdFactor⟩
  have adjacent_shape : [some ab.ordering, some bc.ordering, some cd.ordering] = adjacent := by
    apply Option.some.inj
    simpa [compareRule6InitialAdjacent?, abEq, bcEq, cdEq] using comparisons.production_eq
  subst adjacent
  have ab_not_lt : ab.ordering ≠ Ordering.lt := by
    intro equation
    apply adjacent_not_lt
    simp [equation]
  have bc_not_lt : bc.ordering ≠ Ordering.lt := by
    intro equation
    apply adjacent_not_lt
    simp [equation]
  have cd_not_lt : cd.ordering ≠ Ordering.lt := by
    intro equation
    apply adjacent_not_lt
    simp [equation]
  have ac := frame.initialPositionComparator_chain_two
    (left := a) (middle := b) (right := c)
    (by simpa [abFactor] using ab_not_lt) (by simpa [bcFactor] using bc_not_lt)
  have bd := frame.initialPositionComparator_chain_two
    (left := b) (middle := c) (right := d)
    (by simpa [bcFactor] using bc_not_lt) (by simpa [cdFactor] using cd_not_lt)
  have ac_not_lt : frame.initialPositionComparator a c ≠ Ordering.lt := by
    rw [ac]
    split <;> simp
  have ad := frame.initialPositionComparator_chain_two
    (left := a) (middle := c) (right := d) ac_not_lt
    (by simpa [cdFactor] using cd_not_lt)
  have ba := frame.initialPositionComparator_swap a b
  have ca := frame.initialPositionComparator_swap a c
  have da := frame.initialPositionComparator_swap a d
  have cb := frame.initialPositionComparator_swap b c
  have db := frame.initialPositionComparator_swap b d
  have dc := frame.initialPositionComparator_swap c d
  have r00 := frame.compare_initial_ranks_eq_comparator sorted_lt
    (leftRank := 0) (rightRank := 0) (by simp) (by simp)
  have r01 := frame.compare_initial_ranks_eq_comparator sorted_lt
    (leftRank := 0) (rightRank := 1) (by simp) (by simp)
  have r02 := frame.compare_initial_ranks_eq_comparator sorted_lt
    (leftRank := 0) (rightRank := 2) (by simp) (by simp)
  have r03 := frame.compare_initial_ranks_eq_comparator sorted_lt
    (leftRank := 0) (rightRank := 3) (by simp) (by simp)
  have r10 := frame.compare_initial_ranks_eq_comparator sorted_lt
    (leftRank := 1) (rightRank := 0) (by simp) (by simp)
  have r11 := frame.compare_initial_ranks_eq_comparator sorted_lt
    (leftRank := 1) (rightRank := 1) (by simp) (by simp)
  have r12 := frame.compare_initial_ranks_eq_comparator sorted_lt
    (leftRank := 1) (rightRank := 2) (by simp) (by simp)
  have r13 := frame.compare_initial_ranks_eq_comparator sorted_lt
    (leftRank := 1) (rightRank := 3) (by simp) (by simp)
  have r20 := frame.compare_initial_ranks_eq_comparator sorted_lt
    (leftRank := 2) (rightRank := 0) (by simp) (by simp)
  have r21 := frame.compare_initial_ranks_eq_comparator sorted_lt
    (leftRank := 2) (rightRank := 1) (by simp) (by simp)
  have r22 := frame.compare_initial_ranks_eq_comparator sorted_lt
    (leftRank := 2) (rightRank := 2) (by simp) (by simp)
  have r23 := frame.compare_initial_ranks_eq_comparator sorted_lt
    (leftRank := 2) (rightRank := 3) (by simp) (by simp)
  have r30 := frame.compare_initial_ranks_eq_comparator sorted_lt
    (leftRank := 3) (rightRank := 0) (by simp) (by simp)
  have r31 := frame.compare_initial_ranks_eq_comparator sorted_lt
    (leftRank := 3) (rightRank := 1) (by simp) (by simp)
  have r32 := frame.compare_initial_ranks_eq_comparator sorted_lt
    (leftRank := 3) (rightRank := 2) (by simp) (by simp)
  have r33 := frame.compare_initial_ranks_eq_comparator sorted_lt
    (leftRank := 3) (rightRank := 3) (by simp) (by simp)
  have directedPairsShape : rule6InitialDirectedRankPairs =
      [(0, 0), (0, 1), (0, 2), (0, 3),
       (1, 0), (1, 1), (1, 2), (1, 3),
       (2, 0), (2, 1), (2, 2), (2, 3),
       (3, 0), (3, 1), (3, 2), (3, 3)] := by
    decide
  have checked : checkRule6InitialDirectedPairs? (mol := mol) state fuel roots
      [a, b, c, d] [some ab.ordering, some bc.ordering, some cd.ordering]
        rule6InitialDirectedRankPairs = some () := by
    rw [directedPairsShape]
    cases abOrder : ab.ordering <;> cases bcOrder : bc.ordering <;>
      cases cdOrder : cd.ordering
    all_goals simp_all [checkRule6InitialDirectedPairs?, checkRule6InitialDirectedPair?,
      rule6ExpectedPartitionOrdering, rule6InitialGroupIndex, rule6GroupOrdering,
      Ordering.swap]
  exact ⟨[a, b, c, d], [some ab.ordering, some bc.ordering, some cd.ordering], sorting,
    comparisons, adjacent_not_lt,
    ⟨rule6InitialDirectedPairsDerivation_of_production state fuel roots [a, b, c, d]
      [some ab.ordering, some bc.ordering, some cd.ordering]
      rule6InitialDirectedRankPairs checked⟩⟩

end DescriptorBranchingRule6CIPFrame

end TetraStereo.OneCenter.ProductionCIPRule6BranchingCompleteness
