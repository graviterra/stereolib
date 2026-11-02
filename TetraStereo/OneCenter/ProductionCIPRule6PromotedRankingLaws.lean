import TetraStereo.OneCenter.ProductionCIPRule6PromotedComparatorLaws
import TetraStereo.OneCenter.ProductionCIPRule6ReferenceExecutionCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter.ProductionCIPRule6BranchingCompleteness

/-!
# Lawfulness of the literal promoted Rule-6 ranking

The complete promoted cursor comparator has an opponent-independent lawful key.  This module
pulls that key back to the four ligand positions and proves that the literal option-valued
insertion/fold used by production returns a lawful-key-sorted order.
-/

open RawMolecule
open ProductionCIPRule6BranchingCompleteness
open ProductionCIPRule6PromotedComparatorLaws
open ProductionCIPOccurrenceDescriptorComparatorLaws
open DeclarativeCIP.ProductionOccurrenceRules456

namespace DescriptorBranchingRule6CIPFrame

/-- Total reference lookup used to state the position key.  Below the certified four-position
bound it is exactly the literal production lookup. -/
def promotedReferenceAt
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (referencePosition : Nat) : Nat :=
  frame.ligands.getD referencePosition 0

/-- Complete Rules 1--6 unary-key comparison pulled back to ligand positions. -/
def promotedPositionComparator
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (referencePosition left right : Nat) : Ordering :=
  comparePromotedOccurrenceBranchKeys
    (buildPromotedOccurrenceBranchKey mol state (frame.promotedReferenceAt referencePosition)
      fuel (frame.initialCursorAt left))
    (buildPromotedOccurrenceBranchKey mol state (frame.promotedReferenceAt referencePosition)
      fuel (frame.initialCursorAt right))

/-- Junior-or-equal relation used by the intermediate, pre-reversal insertion accumulator. -/
def PromotedPositionLE
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (referencePosition left right : Nat) : Prop :=
  frame.promotedPositionComparator referencePosition left right ≠ .gt

/-- Senior-or-equal relation exposed by the final reversed ranking. -/
def PromotedPositionGE
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (referencePosition left right : Nat) : Prop :=
  frame.promotedPositionComparator referencePosition left right ≠ .lt

/-- Strict junior-to-senior relation used by a tie-free intermediate accumulator. -/
def PromotedPositionLT
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (referencePosition left right : Nat) : Prop :=
  frame.promotedPositionComparator referencePosition left right = .lt

/-- Strict senior-to-junior relation exposed by a tie-free final ranking. -/
def PromotedPositionGT
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (referencePosition left right : Nat) : Prop :=
  frame.promotedPositionComparator referencePosition left right = .gt

/-- Two positions have distinct complete Rules 1--6 keys. -/
def PromotedPositionNE
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (referencePosition left right : Nat) : Prop :=
  frame.promotedPositionComparator referencePosition left right ≠ .eq

instance promotedPositionLE_decidable
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (referencePosition : Nat) : DecidableRel (frame.PromotedPositionLE referencePosition) := by
  intro left right
  unfold PromotedPositionLE
  infer_instance

theorem promotedPositionComparator_transCmp
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (referencePosition : Nat) :
    Std.TransCmp (frame.promotedPositionComparator referencePosition) := by
  letI := comparePromotedOccurrenceBranchKeys_transCmp
  exact
    { eq_swap := by
        exact Std.OrientedCmp.eq_swap (cmp := comparePromotedOccurrenceBranchKeys)
      isLE_trans := by
        intro left middle right leftMiddle middleRight
        exact Std.TransCmp.isLE_trans (cmp := comparePromotedOccurrenceBranchKeys)
          leftMiddle middleRight }

theorem promotedPositionComparator_swap
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (referencePosition left right : Nat) :
    frame.promotedPositionComparator referencePosition right left =
      (frame.promotedPositionComparator referencePosition left right).swap := by
  letI := frame.promotedPositionComparator_transCmp referencePosition
  exact Std.OrientedCmp.eq_swap

theorem promotedPositionNE_symm
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (referencePosition left right : Nat)
    (different : frame.PromotedPositionNE referencePosition left right) :
    frame.PromotedPositionNE referencePosition right left := by
  unfold PromotedPositionNE at different ⊢
  rw [frame.promotedPositionComparator_swap referencePosition left right]
  cases current : frame.promotedPositionComparator referencePosition left right <;>
    simp_all

theorem promotedPositionLE_total
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (referencePosition : Nat) :
    Std.Total (frame.PromotedPositionLE referencePosition) := by
  constructor
  intro left right
  cases current : frame.promotedPositionComparator referencePosition left right with
  | lt => exact Or.inl (by simp [PromotedPositionLE, current])
  | eq => exact Or.inl (by simp [PromotedPositionLE, current])
  | gt =>
      exact Or.inr (by
        unfold PromotedPositionLE
        rw [frame.promotedPositionComparator_swap referencePosition left right, current]
        simp)

theorem promotedPositionLE_trans
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (referencePosition : Nat) :
    IsTrans Nat (frame.PromotedPositionLE referencePosition) := by
  letI := frame.promotedPositionComparator_transCmp referencePosition
  constructor
  intro left middle right leftMiddle middleRight
  have leftMiddleLE :
      (frame.promotedPositionComparator referencePosition left middle).isLE = true := by
    cases current : frame.promotedPositionComparator referencePosition left middle <;>
      simp_all [PromotedPositionLE]
  have middleRightLE :
      (frame.promotedPositionComparator referencePosition middle right).isLE = true := by
    cases current : frame.promotedPositionComparator referencePosition middle right <;>
      simp_all [PromotedPositionLE]
  have endpointLE := Std.TransCmp.isLE_trans leftMiddleLE middleRightLE
  cases current : frame.promotedPositionComparator referencePosition left right <;>
    simp_all [PromotedPositionLE]

theorem promotedPositionLT_trans
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (referencePosition : Nat) :
    IsTrans Nat (frame.PromotedPositionLT referencePosition) := by
  letI := frame.promotedPositionComparator_transCmp referencePosition
  constructor
  intro left middle right leftMiddle middleRight
  exact Std.TransCmp.lt_trans leftMiddle middleRight

theorem ligands_getElem?_eq_promotedReferenceAt
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (referencePosition : Nat) (reference_lt : referencePosition < 4) :
    frame.ligands[referencePosition]? = some (frame.promotedReferenceAt referencePosition) := by
  have bound : referencePosition < frame.ligands.length := by
    simpa [frame.ligands_length] using reference_lt
  rw [List.getElem?_eq_getElem bound]
  congr 1
  simpa [promotedReferenceAt] using
    (List.getElem_eq_getD (l := frame.ligands) (i := referencePosition) 0)

/-- Every literal position comparison factors through the complete promoted position key. -/
theorem compare_promoted_positions_factors
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    {referencePosition left right : Nat}
    (reference_lt : referencePosition < 4) (left_lt : left < 4) (right_lt : right < 4) :
    ∃ decision,
      comparePositionsThroughRule6? (mol := mol) state fuel roots frame.ligands
          referencePosition left right = some decision ∧
        frame.promotedPositionComparator referencePosition left right = decision.ordering := by
  have referenceEq := frame.ligands_getElem?_eq_promotedReferenceAt
    referencePosition reference_lt
  have leftEq := frame.roots_getElem?_eq_initialCursorAt left left_lt
  have rightEq := frame.roots_getElem?_eq_initialCursorAt right right_lt
  rcases frame.compare_positions_exists referenceEq
      (frame.positionInFrame_of_lt_four left left_lt)
      (frame.positionInFrame_of_lt_four right right_lt) with ⟨decision, decisionEq⟩
  have occurrenceEq :
      compareOccurrenceBranchesThroughRule6At? mol state
          (frame.promotedReferenceAt referencePosition) fuel
          (frame.initialCursorAt left) (frame.initialCursorAt right) = some decision := by
    simpa [comparePositionsThroughRule6?, referenceEq, leftEq, rightEq] using decisionEq
  exact ⟨decision, decisionEq,
    compareOccurrenceBranchesThroughRule6At_ordering_success_factors mol state
      (frame.promotedReferenceAt referencePosition) fuel
      (frame.initialCursorAt left) (frame.initialCursorAt right) decision occurrenceEq⟩

/-- Literal promoted insertion has exactly the lawful ordered-insertion position projection. -/
theorem insert_promoted_positions_eq_orderedInsert
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (referencePosition : Nat) (reference_lt : referencePosition < 4)
    (candidate : Nat) (candidate_lt : candidate < 4) :
    ∀ input, (∀ position, position ∈ input → position < 4) → ∀ output,
      insertOccurrencePositionRule6Tracked? (mol := mol) state fuel roots frame.ligands
          referencePosition candidate input = some output →
        output.1 = input.orderedInsert (frame.PromotedPositionLE referencePosition) candidate
  | [], _, output, computed => by
      simp [insertOccurrencePositionRule6Tracked?] at computed
      subst output
      rfl
  | low :: remaining, input_lt, output, computed => by
      have low_lt : low < 4 := input_lt low (by simp)
      have remaining_lt : ∀ position, position ∈ remaining → position < 4 := by
        intro position member
        exact input_lt position (by simp [member])
      rcases frame.compare_promoted_positions_factors reference_lt low_lt candidate_lt with
        ⟨decision, decisionEq, factor⟩
      cases orderingEq : decision.ordering with
      | lt =>
          cases deeperEq : insertOccurrencePositionRule6Tracked? (mol := mol) state fuel roots
              frame.ligands referencePosition candidate remaining with
          | none => simp [insertOccurrencePositionRule6Tracked?, decisionEq, orderingEq,
              deeperEq] at computed
          | some deeper =>
              have outputEq : output =
                  (low :: deeper.1,
                    (if decision.pseudo then 1 else 0) + deeper.2.1, deeper.2.2) := by
                simpa [insertOccurrencePositionRule6Tracked?, decisionEq, orderingEq,
                  deeperEq] using computed.symm
              subst output
              have relationFalse :
                  ¬ frame.PromotedPositionLE referencePosition candidate low := by
                simp [PromotedPositionLE,
                  frame.promotedPositionComparator_swap referencePosition low candidate,
                  factor, orderingEq]
              rw [List.orderedInsert_cons, if_neg relationFalse]
              exact congrArg (List.cons low)
                (frame.insert_promoted_positions_eq_orderedInsert referencePosition
                  reference_lt candidate candidate_lt remaining remaining_lt deeper deeperEq)
      | eq =>
          have outputEq : output =
              (candidate :: low :: remaining,
                (if decision.pseudo then 1 else 0), false) := by
            simpa [insertOccurrencePositionRule6Tracked?, decisionEq, orderingEq] using
              computed.symm
          subst output
          have relationTrue : frame.PromotedPositionLE referencePosition candidate low := by
            simp [PromotedPositionLE,
              frame.promotedPositionComparator_swap referencePosition low candidate,
              factor, orderingEq]
          simp [List.orderedInsert, relationTrue]
      | gt =>
          have outputEq : output =
              (candidate :: low :: remaining,
                (if decision.pseudo then 1 else 0), true) := by
            simpa [insertOccurrencePositionRule6Tracked?, decisionEq, orderingEq] using
              computed.symm
          subst output
          have relationTrue : frame.PromotedPositionLE referencePosition candidate low := by
            simp [PromotedPositionLE,
              frame.promotedPositionComparator_swap referencePosition low candidate,
              factor, orderingEq]
          simp [List.orderedInsert, relationTrue]

/-- When literal promoted insertion reports no tie, it preserves strict key order. -/
theorem insert_promoted_positions_pairwise_lt_of_unique
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (referencePosition : Nat) (reference_lt : referencePosition < 4)
    (candidate : Nat) (candidate_lt : candidate < 4) :
    ∀ input, (∀ position, position ∈ input → position < 4) →
      input.Pairwise (frame.PromotedPositionLT referencePosition) → ∀ output,
      insertOccurrencePositionRule6Tracked? (mol := mol) state fuel roots frame.ligands
          referencePosition candidate input = some output →
        output.2.2 = true →
        output.1.Pairwise (frame.PromotedPositionLT referencePosition)
  | [], _, _, output, computed, _ => by
      simp [insertOccurrencePositionRule6Tracked?] at computed
      subst output
      simp
  | low :: remaining, input_lt, inputOrdered, output, computed, unique => by
      have low_lt : low < 4 := input_lt low (by simp)
      have remaining_lt : ∀ position, position ∈ remaining → position < 4 := by
        intro position member
        exact input_lt position (by simp [member])
      have lowBeforeRemaining :
          ∀ position ∈ remaining,
            frame.PromotedPositionLT referencePosition low position :=
        (List.pairwise_cons.mp inputOrdered).1
      have remainingOrdered :
          remaining.Pairwise (frame.PromotedPositionLT referencePosition) :=
        (List.pairwise_cons.mp inputOrdered).2
      rcases frame.compare_promoted_positions_factors reference_lt low_lt candidate_lt with
        ⟨decision, decisionEq, factor⟩
      cases orderingEq : decision.ordering with
      | lt =>
          cases deeperEq : insertOccurrencePositionRule6Tracked? (mol := mol) state fuel roots
              frame.ligands referencePosition candidate remaining with
          | none => simp [insertOccurrencePositionRule6Tracked?, decisionEq, orderingEq,
              deeperEq] at computed
          | some deeper =>
              have outputEq : output =
                  (low :: deeper.1,
                    (if decision.pseudo then 1 else 0) + deeper.2.1, deeper.2.2) := by
                simpa [insertOccurrencePositionRule6Tracked?, decisionEq, orderingEq,
                  deeperEq] using computed.symm
              subst output
              have deeperUnique : deeper.2.2 = true := by simpa using unique
              have deeperOrdered := frame.insert_promoted_positions_pairwise_lt_of_unique
                referencePosition reference_lt candidate candidate_lt remaining remaining_lt
                remainingOrdered deeper deeperEq deeperUnique
              apply List.pairwise_cons.mpr
              refine ⟨?_, deeperOrdered⟩
              intro position member
              have deeperProjection := frame.insert_promoted_positions_eq_orderedInsert
                referencePosition reference_lt candidate candidate_lt remaining remaining_lt
                deeper deeperEq
              rw [deeperProjection] at member
              rcases (List.mem_orderedInsert _).mp member with rfl | remainingMember
              · simp [PromotedPositionLT, factor, orderingEq]
              · exact lowBeforeRemaining position remainingMember
      | eq =>
          have outputEq : output =
              (candidate :: low :: remaining,
                (if decision.pseudo then 1 else 0), false) := by
            simpa [insertOccurrencePositionRule6Tracked?, decisionEq, orderingEq] using
              computed.symm
          subst output
          simp at unique
      | gt =>
          have outputEq : output =
              (candidate :: low :: remaining,
                (if decision.pseudo then 1 else 0), true) := by
            simpa [insertOccurrencePositionRule6Tracked?, decisionEq, orderingEq] using
              computed.symm
          subst output
          have candidateBeforeLow :
              frame.PromotedPositionLT referencePosition candidate low := by
            unfold PromotedPositionLT
            rw [frame.promotedPositionComparator_swap referencePosition low candidate,
              factor, orderingEq]
            rfl
          apply List.pairwise_cons.mpr
          refine ⟨?_, inputOrdered⟩
          intro position member
          rcases (List.mem_cons.mp member) with rfl | remainingMember
          · exact candidateBeforeLow
          · exact (frame.promotedPositionLT_trans referencePosition).trans candidate low position
              candidateBeforeLow (lowBeforeRemaining position remainingMember)

/-- Pairwise separation of the incoming keys makes every literal insertion comparison non-equal;
the returned insertion is therefore unique and preserves pairwise key separation. -/
theorem insert_promoted_positions_unique_of_pairwise_ne
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (referencePosition : Nat) (reference_lt : referencePosition < 4)
    (candidate : Nat) (candidate_lt : candidate < 4) :
    ∀ input, (∀ position, position ∈ input → position < 4) →
      (∀ position, position ∈ input →
        frame.PromotedPositionNE referencePosition candidate position) →
      input.Pairwise (frame.PromotedPositionNE referencePosition) → ∀ output,
      insertOccurrencePositionRule6Tracked? (mol := mol) state fuel roots frame.ligands
          referencePosition candidate input = some output →
        output.2.2 = true ∧
        output.1.Pairwise (frame.PromotedPositionNE referencePosition)
  | [], _, _, _, output, computed => by
      simp [insertOccurrencePositionRule6Tracked?] at computed
      subst output
      simp
  | low :: remaining, input_lt, candidateSeparated, inputSeparated, output, computed => by
      have low_lt : low < 4 := input_lt low (by simp)
      have remaining_lt : ∀ position, position ∈ remaining → position < 4 := by
        intro position member
        exact input_lt position (by simp [member])
      have candidateLow : frame.PromotedPositionNE referencePosition candidate low :=
        candidateSeparated low (by simp)
      have candidateRemaining : ∀ position, position ∈ remaining →
          frame.PromotedPositionNE referencePosition candidate position := by
        intro position member
        exact candidateSeparated position (by simp [member])
      have lowBeforeRemaining : ∀ position ∈ remaining,
          frame.PromotedPositionNE referencePosition low position :=
        (List.pairwise_cons.mp inputSeparated).1
      have remainingSeparated :
          remaining.Pairwise (frame.PromotedPositionNE referencePosition) :=
        (List.pairwise_cons.mp inputSeparated).2
      rcases frame.compare_promoted_positions_factors reference_lt low_lt candidate_lt with
        ⟨decision, decisionEq, factor⟩
      cases orderingEq : decision.ordering with
      | lt =>
          cases deeperEq : insertOccurrencePositionRule6Tracked? (mol := mol) state fuel roots
              frame.ligands referencePosition candidate remaining with
          | none => simp [insertOccurrencePositionRule6Tracked?, decisionEq, orderingEq,
              deeperEq] at computed
          | some deeper =>
              have outputEq : output =
                  (low :: deeper.1,
                    (if decision.pseudo then 1 else 0) + deeper.2.1, deeper.2.2) := by
                simpa [insertOccurrencePositionRule6Tracked?, decisionEq, orderingEq,
                  deeperEq] using computed.symm
              subst output
              rcases frame.insert_promoted_positions_unique_of_pairwise_ne referencePosition
                  reference_lt candidate candidate_lt remaining remaining_lt candidateRemaining
                  remainingSeparated deeper deeperEq with ⟨deeperUnique, deeperSeparated⟩
              refine ⟨by simpa using deeperUnique, List.pairwise_cons.mpr ⟨?_, deeperSeparated⟩⟩
              intro position member
              have deeperProjection := frame.insert_promoted_positions_eq_orderedInsert
                referencePosition reference_lt candidate candidate_lt remaining remaining_lt
                deeper deeperEq
              rw [deeperProjection] at member
              rcases (List.mem_orderedInsert _).mp member with rfl | remainingMember
              · simp [PromotedPositionNE, factor, orderingEq]
              · exact lowBeforeRemaining position remainingMember
      | eq =>
          exfalso
          apply candidateLow
          rw [frame.promotedPositionComparator_swap referencePosition low candidate,
            factor, orderingEq]
          rfl
      | gt =>
          have outputEq : output =
              (candidate :: low :: remaining,
                (if decision.pseudo then 1 else 0), true) := by
            simpa [insertOccurrencePositionRule6Tracked?, decisionEq, orderingEq] using
              computed.symm
          subst output
          exact ⟨rfl, List.pairwise_cons.mpr ⟨candidateSeparated, inputSeparated⟩⟩

/-- Pure position model of the literal promoted `foldlM`. -/
def foldPromotedPositionOrder
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (referencePosition : Nat) (candidates accumulator : List Nat) : List Nat :=
  candidates.foldl
    (fun current candidate =>
      current.orderedInsert (frame.PromotedPositionLE referencePosition) candidate)
    accumulator

/-- The complete production fold has exactly the pure lawful-order position projection. -/
theorem fold_promoted_positions_eq_model
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (referencePosition : Nat) (reference_lt : referencePosition < 4) :
    ∀ candidates accumulator,
      (∀ position, position ∈ candidates → position < 4) →
      (∀ position, position ∈ accumulator.1 → position < 4) → ∀ output,
      candidates.foldlM (fun current candidate => do
          let inserted ← insertOccurrencePositionRule6Tracked? (mol := mol) state fuel roots
            frame.ligands referencePosition candidate current.1
          some (inserted.1, current.2.1 + inserted.2.1,
            current.2.2 && inserted.2.2)) accumulator = some output →
        output.1 = frame.foldPromotedPositionOrder referencePosition candidates accumulator.1
  | [], accumulator, _, _, output, computed => by
      simp [List.foldlM] at computed
      subst output
      rfl
  | candidate :: remaining, accumulator, candidates_lt, accumulator_lt, output, computed => by
      have candidate_lt : candidate < 4 := candidates_lt candidate (by simp)
      have remaining_lt : ∀ position, position ∈ remaining → position < 4 := by
        intro position member
        exact candidates_lt position (by simp [member])
      simp only [List.foldlM] at computed
      cases insertedEq : insertOccurrencePositionRule6Tracked? (mol := mol) state fuel roots
          frame.ligands referencePosition candidate accumulator.1 with
      | none => simp [insertedEq] at computed
      | some inserted =>
          have insertedProjection := frame.insert_promoted_positions_eq_orderedInsert
            referencePosition reference_lt candidate candidate_lt accumulator.1 accumulator_lt
            inserted insertedEq
          have inserted_lt : ∀ position, position ∈ inserted.1 → position < 4 := by
            intro position member
            rw [insertedProjection] at member
            rcases (List.mem_orderedInsert _).mp member with rfl | oldMember
            · exact candidate_lt
            · exact accumulator_lt position oldMember
          let next : List Nat × Nat × Bool :=
            (inserted.1, accumulator.2.1 + inserted.2.1,
              accumulator.2.2 && inserted.2.2)
          have tailComputed : remaining.foldlM (fun current candidate => do
                let nextInserted ← insertOccurrencePositionRule6Tracked? (mol := mol) state fuel
                  roots frame.ligands referencePosition candidate current.1
                some (nextInserted.1, current.2.1 + nextInserted.2.1,
                  current.2.2 && nextInserted.2.2)) next = some output := by
            simpa [insertedEq, next] using computed
          have tailProjection := frame.fold_promoted_positions_eq_model referencePosition
            reference_lt remaining next remaining_lt inserted_lt output tailComputed
          change output.1 = frame.foldPromotedPositionOrder referencePosition remaining
            (List.orderedInsert (frame.PromotedPositionLE referencePosition) candidate accumulator.1)
          rw [← insertedProjection]
          exact tailProjection

/-- A successful tracked fold can finish `true` only if the incoming uniqueness flag was
already `true`.  This exposes the monotonicity of the literal conjunction accumulator. -/
theorem fold_promoted_unique_implies_accumulator_unique
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (referencePosition : Nat) : ∀ (candidates : List Nat)
      (accumulator output : List Nat × Nat × Bool),
      candidates.foldlM (fun current candidate => do
          let inserted ← insertOccurrencePositionRule6Tracked? (mol := mol) state fuel roots
            frame.ligands referencePosition candidate current.1
          some (inserted.1, current.2.1 + inserted.2.1,
            current.2.2 && inserted.2.2)) accumulator = some output →
        output.2.2 = true → accumulator.2.2 = true
  | [], accumulator, output, computed, unique => by
      simp [List.foldlM] at computed
      subst output
      exact unique
  | candidate :: remaining, accumulator, output, computed, unique => by
      simp only [List.foldlM] at computed
      cases insertedEq : insertOccurrencePositionRule6Tracked? (mol := mol) state fuel roots
          frame.ligands referencePosition candidate accumulator.1 with
      | none => simp [insertedEq] at computed
      | some inserted =>
          let next : List Nat × Nat × Bool :=
            (inserted.1, accumulator.2.1 + inserted.2.1,
              accumulator.2.2 && inserted.2.2)
          have tailComputed : remaining.foldlM (fun current candidate => do
                let nextInserted ← insertOccurrencePositionRule6Tracked? (mol := mol) state fuel
                  roots frame.ligands referencePosition candidate current.1
                some (nextInserted.1, current.2.1 + nextInserted.2.1,
                  current.2.2 && nextInserted.2.2)) next = some output := by
            simpa [insertedEq, next] using computed
          have nextUnique := frame.fold_promoted_unique_implies_accumulator_unique
            referencePosition remaining next output tailComputed unique
          have bothUnique : accumulator.2.2 = true ∧ inserted.2.2 = true := by
            simpa [next, Bool.and_eq_true] using nextUnique
          exact bothUnique.1

/-- If the complete tracked fold reports uniqueness, its position projection is strictly
ordered by the complete Rules 1--6 key. -/
theorem fold_promoted_positions_pairwise_lt_of_unique
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (referencePosition : Nat) (reference_lt : referencePosition < 4) :
    ∀ (candidates : List Nat) (accumulator : List Nat × Nat × Bool),
      (∀ position, position ∈ candidates → position < 4) →
      (∀ position, position ∈ accumulator.1 → position < 4) →
      accumulator.1.Pairwise (frame.PromotedPositionLT referencePosition) →
      ∀ (output : List Nat × Nat × Bool),
      candidates.foldlM (fun current candidate => do
          let inserted ← insertOccurrencePositionRule6Tracked? (mol := mol) state fuel roots
            frame.ligands referencePosition candidate current.1
          some (inserted.1, current.2.1 + inserted.2.1,
            current.2.2 && inserted.2.2)) accumulator = some output →
        output.2.2 = true →
        output.1.Pairwise (frame.PromotedPositionLT referencePosition)
  | [], accumulator, _, _, accumulatorOrdered, output, computed, _ => by
      simp [List.foldlM] at computed
      subst output
      exact accumulatorOrdered
  | candidate :: remaining, accumulator, candidates_lt, accumulator_lt,
      accumulatorOrdered, output, computed, unique => by
      have candidate_lt : candidate < 4 := candidates_lt candidate (by simp)
      have remaining_lt : ∀ position, position ∈ remaining → position < 4 := by
        intro position member
        exact candidates_lt position (by simp [member])
      simp only [List.foldlM] at computed
      cases insertedEq : insertOccurrencePositionRule6Tracked? (mol := mol) state fuel roots
          frame.ligands referencePosition candidate accumulator.1 with
      | none => simp [insertedEq] at computed
      | some inserted =>
          let next : List Nat × Nat × Bool :=
            (inserted.1, accumulator.2.1 + inserted.2.1,
              accumulator.2.2 && inserted.2.2)
          have tailComputed : remaining.foldlM (fun current candidate => do
                let nextInserted ← insertOccurrencePositionRule6Tracked? (mol := mol) state fuel
                  roots frame.ligands referencePosition candidate current.1
                some (nextInserted.1, current.2.1 + nextInserted.2.1,
                  current.2.2 && nextInserted.2.2)) next = some output := by
            simpa [insertedEq, next] using computed
          have nextUnique := frame.fold_promoted_unique_implies_accumulator_unique
            referencePosition remaining next output tailComputed unique
          have bothUnique : accumulator.2.2 = true ∧ inserted.2.2 = true := by
            simpa [next, Bool.and_eq_true] using nextUnique
          have insertedOrdered := frame.insert_promoted_positions_pairwise_lt_of_unique
            referencePosition reference_lt candidate candidate_lt accumulator.1 accumulator_lt
            accumulatorOrdered inserted insertedEq bothUnique.2
          have insertedProjection := frame.insert_promoted_positions_eq_orderedInsert
            referencePosition reference_lt candidate candidate_lt accumulator.1 accumulator_lt
            inserted insertedEq
          have inserted_lt : ∀ position, position ∈ inserted.1 → position < 4 := by
            intro position member
            rw [insertedProjection] at member
            rcases (List.mem_orderedInsert _).mp member with rfl | oldMember
            · exact candidate_lt
            · exact accumulator_lt position oldMember
          exact frame.fold_promoted_positions_pairwise_lt_of_unique referencePosition reference_lt
            remaining next remaining_lt inserted_lt insertedOrdered output tailComputed unique

/-- Pairwise separation of the unprocessed candidates and the accumulator is an invariant of the
literal fold.  Starting from a `true` flag, it forces the final flag to remain `true`. -/
theorem fold_promoted_positions_unique_of_pairwise_ne
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (referencePosition : Nat) (reference_lt : referencePosition < 4) :
    ∀ (candidates : List Nat) (accumulator : List Nat × Nat × Bool),
      (∀ position, position ∈ candidates → position < 4) →
      (∀ position, position ∈ accumulator.1 → position < 4) →
      candidates.Pairwise (frame.PromotedPositionNE referencePosition) →
      accumulator.1.Pairwise (frame.PromotedPositionNE referencePosition) →
      (∀ candidate, candidate ∈ candidates → ∀ old, old ∈ accumulator.1 →
        frame.PromotedPositionNE referencePosition candidate old) →
      accumulator.2.2 = true → ∀ (output : List Nat × Nat × Bool),
      candidates.foldlM (fun current candidate => do
          let inserted ← insertOccurrencePositionRule6Tracked? (mol := mol) state fuel roots
            frame.ligands referencePosition candidate current.1
          some (inserted.1, current.2.1 + inserted.2.1,
            current.2.2 && inserted.2.2)) accumulator = some output →
        output.2.2 = true ∧
        output.1.Pairwise (frame.PromotedPositionNE referencePosition)
  | [], accumulator, _, _, _, accumulatorSeparated, _, accumulatorUnique, output,
      computed => by
      simp [List.foldlM] at computed
      subst output
      exact ⟨accumulatorUnique, accumulatorSeparated⟩
  | candidate :: remaining, accumulator, candidates_lt, accumulator_lt,
      candidatesSeparated, accumulatorSeparated, crossSeparated, accumulatorUnique, output,
      computed => by
      have candidate_lt : candidate < 4 := candidates_lt candidate (by simp)
      have remaining_lt : ∀ position, position ∈ remaining → position < 4 := by
        intro position member
        exact candidates_lt position (by simp [member])
      have candidateBeforeRemaining : ∀ position ∈ remaining,
          frame.PromotedPositionNE referencePosition candidate position :=
        (List.pairwise_cons.mp candidatesSeparated).1
      have remainingSeparated :
          remaining.Pairwise (frame.PromotedPositionNE referencePosition) :=
        (List.pairwise_cons.mp candidatesSeparated).2
      have candidateFromAccumulator : ∀ position, position ∈ accumulator.1 →
          frame.PromotedPositionNE referencePosition candidate position := by
        intro position member
        exact crossSeparated candidate (by simp) position member
      simp only [List.foldlM] at computed
      cases insertedEq : insertOccurrencePositionRule6Tracked? (mol := mol) state fuel roots
          frame.ligands referencePosition candidate accumulator.1 with
      | none => simp [insertedEq] at computed
      | some inserted =>
          rcases frame.insert_promoted_positions_unique_of_pairwise_ne referencePosition
              reference_lt candidate candidate_lt accumulator.1 accumulator_lt
              candidateFromAccumulator accumulatorSeparated inserted insertedEq with
            ⟨insertedUnique, insertedSeparated⟩
          have insertedProjection := frame.insert_promoted_positions_eq_orderedInsert
            referencePosition reference_lt candidate candidate_lt accumulator.1 accumulator_lt
            inserted insertedEq
          have inserted_lt : ∀ position, position ∈ inserted.1 → position < 4 := by
            intro position member
            rw [insertedProjection] at member
            rcases (List.mem_orderedInsert _).mp member with rfl | oldMember
            · exact candidate_lt
            · exact accumulator_lt position oldMember
          have remainingCrossInserted : ∀ remainingPosition,
              remainingPosition ∈ remaining → ∀ insertedPosition,
              insertedPosition ∈ inserted.1 →
                frame.PromotedPositionNE referencePosition remainingPosition insertedPosition := by
            intro remainingPosition remainingMember insertedPosition insertedMember
            rw [insertedProjection] at insertedMember
            rcases (List.mem_orderedInsert _).mp insertedMember with rfl | oldMember
            · exact frame.promotedPositionNE_symm referencePosition _ _
                (candidateBeforeRemaining remainingPosition remainingMember)
            · exact crossSeparated remainingPosition (by simp [remainingMember])
                insertedPosition oldMember
          let next : List Nat × Nat × Bool :=
            (inserted.1, accumulator.2.1 + inserted.2.1,
              accumulator.2.2 && inserted.2.2)
          have nextUnique : next.2.2 = true := by
            simp [next, accumulatorUnique, insertedUnique]
          have tailComputed : remaining.foldlM (fun current candidate => do
                let nextInserted ← insertOccurrencePositionRule6Tracked? (mol := mol) state fuel
                  roots frame.ligands referencePosition candidate current.1
                some (nextInserted.1, current.2.1 + nextInserted.2.1,
                  current.2.2 && nextInserted.2.2)) next = some output := by
            simpa [insertedEq, next] using computed
          exact frame.fold_promoted_positions_unique_of_pairwise_ne referencePosition reference_lt
            remaining next remaining_lt inserted_lt remainingSeparated insertedSeparated
            remainingCrossInserted nextUnique output tailComputed

/-- The literal promoted ranking's returned order is the reversal of the pure lawful fold. -/
theorem promoted_ranking_positions_eq_model
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (referencePosition : Nat) (reference_lt : referencePosition < 4)
    (start : List Nat) (start_lt : ∀ position, position ∈ start → position < 4)
    (ranking : Rule6TrackedRanking)
    (computed : rankOccurrencePositionsThroughRule6Tracked? (mol := mol) state fuel roots
      frame.ligands start referencePosition = some ranking) :
    ranking.positions =
      (frame.foldPromotedPositionOrder referencePosition start []).reverse := by
  unfold rankOccurrencePositionsThroughRule6Tracked? at computed
  cases trackedEq : start.foldlM (fun current candidate => do
      let inserted ← insertOccurrencePositionRule6Tracked? (mol := mol) state fuel roots
        frame.ligands referencePosition candidate current.1
      some (inserted.1, current.2.1 + inserted.2.1,
        current.2.2 && inserted.2.2)) ([], 0, true) with
  | none =>
      rw [trackedEq] at computed
      simp at computed
  | some tracked =>
      rw [trackedEq] at computed
      have rankingEq : ranking =
          { positions := tracked.1.reverse
            pseudoComparisons := tracked.2.1
            unique := tracked.2.2 } := by
        simpa using computed.symm
      subst ranking
      have projection := frame.fold_promoted_positions_eq_model referencePosition reference_lt
        start ([], 0, true) start_lt (by simp) tracked trackedEq
      exact congrArg List.reverse projection

/-- Pairwise distinct complete keys in the supplied position list force the literal production
ranking to report `unique = true`. -/
theorem promoted_ranking_unique_of_pairwise_ne
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (referencePosition : Nat) (reference_lt : referencePosition < 4)
    (start : List Nat) (start_lt : ∀ position, position ∈ start → position < 4)
    (startSeparated : start.Pairwise (frame.PromotedPositionNE referencePosition))
    (ranking : Rule6TrackedRanking)
    (computed : rankOccurrencePositionsThroughRule6Tracked? (mol := mol) state fuel roots
      frame.ligands start referencePosition = some ranking) :
    ranking.unique = true := by
  unfold rankOccurrencePositionsThroughRule6Tracked? at computed
  cases trackedEq : start.foldlM (fun current candidate => do
      let inserted ← insertOccurrencePositionRule6Tracked? (mol := mol) state fuel roots
        frame.ligands referencePosition candidate current.1
      some (inserted.1, current.2.1 + inserted.2.1,
        current.2.2 && inserted.2.2)) ([], 0, true) with
  | none =>
      rw [trackedEq] at computed
      simp at computed
  | some tracked =>
      rw [trackedEq] at computed
      have rankingEq : ranking =
          { positions := tracked.1.reverse
            pseudoComparisons := tracked.2.1
            unique := tracked.2.2 } := by
        simpa using computed.symm
      have folded := frame.fold_promoted_positions_unique_of_pairwise_ne referencePosition
        reference_lt start ([], 0, true) start_lt (by simp) startSeparated (by simp) (by simp)
        (by simp) tracked trackedEq
      rw [rankingEq]
      exact folded.1

theorem foldPromotedPositionOrder_pairwise
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (referencePosition : Nat) : ∀ candidates accumulator,
    accumulator.Pairwise (frame.PromotedPositionLE referencePosition) →
      (frame.foldPromotedPositionOrder referencePosition candidates accumulator).Pairwise
        (frame.PromotedPositionLE referencePosition)
  | [], accumulator, ordered => ordered
  | candidate :: remaining, accumulator, ordered => by
      letI := frame.promotedPositionLE_total referencePosition
      letI := frame.promotedPositionLE_trans referencePosition
      exact frame.foldPromotedPositionOrder_pairwise referencePosition remaining
        (accumulator.orderedInsert (frame.PromotedPositionLE referencePosition) candidate)
        (ordered.orderedInsert candidate accumulator)

/-- Every successful literal promoted ranking is pairwise nonincreasing in the complete lawful
Rules 1--6 key. -/
theorem promoted_ranking_positions_pairwise
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (referencePosition : Nat) (reference_lt : referencePosition < 4)
    (start : List Nat) (start_lt : ∀ position, position ∈ start → position < 4)
    (ranking : Rule6TrackedRanking)
    (computed : rankOccurrencePositionsThroughRule6Tracked? (mol := mol) state fuel roots
      frame.ligands start referencePosition = some ranking) :
    ranking.positions.Pairwise (frame.PromotedPositionGE referencePosition) := by
  rw [frame.promoted_ranking_positions_eq_model referencePosition reference_lt start start_lt
    ranking computed]
  rw [List.pairwise_reverse]
  have ordered := frame.foldPromotedPositionOrder_pairwise referencePosition start [] (by simp)
  exact ordered.imp (by
    intro left right relation
    unfold PromotedPositionLE at relation
    unfold PromotedPositionGE
    rw [frame.promotedPositionComparator_swap referencePosition left right]
    cases current : frame.promotedPositionComparator referencePosition left right <;>
      simp_all)

/-- The production `unique` flag has a kernel-checked semantic consequence: whenever it is
`true`, every earlier position in the returned ranking has a strictly senior complete Rules
1--6 key than every later position. -/
theorem promoted_ranking_positions_pairwise_gt_of_unique
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (referencePosition : Nat) (reference_lt : referencePosition < 4)
    (start : List Nat) (start_lt : ∀ position, position ∈ start → position < 4)
    (ranking : Rule6TrackedRanking)
    (computed : rankOccurrencePositionsThroughRule6Tracked? (mol := mol) state fuel roots
      frame.ligands start referencePosition = some ranking)
    (unique : ranking.unique = true) :
    ranking.positions.Pairwise (frame.PromotedPositionGT referencePosition) := by
  unfold rankOccurrencePositionsThroughRule6Tracked? at computed
  cases trackedEq : start.foldlM (fun current candidate => do
      let inserted ← insertOccurrencePositionRule6Tracked? (mol := mol) state fuel roots
        frame.ligands referencePosition candidate current.1
      some (inserted.1, current.2.1 + inserted.2.1,
        current.2.2 && inserted.2.2)) ([], 0, true) with
  | none =>
      rw [trackedEq] at computed
      simp at computed
  | some tracked =>
      rw [trackedEq] at computed
      have rankingEq : ranking =
          { positions := tracked.1.reverse
            pseudoComparisons := tracked.2.1
            unique := tracked.2.2 } := by
        simpa using computed.symm
      have trackedUnique : tracked.2.2 = true := by
        rw [rankingEq] at unique
        exact unique
      subst ranking
      rw [List.pairwise_reverse]
      have ordered := frame.fold_promoted_positions_pairwise_lt_of_unique
        referencePosition reference_lt start ([], 0, true) start_lt (by simp) (by simp)
        tracked trackedEq trackedUnique
      exact ordered.imp (by
        intro left right relation
        unfold PromotedPositionLT at relation
        unfold PromotedPositionGT
        rw [frame.promotedPositionComparator_swap referencePosition left right, relation]
        rfl)

/-- Exact algorithmic sufficiency of complete-key separation: distinct input keys force a
successful unique flag and a strictly senior-to-junior final ranking. -/
theorem promoted_ranking_unique_and_pairwise_gt_of_pairwise_ne
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (referencePosition : Nat) (reference_lt : referencePosition < 4)
    (start : List Nat) (start_lt : ∀ position, position ∈ start → position < 4)
    (startSeparated : start.Pairwise (frame.PromotedPositionNE referencePosition))
    (ranking : Rule6TrackedRanking)
    (computed : rankOccurrencePositionsThroughRule6Tracked? (mol := mol) state fuel roots
      frame.ligands start referencePosition = some ranking) :
    ranking.unique = true ∧
      ranking.positions.Pairwise (frame.PromotedPositionGT referencePosition) := by
  have unique := frame.promoted_ranking_unique_of_pairwise_ne referencePosition reference_lt start
    start_lt startSeparated ranking computed
  exact ⟨unique,
    frame.promoted_ranking_positions_pairwise_gt_of_unique referencePosition reference_lt start
      start_lt ranking computed unique⟩

/-- A descriptor accepted by the occurrence Rule-6 backend is witnessed by a ranking that is
strictly ordered by the complete lawful Rules 1--6 key, and the descriptor is exactly the parity
read from that ranking.  Thus the descriptor judgment no longer relies on an uninterpreted
`unique` flag. -/
theorem productionOccurrenceRule6DescriptorJudgment_has_strict_key_ranking
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (start : List Nat) (start_lt : ∀ position, position ∈ start → position < 4)
    (parity : TetrahedralInputParity) (referencePosition : Nat)
    (reference_lt : referencePosition < 4) (descriptor : RS)
    (judgment : ProductionOccurrenceRule6DescriptorJudgment (mol := mol) state fuel roots
      frame.ligands start parity referencePosition descriptor) :
    ∃ ranking,
      rankOccurrencePositionsThroughRule6Tracked? (mol := mol) state fuel roots frame.ligands
          start referencePosition = some ranking ∧
        ranking.positions.Pairwise (frame.PromotedPositionGT referencePosition) ∧
        RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven ranking.positions) = descriptor := by
  rcases judgment with ⟨ranking, accepted, unique, descriptorEq⟩
  exact ⟨ranking, accepted,
    frame.promoted_ranking_positions_pairwise_gt_of_unique referencePosition reference_lt start
      start_lt ranking accepted unique,
    descriptorEq⟩

end DescriptorBranchingRule6CIPFrame

end TetraStereo.OneCenter.ProductionCIPRule6BranchingCompleteness
