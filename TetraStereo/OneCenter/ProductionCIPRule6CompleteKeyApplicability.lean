import TetraStereo.OneCenter.ProductionCIPRule6PromotedRankingLaws
import TetraStereo.OneCenter.Rule6ReferenceFamilySemantics

set_option autoImplicit false

namespace TetraStereo.OneCenter.ProductionCIPRule6BranchingCompleteness

/-!
# Complete-key applicability for the production Rule-6 reference family

The constitutional-orbit condition is sufficient for reference independence, but it is not the
definition of chemical Rule-6 applicability: ligands tied by Rules 1--5 need not be related by a
whole-molecule automorphism.  The chemically relevant finite condition is instead that promotion
of every admitted reference gives four distinct complete Rules-1--6 keys and that the handedness
induced by those keys is independent of the reference choice.

This module states that condition without mentioning the option-valued ranking algorithm and
proves it equivalent to the literal production reference judgment and all-reference checker on a
structurally supported four-ligand frame.
-/

open RawMolecule
open DeclarativeCIP.ProductionOccurrenceRules456
open Rule6ReferenceFamilySemantics

namespace DescriptorBranchingRule6CIPFrame

/-- Pure complete-key order selected for one promoted reference.  This is the reversal of stable
junior-first insertion by the lawful unary Rules-1--6 key; it contains no optional production
call and no `unique` Boolean. -/
def completeKeyRule6Ordering
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (referencePosition : Nat) (positions : List Nat) : List Nat :=
  (frame.foldPromotedPositionOrder referencePosition positions []).reverse

/-- Independent applicability-and-descriptor judgment for one Rule-6 reference.

The supplied four positions must have pairwise distinct complete promoted keys.  The descriptor
is then read from the pure key-sorted order.  In particular, neither production ranking success
nor its `unique` flag occurs in this proposition. -/
def CompleteKeyRule6ReferenceDescriptor
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (positions : List Nat) (parity : TetrahedralInputParity)
    (referencePosition : Nat) (descriptor : RS) : Prop :=
  positions.Pairwise (frame.PromotedPositionNE referencePosition) ∧
    RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven
          (frame.completeKeyRule6Ordering referencePosition positions)) =
      descriptor

/-- Reference-choice-independent complete-key Rule-6 applicability.  The reference family is
nonempty and every admitted reference gives the same descriptor by a strict complete-key order. -/
def CompleteKeyRule6FamilyDescriptor
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (positions : List Nat) (parity : TetrahedralInputParity)
    (references : List Nat) (descriptor : RS) : Prop :=
  references ≠ [] ∧
    ∀ referencePosition, referencePosition ∈ references →
      frame.CompleteKeyRule6ReferenceDescriptor positions parity referencePosition descriptor

/-- A production-strict ranking separates every pair of positions in its returned order. -/
theorem promoted_ranking_positions_pairwise_ne_of_unique
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (referencePosition : Nat) (reference_lt : referencePosition < 4)
    (start : List Nat) (start_lt : ∀ position, position ∈ start → position < 4)
    (ranking : Rule6TrackedRanking)
    (computed : rankOccurrencePositionsThroughRule6Tracked? (mol := mol) state fuel roots
      frame.ligands start referencePosition = some ranking)
    (unique : ranking.unique = true) :
    ranking.positions.Pairwise (frame.PromotedPositionNE referencePosition) := by
  have strict := frame.promoted_ranking_positions_pairwise_gt_of_unique referencePosition
    reference_lt start start_lt ranking computed unique
  exact strict.imp (by
    intro left right greater
    unfold PromotedPositionGT at greater
    unfold PromotedPositionNE
    rw [greater]
    decide)

/-- For a completed four-position ranking, the production uniqueness flag is exactly pairwise
separation of the supplied complete promoted keys. -/
theorem promoted_ranking_unique_iff_input_pairwise_ne
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (referencePosition : Nat) (reference_lt : referencePosition < 4)
    (start : List Nat) (start_lt : ∀ position, position ∈ start → position < 4)
    (ranking : Rule6TrackedRanking)
    (computed : rankOccurrencePositionsThroughRule6Tracked? (mol := mol) state fuel roots
      frame.ligands start referencePosition = some ranking) :
    ranking.unique = true ↔
      start.Pairwise (frame.PromotedPositionNE referencePosition) := by
  constructor
  · intro unique
    have rankingSeparated := frame.promoted_ranking_positions_pairwise_ne_of_unique
      referencePosition reference_lt start start_lt ranking computed unique
    have rankingTrace := promotedRankingTrace_complete state fuel roots frame.ligands start
      referencePosition ranking computed
    exact rankingSeparated.perm rankingTrace.positions_perm (by
      intro left right different
      exact frame.promotedPositionNE_symm referencePosition left right different)
  · intro separated
    exact frame.promoted_ranking_unique_of_pairwise_ne referencePosition reference_lt start
      start_lt separated ranking computed

/-- The pure complete-key order contains exactly the input positions. -/
theorem completeKeyRule6Ordering_perm
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    (referencePosition : Nat) (reference_lt : referencePosition < 4)
    (positions : List Nat) (positions_lt : ∀ position, position ∈ positions → position < 4) :
    (frame.completeKeyRule6Ordering referencePosition positions).Perm positions := by
  rcases frame.promoted_four_position_ranking_exists referencePosition reference_lt positions
      positions_lt with ⟨ranking, computed⟩
  have trace := promotedRankingTrace_complete state fuel roots frame.ligands positions
    referencePosition ranking computed
  have positionsEq := frame.promoted_ranking_positions_eq_model referencePosition reference_lt
    positions positions_lt ranking computed
  simpa [completeKeyRule6Ordering, positionsEq] using trace.positions_perm

/-- Exact one-reference boundary: on a generated four-position carrier, the production descriptor
judgment holds iff the independent complete-key strictness and descriptor judgment holds. -/
theorem productionOccurrenceRule6DescriptorJudgment_iff_completeKey
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    {positions : List Nat}
    (positions_perm : positions.Perm (List.range 4))
    (parity : TetrahedralInputParity) (referencePosition : Nat)
    (reference_lt : referencePosition < 4) (descriptor : RS) :
    ProductionOccurrenceRule6DescriptorJudgment (mol := mol) state fuel roots
        frame.ligands positions parity referencePosition descriptor ↔
      frame.CompleteKeyRule6ReferenceDescriptor positions parity referencePosition descriptor := by
  have positions_lt : ∀ position, position ∈ positions → position < 4 := by
    intro position member
    exact List.mem_range.mp (positions_perm.mem_iff.mp member)
  constructor
  · rintro ⟨ranking, computed, unique, descriptorEq⟩
    have rankingSeparated := frame.promoted_ranking_positions_pairwise_ne_of_unique
      referencePosition reference_lt positions positions_lt ranking computed unique
    have rankingTrace := promotedRankingTrace_complete state fuel roots frame.ligands positions
      referencePosition ranking computed
    have positionsSeparated :
        positions.Pairwise (frame.PromotedPositionNE referencePosition) :=
      rankingSeparated.perm rankingTrace.positions_perm (by
        intro left right different
        exact frame.promotedPositionNE_symm referencePosition left right different)
    have positionsEq := frame.promoted_ranking_positions_eq_model referencePosition reference_lt
      positions positions_lt ranking computed
    refine ⟨positionsSeparated, ?_⟩
    simpa [completeKeyRule6Ordering, positionsEq] using descriptorEq
  · rintro ⟨positionsSeparated, descriptorEq⟩
    rcases frame.promoted_four_position_ranking_exists referencePosition reference_lt positions
        positions_lt with ⟨ranking, computed⟩
    have unique := frame.promoted_ranking_unique_of_pairwise_ne referencePosition reference_lt
      positions positions_lt positionsSeparated ranking computed
    have positionsEq := frame.promoted_ranking_positions_eq_model referencePosition reference_lt
      positions positions_lt ranking computed
    refine ⟨ranking, computed, unique, ?_⟩
    simpa [completeKeyRule6Ordering, positionsEq] using descriptorEq

/-- The independently stated complete-key family descriptor is exactly the existing abstract
common-reference descriptor, once every listed reference is one of the four ligand positions. -/
theorem completeKeyRule6FamilyDescriptor_iff_commonRule6Descriptor
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    {positions : List Nat} (positions_perm : positions.Perm (List.range 4))
    (parity : TetrahedralInputParity) (references : List Nat)
    (reference_lt : ∀ referencePosition, referencePosition ∈ references →
      referencePosition < 4) (descriptor : RS) :
    frame.CompleteKeyRule6FamilyDescriptor positions parity references descriptor ↔
      CommonRule6Descriptor
        (productionOccurrenceRule6RankingBackend (mol := mol) state fuel roots frame.ligands
          positions)
        parity references descriptor := by
  unfold CompleteKeyRule6FamilyDescriptor CommonRule6Descriptor
  apply and_congr Iff.rfl
  constructor
  · intro family referencePosition member
    apply (frame.productionOccurrenceRule6DescriptorJudgment_iff_completeKey positions_perm parity
      referencePosition (reference_lt referencePosition member) descriptor).2
    exact family referencePosition member
  · intro family referencePosition member
    apply (frame.productionOccurrenceRule6DescriptorJudgment_iff_completeKey positions_perm parity
      referencePosition (reference_lt referencePosition member) descriptor).1
    exact family referencePosition member

/-- Exact all-reference boundary with the final descriptor exposed: production returns a first
ranking carrying `descriptor` iff every admitted reference has four separated complete keys and
the pure key orders all carry that same descriptor. -/
theorem rankOccurrenceEquivalentReferences?_success_with_descriptor_iff_completeKeyFamily
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    {positions : List Nat} (positions_perm : positions.Perm (List.range 4))
    (parity : TetrahedralInputParity) (references : List Nat)
    (reference_lt : ∀ referencePosition, referencePosition ∈ references →
      referencePosition < 4) (descriptor : RS) :
    (∃ first,
      rankOccurrenceEquivalentReferences? (mol := mol) state fuel roots parity frame.ligands
          positions references = some first ∧
        RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven first.positions) = descriptor) ↔
      frame.CompleteKeyRule6FamilyDescriptor positions parity references descriptor := by
  let backend := productionOccurrenceRule6RankingBackend (mol := mol) state fuel roots
    frame.ligands positions
  constructor
  · rintro ⟨first, accepted, descriptorEq⟩
    have commonFirst : CommonRule6Descriptor backend parity references descriptor := by
      rcases rankProductionRule6EquivalentReferencesWithBackend?_sound backend parity references
          first (by simpa [rankOccurrenceEquivalentReferences?, backend] using accepted) with
        ⟨certificate⟩
      refine ⟨?_, ?_⟩
      · intro referencesEq
        simpa [referencesEq] using certificate.reference_head
      · intro referencePosition member
        rcases certificate.all_references referencePosition member with
          ⟨ranking, rankingEq, unique, rankingDescriptor⟩
        exact ⟨ranking, rankingEq, unique, rankingDescriptor.trans descriptorEq⟩
    exact (frame.completeKeyRule6FamilyDescriptor_iff_commonRule6Descriptor positions_perm
      parity references reference_lt descriptor).2 commonFirst
  · intro complete
    have common : CommonRule6Descriptor backend parity references descriptor :=
      (frame.completeKeyRule6FamilyDescriptor_iff_commonRule6Descriptor positions_perm parity
        references reference_lt descriptor).1 complete
    rcases
        (rankProductionRule6EquivalentReferencesWithBackend?_success_iff_commonDescriptor
          backend parity references).2 ⟨descriptor, common⟩ with
      ⟨first, accepted⟩
    rcases rankProductionRule6EquivalentReferencesWithBackend?_sound backend parity references
        first accepted with ⟨certificate⟩
    have firstMember : certificate.firstReferencePosition ∈ references := by
      cases references with
      | nil => exact False.elim (complete.1 rfl)
      | cons head tail =>
          have headEq : certificate.firstReferencePosition = head := by
            simpa using certificate.reference_head.symm
          simp [headEq]
    rcases common.2 certificate.firstReferencePosition firstMember with
      ⟨commonRanking, commonRankingEq, _, commonDescriptor⟩
    have firstEq : first = commonRanking :=
      Option.some.inj (certificate.first_ranking.symm.trans commonRankingEq)
    subst commonRanking
    exact ⟨first, by simpa [rankOccurrenceEquivalentReferences?, backend] using accepted,
      commonDescriptor⟩

/-- Specialization to the exact two-group reference enumeration.  This discharges nonemptiness,
position bounds, ranking totality, strictness, and cross-reference descriptor agreement from the
single independent complete-key family predicate. -/
theorem rankOccurrenceEquivalentReferences?_twoGroup_success_with_descriptor_iff_completeKeyFamily
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    {sorted : List Nat} {adjacent : List (Option Ordering)}
    (sorting : SortRule6InitialDerivation (mol := mol) state fuel roots
      (List.range 4) sorted) (parity : TetrahedralInputParity) (descriptor : RS) :
    (∃ first,
      rankOccurrenceEquivalentReferences? (mol := mol) state fuel roots parity frame.ligands
          sorted (rule6EquivalentReferencePositions sorted adjacent) = some first ∧
        RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven first.positions) = descriptor) ↔
      frame.CompleteKeyRule6FamilyDescriptor sorted parity
        (rule6EquivalentReferencePositions sorted adjacent) descriptor := by
  apply frame.rankOccurrenceEquivalentReferences?_success_with_descriptor_iff_completeKeyFamily
    sorting.perm parity (rule6EquivalentReferencePositions sorted adjacent)
  intro referencePosition member
  exact frame.equivalentReference_lt_four sorting adjacent member

/-- Full two-group production composition.  Structural Rule-6 execution, a negative exact
odd-topology decision, the two-group initial partition, and the independent complete-key family
descriptor construct an actual `rule6Result?` value whose emitted descriptor is exactly the
independent descriptor.

No promoted ranking equation, `unique` flag, or cross-reference agreement is assumed: all three
are derived from `CompleteKeyRule6FamilyDescriptor`. -/
theorem rule6Result?_twoGroup_success_of_completeKeyFamily
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    {sorted : List Nat} {adjacent : List (Option Ordering)}
    (sorting : SortRule6InitialDerivation (mol := mol) state fuel roots
      (List.range 4) sorted)
    (comparisons : Rule6InitialAdjacentDerivation (mol := mol) state fuel roots sorted adjacent)
    (adjacent_not_lt : some Ordering.lt ∉ adjacent)
    (partition : Rule6InitialCompletePartitionCertificate (mol := mol) state fuel roots sorted
      adjacent)
    (odd_false : hasOddConstitutionAutomorphismAtCenter mol node.atom frame.ligands
      (fun left right =>
        rule6CompareAt? (mol := mol) state fuel roots left right == some Ordering.eq) =
      some false)
    (group_two : rule6GroupCount adjacent = 2)
    (descriptor : RS)
    (applicable : frame.CompleteKeyRule6FamilyDescriptor sorted frame.parity
      (rule6EquivalentReferencePositions sorted adjacent) descriptor) :
    ∃ result,
      rule6Result? (mol := mol) state fuel node roots = some result ∧
        result.fact.descriptor = descriptor := by
  let references := rule6EquivalentReferencePositions sorted adjacent
  rcases
      (frame.rankOccurrenceEquivalentReferences?_twoGroup_success_with_descriptor_iff_completeKeyFamily
        sorting frame.parity descriptor).2 (by simpa [references] using applicable) with
    ⟨ranking, ranked, rankingDescriptor⟩
  rcases occurrenceEquivalentReferencesTrace_complete state fuel roots frame.parity
      frame.ligands sorted references ranking (by simpa [references] using ranked) with
    ⟨trace⟩
  let carrier : Rule6FrameCertificate (mol := mol) state fuel node roots :=
    frame.toRule6FrameCertificateOfOddFalse sorting comparisons adjacent_not_lt partition
      odd_false
  let result : OccurrenceRule6Result :=
    { fact :=
        { key := canonicalOccurrenceKey node
          atom := node.atom
          descriptor := RawMolecule.descriptorOfParity frame.parity
            (RawMolecule.permutationIsEven ranking.positions)
          uppercase := ranking.pseudoComparisons != 1
          priorityPositions := ranking.positions }
      parity := frame.parity
      ligands := frame.ligands
      roots := roots
      sorted := sorted
      adjacent := adjacent
      groupCount := rule6GroupCount adjacent
      oddTopology? := some false
      carrier := .twoGroup references ranking }
  have derived : Rule6ResultDerivation (mol := mol) state fuel node roots result := by
    apply Rule6ResultDerivation.twoGroup (result := result) carrier
        (by simpa [carrier] using group_two) references (by rfl) ranking
    · simpa [carrier] using trace
    · rfl
  refine ⟨result, derived.production_eq, ?_⟩
  simpa [result] using rankingDescriptor

end DescriptorBranchingRule6CIPFrame

end TetraStereo.OneCenter.ProductionCIPRule6BranchingCompleteness
