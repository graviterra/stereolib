import TetraStereo.OneCenter.ProductionCIPRule6ThreeGroupCompleteKeyApplicability
import TetraStereo.OneCenter.ProductionCIPRule6FourWayCompleteKeyApplicability

set_option autoImplicit false

namespace TetraStereo.OneCenter.ProductionCIPRule6BranchingCompleteness

open RawMolecule
open DeclarativeCIP.ProductionOccurrenceRules456

namespace DescriptorBranchingRule6CIPFrame

/-!
# Exact complete-key semantics of final production Rule-6 results

The branch modules construct successful production results from pure complete-key applicability.
This module proves the converse at the final `rule6Result?` boundary.  Thus applicability,
descriptor value, and production success agree in both directions for every admitted carrier
shape.
-/

/-- Determinism aligns the data in any successful production frame certificate with the same
literal initial sort and adjacency derivations supplied for a descriptor-bearing branching frame. -/
theorem Rule6FrameCertificate.align_completeKeyFrame
    {mol : RawMolecule} {state : OccurrenceAuxState} {fuel : Nat}
    {node : RawMolecule.CanonicalBranchNode} {roots : List CanonicalRerootCursor}
    (carrier : Rule6FrameCertificate (mol := mol) state fuel node roots)
    (frame : DescriptorBranchingRule6CIPFrame mol state fuel node roots)
    {sorted : List Nat} {adjacent : List (Option Ordering)}
    (sorting : SortRule6InitialDerivation (mol := mol) state fuel roots
      (List.range 4) sorted)
    (comparisons : Rule6InitialAdjacentDerivation (mol := mol) state fuel roots sorted adjacent) :
    carrier.sorted = sorted ∧ carrier.adjacent = adjacent ∧
      carrier.ligands = frame.ligands ∧ carrier.parity = frame.parity := by
  have sortedEq : carrier.sorted = sorted :=
    Option.some.inj (carrier.ranking.production_eq.symm.trans sorting.production_eq)
  have adjacentEq : carrier.adjacent = adjacent := by
    have carrierComparisons := carrier.comparisons.production_eq
    rw [sortedEq] at carrierComparisons
    exact Option.some.inj (carrierComparisons.symm.trans comparisons.production_eq)
  have ligandsEq : carrier.ligands = frame.ligands :=
    carrier.ligands_eq.trans frame.ligands_eq.symm
  have specEq : carrier.spec = frame.spec :=
    Option.some.inj (carrier.atom_spec.symm.trans frame.atom_spec)
  have parityEq : carrier.parity = frame.parity := by
    have carrierTetrahedral := carrier.tetrahedral
    rw [specEq] at carrierTetrahedral
    exact Option.some.inj (carrierTetrahedral.symm.trans frame.tetrahedral)
  exact ⟨sortedEq, adjacentEq, ligandsEq, parityEq⟩

/-- Exact final two-group boundary.  Under the common structural frame and topology premises,
production emits `descriptor` exactly when the pure complete-key reference family has that common
strict descriptor. -/
theorem rule6Result?_twoGroup_success_with_descriptor_iff_completeKeyFamily
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
    (descriptor : RS) :
    (∃ result,
      rule6Result? (mol := mol) state fuel node roots = some result ∧
        result.fact.descriptor = descriptor) ↔
      frame.CompleteKeyRule6FamilyDescriptor sorted frame.parity
        (rule6EquivalentReferencePositions sorted adjacent) descriptor := by
  constructor
  · rintro ⟨result, computed, resultDescriptor⟩
    have derived := rule6ResultDerivation_of_production computed
    cases derived with
    | fourWay carrier carrierGroup agreement trace resultEq =>
        rcases Rule6FrameCertificate.align_completeKeyFrame carrier frame sorting comparisons with
          ⟨_, adjacentEq, _, _⟩
        have impossible : (1 : Nat) = 2 := calc
          1 = carrier.groupCount := carrierGroup.symm
          _ = rule6GroupCount carrier.adjacent := carrier.groupCount_eq
          _ = rule6GroupCount adjacent := by rw [adjacentEq]
          _ = 2 := group_two
        omega
    | twoGroup carrier carrierGroup references referencesEq ranking trace resultEq =>
        rcases Rule6FrameCertificate.align_completeKeyFrame carrier frame sorting comparisons with
          ⟨sortedEq, adjacentEq, ligandsEq, parityEq⟩
        have ranked :
            rankOccurrenceEquivalentReferences? (mol := mol) state fuel roots frame.parity
                frame.ligands sorted (rule6EquivalentReferencePositions sorted adjacent) =
              some ranking := by
          simpa [referencesEq, sortedEq, adjacentEq, ligandsEq, parityEq] using trace.sound
        have rankingDescriptor :
            RawMolecule.descriptorOfParity frame.parity
                (RawMolecule.permutationIsEven ranking.positions) = descriptor := by
          rw [resultEq] at resultDescriptor
          simpa [parityEq] using resultDescriptor
        exact
          (frame.rankOccurrenceEquivalentReferences?_twoGroup_success_with_descriptor_iff_completeKeyFamily
            sorting frame.parity descriptor).1 ⟨ranking, ranked, rankingDescriptor⟩
    | threeGroup carrier carrierGroup reference referenceEq referenceRoot referenceRootEq
        middleTie localReference ranking trace resultEq =>
        rcases Rule6FrameCertificate.align_completeKeyFrame carrier frame sorting comparisons with
          ⟨_, adjacentEq, _, _⟩
        have impossible : (3 : Nat) = 2 := calc
          3 = carrier.groupCount := carrierGroup.symm
          _ = rule6GroupCount carrier.adjacent := carrier.groupCount_eq
          _ = rule6GroupCount adjacent := by rw [adjacentEq]
          _ = 2 := group_two
        omega
  · intro applicable
    exact frame.rule6Result?_twoGroup_success_of_completeKeyFamily sorting comparisons
      adjacent_not_lt partition odd_false group_two descriptor applicable

/-- Exact final three-group boundary, including its prescribed descriptor reversal. -/
theorem rule6Result?_threeGroup_success_with_descriptor_iff_completeKey
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
    (group_three : rule6GroupCount adjacent = 3)
    (referencePosition : Nat) (reference_position : sorted[1]? = some referencePosition)
    (referenceRoot : CanonicalRerootCursor)
    (reference_root : roots[referencePosition]? = some referenceRoot)
    (middle_tie : adjacent[1]?.getD none = some Ordering.eq)
    (local_reference : occurrenceBranchHasLocalReference (mol := mol) state fuel
      [referenceRoot] = true)
    (descriptor : RS) :
    (∃ result,
      rule6Result? (mol := mol) state fuel node roots = some result ∧
        result.fact.descriptor = descriptor) ↔
      frame.CompleteKeyRule6ThreeGroupDescriptor sorted frame.parity referencePosition
        descriptor := by
  constructor
  · rintro ⟨result, computed, resultDescriptor⟩
    have derived := rule6ResultDerivation_of_production computed
    cases derived with
    | fourWay carrier carrierGroup agreement trace resultEq =>
        rcases Rule6FrameCertificate.align_completeKeyFrame carrier frame sorting comparisons with
          ⟨_, adjacentEq, _, _⟩
        have impossible : (1 : Nat) = 3 := calc
          1 = carrier.groupCount := carrierGroup.symm
          _ = rule6GroupCount carrier.adjacent := carrier.groupCount_eq
          _ = rule6GroupCount adjacent := by rw [adjacentEq]
          _ = 3 := group_three
        omega
    | twoGroup carrier carrierGroup references referencesEq ranking trace resultEq =>
        rcases Rule6FrameCertificate.align_completeKeyFrame carrier frame sorting comparisons with
          ⟨_, adjacentEq, _, _⟩
        have impossible : (2 : Nat) = 3 := calc
          2 = carrier.groupCount := carrierGroup.symm
          _ = rule6GroupCount carrier.adjacent := carrier.groupCount_eq
          _ = rule6GroupCount adjacent := by rw [adjacentEq]
          _ = 3 := group_three
        omega
    | threeGroup carrier carrierGroup reference referenceEq referenceRoot' referenceRootEq
        middleTie localReference ranking trace resultEq =>
        rcases Rule6FrameCertificate.align_completeKeyFrame carrier frame sorting comparisons with
          ⟨sortedEq, adjacentEq, ligandsEq, parityEq⟩
        have referenceEq' : reference = referencePosition := calc
          reference = carrier.sorted[1]?.getD 0 := referenceEq
          _ = sorted[1]?.getD 0 := by rw [sortedEq]
          _ = referencePosition := by simp [reference_position]
        have ranked :
            rankOccurrenceEquivalentReferences? (mol := mol) state fuel roots frame.parity
                frame.ligands sorted [referencePosition] = some ranking := by
          simpa [sortedEq, ligandsEq, parityEq, referenceEq'] using trace.sound
        have rankingDescriptor :
            RS.swap (RawMolecule.descriptorOfParity frame.parity
              (RawMolecule.permutationIsEven ranking.positions)) = descriptor := by
          rw [resultEq] at resultDescriptor
          simpa [parityEq] using resultDescriptor
        exact
          (frame.rankOccurrenceEquivalentReferences?_singleton_success_with_descriptor_iff_completeKey
            sorting.perm frame.parity referencePosition
              (List.mem_range.mp (sorting.perm.mem_iff.mp
                (List.mem_iff_getElem?.2 ⟨1, reference_position⟩))) descriptor).1
            ⟨ranking, ranked, rankingDescriptor⟩
  · intro applicable
    exact frame.rule6Result?_threeGroup_success_of_completeKey sorting comparisons adjacent_not_lt
      partition odd_false group_three referencePosition reference_position referenceRoot
      reference_root middle_tie local_reference descriptor applicable

/-- Exact final four-way boundary, including the non-strict quotient-reversal case. -/
theorem rule6Result?_fourWay_success_with_descriptor_iff_completeKey
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
    (group_one : rule6GroupCount adjacent = 1)
    (descriptor : RS) :
    (∃ result,
      rule6Result? (mol := mol) state fuel node roots = some result ∧
        result.fact.descriptor = descriptor) ↔
      Nonempty (frame.CompleteKeyRule6FourWayDescriptor sorted frame.parity descriptor) := by
  constructor
  · rintro ⟨result, computed, resultDescriptor⟩
    have derived := rule6ResultDerivation_of_production computed
    cases derived with
    | fourWay carrier carrierGroup agreement trace resultEq =>
        rcases Rule6FrameCertificate.align_completeKeyFrame carrier frame sorting comparisons with
          ⟨sortedEq, _, ligandsEq, parityEq⟩
        have ranked :
            rankOccurrenceFourWayReferences? (mol := mol) state fuel roots frame.parity
                frame.ligands sorted = some agreement := by
          simpa [sortedEq, ligandsEq, parityEq] using trace.sound
        have agreementDescriptor : agreement.descriptor = descriptor := by
          rw [resultEq] at resultDescriptor
          simpa using resultDescriptor
        exact
          (frame.rankOccurrenceFourWayReferences?_success_with_descriptor_iff_completeKey
            sorting frame.parity descriptor).1 ⟨agreement, ranked, agreementDescriptor⟩
    | twoGroup carrier carrierGroup references referencesEq ranking trace resultEq =>
        rcases Rule6FrameCertificate.align_completeKeyFrame carrier frame sorting comparisons with
          ⟨_, adjacentEq, _, _⟩
        have impossible : (2 : Nat) = 1 := calc
          2 = carrier.groupCount := carrierGroup.symm
          _ = rule6GroupCount carrier.adjacent := carrier.groupCount_eq
          _ = rule6GroupCount adjacent := by rw [adjacentEq]
          _ = 1 := group_one
        omega
    | threeGroup carrier carrierGroup reference referenceEq referenceRoot referenceRootEq
        middleTie localReference ranking trace resultEq =>
        rcases Rule6FrameCertificate.align_completeKeyFrame carrier frame sorting comparisons with
          ⟨_, adjacentEq, _, _⟩
        have impossible : (3 : Nat) = 1 := calc
          3 = carrier.groupCount := carrierGroup.symm
          _ = rule6GroupCount carrier.adjacent := carrier.groupCount_eq
          _ = rule6GroupCount adjacent := by rw [adjacentEq]
          _ = 1 := group_one
        omega
  · rintro ⟨applicable⟩
    exact frame.rule6Result?_fourWay_success_of_completeKey sorting comparisons adjacent_not_lt
      partition odd_false group_one descriptor applicable

end DescriptorBranchingRule6CIPFrame

end TetraStereo.OneCenter.ProductionCIPRule6BranchingCompleteness
