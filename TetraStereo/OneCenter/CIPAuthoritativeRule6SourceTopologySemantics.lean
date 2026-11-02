import TetraStereo.OneCenter.CIPAuthoritativeRule6UnannotatedPerception
import TetraStereo.OneCenter.ProductionCIPRule6ReferenceExecutionCompleteness

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter.AuthoritativeCIPRule6Scheduler

open RawMolecule
open DeclarativeCIP
open DeclarativeCIP.ProductionOccurrenceRules456
open ProductionCIPRule6BranchingCompleteness.DescriptorBranchingRule6CIPFrame

/-!
# Independent constitutional-topology semantics for the source Rule-6 frame

The source adapter is unannotated and uses the width-unbounded authoritative comparator, so it
does not inhabit the older descriptor-bearing bounded-frame structure. The finite topology search
it calls is nevertheless independent of those details. This file proves its exact meaning for any
four-position ligand frame and any supplied pre-Rule-6 equivalence relation.
-/

/-- The independent mathematical obstruction searched for by the source Rule-6 topology gate:
an odd permutation of the four ligand positions that preserves the pre-Rule-6 partition and
extends to a constitution-preserving bijection of the complete centered molecular carrier. -/
def SourceHasOddPartitionPreservingConstitutionAutomorphism
    (mol : RawMolecule) (center : Nat) (ligands : List Nat)
    (sameGroup : Nat → Nat → Bool) : Prop :=
  ∃ permutation,
    permutation ∈ List.permutations (List.range 4) ∧
    RawMolecule.permutationIsEven permutation = false ∧
    (List.range 4).all
      (fun index => sameGroup index (permutation.getD index 0)) = true ∧
    mol.HasSeededConstitutionAutomorphism mol.localizedMancudeEdges
      (oddConstitutionVertices mol center ligands)
      (oddConstitutionSeed center ligands permutation)

/-- The production fold over all four-position permutations is extensionally the disjunction of
its status-free per-permutation acceptance predicates. -/
theorem hasOddConstitutionAutomorphismAtCenter_eq_some_any
    (mol : RawMolecule) (center : Nat) (ligands : List Nat)
    (sameGroup : Nat → Nat → Bool)
    (ligandsLength : ligands.length = 4) :
    hasOddConstitutionAutomorphismAtCenter mol center ligands sameGroup =
      some ((List.permutations (List.range 4)).any fun permutation =>
        oddConstitutionPermutationAccepted mol center ligands sameGroup permutation) := by
  let step := oddConstitutionPermutationStep mol center ligands sameGroup
  let accepted := fun permutation =>
    oddConstitutionPermutationAccepted mol center ligands sameGroup permutation
  have stepEq : ∀ status permutation,
      step (some status) permutation = some (status || accepted permutation) := by
    intro status permutation
    cases status with
    | true => simp [step, oddConstitutionPermutationStep]
    | false =>
        have resultSome : (step (some false) permutation).isSome := by
          apply oddConstitutionPermutationStep_isSome
          rfl
        rcases Option.isSome_iff_exists.mp resultSome with ⟨result, resultEq⟩
        have acceptedEq : accepted permutation = result := by
          simp [accepted, oddConstitutionPermutationAccepted, step, resultEq]
        simpa [acceptedEq] using resultEq
  have foldEq : ∀ (permutations : List (List Nat)) status,
      permutations.foldl step (some status) =
        some (status || permutations.any accepted) := by
    intro permutations
    induction permutations with
    | nil => intro status; simp
    | cons permutation remaining inductionHypothesis =>
        intro status
        simp only [List.foldl_cons, stepEq]
        rw [inductionHypothesis]
        simp [Bool.or_assoc]
  have productionEq :
      hasOddConstitutionAutomorphismAtCenter mol center ligands sameGroup =
        (List.permutations (List.range 4)).foldl step (some false) := by
    unfold hasOddConstitutionAutomorphismAtCenter
    rw [KernelPermutationEnumeration.kernelPermutations_eq_permutations]
    rw [ligandsLength]
    have fourBne : (4 != 4) = false := by decide
    rw [fourBne]
    rfl
  rw [productionEq]
  simpa [accepted] using (foldEq (List.permutations (List.range 4)) false)

/-- A positive source topology result is exactly one accepted member of the exhaustive
four-position permutation enumeration. -/
theorem hasOddConstitutionAutomorphismAtCenter_eq_some_true_iff_accepted
    (mol : RawMolecule) (center : Nat) (ligands : List Nat)
    (sameGroup : Nat → Nat → Bool)
    (ligandsLength : ligands.length = 4) :
    hasOddConstitutionAutomorphismAtCenter mol center ligands sameGroup = some true ↔
      ∃ permutation,
        permutation ∈ List.permutations (List.range 4) ∧
        oddConstitutionPermutationAccepted mol center ligands sameGroup permutation = true := by
  rw [hasOddConstitutionAutomorphismAtCenter_eq_some_any
    mol center ligands sameGroup ligandsLength]
  simp

/-- Exact independent semantics of a positive source topology result. -/
theorem hasOddConstitutionAutomorphismAtCenter_eq_some_true_iff
    (mol : RawMolecule) (center : Nat) (ligands : List Nat)
    (sameGroup : Nat → Nat → Bool)
    (ligandsLength : ligands.length = 4)
    (centeredLigandsNodup : (center :: ligands).Nodup) :
    hasOddConstitutionAutomorphismAtCenter mol center ligands sameGroup = some true ↔
      SourceHasOddPartitionPreservingConstitutionAutomorphism
        mol center ligands sameGroup := by
  rw [hasOddConstitutionAutomorphismAtCenter_eq_some_true_iff_accepted
    mol center ligands sameGroup ligandsLength]
  unfold SourceHasOddPartitionPreservingConstitutionAutomorphism
  constructor
  · rintro ⟨permutation, permutationMem, accepted⟩
    let carrier := oddConstitutionPermutationCarrier_of_accepted ligandsLength
      centeredLigandsNodup permutationMem accepted
    have automorphism :=
      (oddConstitutionPermutationAccepted_eq_true_iff carrier).mp accepted
    exact ⟨permutation, permutationMem, carrier.odd,
      carrier.partition_preserving, automorphism⟩
  · rintro ⟨permutation, permutationMem, odd, partitionPreserving, automorphism⟩
    let carrier : OddConstitutionPermutationCarrier mol center ligands sameGroup permutation :=
      oddConstitutionPermutationCarrier_of_automorphism ligandsLength centeredLigandsNodup
        permutationMem odd partitionPreserving automorphism
    exact ⟨permutation, permutationMem,
      (oddConstitutionPermutationAccepted_eq_true_iff carrier).mpr automorphism⟩

/-- On a four-position frame the topology search is total, independently of which equivalence
relation was supplied. -/
theorem hasOddConstitutionAutomorphismAtCenter_exists
    (mol : RawMolecule) (center : Nat) (ligands : List Nat)
    (sameGroup : Nat → Nat → Bool)
    (ligandsLength : ligands.length = 4) :
    ∃ odd, hasOddConstitutionAutomorphismAtCenter mol center ligands sameGroup = some odd := by
  let odd := (List.permutations (List.range 4)).any fun permutation =>
    oddConstitutionPermutationAccepted mol center ligands sameGroup permutation
  exact ⟨odd, hasOddConstitutionAutomorphismAtCenter_eq_some_any
    mol center ligands sameGroup ligandsLength⟩

/-- Exact independent semantics of the negative source topology result. -/
theorem hasOddConstitutionAutomorphismAtCenter_eq_some_false_iff
    (mol : RawMolecule) (center : Nat) (ligands : List Nat)
    (sameGroup : Nat → Nat → Bool)
    (ligandsLength : ligands.length = 4)
    (centeredLigandsNodup : (center :: ligands).Nodup) :
    hasOddConstitutionAutomorphismAtCenter mol center ligands sameGroup = some false ↔
      ¬ SourceHasOddPartitionPreservingConstitutionAutomorphism
        mol center ligands sameGroup := by
  have positive := hasOddConstitutionAutomorphismAtCenter_eq_some_true_iff
    mol center ligands sameGroup ligandsLength centeredLigandsNodup
  constructor
  · intro resultFalse hasOdd
    have resultTrue := positive.mpr hasOdd
    rw [resultFalse] at resultTrue
    contradiction
  · intro noOdd
    rcases hasOddConstitutionAutomorphismAtCenter_exists
      mol center ligands sameGroup ligandsLength with ⟨odd, result⟩
    cases odd with
    | false => exact result
    | true => exact False.elim (noOdd (positive.mp result))

end TetraStereo.OneCenter.AuthoritativeCIPRule6Scheduler
