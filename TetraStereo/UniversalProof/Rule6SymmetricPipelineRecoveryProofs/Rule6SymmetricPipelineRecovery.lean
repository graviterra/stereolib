import TetraStereo.OneCenter.CIPAuthoritativeRule6SourceTopologySemantics
import TetraStereo.OneCenter.CIPAuthoritativeRule6UnannotatedPerception

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace TetraStereo.UniversalProof.Rule6SymmetricPipelineRecoveryProofs.Rule6SymmetricPipelineRecovery

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPRule6Scheduler
open TetraStereo.OneCenter.ProductionCIPRule6BranchingCompleteness.DescriptorBranchingRule6CIPFrame
















def molecule : RawMolecule where
  atoms := [AtomSpec.aliphatic .C, AtomSpec.aliphatic .F, AtomSpec.aliphatic .F,
    AtomSpec.aliphatic .Cl, AtomSpec.aliphatic .Br]
  bonds := [⟨0, 1, .single⟩, ⟨0, 2, .single⟩, ⟨0, 3, .single⟩, ⟨0, 4, .single⟩]

def normalized : ChemistryNormalizationResult := normalizeRawMolecule molecule

theorem actual_normalization : normalized.parsed = molecule := rfl

theorem actual_admissible : molecule.Admissible :=
  molecule.admissible?_eq_true_iff.mp (by decide +kernel)

theorem actual_valence : molecule.ValenceOK :=
  molecule.valenceOK?_eq_true_iff.mp (by decide +kernel)

theorem actual_written_exact : molecule.WrittenNeighborExact :=
  molecule.writtenNeighborExact?_eq_true_iff.mp (by decide +kernel)

theorem actual_unannotated : ∀ spec ∈ molecule.atoms, spec.tetrahedral? = none := by
  decide +kernel

abbrev ligands : List Nat := molecule.ligandsWithLonePair 0

theorem actual_ligands : ligands = [1, 2, 3, 4] := by decide +kernel

theorem actual_ligands_length : ligands.length = 4 := by decide +kernel

theorem actual_centered_ligands_nodup : (0 :: ligands).Nodup := by decide +kernel

def ligandCursor (atom : Nat) : CanonicalRerootCursor :=
  { node := canonicalRoot 0 atom, previous? := some (canonicalCenterRoot 0) }

abbrev roots : List CanonicalRerootCursor := authoritativeSourceRule6LigandCursors molecule 0

theorem actual_roots : roots =
    [ligandCursor 1, ligandCursor 2, ligandCursor 3, ligandCursor 4] := by decide +kernel

/-- Actual two-level collection, before any annotation filtering or discovery. -/
theorem actual_tree : collectCanonicalTreeAuthoritative molecule 2 [canonicalCenterRoot 0] =
    some [canonicalCenterRoot 0, canonicalRoot 0 1, canonicalRoot 0 2,
      canonicalRoot 0 3, canonicalRoot 0 4] := by decide +kernel

theorem actual_auxiliary_state : buildOccurrenceAuxStateFullyAuthoritative? molecule 2 0 = some [] := by
  unfold buildOccurrenceAuxStateFullyAuthoritative?
  rw [actual_tree]
  decide +kernel

/-- The exact compiled sixteen-entry ordinary comparison table includes the equal-fluorine tie. -/
def atomicNumbers : List Nat := [9, 9, 17, 35]

theorem actual_initial_comparison_table (left right : Fin 4) :
    compareAuthoritativeRule6InitialPositions? molecule [] 2 roots left.val right.val =
      some ({ ordering := compare (atomicNumbers.getD left.val 0) (atomicNumbers.getD right.val 0) } : OccurrenceComparison) := by
  decide +revert +kernel

theorem actual_equal_fluorines :
    compareAuthoritativeRule6InitialPositions? molecule [] 2 roots 0 1 =
      some ({ ordering := .eq } : OccurrenceComparison) :=
  actual_initial_comparison_table 0 1

theorem actual_initial_sort :
    sortAuthoritativeRule6InitialPositions? molecule [] 2 roots (List.range 4) =
      some [3, 2, 0, 1] := by
  decide +kernel

theorem actual_adjacent :
    compareAuthoritativeRule6InitialAdjacent? molecule [] 2 roots [3, 2, 0, 1] =
      some [some .gt, some .gt, some .eq] := by
  decide +kernel

def actualPartition (left right : Nat) : Bool :=
  (compareAuthoritativeRule6InitialPositions? molecule [] 2 roots left right).any
    fun decision => decision.ordering = Ordering.eq

def exchange : List Nat := [1, 0, 2, 3]

theorem actual_exchange_member : exchange ∈ List.permutations (List.range 4) := by
  apply List.mem_permutations.mpr
  change [1, 0, 2, 3].Perm [0, 1, 2, 3]
  exact List.Perm.swap 0 1 [2, 3]

theorem actual_exchange_odd : RawMolecule.permutationIsEven exchange = false := by decide +kernel

theorem actual_partition_preserved :
    (List.range 4).all (fun index => actualPartition index (exchange.getD index 0)) = true := by
  unfold actualPartition
  decide +kernel

/-- Acceptance tests the ACTUAL initial-comparison relation, not a supplied constitution partition. -/
theorem actual_exchange_accepted :
    oddConstitutionPermutationAccepted molecule 0 ligands actualPartition exchange = true := by
  decide +kernel

theorem actual_source_guard :
    hasOddConstitutionAutomorphismAtCenter molecule 0 ligands actualPartition = some true :=
  (hasOddConstitutionAutomorphismAtCenter_eq_some_true_iff_accepted molecule 0 ligands
    actualPartition actual_ligands_length).mpr ⟨exchange, actual_exchange_member, actual_exchange_accepted⟩

theorem actual_source_guard_meaning :
    SourceHasOddPartitionPreservingConstitutionAutomorphism molecule 0 ligands actualPartition :=
  (hasOddConstitutionAutomorphismAtCenter_eq_some_true_iff molecule 0 ligands actualPartition
    actual_ligands_length actual_centered_ligands_nodup).mp actual_source_guard

theorem actual_source_not_stereogenic :
    authoritativeSourceRule6Stereogenicity? molecule 2 0 = some false := by
  have guardEq : hasOddConstitutionAutomorphismAtCenter molecule 0 ligands
      (fun left right => (compareAuthoritativeRule6InitialPositions? molecule [] 2 roots
        left right).any fun decision => decision.ordering = Ordering.eq) = some true :=
    actual_source_guard
  simp [authoritativeSourceRule6Stereogenicity?, actual_ligands_length, actual_auxiliary_state,
    actual_initial_sort, actual_adjacent, guardEq]

theorem actual_unannotated_outcome_none :
    authoritativeSourceRule6UnannotatedOutcome? molecule 2 0 = none := by
  simp [authoritativeSourceRule6UnannotatedOutcome?, actual_source_not_stereogenic]

theorem actual_not_stereogenic_applicability : ¬ AuthoritativeSourceRule6Stereogenic molecule 2 0 := by
  intro admitted
  have opposite := (authoritativeSourceRule6Stereogenicity?_eq_some_true_iff molecule 2 0).mpr admitted
  rw [actual_source_not_stereogenic] at opposite
  contradiction

end TetraStereo.UniversalProof.Rule6SymmetricPipelineRecoveryProofs.Rule6SymmetricPipelineRecovery
