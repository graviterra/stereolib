import TetraStereo.UniversalProof.NativeRawAtomicNumber
import TetraStereo.UniversalProof.NativeFamilyRawSupport

set_option autoImplicit false

/-! SOURCE-only shared physical seed support; declarations retain their original namespaces.
No occurrence-frame/ranking, FirstZ-domain or source-model closure is imported. -/

namespace TetraStereo.UniversalProof.NativeInitialSeedRuntimeSupportProofs.RuntimeNormalizedClassifierDomainRecovery

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery

/-- The actual LEGACY branch consumer has the same strict Rule-1a decision, at any fuel.
No surrogate comparator is substituted into the program. The tied case is deliberately excluded. -/
theorem actual_legacy_root_rule1a (raw : RawMolecule) (center left right : Nat) :
    raw.compareCanonicalNodeRule .rule1a (canonicalRoot center left) (canonicalRoot center right) =
      compare (raw.atomZAt left) (raw.atomZAt right) := by
  unfold compareCanonicalNodeRule canonicalRule1aLabel
  rw [NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery.canonicalRule1aLabel?_realAtom raw _ rfl,
    NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery.canonicalRule1aLabel?_realAtom raw _ rfl]
  exact NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery.compareCIPAtomicLabel_unitValue _ _

theorem actual_legacy_strict_branch (raw : RawMolecule) (fuel center left right : Nat)
    (different : raw.atomZAt left ≠ raw.atomZAt right) :
    raw.compareBranches? fuel center left right = some (compare (raw.atomZAt left) (raw.atomZAt right)) := by
  cases comparison : compare (raw.atomZAt left) (raw.atomZAt right) with
  | lt => simp only [compareBranches?, actual_legacy_root_rule1a, comparison]
  | eq => exact False.elim (different (Nat.compare_eq_eq.mp comparison))
  | gt => simp only [compareBranches?, actual_legacy_root_rule1a, comparison]

end TetraStereo.UniversalProof.NativeInitialSeedRuntimeSupportProofs.RuntimeNormalizedClassifierDomainRecovery

namespace TetraStereo.UniversalProof.NativeInitialSeedRuntimeSupportProofsLibrary.GeneratedPendantOccurrenceRecovery

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery

/-- Actual undirected incidence follows from the two endpoints of one retained bond. -/
theorem record_neighbors_symmetric (raw : RawMolecule) (well : raw.WellFormed)
    {left right : Nat} (member : right ∈ recordNeighbors raw left) :
    left ∈ recordNeighbors raw right := by
  obtain ⟨bond, retained, observed⟩ := List.mem_filterMap.mp member
  refine List.mem_filterMap.mpr ⟨bond, retained, ?_⟩
  have endpoints := well bond retained
  unfold recordNeighbor? at observed ⊢
  by_cases source : bond.source = left
  · have target : bond.target = right := by simpa [source] using observed
    have different : left ≠ right := by simpa only [source, target] using endpoints.2.2
    simp [target, source, different]
  · by_cases target : bond.target = left
    · have sourceRight : bond.source = right := by simpa [source, target] using observed
      simp [sourceRight, target]
    · simp [source, target] at observed

end TetraStereo.UniversalProof.NativeInitialSeedRuntimeSupportProofsLibrary.GeneratedPendantOccurrenceRecovery

namespace TetraStereo.UniversalProof.FirstZSeedDiscoveryRecoveryProofs.FirstZSeedDiscoveryRecovery

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery

def materialized (result : ChemistryNormalizationResult) : RawMolecule :=
  result.parsed.withExplicitHydrogens

end TetraStereo.UniversalProof.FirstZSeedDiscoveryRecoveryProofs.FirstZSeedDiscoveryRecovery
