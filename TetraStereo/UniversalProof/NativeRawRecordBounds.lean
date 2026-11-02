import TetraStereo.UniversalProof.NativeFamilyRawSupport

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule

/-- Raw endpoint validity derives both the actual neighbor bound and exclusion of the center. -/
theorem recordNeighbor_bounds {molecule : RawMolecule} {center : ℕ}
    (well : molecule.WellFormed) {atom : ℕ} (member : atom ∈ recordNeighbors molecule center) :
    atom < molecule.atomCount ∧ atom ≠ center := by
  obtain ⟨bond, inBonds, observed⟩ := List.mem_filterMap.mp member
  have endpoints := well bond inBonds
  unfold recordNeighbor? at observed
  split at observed
  · rename_i sourceIsCenter
    have sourceEqual : bond.source = center := by simpa using sourceIsCenter
    have targetEqual : bond.target = atom := Option.some.inj observed
    refine ⟨?_, ?_⟩
    · simpa only [targetEqual] using endpoints.2.1
    · intro equal
      exact endpoints.2.2 (sourceEqual.trans (equal.symm.trans targetEqual.symm))
  · split at observed
    · rename_i targetIsCenter
      have targetEqual : bond.target = center := by simpa using targetIsCenter
      have sourceEqual : bond.source = atom := Option.some.inj observed
      refine ⟨?_, ?_⟩
      · simpa only [sourceEqual] using endpoints.1
      · intro equal
        exact endpoints.2.2 (sourceEqual.trans (equal.trans targetEqual.symm))
    · cases observed

end TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
