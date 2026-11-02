import TetraStereo.UniversalProof.NextFrontier.NativeRingDuplicateProvenance
import TetraStereo.UniversalProof.FiniteCanonicalCollectorRecoveryProofs.FiniteCanonicalCollectorRecovery

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeRingRuntimeCollection

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeRingHydrogenFacts
open TetraStereo.UniversalProof.NativeRingDuplicateProvenance
open TetraStereo.UniversalProof.RuntimeSourcePublicPipelineRecoveryProofs.RuntimeSourcePublicPipelineRecovery
open TetraStereo.UniversalProof.FiniteCanonicalCollectorRecoveryProofs.FiniteCanonicalCollectorRecovery

/-- Finite graph fuel derived from the actual expanded atom inventory. -/
def familyFuel (n : Nat) : Nat := 3 * n + 10

def collectedNodes (n : Nat) (parity : TetrahedralInputParity) : List CanonicalBranchNode :=
  prefixTree (expanded n parity) 0 0 (familyFuel n)

theorem familyFuel_eq_atomCount (n : Nat) (parity : TetrahedralInputParity) :
    familyFuel n = (expanded n parity).atomCount + 1 := by
  rw [expanded_atom_count]
  rfl

/-- The real authoritative collector terminates on the entire cyclic family, not only on a
bounded sample. The fuel is derived from the independently proved expanded atom count. -/
theorem actual_collector (n : Nat) (parity : TetrahedralInputParity) :
    collectCanonicalTreeAuthoritative (expanded n parity) (familyFuel n) [canonicalCenterRoot 0] =
      some (collectedNodes n parity) := by
  exact actual_collector_complete _ 0 _ (expanded_stereochemical_admissible n parity).1.1
    (by rw [expanded_atom_count]; omega) (by rw [familyFuel_eq_atomCount])

/-- Auxiliary discovery really returns the empty environment, because only the original root
carries a tag and the complete actual cyclic tree has been collected. -/
theorem actual_auxiliary_environment (n : Nat) (parity : TetrahedralInputParity) :
    buildOccurrenceAuxStateFullyAuthoritative? (expanded n parity) (familyFuel n) 0 = some [] :=
  auxiliary_state_empty_of_actual_tree _ _ _ (expanded_only_root_tagged n parity) _
    (actual_collector n parity)

theorem actual_fast_dispatch (n fuel : Nat) (parity : TetrahedralInputParity)
    (state : OccurrenceAuxState) :
    occurrenceFact? (expanded n parity) fuel state (canonicalCenterRoot 0) =
      legacyOccurrenceFact? (expanded n parity) fuel state (canonicalCenterRoot 0) :=
  occurrenceFact?_eq_legacy_of_profile_none _ _ _ _ (expanded_profile_none n parity)

theorem actual_authoritative_dispatch (n fuel : Nat) (parity : TetrahedralInputParity)
    (state : OccurrenceAuxState) :
    occurrenceFactAuthoritative? (expanded n parity) fuel state (canonicalCenterRoot 0) =
      legacyOccurrenceFactAuthoritative? (expanded n parity) fuel state (canonicalCenterRoot 0) :=
  occurrenceFactAuthoritative?_eq_legacy_of_profile_none _ _ _ _ (expanded_profile_none n parity)

end TetraStereo.UniversalProof.NativeRingRuntimeCollection
