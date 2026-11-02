import TetraStereo.UniversalProof.NextFrontier.NativeNitrilePhysicalAdmission
import TetraStereo.UniversalProof.RuntimeSourcePublicPipelineRecoveryProofs.RuntimeSourcePublicPipelineRecovery
import TetraStereo.UniversalProof.FiniteCanonicalCollectorRecoveryProofs.FiniteCanonicalCollectorRecovery

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.RuntimeSourcePublicPipelineRecoveryProofs.RuntimeSourcePublicPipelineRecovery
open TetraStereo.UniversalProof.FiniteCanonicalCollectorRecoveryProofs.FiniteCanonicalCollectorRecovery

/-- The public runtime's graph-size budget, derived from the actual expanded atom inventory. -/
def runtimeFuel (n : Nat) : Nat := 6 * n + 30

def actualCollectedNodes (parity : TetrahedralInputParity) (n : Nat) :
    List CanonicalBranchNode :=
  prefixTree (expanded parity n) 0 0 (runtimeFuel n)

theorem runtimeFuel_eq_public_budget (parity : TetrahedralInputParity) (n : Nat) :
    runtimeFuel n = 2 * (expanded parity n).atomCount + 2 := by
  rw [expanded_atomCount]
  unfold runtimeFuel
  omega

/-- Actual collection terminates uniformly, including the multiple-bond duplicate nodes. -/
theorem actual_runtime_collector (parity : TetrahedralInputParity) (n : Nat) :
    collectCanonicalTreeAuthoritative (expanded parity n) (runtimeFuel n)
      [canonicalCenterRoot 0] = some (actualCollectedNodes parity n) := by
  exact actual_collector_complete _ 0 _ (expanded_admissible parity n).1
    (by rw [expanded_atomCount]; omega)
    (by rw [expanded_atomCount]; unfold runtimeFuel; omega)



theorem actual_runtime_auxiliary_environment (parity : TetrahedralInputParity) (n : Nat) :
    buildOccurrenceAuxStateFullyAuthoritative? (expanded parity n) (runtimeFuel n) 0 = some [] :=
  auxiliary_state_empty_of_actual_tree _ _ _ (expanded_only_center_tagged parity n) _
    (actual_runtime_collector parity n)

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
