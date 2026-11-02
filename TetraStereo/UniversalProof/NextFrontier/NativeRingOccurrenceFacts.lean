import TetraStereo.UniversalProof.NextFrontier.NativeRingTrackedSort
import TetraStereo.UniversalProof.NextFrontier.NativeRingRuntimeCollection

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeRingOccurrenceFacts

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeRingDomain
open TetraStereo.UniversalProof.GeneralRingPhysicalAdmission
open TetraStereo.UniversalProof.NativeRingHydrogenFacts
open TetraStereo.UniversalProof.NativeRingRuntimeRoot
open TetraStereo.UniversalProof.NativeRingTrackedSort
open TetraStereo.UniversalProof.NativeRingRuntimeCollection
open TetraStereo.UniversalProof.RuntimeSourcePublicPipelineRecoveryProofs.RuntimeSourcePublicPipelineRecovery

def localFact (parity : TetrahedralInputParity) : OccurrenceAuxFact :=
  { key := canonicalOccurrenceKey (canonicalCenterRoot 0)
    atom := 0
    descriptor := descriptorOfParity parity false
    uppercase := true
    priorityPositions := [1, 2, 3, 0] }

/-- This is the actual local authoritative occurrence consumer. The ring's generated duplicate
forces legacy dispatch, and the complete physical sort determines parity and uppercase status. -/
theorem actual_local_fact (n fuel : Nat) (parity : TetrahedralInputParity)
    (state : OccurrenceAuxState) (enough : n ≤ fuel) :
    occurrenceFactAuthoritative? (expanded n parity) (fuel + 1) state (canonicalCenterRoot 0) =
      some (localFact parity) := by
  rw [actual_authoritative_dispatch]
  have observed := expanded_original_atom n parity 0 _ (ringRaw_atomAt_zero n parity)
  have positions := actual_priority_positions n parity
  rw [actual_root_ligands] at positions
  simp only [legacyOccurrenceFactAuthoritative?, show (canonicalCenterRoot 0).atom = 0 from rfl,
    observed, Bind.bind, Option.bind, materializedAtomSpec, taggedCarbon,
    actual_root_ligands, actual_root_frame, actual_tracked_sort n fuel parity state enough,
    positions, actual_adjacent n fuel parity state enough]
  rfl

theorem actual_local_family_fuel (n : Nat) (parity : TetrahedralInputParity)
    (state : OccurrenceAuxState) :
    occurrenceFactAuthoritative? (expanded n parity) (familyFuel n) state (canonicalCenterRoot 0) =
      some (localFact parity) := by
  change occurrenceFactAuthoritative? _ ((3 * n + 9) + 1) _ _ = _
  exact actual_local_fact n (3 * n + 9) parity state (by omega)

/-- Full actual collector and actual auxiliary state feed the public occurrence API. This
statement is distinct from the initial descriptor seed and discovery report, proved downstream. -/
theorem actual_public_occurrence (n : Nat) (parity : TetrahedralInputParity) :
    tetrahedralOccurrenceFact? (expanded n parity) (familyFuel n) 0 =
      some (recoveredPublicFact 0 [1, 2, 3, 0] (descriptorOfParity parity false)) := by
  exact public_fact_of_actual_local_fact _ _ 0 (expanded_only_root_tagged n parity)
    (collectedNodes n parity) (actual_collector n parity) [1, 2, 3, 0]
    (descriptorOfParity parity false) (actual_local_family_fuel n parity [])

/-- The same actual occurrence result at the public reporter's analysis fuel. -/
theorem actual_public_analysis_fuel (n : Nat) (parity : TetrahedralInputParity) :
    tetrahedralOccurrenceFactAuthoritative? (expanded n parity) (analysisFuel (expanded n parity)) 0 =
      some (recoveredPublicFact 0 [1, 2, 3, 0] (descriptorOfParity parity false)) := by
  have collected := FiniteCanonicalCollectorRecoveryProofs.FiniteCanonicalCollectorRecovery.actual_collector_complete
    (expanded n parity) 0 (analysisFuel (expanded n parity))
    (expanded_stereochemical_admissible n parity).1.1
    (by rw [expanded_atom_count]; omega) (by unfold analysisFuel; omega)
  have localComputed : occurrenceFactAuthoritative? (expanded n parity)
      (analysisFuel (expanded n parity)) [] (canonicalCenterRoot 0) = some (localFact parity) := by
    change occurrenceFactAuthoritative? _ ((2 * (expanded n parity).atomCount + 1) + 1) _ _ = _
    exact actual_local_fact n _ parity [] (by rw [expanded_atom_count]; omega)
  exact public_fact_of_actual_local_fact _ _ 0 (expanded_only_root_tagged n parity)
    _ collected [1, 2, 3, 0] (descriptorOfParity parity false) localComputed

end TetraStereo.UniversalProof.NativeRingOccurrenceFacts
