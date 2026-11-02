import TetraStereo.UniversalProof.SecondSphereFamilyTrackedRanking
import TetraStereo.KernelOnly

set_option autoImplicit false

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords
open TetraStereo.UniversalProof.SecondSphereFamilyTrackedRanking

assert_kernel_only actual_all_pairs
assert_kernel_only actual_original_frame
assert_kernel_only actual_four_generated
assert_kernel_only actual_tracked_sort
assert_kernel_only actual_written_positions
assert_kernel_only actual_adjacent
assert_kernel_only actual_occurrence_fact
assert_kernel_only actual_update_fixed
assert_kernel_only actual_schedule_fixed
assert_kernel_only actual_pass_fixed
assert_kernel_only actual_stabilized
assert_kernel_only actual_unresolved_nil
assert_kernel_only actual_auxiliary_fixed
assert_kernel_only actual_exact_auxiliary_fixed
assert_kernel_only actual_finish_fixed
assert_kernel_only actual_constructive_fixed
assert_kernel_only actual_source_selected
assert_kernel_only actual_rule6_neutral
assert_kernel_only actual_discovery_is_initial
assert_kernel_only actual_discovered_tag

example (ps : List TetrahedralInputParity) (i : Fin ps.length) (fuel : Nat) (positive : 1 ≤ fuel) :
    ∀ state : OccurrenceAuxState,
    sortOccurrencesTrackedAuthoritative? (familyRaw ps) state fuel (writtenCursors ps i) =
      some (priorityCursors ps i, 0) := actual_tracked_sort ps i fuel positive

example (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    occurrenceLigandFrame? (familyRaw ps)
      (TetraStereo.UniversalProof.SecondSphereFamilyGeneratedHistories.tagNode i.val) =
      some (writtenCursors ps i) := actual_original_frame ps i

example (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    discoverRawDescriptors (familyResult ps) (familyRaw ps) (familyFuel ps) = familyInitial ps :=
  actual_discovery_is_initial ps i

example (ps : List TetrahedralInputParity) (maxEvidence remaining : Nat) :
    stabilizedRawDescriptorState? (familyResult ps) (familyRaw ps) maxEvidence (familyFuel ps)
      (remaining + 1) (familyInitial ps) = some (familyInitial ps) :=
  actual_stabilized ps maxEvidence remaining
