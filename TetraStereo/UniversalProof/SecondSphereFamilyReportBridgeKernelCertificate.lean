import TetraStereo.UniversalProof.SecondSphereFamilyReportBridge
import TetraStereo.KernelOnly

set_option autoImplicit false

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords
open TetraStereo.UniversalProof.SecondSphereFamilyValenceInstantiation
open TetraStereo.UniversalProof.SecondSphereFamilyReportBridge

assert_kernel_only actual_normalized_parsed
assert_kernel_only actual_materialized_identity
assert_kernel_only actual_fuel
assert_kernel_only actual_tag_atom
assert_kernel_only actual_discovered_tag
assert_kernel_only tagged_public_adapter
assert_kernel_only actual_tag_public_row
assert_kernel_only actual_tetrahedral_entry
assert_kernel_only actual_full_tetrahedral_report
assert_kernel_only actual_assigned_projection
assert_kernel_only actual_tag_rows_units
assert_kernel_only actual_observed_centers_mem
assert_kernel_only actual_observed_centers
assert_kernel_only actual_tag_units
assert_kernel_only actual_tag_count
assert_kernel_only actual_refusal_vocabulary
assert_kernel_only actual_stereobonds_nil
assert_kernel_only actual_other_four_segments_nil
assert_kernel_only actual_mass_guard
assert_kernel_only actual_expanded_guard
assert_kernel_only actual_normalized_whole_report
assert_kernel_only actual_tag_public_membership
assert_kernel_only familyReport_holds
assert_kernel_only actual_early_assignment_none
assert_kernel_only actual_certified_string_intake
assert_kernel_only actual_string_report
assert_kernel_only actual_string_full_report
assert_kernel_only actual_string_assigned_projection

example (ps : List TetrahedralInputParity) : FamilyReport ps := familyReport_holds ps

example (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    ({ unit := .tetrahedral (tagIndex i.val),
       outcome := .tetrahedral (descriptorOfParity (ps.get i) false) } : StereoAssignment) ∈
      analyzeNormalized (certifiedFamily ps).result := actual_tag_public_membership ps i

example (ps : List TetrahedralInputParity) :
    analyzeSmiles (TetraStereo.UniversalProof.SecondSphereNativeBlockParser.nativeFamilyString ps) =
      Except.ok (familyFullRows ps) := actual_string_full_report ps
