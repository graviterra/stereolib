import TetraStereo.UniversalProof.SecondSphereFamilyRuntimeInstantiation
import TetraStereo.KernelOnly

set_option autoImplicit false

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords
open TetraStereo.UniversalProof.SecondSphereFamilyRuntimeInstantiation

assert_kernel_only familyInteriorDomain
assert_kernel_only family_observed_carbon
assert_kernel_only family_observed_hydrogen
assert_kernel_only family_observed_root
assert_kernel_only generic_bridge_cursor_eq
assert_kernel_only generic_methyl_cursor_eq
assert_kernel_only family_incoming_generated
assert_kernel_only family_outgoing_generated
assert_kernel_only family_fast_raw_both
assert_kernel_only family_authoritative_raw_both
assert_kernel_only family_certified_both
assert_kernel_only family_certified_authoritative_both
assert_kernel_only family_fast_protocol_both
assert_kernel_only family_authoritative_protocol_both
assert_kernel_only family_complete_protocol_both
assert_kernel_only family_complete_protocol_positive

example (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    CanonicalCenterRerootCursor (familyRaw ps) 1 (familyBridgeCursor ps i) :=
  family_incoming_generated ps i

example (ps : List TetrahedralInputParity) (i : Fin ps.length) :
    CanonicalCenterRerootCursor (familyRaw ps) 1 (familyMethylCursor ps i) :=
  family_outgoing_generated ps i

example (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (fuel : Nat) (stage : CanonicalRuleStage) :
    compareCursorBranchAtAuthoritative? (familyRaw ps) (fuel + 1) stage
      (familyBridgeCursor ps i) (familyMethylCursor ps i) = some Ordering.gt ∧
    compareCursorBranchAtAuthoritative? (familyRaw ps) (fuel + 1) stage
      (familyMethylCursor ps i) (familyBridgeCursor ps i) = some Ordering.lt :=
  family_authoritative_raw_both ps i fuel stage

example (ps : List TetrahedralInputParity) (i : Fin ps.length)
    (fuel : Nat) (positive : 1 ≤ fuel) :
    ∀ state : OccurrenceAuxState,
    compareOccurrenceBranchesComplete? (familyRaw ps) state fuel
      (familyBridgeCursor ps i) (familyMethylCursor ps i) = some { ordering := Ordering.gt } ∧
    compareOccurrenceBranchesComplete? (familyRaw ps) state fuel
      (familyMethylCursor ps i) (familyBridgeCursor ps i) = some { ordering := Ordering.lt } :=
  family_complete_protocol_positive ps i fuel positive
