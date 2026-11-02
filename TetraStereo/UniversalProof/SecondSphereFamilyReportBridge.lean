import TetraStereo.UniversalProof.NativeSecondSphereFamilyReport
import TetraStereo.UniversalProof.SecondSphereFamilyTrackedRanking
import TetraStereo.UniversalProof.SecondSphereNativeBlockParser
import TetraStereo.UniversalProof.ActualFamilyReportBridgeProofs.ActualFamilyReportBridge

set_option autoImplicit false

namespace TetraStereo.UniversalProof.SecondSphereFamilyReportBridge

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.SecondSpherePhysicalFamilyRecordsProofs.SecondSpherePhysicalFamilyRecords
open TetraStereo.UniversalProof.SecondSphereFamilyPhysicalInstantiation
open TetraStereo.UniversalProof.SecondSphereFamilyValenceInstantiation

/-! Proposed actual twelve-role-family public report adapter. The native
STRING dependency is separately accepted at commit712c3b3c (parser05); this report pair
still requires its own independently reviewed ROOT kernel gate. The tracked
ranking dependency is separately accepted at commit a32910c1, source78b996/cert9c2c.
No FirstZTagDomain is instantiated: the physical written heads are [6,1,9,6]. Generic local
adapter inputs expose actual descriptor lookup and physical written degree; every family use
derives them internally. All final family report/String statements take only ps (and valid i for per-tag statements). No report,
parser success, desired state/output, sorted roots or descriptor result is supplied. -/

-- familyResult is re-exported from NativeSecondSphereFamilyReport.


-- familyExpanded is re-exported from NativeSecondSphereFamilyReport.


-- familyFuel is re-exported from NativeSecondSphereFamilyReport.


-- familyState is re-exported from NativeSecondSphereFamilyReport.


-- actual_normalized_parsed is re-exported from NativeSecondSphereFamilyReport.


-- actual_materialized_identity is re-exported from NativeSecondSphereFamilyReport.


-- actual_fuel is re-exported from NativeSecondSphereFamilyReport.


private theorem role_tag_index (i : Nat) : SecondSphereInitialSeedBridge.roleIndex i 5 = tagIndex i := by
  unfold SecondSphereInitialSeedBridge.roleIndex tagIndex
  omega

-- actual_tag_atom is re-exported from NativeSecondSphereFamilyReport.


-- actual_discovered_tag is re-exported from NativeSecondSphereFamilyReport.



-- tagged_public_adapter is re-exported from NativeSecondSphereFamilyReport.


-- parityRow is re-exported from NativeSecondSphereFamilyReport.


-- familyTagRow is re-exported from NativeSecondSphereFamilyReport.


-- familyTagEntry is re-exported from NativeSecondSphereFamilyReport.


-- familyResidualEntry is re-exported from NativeSecondSphereFamilyReport.



-- familyFullEntry is re-exported from NativeSecondSphereFamilyReport.


-- familyTagRows is re-exported from NativeSecondSphereFamilyReport.


-- familyFullRows is re-exported from NativeSecondSphereFamilyReport.


-- actual_tag_public_row is re-exported from NativeSecondSphereFamilyReport.


-- actual_tetrahedral_entry is re-exported from NativeSecondSphereFamilyReport.


-- actual_full_tetrahedral_report is re-exported from NativeSecondSphereFamilyReport.


private theorem filter_full_entries_eq_tags (ps : List TetrahedralInputParity) (indices : List Nat) :
    ((indices.filterMap (familyFullEntry ps)).filter fun assignment => assignment.outcome.assigned) =
      indices.filterMap (familyTagEntry ps) := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      cases observed : (familyResult ps).parsed.atomAt? index with
      | none => simp [familyFullEntry, familyTagEntry, observed, ih]
      | some spec =>
          cases tagged : spec.tetrahedral? with
          | some parity =>
              have fullEntry : familyFullEntry ps index = some (parityRow index parity) := by
                simp only [familyFullEntry, observed, tagged]
              have tagEntry : familyTagEntry ps index = some (parityRow index parity) := by
                simp only [familyTagEntry, Bind.bind, Option.bind, observed, tagged]
              have assigned : (parityRow index parity).outcome.assigned = true := rfl
              rw [List.filterMap_cons_some fullEntry, List.filterMap_cons_some tagEntry,
                List.filter_cons_of_pos
                  (p := fun assignment : StereoAssignment => assignment.outcome.assigned)
                  (a := parityRow index parity) assigned, ih]
          | none =>
              cases residual : familyResidualEntry ps index with
              | none => simp [familyFullEntry, familyTagEntry, observed, tagged, residual, ih]
              | some assignment =>
                  have unassigned := ActualFamilyReportBridgeProofs.ActualFamilyReportBridge.residual_entry_unassigned (familyResult ps)
                    (familyFuel ps) index assignment residual
                  simp [familyFullEntry, familyTagEntry, observed, tagged, residual, unassigned, ih]

-- actual_assigned_projection is re-exported from NativeSecondSphereFamilyReport.


-- actual_tag_rows_units is re-exported from NativeSecondSphereFamilyReport.


-- actual_observed_centers_mem is re-exported from NativeSecondSphereFamilyReport.


-- actual_observed_centers is re-exported from NativeSecondSphereFamilyReport.


-- actual_tag_units is re-exported from NativeSecondSphereFamilyReport.


-- actual_tag_count is re-exported from NativeSecondSphereFamilyReport.


-- actual_refusal_vocabulary is re-exported from NativeSecondSphereFamilyReport.


-- actual_stereobonds_nil is re-exported from NativeSecondSphereFamilyReport.


-- actual_other_four_segments_nil is re-exported from NativeSecondSphereFamilyReport.


-- actual_mass_guard is re-exported from NativeSecondSphereFamilyReport.


-- actual_expanded_guard is re-exported from NativeSecondSphereFamilyReport.



-- actual_normalized_whole_report is re-exported from NativeSecondSphereFamilyReport.



-- actual_tag_public_membership is re-exported from NativeSecondSphereFamilyReport.



-- FamilyReport is re-exported from NativeSecondSphereFamilyReport.


-- familyReport_holds is re-exported from NativeSecondSphereFamilyReport.



-- actual_early_assignment_none is re-exported from NativeSecondSphereFamilyReport.


-- actual_certified_string_intake is re-exported from NativeSecondSphereFamilyReport.



-- actual_string_report is re-exported from NativeSecondSphereFamilyReport.


-- actual_string_full_report is re-exported from NativeSecondSphereFamilyReport.


-- actual_string_assigned_projection is re-exported from NativeSecondSphereFamilyReport.


end TetraStereo.UniversalProof.SecondSphereFamilyReportBridge
