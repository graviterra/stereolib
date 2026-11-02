import TetraStereo.UniversalProof.NextFrontier.NativeNitrileSeedDiscovery
import TetraStereo.UniversalProof.NextFrontier.NativeNitrileNonTetrahedralSegments
import TetraStereo.UniversalProof.NativeSecondSphereFamilyReport
import TetraStereo.UniversalProof.FamilyReportBridge

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamilyReport

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
open TetraStereo.UniversalProof.NextFrontier.NativeNitrileInitialSeed
open TetraStereo.UniversalProof.NextFrontier.NativeNitrileSeedDiscovery
open TetraStereo.UniversalProof.ActualFamilyReportBridgeProofs.ActualFamilyReportBridge

def nitrileState (n : Nat) (parity : TetrahedralInputParity) : RawDescriptorState :=
  discoverRawDescriptors (nitrileResult n parity) (expanded parity n) (nitrileFuel n parity)

def parityRow (parity : TetrahedralInputParity) : StereoAssignment :=
  { unit := .tetrahedral 0, outcome := .tetrahedral (descriptorOfParity parity false) }

/-- Complete atom-enumeration entry, preserving every computed unannotated refusal. -/
def fullEntry (n : Nat) (parity : TetrahedralInputParity) (index : Nat) : Option StereoAssignment :=
  FamilyReportBridge.entry (nitrileResult n parity) (nitrileFuel n parity) 0 (parityRow parity) index

def fullRows (n : Nat) (parity : TetrahedralInputParity) : List StereoAssignment :=
  (List.range (raw parity n).atomCount).filterMap (fullEntry n parity)

theorem parsed_nonroot_untagged (n : Nat) (parity : TetrahedralInputParity)
    (index : Nat) (spec : AtomSpec) (different : index ≠ 0)
    (observed : (nitrileResult n parity).parsed.atomAt? index = some spec) :
    spec.tetrahedral? = none := by
  rw [nitrileResult, raw_normalized_parsed] at observed
  cases tagged : spec.tetrahedral? with
  | none => rfl
  | some tag =>
      have bounded := listGet?_eq_some_implies_lt (raw parity n).atoms index spec observed
      exact (different (raw_only_center_tagged parity n ⟨index, bounded⟩ spec observed
        (by rw [tagged]; rfl))).elim

theorem actual_tag_public_row (n : Nat) (parity : TetrahedralInputParity) :
    tetrahedralAssignment? (nitrileResult n parity) (expanded parity n) (nitrileState n parity)
      (nitrileFuel n parity) 0 = some (parityRow parity) := by
  have observed : (nitrileResult n parity).parsed.atomAt? 0 = some (centerSpec parity) := by
    rw [nitrileResult, raw_normalized_parsed]
    exact raw_center parity n
  have joined := SecondSphereFamilyReportBridge.tagged_public_adapter
    (nitrileResult n parity) (expanded parity n) (nitrileState n parity) (nitrileFuel n parity)
    0 (centerSpec parity) parity (seedFact parity) observed rfl
    (actual_discovered_tag n parity) (by rw [expanded_center_row]; rfl)
  simpa only [rawDescriptorFactOutcome, seedFact, ↓reduceIte, parityRow] using joined

theorem actual_tetrahedral_entry (n : Nat) (parity : TetrahedralInputParity) (index : Nat) :
    tetrahedralAssignment? (nitrileResult n parity) (expanded parity n) (nitrileState n parity)
      (nitrileFuel n parity) index = fullEntry n parity index :=
  FamilyReportBridge.tetrahedral_entry (nitrileResult n parity) (expanded parity n) (nitrileState n parity) (nitrileFuel n parity)
    0 (parityRow parity) (actual_normalized_materialization n parity) rfl
    (actual_tag_public_row n parity) (parsed_nonroot_untagged n parity) index

theorem actual_full_tetrahedral_report (n : Nat) (parity : TetrahedralInputParity) :
    tetrahedralAssignments (nitrileResult n parity) (expanded parity n) (nitrileState n parity)
      (nitrileFuel n parity) = fullRows n parity := by
  unfold tetrahedralAssignments fullRows
  rw [nitrileResult, raw_normalized_parsed]
  apply List.filterMap_congr
  intro index _
  exact actual_tetrahedral_entry n parity index

theorem actual_assigned_projection (n : Nat) (parity : TetrahedralInputParity) :
    (fullRows n parity).filter (fun row => row.outcome.assigned) = [parityRow parity] := by
  rw [fullRows, raw_atomCount, show n + 7 = (n + 6) + 1 by omega]
  exact FamilyReportBridge.root_assigned_projection (nitrileResult n parity) (nitrileFuel n parity) (n + 6)
    (parityRow parity) rfl

theorem actual_refusal_vocabulary (n : Nat) (parity : TetrahedralInputParity)
    (row : StereoAssignment) (member : row ∈ fullRows n parity)
    (unassigned : row.outcome.assigned = false) :
    row.outcome = .refused .notSpecified ∨ row.outcome = .refused .rankingUnresolved :=
  FamilyReportBridge.refusal_vocabulary (nitrileResult n parity) (nitrileFuel n parity) 0 (parityRow parity)
    rfl _ row member unassigned

theorem actual_observed_centers (n : Nat) (parity : TetrahedralInputParity) :
    rawAnnotatedCenters (nitrileResult n parity) = [0] := by
  apply FamilyReportBridge.annotated_centers_single (nitrileResult n parity) 0 (centerSpec parity) parity
    ?_ ?_ rfl (parsed_nonroot_untagged n parity)
  · rw [nitrileResult, raw_normalized_parsed, raw_atomCount]
    omega
  · rw [nitrileResult, raw_normalized_parsed]
    exact raw_center parity n

theorem actual_mass_guard (n : Nat) (parity : TetrahedralInputParity) :
    (nitrileResult n parity).parsed.rule2MassesKnown? = true := by
  apply (RawMolecule.rule2MassesKnown?_eq_true_iff _).mpr
  rw [nitrileResult, raw_normalized_parsed]
  exact raw_rule2_masses_known parity n

theorem actual_expanded_guard (n : Nat) (parity : TetrahedralInputParity) :
    (nitrileResult n parity).expandedStereochemicalAdmissible? = true := by
  apply ((nitrileResult n parity).expandedStereochemicalAdmissible?_eq_true_iff).mpr
  change (nitrileResult n parity).parsed.withExplicitHydrogens.StereochemicalAdmissible
  rw [actual_normalized_materialization]
  exact expanded_stereochemical_admissible parity n

/-- The entire production report retains unannotated refusals; its assigned projection is
exactly the one annotated nitrile-family center. -/
theorem actual_normalized_whole_report (n : Nat) (parity : TetrahedralInputParity) :
    analyzeNormalized (nitrileResult n parity) = fullRows n parity := by
  apply FamilyReportBridge.normalized_report (nitrileResult n parity) (fullRows n parity)
    (actual_mass_guard n parity) (actual_expanded_guard n parity) ?_
    (actual_other_four_segments_nil n parity)
  simpa only [normalizedStereoAnalysisBranches, actual_normalized_materialization,
    nitrileFuel, nitrileState] using actual_full_tetrahedral_report n parity

theorem actual_early_assignment_none (n : Nat) (parity : TetrahedralInputParity) :
    singleInvariantEarlyAssignment? (nitrileResult n parity) = none := by
  have chains : (nitrileResult n parity).parsed.extendedDoubleBondChains = [] := by
    rw [nitrileResult, raw_normalized_parsed]
    exact no_double_extended_chains _ (raw_no_double parity n)
  simp only [singleInvariantEarlyAssignment?, actual_stereobonds_nil, chains,
    List.isEmpty_nil, Bool.not_true, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
    actual_observed_centers, actual_expanded_guard, actual_normalized_materialization]
  have outcome := actual_legacy_outcome n parity
  change (expanded parity n).tetrahedralOutcome (analysisFuel (expanded parity n)) 0 = _ at outcome
  rw [outcome]

theorem actual_string_full_report (n : Nat) (parity : TetrahedralInputParity) :
    analyzeSmiles (smiles parity n) = Except.ok (fullRows n parity) :=
  FamilyReportBridge.string_report (smiles parity n) (raw parity n) (rawCertified parity n) (fullRows n parity)
    (actual_parse parity n) ((RawMolecule.rule2MassesKnown?_eq_true_iff _).mpr (raw_rule2_masses_known parity n))
    (actual_certified_raw_intake parity n) (actual_expanded_guard n parity)
    (actual_early_assignment_none n parity) (actual_normalized_whole_report n parity)

theorem actual_string_assigned_projection (n : Nat) (parity : TetrahedralInputParity) :
    (analyzeSmiles (smiles parity n)).map
      (fun rows => rows.filter fun row => row.outcome.assigned) = Except.ok [parityRow parity] := by
  rw [actual_string_full_report]
  change Except.ok ((fullRows n parity).filter fun row => row.outcome.assigned) = _
  rw [actual_assigned_projection]

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamilyReport
