import TetraStereo.UniversalProof.NextFrontier.NativeRingSeedDiscovery
import TetraStereo.UniversalProof.NativeSecondSphereFamilyReport
import TetraStereo.UniversalProof.FamilyReportBridge

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeRingFamilyReport

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeRingDomain
open TetraStereo.UniversalProof.GeneralRingPhysicalAdmission
open TetraStereo.UniversalProof.NativeRingHydrogenFacts
open TetraStereo.UniversalProof.NativeRingRuntimeGraphFacts
open TetraStereo.UniversalProof.NativeRingInitialSeed
open TetraStereo.UniversalProof.NativeRingSeedDiscovery
open TetraStereo.UniversalProof.ActualFamilyReportBridgeProofs.ActualFamilyReportBridge

def ringState (n : Nat) (parity : TetrahedralInputParity) : RawDescriptorState :=
  discoverRawDescriptors (ringResult n parity) (expanded n parity) (ringFuel n parity)

def parityRow (parity : TetrahedralInputParity) : StereoAssignment :=
  { unit := .tetrahedral 0, outcome := .tetrahedral (descriptorOfParity parity false) }

/-- Complete atom-enumeration entry, preserving every computed unannotated refusal. -/
def fullEntry (n : Nat) (parity : TetrahedralInputParity) (index : Nat) : Option StereoAssignment :=
  FamilyReportBridge.entry (ringResult n parity) (ringFuel n parity) 0 (parityRow parity) index

def fullRows (n : Nat) (parity : TetrahedralInputParity) : List StereoAssignment :=
  (List.range (ringRaw n parity).atomCount).filterMap (fullEntry n parity)

theorem parsed_nonroot_untagged (n : Nat) (parity : TetrahedralInputParity)
    (index : Nat) (spec : AtomSpec) (different : index ≠ 0)
    (observed : (ringResult n parity).parsed.atomAt? index = some spec) :
    spec.tetrahedral? = none := by
  rw [ringResult, ringRaw_normalized_parsed] at observed
  cases tagged : spec.tetrahedral? with
  | none => rfl
  | some tag =>
      have bounded := listGet?_eq_some_implies_lt (ringRaw n parity).atoms index spec observed
      exact (different (raw_only_root_tagged n parity ⟨index, bounded⟩ spec observed
        (by rw [tagged]; rfl))).elim

theorem actual_tag_public_row (n : Nat) (parity : TetrahedralInputParity) :
    tetrahedralAssignment? (ringResult n parity) (expanded n parity) (ringState n parity)
      (ringFuel n parity) 0 = some (parityRow parity) := by
  have observed : (ringResult n parity).parsed.atomAt? 0 = some (taggedCarbon parity) := by
    rw [ringResult, ringRaw_normalized_parsed]
    exact ringRaw_atomAt_zero n parity
  have joined := SecondSphereFamilyReportBridge.tagged_public_adapter
    (ringResult n parity) (expanded n parity) (ringState n parity) (ringFuel n parity)
    0 (taggedCarbon parity) parity (seedFact parity) observed rfl
    (actual_discovered_tag n parity) (by rw [expanded_root_written_row]; rfl)
  simpa only [rawDescriptorFactOutcome, seedFact, ↓reduceIte, parityRow] using joined

theorem actual_tetrahedral_entry (n : Nat) (parity : TetrahedralInputParity) (index : Nat) :
    tetrahedralAssignment? (ringResult n parity) (expanded n parity) (ringState n parity)
      (ringFuel n parity) index = fullEntry n parity index :=
  FamilyReportBridge.tetrahedral_entry (ringResult n parity) (expanded n parity) (ringState n parity) (ringFuel n parity)
    0 (parityRow parity) (actual_normalized_materialization n parity) rfl
    (actual_tag_public_row n parity) (parsed_nonroot_untagged n parity) index

theorem actual_full_tetrahedral_report (n : Nat) (parity : TetrahedralInputParity) :
    tetrahedralAssignments (ringResult n parity) (expanded n parity) (ringState n parity)
      (ringFuel n parity) = fullRows n parity := by
  unfold tetrahedralAssignments fullRows
  rw [ringResult, ringRaw_normalized_parsed]
  apply List.filterMap_congr
  intro index _
  exact actual_tetrahedral_entry n parity index

theorem actual_assigned_projection (n : Nat) (parity : TetrahedralInputParity) :
    (fullRows n parity).filter (fun row => row.outcome.assigned) = [parityRow parity] := by
  rw [fullRows, atom_count, show n + 5 = (n + 4) + 1 by omega]
  exact FamilyReportBridge.root_assigned_projection (ringResult n parity) (ringFuel n parity) (n + 4)
    (parityRow parity) rfl

theorem actual_refusal_vocabulary (n : Nat) (parity : TetrahedralInputParity)
    (row : StereoAssignment) (member : row ∈ fullRows n parity)
    (unassigned : row.outcome.assigned = false) :
    row.outcome = .refused .notSpecified ∨ row.outcome = .refused .rankingUnresolved :=
  FamilyReportBridge.refusal_vocabulary (ringResult n parity) (ringFuel n parity) 0 (parityRow parity)
    rfl _ row member unassigned

theorem actual_observed_centers (n : Nat) (parity : TetrahedralInputParity) :
    rawAnnotatedCenters (ringResult n parity) = [0] := by
  apply FamilyReportBridge.annotated_centers_single (ringResult n parity) 0 (taggedCarbon parity) parity
    ?_ ?_ rfl (parsed_nonroot_untagged n parity)
  · rw [ringResult, ringRaw_normalized_parsed, atom_count]
    omega
  · rw [ringResult, ringRaw_normalized_parsed]
    exact ringRaw_atomAt_zero n parity

theorem actual_stereobonds_nil (n : Nat) (parity : TetrahedralInputParity) :
    (ringResult n parity).stereobonds.doubleBondAssignments = [] := by
  change (stereobondSemantics (ringRaw n parity).normalizeUnspecifiedBonds).doubleBondAssignments = []
  rw [ringRaw_normalizeUnspecifiedBonds]
  exact single_stereobond_assignments_nil _ (ringBonds_kind_single n)

theorem actual_other_four_segments_nil (n : Nat) (parity : TetrahedralInputParity) :
    let branches := normalizedStereoAnalysisBranches (ringResult n parity)
    branches.ordinaryDoubleBond = [] ∧ branches.coupledDoubleBond = [] ∧
      branches.oddCumuleneDoubleBond = [] ∧ branches.extendedAxial = [] := by
  have ordinary := actual_stereobonds_nil n parity
  have chains : (ringResult n parity).parsed.extendedDoubleBondChains = [] := by
    rw [ringResult, ringRaw_normalized_parsed]
    exact single_extended_chains_nil _ (ringBonds_kind_single n)
  have expandedChains : (expanded n parity).extendedDoubleBondChains = [] :=
    single_extended_chains_nil _ (expanded_bonds_single n parity)
  have carriers : (ringResult n parity).parsed.withExplicitHydrogens.extendedTetrahedralParityCarriers = [] := by
    rw [actual_normalized_materialization]
    simp [extendedTetrahedralParityCarriers, expandedChains]
  simp [normalizedStereoAnalysisBranches, ordinaryDoubleBondAssignments,
    oddCumuleneDoubleBondAssignments, ordinary, chains, carriers]

theorem actual_mass_guard (n : Nat) (parity : TetrahedralInputParity) :
    (ringResult n parity).parsed.rule2MassesKnown? = true := by
  apply (RawMolecule.rule2MassesKnown?_eq_true_iff _).mpr
  rw [ringResult, ringRaw_normalized_parsed]
  exact ringRaw_rule2MassesKnown n parity

theorem actual_expanded_guard (n : Nat) (parity : TetrahedralInputParity) :
    (ringResult n parity).expandedStereochemicalAdmissible? = true := by
  apply ((ringResult n parity).expandedStereochemicalAdmissible?_eq_true_iff).mpr
  change (ringResult n parity).parsed.withExplicitHydrogens.StereochemicalAdmissible
  rw [actual_normalized_materialization]
  exact expanded_stereochemical_admissible n parity

/-- The entire production report retains unannotated refusals; its assigned projection is
exactly the one annotated ring center. -/
theorem actual_normalized_whole_report (n : Nat) (parity : TetrahedralInputParity) :
    analyzeNormalized (ringResult n parity) = fullRows n parity := by
  apply FamilyReportBridge.normalized_report (ringResult n parity) (fullRows n parity)
    (actual_mass_guard n parity) (actual_expanded_guard n parity) ?_
    (actual_other_four_segments_nil n parity)
  simpa only [normalizedStereoAnalysisBranches, actual_normalized_materialization,
    ringFuel, ringState] using actual_full_tetrahedral_report n parity

theorem actual_early_assignment_none (n : Nat) (parity : TetrahedralInputParity) :
    singleInvariantEarlyAssignment? (ringResult n parity) = none := by
  have chains : (ringResult n parity).parsed.extendedDoubleBondChains = [] := by
    rw [ringResult, ringRaw_normalized_parsed]
    exact single_extended_chains_nil _ (ringBonds_kind_single n)
  simp only [singleInvariantEarlyAssignment?, actual_stereobonds_nil, chains,
    List.isEmpty_nil, Bool.not_true, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
    actual_observed_centers, actual_expanded_guard, actual_normalized_materialization]
  have outcome := actual_legacy_outcome n parity
  change (expanded n parity).tetrahedralOutcome (analysisFuel (expanded n parity)) 0 = _ at outcome
  rw [outcome]

theorem actual_string_full_report (n : Nat) (parity : TetrahedralInputParity) :
    analyzeSmiles (ringSyntax n parity) = Except.ok (fullRows n parity) :=
  FamilyReportBridge.string_report (ringSyntax n parity) (ringRaw n parity) (ringRawCertified n parity) (fullRows n parity)
    (NativeRingParserPublic.parse_ring n parity) ((RawMolecule.rule2MassesKnown?_eq_true_iff _).mpr (ringRaw_rule2MassesKnown n parity))
    (ringRaw_actual_certified_intake n parity) (actual_expanded_guard n parity)
    (actual_early_assignment_none n parity) (actual_normalized_whole_report n parity)

theorem actual_string_assigned_projection (n : Nat) (parity : TetrahedralInputParity) :
    (analyzeSmiles (ringSyntax n parity)).map
      (fun rows => rows.filter fun row => row.outcome.assigned) = Except.ok [parityRow parity] := by
  rw [actual_string_full_report]
  change Except.ok ((fullRows n parity).filter fun row => row.outcome.assigned) = _
  rw [actual_assigned_projection]

end TetraStereo.UniversalProof.NativeRingFamilyReport
