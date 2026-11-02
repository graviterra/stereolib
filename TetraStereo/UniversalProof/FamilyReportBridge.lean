import TetraStereo.UniversalProof.NativeFamilyReportRawHelpers

set_option autoImplicit false

namespace TetraStereo.UniversalProof.FamilyReportBridge

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.ActualFamilyReportBridgeProofs.ActualFamilyReportBridge

/-! Report composition depends on actual discovery, annotation and guard facts. It
does not restrict bond kinds or ranking rules and never discards residual refusals. -/

def entry (result : ChemistryNormalizationResult) (fuel center : Nat)
    (assigned : StereoAssignment) (index : Nat) : Option StereoAssignment :=
  if index = center then some assigned else residualEntry result fuel index

theorem tetrahedral_entry (result : ChemistryNormalizationResult) (molecule : RawMolecule)
    (state : RawDescriptorState) (fuel center : Nat) (assigned : StereoAssignment)
    (materialized : result.parsed.withExplicitHydrogens = molecule)
    (discovered : state = discoverRawDescriptors result molecule fuel)
    (tagged : tetrahedralAssignment? result molecule state fuel center = some assigned)
    (untagged : ∀ index spec, index ≠ center → result.parsed.atomAt? index = some spec →
      spec.tetrahedral? = none) (index : Nat) :
    tetrahedralAssignment? result molecule state fuel index = entry result fuel center assigned index := by
  by_cases atCenter : index = center
  · subst index
    simpa only [entry, ↓reduceIte] using tagged
  · cases observed : result.parsed.atomAt? index with
    | none =>
        simp [tetrahedralAssignment?, entry, atCenter, residualEntry,
          unannotatedTetrahedralOutcome?, observed]
    | some spec =>
        simp only [tetrahedralAssignment?, entry, atCenter, ↓reduceIte, observed,
          untagged index spec atCenter observed]
        simp only [residualEntry, FirstZSeedDiscoveryRecoveryProofs.FirstZSeedDiscoveryRecovery.materialized,
          computedState, materialized, discovered]

theorem filter_entries (result : ChemistryNormalizationResult) (fuel center : Nat)
    (assigned : StereoAssignment) (isAssigned : assigned.outcome.assigned = true)
    (indices : List Nat) :
    ((indices.filterMap (entry result fuel center assigned)).filter fun row => row.outcome.assigned) =
      indices.filterMap (fun index => if index = center then some assigned else none) := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      by_cases atCenter : index = center
      · simpa [entry, atCenter, isAssigned] using ih
      · cases residual : residualEntry result fuel index with
        | none => simp [entry, atCenter, residual, ih]
        | some row =>
            have unassigned := residual_entry_unassigned _ _ _ row residual
            simp [entry, atCenter, residual, unassigned, ih]

theorem root_assigned_projection (result : ChemistryNormalizationResult) (fuel tailCount : Nat)
    (assigned : StereoAssignment) (isAssigned : assigned.outcome.assigned = true) :
    (((List.range (tailCount + 1)).filterMap (entry result fuel 0 assigned)).filter
      fun row => row.outcome.assigned) = [assigned] := by
  rw [filter_entries result fuel 0 assigned isAssigned, List.range_succ_eq_map]
  simp only [List.filterMap_cons, ↓reduceIte, List.filterMap_map]
  have absent : (List.range tailCount).filterMap
      (fun index => if index + 1 = 0 then some assigned else none) = [] := by simp
  simp only [Function.comp_def, Nat.succ_eq_add_one, absent]

theorem annotated_centers_single (result : ChemistryNormalizationResult) (center : Nat)
    (spec : AtomSpec) (parity : TetrahedralInputParity)
    (bounded : center < result.parsed.atomCount)
    (observed : result.parsed.atomAt? center = some spec)
    (tagged : spec.tetrahedral? = some parity)
    (untagged : ∀ index atom, index ≠ center → result.parsed.atomAt? index = some atom →
      atom.tetrahedral? = none) : rawAnnotatedCenters result = [center] := by
  apply List.Perm.eq_singleton
  apply (List.perm_ext_iff_of_nodup
    ((List.nodup_range (n := result.parsed.atomCount)).filter _) (by simp)).mpr
  intro index
  simp only [List.mem_singleton, List.mem_filter]
  constructor
  · rintro ⟨_, hasTag⟩
    by_contra different
    cases atIndex : result.parsed.atomAt? index with
    | none => simp [atIndex] at hasTag
    | some atom => simp [atIndex, untagged index atom different atIndex] at hasTag
  · intro same
    subst index
    simp [List.mem_range, bounded, observed, tagged]

theorem refusal_vocabulary (result : ChemistryNormalizationResult) (fuel center : Nat)
    (assigned : StereoAssignment) (isAssigned : assigned.outcome.assigned = true)
    (indices : List Nat) (row : StereoAssignment)
    (member : row ∈ indices.filterMap (entry result fuel center assigned))
    (unassigned : row.outcome.assigned = false) :
    row.outcome = .refused .notSpecified ∨ row.outcome = .refused .rankingUnresolved := by
  obtain ⟨index, _, computed⟩ := List.mem_filterMap.mp member
  by_cases atCenter : index = center
  · have same : assigned = row := by simpa [entry, atCenter] using computed
    rw [← same, isAssigned] at unassigned
    cases unassigned
  · have residual : residualEntry result fuel index = some row := by
      simpa only [entry, atCenter, ↓reduceIte] using computed
    exact (residual_entry_only_refusals _ _ _ _ residual).2

/-- Assemble all five actual production segments after both admission guards. -/
theorem normalized_report (result : ChemistryNormalizationResult) (rows : List StereoAssignment)
    (masses : result.parsed.rule2MassesKnown? = true)
    (admissible : result.expandedStereochemicalAdmissible? = true)
    (tetra : (normalizedStereoAnalysisBranches result).tetrahedral = rows)
    (other : let branches := normalizedStereoAnalysisBranches result
      branches.ordinaryDoubleBond = [] ∧ branches.coupledDoubleBond = [] ∧
        branches.oddCumuleneDoubleBond = [] ∧ branches.extendedAxial = []) :
    analyzeNormalized result = rows := by
  obtain ⟨ordinary, coupled, cumulene, axial⟩ := other
  unfold analyzeNormalized
  rw [masses, admissible]
  change (normalizedStereoAnalysisBranches result).tetrahedral ++
    (normalizedStereoAnalysisBranches result).ordinaryDoubleBond ++
    (normalizedStereoAnalysisBranches result).coupledDoubleBond ++
    (normalizedStereoAnalysisBranches result).oddCumuleneDoubleBond ++
    (normalizedStereoAnalysisBranches result).extendedAxial = _
  rw [ordinary, coupled, cumulene, axial]
  simpa only [List.append_nil] using tetra

/-- Carry actual string intake through the certified normalization and early-output guards.
The report premise concerns the normalized stage, not the final string consumer. -/
theorem string_report (input : String) (raw : RawMolecule)
    (certified : CertifiedChemistryNormalizationResult) (rows : List StereoAssignment)
    (parsed : parseOpenSMILES input = .ok raw)
    (masses : raw.rule2MassesKnown? = true)
    (admitted : (normalizeRawMolecule raw).certify? = some certified)
    (expanded : certified.result.expandedStereochemicalAdmissible? = true)
    (early : singleInvariantEarlyAssignment? certified.result = none)
    (report : analyzeNormalized certified.result = rows) : analyzeSmiles input = .ok rows := by
  simp only [analyzeSmiles, parsed, masses, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, admitted, expanded, early]
  rw [report]

end TetraStereo.UniversalProof.FamilyReportBridge
