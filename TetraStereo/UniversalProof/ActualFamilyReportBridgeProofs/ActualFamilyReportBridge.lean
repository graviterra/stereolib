import TetraStereo.UniversalProof.NativeFamilyReportRawHelpers
import TetraStereo.UniversalProof.FirstZSeedDiscoveryRecoveryProofs.FirstZSeedDiscoveryRecovery
import TetraStereo.UniversalProof.FirstZSourceDiscoveryAlignmentProofs.FirstZSourceDiscoveryAlignment
import TetraStereo.UniversalProof.NativeOrdinarySourceInputProofs.SourceInputPremiseRecovery

set_option autoImplicit false

namespace TetraStereo.UniversalProof.ActualFamilyReportBridgeProofs.ActualFamilyReportBridge

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.UniversalProof.ExplicitHydrogenExpansionIdentityProofs.ExplicitHydrogenExpansionIdentity
open TetraStereo.UniversalProof.NativeInitialSeedRuntimeSupportProofs.RuntimeNormalizedClassifierDomainRecovery
open TetraStereo.UniversalProof.NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery
open TetraStereo.UniversalProof.FirstZSeedDiscoveryRecoveryProofs.FirstZSeedDiscoveryRecovery
open TetraStereo.UniversalProof.NativeOrdinarySourceInputProofs.SourceInputPremiseRecovery










-- computedState is re-exported from NativeFamilyReportRawHelpers.


def tagRow (result : ChemistryNormalizationResult) (fuel index : Nat)
    (parity : TetrahedralInputParity) : StereoAssignment :=
  { unit := .tetrahedral index, outcome := .tetrahedral (seedDescriptor result fuel index parity) }

def tagEntry (result : ChemistryNormalizationResult) (fuel index : Nat) : Option StereoAssignment := do
  let spec ← result.parsed.atomAt? index
  let parity ← spec.tetrahedral?
  some (tagRow result fuel index parity)


-- residualEntry is re-exported from NativeFamilyReportRawHelpers.


/-- Parser order is retained; tagged and residual rows are not concatenated out of order. -/
def fullEntry (result : ChemistryNormalizationResult) (fuel index : Nat) : Option StereoAssignment :=
  match result.parsed.atomAt? index with
  | none => none
  | some spec => match spec.tetrahedral? with
    | none => residualEntry result fuel index
    | some parity => some (tagRow result fuel index parity)

def tagRows (result : ChemistryNormalizationResult) (fuel : Nat) : List StereoAssignment :=
  (List.range result.parsed.atomCount).filterMap (tagEntry result fuel)

def fullRows (result : ChemistryNormalizationResult) (fuel : Nat) : List StereoAssignment :=
  (List.range result.parsed.atomCount).filterMap (fullEntry result fuel)

def residualRows (result : ChemistryNormalizationResult) (fuel : Nat) : List StereoAssignment :=
  (List.range result.parsed.atomCount).filterMap (residualEntry result fuel)

theorem actual_tag_written_four (result : ChemistryNormalizationResult)
    (domain : FirstZTagDomain result.parsed) (index : Nat) (spec : AtomSpec)
    (parity : TetrahedralInputParity) (observed : result.parsed.atomAt? index = some spec)
    (tagged : spec.tetrahedral? = some parity) :
    ((materialized result).writtenNeighbors index).length = 4 :=
  (actual_materialized_legacy_intake result domain index spec parity observed tagged).four

/-- The four-neighbor theorem discharges the separate public extended-carrier guard. -/
theorem actual_tag_public_row (result : ChemistryNormalizationResult)
    (domain : FirstZTagDomain result.parsed) (fuel index : Nat) (spec : AtomSpec)
    (parity : TetrahedralInputParity) (observed : result.parsed.atomAt? index = some spec)
    (tagged : spec.tetrahedral? = some parity) :
    tetrahedralAssignment? result (materialized result) (computedState result fuel) fuel index =
      some (tagRow result fuel index parity) := by
  have lookup := actual_discovered_tag result domain fuel index spec parity observed tagged
  have notExtended := isExtendedTetrahedralParityCarrier_eq_false_of_writtenNeighbors_length_eq_four
    (materialized result) index (actual_tag_written_four result domain index spec parity observed tagged)
  simp [tetrahedralAssignment?, annotatedTetrahedralAssignment?, annotatedTetrahedralOutcome?,
    observed, tagged, notExtended, computedState, lookup, rawDescriptorFactOutcome, seedFact, tagRow]


-- unannotated_outcome_only_refusals is re-exported from NativeFamilyReportRawHelpers.


-- residual_entry_only_refusals is re-exported from NativeFamilyReportRawHelpers.


-- residual_entry_unassigned is re-exported from NativeFamilyReportRawHelpers.


theorem actual_tetrahedral_entry (result : ChemistryNormalizationResult)
    (domain : FirstZTagDomain result.parsed) (fuel index : Nat) :
    tetrahedralAssignment? result (materialized result) (computedState result fuel) fuel index =
      fullEntry result fuel index := by
  cases observed : result.parsed.atomAt? index with
  | none => simp [tetrahedralAssignment?, fullEntry, observed]
  | some spec =>
      cases tagged : spec.tetrahedral? with
      | none => simp [tetrahedralAssignment?, fullEntry, residualEntry, observed, tagged]
      | some parity =>
          simpa [fullEntry, observed, tagged] using
            actual_tag_public_row result domain fuel index spec parity observed tagged

/-- Exact full tetrahedral segment, preserving every interleaved actual refusal row. -/
theorem actual_full_tetrahedral_report (result : ChemistryNormalizationResult)
    (domain : FirstZTagDomain result.parsed) (fuel : Nat) :
    tetrahedralAssignments result (materialized result) (computedState result fuel) fuel =
      fullRows result fuel := by
  unfold tetrahedralAssignments fullRows
  apply congrArg (fun entry => (List.range result.parsed.atomCount).filterMap entry)
  funext index
  exact actual_tetrahedral_entry result domain fuel index

private theorem filter_full_entries_eq_tags (result : ChemistryNormalizationResult)
    (fuel : Nat) (indices : List Nat) :
    ((indices.filterMap (fullEntry result fuel)).filter fun assignment =>
      assignment.outcome.assigned) = indices.filterMap (tagEntry result fuel) := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      cases observed : result.parsed.atomAt? index with
      | none => simp [fullEntry, tagEntry, observed, ih]
      | some spec =>
          cases tagged : spec.tetrahedral? with
          | some parity =>
              simp [fullEntry, tagEntry, observed, tagged, tagRow, StereoOutcome.assigned]
              simpa only [StereoOutcome.assigned] using ih
          | none =>
              cases residual : residualEntry result fuel index with
              | none => simp [fullEntry, tagEntry, observed, tagged, residual, ih]
              | some assignment =>
                  have unassigned := residual_entry_unassigned result fuel index assignment residual
                  simp [fullEntry, tagEntry, observed, tagged, residual, unassigned, ih]

theorem actual_assigned_projection (result : ChemistryNormalizationResult)
    (domain : FirstZTagDomain result.parsed) (fuel : Nat) :
    (tetrahedralAssignments result (materialized result) (computedState result fuel) fuel).filter
      (fun assignment => assignment.outcome.assigned) = tagRows result fuel := by
  rw [actual_full_tetrahedral_report result domain fuel]
  exact filter_full_entries_eq_tags result fuel _

theorem residual_rows_only_refusals (result : ChemistryNormalizationResult) (fuel : Nat)
    (assignment : StereoAssignment) (retained : assignment ∈ residualRows result fuel) :
    assignment.outcome = .refused .notSpecified ∨ assignment.outcome = .refused .rankingUnresolved := by
  obtain ⟨index, _, computed⟩ := List.mem_filterMap.mp retained
  exact (residual_entry_only_refusals result fuel index assignment computed).2

theorem full_rows_unassigned_only_refusals (result : ChemistryNormalizationResult) (fuel : Nat)
    (assignment : StereoAssignment) (retained : assignment ∈ fullRows result fuel)
    (unassigned : assignment.outcome.assigned = false) :
    assignment.outcome = .refused .notSpecified ∨ assignment.outcome = .refused .rankingUnresolved := by
  obtain ⟨index, _, computed⟩ := List.mem_filterMap.mp retained
  cases observed : result.parsed.atomAt? index with
  | none => simp [fullEntry, observed] at computed
  | some spec =>
      cases tagged : spec.tetrahedral? with
      | none =>
          have residual : residualEntry result fuel index = some assignment := by
            simpa [fullEntry, observed, tagged] using computed
          exact (residual_entry_only_refusals result fuel index assignment residual).2
      | some parity =>
          have equal : tagRow result fuel index parity = assignment := by
            simpa [fullEntry, observed, tagged] using computed
          rw [← equal] at unassigned
          simp [tagRow, StereoOutcome.assigned] at unassigned

theorem tag_rows_units (result : ChemistryNormalizationResult) (fuel : Nat) :
    (tagRows result fuel).map StereoAssignment.unit =
      (rawAnnotatedCenters result).map StereoUnit.tetrahedral := by
  unfold tagRows rawAnnotatedCenters
  generalize List.range result.parsed.atomCount = indices
  induction indices with
  | nil => rfl
  | cons index rest ih =>
      cases observed : result.parsed.atomAt? index with
      | none => simp [tagEntry, observed, ih]
      | some spec =>
          cases tagged : spec.tetrahedral? <;>
            simp [tagEntry, observed, tagged, tagRow, ih]

theorem assigned_row_count (result : ChemistryNormalizationResult)
    (domain : FirstZTagDomain result.parsed) (fuel : Nat) :
    ((tetrahedralAssignments result (materialized result) (computedState result fuel) fuel).filter
      fun assignment => assignment.outcome.assigned).length = (rawAnnotatedCenters result).length := by
  rw [actual_assigned_projection result domain fuel]
  simpa only [List.length_map] using congrArg List.length (tag_rows_units result fuel)

/-- Ordinary source-input records are transported to the actual zero-demand materialized owner. -/
def materializedSourceInput (result : ChemistryNormalizationResult)
    (domain : FirstZTagDomain result.parsed) (input : OrdinarySourceInput result.parsed) :
    OrdinarySourceInput (materialized result) := by
  rw [materialized, zero_demand_expansion_exact_record result.parsed domain.zero domain.written]
  refine ⟨materialized_well_formed result.parsed input.well,
    materialized_record_written_exact result.parsed domain.written, ?_, input.single⟩
  intro spec retained
  change spec ∈ result.parsed.atoms.map materializedAtomSpec at retained
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp retained
  exact input.known original originalMember

def familySource (result : ChemistryNormalizationResult) : AuthoritativeChemicalInput :=
  ownSource (materialized result)

def familyAgreement (result : ChemistryNormalizationResult) (domain : FirstZTagDomain result.parsed)
    (input : OrdinarySourceInput result.parsed) :
    SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement.RawAnnotationAgreement
      (materialized result) (familySource result) :=
  actual_annotation_agreement (materialized result) (materializedSourceInput result domain input)

def tagCenter (result : ChemistryNormalizationResult) (domain : FirstZTagDomain result.parsed)
    (input : OrdinarySourceInput result.parsed) (index : Nat) (spec : AtomSpec)
    (parity : TetrahedralInputParity) (observed : result.parsed.atomAt? index = some spec)
    (tagged : spec.tetrahedral? = some parity) :
    (familySource result).AromaticCanonicalTetrahedralCenter := by
  let intake := actual_materialized_legacy_intake result domain index spec parity observed tagged
  have bound : index < (materialized result).atomCount :=
    listGet?_eq_some_implies_lt (materialized result).atoms index (materializedAtomSpec spec) intake.observed
  exact actualCenter (materialized result) (materializedSourceInput result domain input)
    ⟨index, bound⟩ (materializedAtomSpec spec) intake.observed
    ((centreElementSupported_iff_connectivityOnlyTetrahedralElement
      (materializedAtomSpec spec).element).mp intake.supported) intake.four

@[simp] theorem tagCenter_index (result : ChemistryNormalizationResult)
    (domain : FirstZTagDomain result.parsed) (input : OrdinarySourceInput result.parsed)
    (index : Nat) (spec : AtomSpec) (parity : TetrahedralInputParity)
    (observed : result.parsed.atomAt? index = some spec) (tagged : spec.tetrahedral? = some parity) :
    (tagCenter result domain input index spec parity observed tagged).1.val = index := rfl

/-- Every actual tagged public label agrees with the same constructed source's OWN scheduled model. -/
theorem actual_tag_public_own_source_model (result : ChemistryNormalizationResult)
    (domain : FirstZTagDomain result.parsed) (input : OrdinarySourceInput result.parsed)
    (carrierFuel fuel index : Nat) (spec : AtomSpec) (parity : TetrahedralInputParity)
    (observed : result.parsed.atomAt? index = some spec) (tagged : spec.tetrahedral? = some parity) :
    tetrahedralAssignment? result (materialized result) (computedState result fuel) fuel index =
      some (tagRow result fuel index parity) ∧
    FirstZSourceDiscoveryAlignmentProofs.FirstZSourceDiscoveryAlignment.ownState result domain (familySource result)
      (familyAgreement result domain input) carrierFuel
      ((familySource result).aromaticCanonicalFinalOccurrence carrierFuel
        (tagCenter result domain input index spec parity observed tagged)) =
      some (.chiral (seedDescriptor result fuel index parity)) := by
  let center := tagCenter result domain input index spec parity observed tagged
  have alignment := FirstZSourceDiscoveryAlignmentProofs.FirstZSourceDiscoveryAlignment.actual_discovered_own_model_alignment
    result domain (familySource result) (familyAgreement result domain input) carrierFuel fuel
    center spec observed parity tagged (fun bond retained _ => input.single bond retained)
    (actual_source_no_double (materialized result) (materializedSourceInput result domain input))
  exact ⟨actual_tag_public_row result domain fuel index spec parity observed tagged, alignment.2.1⟩

private theorem filterMap_nil_of_none {Alpha Beta : Type*} (values : List Alpha)
    (f : Alpha → Option Beta) (absent : ∀ value ∈ values, f value = none) :
    values.filterMap f = [] := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
      have tail : ∀ value ∈ rest, f value = none :=
        fun value retained => absent value (List.mem_cons_of_mem first retained)
      simp only [List.filterMap_cons, absent first (by simp)]
      exact ih tail

-- single_double_neighbors_nil is re-exported from NativeFamilyReportRawHelpers.


-- single_extended_chains_nil is re-exported from NativeFamilyReportRawHelpers.


-- single_stereobond_assignments_nil is re-exported from NativeFamilyReportRawHelpers.


-- normalize_single_identity is re-exported from NativeFamilyReportRawHelpers.


theorem actual_other_four_segments_nil (raw : RawMolecule)
    (domain : FirstZTagDomain (normalizeRawMolecule raw).parsed)
    (input : OrdinarySourceInput (normalizeRawMolecule raw).parsed) :
    let branches := normalizedStereoAnalysisBranches (normalizeRawMolecule raw)
    branches.ordinaryDoubleBond = [] ∧ branches.coupledDoubleBond = [] ∧
      branches.oddCumuleneDoubleBond = [] ∧ branches.extendedAxial = [] := by
  have ordinary : (normalizeRawMolecule raw).stereobonds.doubleBondAssignments = [] :=
    single_stereobond_assignments_nil (normalizeRawMolecule raw).parsed input.single
  have chains := single_extended_chains_nil (normalizeRawMolecule raw).parsed input.single
  have expandedSingle : ∀ bond ∈ (materialized (normalizeRawMolecule raw)).bonds,
      bond.kind = .single :=
    (materializedSourceInput (normalizeRawMolecule raw) domain input).single
  have expandedChains :=
    single_extended_chains_nil (materialized (normalizeRawMolecule raw)) expandedSingle
  have carriers : (normalizeRawMolecule raw).parsed.withExplicitHydrogens.extendedTetrahedralParityCarriers = [] := by
    change (materialized (normalizeRawMolecule raw)).extendedTetrahedralParityCarriers = []
    simp [extendedTetrahedralParityCarriers, expandedChains]
  simp [normalizedStereoAnalysisBranches, ordinaryDoubleBondAssignments,
    oddCumuleneDoubleBondAssignments, ordinary, chains, carriers]

/-- Full actual five-segment analyzer: independently admitted records discharge the guards;
all actual untagged rows remain in fullRows and only observed tags survive assigned projection. -/
theorem actual_normalized_whole_report (raw : RawMolecule)
    (domain : FirstZTagDomain (normalizeRawMolecule raw).parsed)
    (input : OrdinarySourceInput (normalizeRawMolecule raw).parsed)
    (admitted : (normalizeRawMolecule raw).parsed.StereochemicalAdmissible)
    (masses : (normalizeRawMolecule raw).parsed.Rule2MassesKnown) :
    let result := normalizeRawMolecule raw
    let fuel := analysisFuel (materialized result)
    analyzeNormalized result = fullRows result fuel ∧
      ((analyzeNormalized result).filter fun assignment => assignment.outcome.assigned) = tagRows result fuel ∧
      (tagRows result fuel).map StereoAssignment.unit =
        (rawAnnotatedCenters result).map StereoUnit.tetrahedral := by
  let result := normalizeRawMolecule raw
  let fuel := analysisFuel (materialized result)
  have known : result.parsed.rule2MassesKnown? = true :=
    result.parsed.rule2MassesKnown?_eq_true_iff.mpr masses
  have expanded : result.expandedStereochemicalAdmissible? = true :=
    result.expandedStereochemicalAdmissible?_eq_true_iff.mpr
      (result.parsed.withExplicitHydrogens_preserves_stereochemicalAdmissible admitted)
  obtain ⟨ordinary, coupled, cumulene, axial⟩ := actual_other_four_segments_nil raw domain input
  have tetra := actual_full_tetrahedral_report result domain fuel
  have ordinaryResult : (normalizedStereoAnalysisBranches result).ordinaryDoubleBond = [] := ordinary
  have coupledResult : (normalizedStereoAnalysisBranches result).coupledDoubleBond = [] := coupled
  have cumuleneResult : (normalizedStereoAnalysisBranches result).oddCumuleneDoubleBond = [] := cumulene
  have axialResult : (normalizedStereoAnalysisBranches result).extendedAxial = [] := axial
  have tetraResult : (normalizedStereoAnalysisBranches result).tetrahedral = fullRows result fuel := by
    change tetrahedralAssignments result (materialized result) (computedState result fuel) fuel = _
    exact tetra
  have full : analyzeNormalized result = fullRows result fuel := by
    unfold analyzeNormalized
    rw [known, expanded]
    change (normalizedStereoAnalysisBranches result).tetrahedral ++
      (normalizedStereoAnalysisBranches result).ordinaryDoubleBond ++
      (normalizedStereoAnalysisBranches result).coupledDoubleBond ++
      (normalizedStereoAnalysisBranches result).oddCumuleneDoubleBond ++
      (normalizedStereoAnalysisBranches result).extendedAxial = fullRows result fuel
    rw [ordinaryResult, coupledResult, cumuleneResult, axialResult]
    simpa only [List.append_nil] using tetraResult
  refine ⟨full, ?_, tag_rows_units result fuel⟩
  rw [full]
  exact filter_full_entries_eq_tags result fuel _

/-- General integrated software/source report target. It applies to arbitrary finite tag counts,
preserves all actual refusal rows, derives the complete assigned projection, and internally
constructs the SAME source/center/model for every observed tag. Positive-size generator, parser,
compiler/export and the dependency kernel gates remain separate obligations. -/
theorem actual_normalized_report_and_own_source (raw : RawMolecule)
    (domain : FirstZTagDomain (normalizeRawMolecule raw).parsed)
    (input : OrdinarySourceInput (normalizeRawMolecule raw).parsed)
    (admitted : (normalizeRawMolecule raw).parsed.StereochemicalAdmissible)
    (masses : (normalizeRawMolecule raw).parsed.Rule2MassesKnown) (carrierFuel : Nat) :
    let result := normalizeRawMolecule raw
    let fuel := analysisFuel (materialized result)
    analyzeNormalized result = fullRows result fuel ∧
      ((analyzeNormalized result).filter fun assignment => assignment.outcome.assigned) = tagRows result fuel ∧
      (tagRows result fuel).map StereoAssignment.unit =
        (rawAnnotatedCenters result).map StereoUnit.tetrahedral ∧
      (∀ assignment ∈ analyzeNormalized result, assignment.outcome.assigned = false →
        assignment.outcome = .refused .notSpecified ∨ assignment.outcome = .refused .rankingUnresolved) ∧
      (∀ index spec parity (observed : result.parsed.atomAt? index = some spec)
        (tagged : spec.tetrahedral? = some parity),
        FirstZSourceDiscoveryAlignmentProofs.FirstZSourceDiscoveryAlignment.ownState result domain (familySource result)
          (familyAgreement result domain input) carrierFuel
          ((familySource result).aromaticCanonicalFinalOccurrence carrierFuel
            (tagCenter result domain input index spec parity observed tagged)) =
          some (.chiral (seedDescriptor result fuel index parity))) := by
  let result := normalizeRawMolecule raw
  let fuel := analysisFuel (materialized result)
  obtain ⟨full, assigned, units⟩ := actual_normalized_whole_report raw domain input admitted masses
  refine ⟨full, assigned, units, ?_, ?_⟩
  · intro assignment retained unassigned
    rw [full] at retained
    exact full_rows_unassigned_only_refusals result fuel assignment retained unassigned
  · intro index spec parity observed tagged
    exact (actual_tag_public_own_source_model result domain input carrierFuel fuel index spec
      parity observed tagged).2

end TetraStereo.UniversalProof.ActualFamilyReportBridgeProofs.ActualFamilyReportBridge
