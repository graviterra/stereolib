import TetraStereo.UniversalProof.NativeFamilyRawSupport
import TetraStereo.UniversalProof.GeneralParserStateBridge
import TetraStereo.UniversalProof.NativeFamilyRawSupportProofs.PositiveFamilyGeneratorRecovery

set_option autoImplicit false

namespace TetraStereo.UniversalProof.ChronologicalFamilyRuntimeSourceBridge

open TetraStereo.OneCenter
open TetraStereo.UniversalProof.GeneralParserStateBridge
open TetraStereo.UniversalProof.ExplicitHydrogenExpansionIdentityProofs.ExplicitHydrogenExpansionIdentity










def blockAtoms (parity : TetrahedralInputParity) : List AtomSpec :=
  [atomSpec .carbon, atomSpec .hydrogen, atomSpec (.taggedCarbon parity),
    atomSpec .hydrogen, atomSpec .fluorine, atomSpec .bromine]

def blocksAtoms : List TetrahedralInputParity → List AtomSpec
  | [] => []
  | parity :: rest => blockAtoms parity ++ blocksAtoms rest

theorem blockResult_atoms (state : ParseState) (parent : ℕ)
    (parity : TetrahedralInputParity) :
    (blockResult state parent parity).atoms = state.atoms ++ blockAtoms parity := by
  simp only [blockResult, pendantBranchResult, singleBranchResult, attachSingle,
    blockAtoms, List.append_assoc, List.cons_append, List.nil_append]

theorem blocksResult_atoms (parities : List TetrahedralInputParity)
    (state : ParseState) (parent : ℕ) :
    (blocksResult parities state parent).atoms = state.atoms ++ blocksAtoms parities := by
  induction parities generalizing state parent with
  | nil => exact (List.append_nil state.atoms).symm
  | cons parity rest ih =>
      rw [blocksResult, ih, blockResult_atoms, blocksAtoms, List.append_assoc]

theorem familyRaw_atoms (parities : List TetrahedralInputParity) :
    (familyRaw parities).atoms =
      ([atomSpec .hydrogen] ++ blocksAtoms parities) ++ [atomSpec .hydrogen] := by
  change (blocksResult parities initialHydrogenState 0).atoms ++ [atomSpec .hydrogen] = _
  rw [blocksResult_atoms]
  simp only [initialHydrogenState]

theorem blockAtoms_origin (parity : TetrahedralInputParity) (atom : AtomSpec)
    (membership : atom ∈ blockAtoms parity) :
    ∃ kind : FamilyAtom, atom = atomSpec kind := by
  simp only [blockAtoms, List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨.carbon, rfl⟩
  · exact ⟨.hydrogen, rfl⟩
  · exact ⟨.taggedCarbon parity, rfl⟩
  · exact ⟨.hydrogen, rfl⟩
  · exact ⟨.fluorine, rfl⟩
  · exact ⟨.bromine, rfl⟩

theorem blocksAtoms_origin (parities : List TetrahedralInputParity) (atom : AtomSpec)
    (membership : atom ∈ blocksAtoms parities) :
    ∃ kind : FamilyAtom, atom = atomSpec kind := by
  induction parities with
  | nil => cases membership
  | cons parity rest ih =>
      rcases List.mem_append.mp membership with current | remaining
      · exact blockAtoms_origin parity atom current
      · exact ih remaining

theorem familyRaw_atom_origin (parities : List TetrahedralInputParity) (atom : AtomSpec)
    (membership : atom ∈ (familyRaw parities).atoms) :
    ∃ kind : FamilyAtom, atom = atomSpec kind := by
  rw [familyRaw_atoms] at membership
  rcases List.mem_append.mp membership with earlier | trailing
  · rcases List.mem_append.mp earlier with leading | blocks
    · exact ⟨.hydrogen, List.mem_singleton.mp leading⟩
    · exact blocksAtoms_origin parities atom blocks
  · exact ⟨.hydrogen, List.mem_singleton.mp trailing⟩

-- atomSpec_known_element is re-exported from NativeFamilyRawSupport.


-- atomSpec_mass_known is re-exported from NativeFamilyRawSupport.


theorem familyRaw_known_elements (parities : List TetrahedralInputParity) :
    ∀ atom ∈ (familyRaw parities).atoms, atom.element ≠ .wildcard := by
  intro atom membership
  obtain ⟨kind, rfl⟩ := familyRaw_atom_origin parities atom membership
  exact atomSpec_known_element kind

theorem familyRaw_mass_known (parities : List TetrahedralInputParity) :
    (familyRaw parities).Rule2MassesKnown := by
  intro atom membership
  obtain ⟨kind, rfl⟩ := familyRaw_atom_origin parities atom membership
  exact atomSpec_mass_known kind

theorem familyRaw_inline_counts (parities : List TetrahedralInputParity) :
    InlineCountsNormalized (familyRaw parities) := by
  intro atom membership
  obtain ⟨kind, rfl⟩ := familyRaw_atom_origin parities atom membership
  exact family_atom_explicit_hydrogens_zero kind

theorem familyRaw_zero_demand (parities : List TetrahedralInputParity) :
    ZeroHydrogenDemand (familyRaw parities) :=
  normalized_inline_counts_zero_demand _ (familyRaw_inline_counts parities)

theorem familyRaw_first_tag (parity : TetrahedralInputParity)
    (remaining : List TetrahedralInputParity) :
    (familyRaw (parity :: remaining)).atomAt? 3 = some (atomSpec (.taggedCarbon parity)) := by
  change listGet? (familyRaw (parity :: remaining)).atoms 3 = _
  calc
    listGet? (familyRaw (parity :: remaining)).atoms 3 =
        listGet? ([atomSpec .hydrogen] ++ blocksAtoms (parity :: remaining) ++
          [atomSpec .hydrogen]) 3 := congrArg (fun atoms => listGet? atoms 3) (familyRaw_atoms _)
    _ = some (atomSpec (.taggedCarbon parity)) := rfl

theorem familyRaw_actual_tag_nonempty (parities : List TetrahedralInputParity)
    (positive : parities ≠ []) :
    ∃ index spec parity, (familyRaw parities).atomAt? index = some spec ∧
      spec.tetrahedral? = some parity := by
  cases parities with
  | nil => exact False.elim (positive rfl)
  | cons parity remaining =>
      exact ⟨3, atomSpec (.taggedCarbon parity), parity,
        familyRaw_first_tag parity remaining, rfl⟩

/-- Current is the most recently appended backbone. This exact allocation formula is useful
for proving that later blocks never touch a previous tagged row. -/
theorem blocksParent_closed (parities : List TetrahedralInputParity)
    (state : ParseState) (parent : ℕ) :
    blocksParent parities state parent =
      match parities with
      | [] => parent
      | _ :: rest => state.atoms.length + 6 * rest.length := by
  induction parities generalizing state parent with
  | nil => rfl
  | cons parity rest ih =>
      rw [blocksParent, ih]
      cases rest with
      | nil => rfl
      | cons next remaining =>
          rw [blockResult_atom_count]
          change state.atoms.length + 6 + 6 * remaining.length =
            state.atoms.length + 6 * (remaining.length + 1)
          omega

/-- These are the two independent PHYSICAL obligations still awaiting family-wide derivation.
There is no state, frame, ranking, label, report, normalization or parse-success conclusion here. -/
structure RemainingPhysicalRecords (parities : List TetrahedralInputParity) : Prop where
  written : (familyRaw parities).WrittenNeighborExact
  sites : ∀ index spec parity, (familyRaw parities).atomAt? index = some spec →
    spec.tetrahedral? = some parity →
    Nonempty (NativeInitialSeedRuntimeSupportProofsLibrary.GeneratedPendantOccurrenceRecovery.PendantSite (familyRaw parities) index) ∧
      spec.element = .C

theorem familyRaw_first_z_domain_of_records (parities : List TetrahedralInputParity)
    (positive : parities ≠ []) (physical : RemainingPhysicalRecords parities) :
    FirstZSeedDiscoveryRecoveryProofs.FirstZSeedDiscoveryRecovery.FirstZTagDomain (familyRaw parities) :=
  FirstZSeedDiscoveryRecoveryProofs.FirstZSeedDiscoveryRecovery.domain_of_pendant_records (familyRaw parities)
    (familyRaw_admissible parities).1 physical.written (familyRaw_zero_demand parities)
    physical.sites (familyRaw_actual_tag_nonempty parities positive)

/-- Intermediate physical guard adapter. Full written adjacency is still to be derived for
the chronological family; it is never silently supplied as a completed final family premise. -/
theorem familyRaw_ordinary_source_input_of_written (parities : List TetrahedralInputParity)
    (written : (familyRaw parities).WrittenNeighborExact) :
    NativeOrdinarySourceInputProofs.SourceInputPremiseRecovery.OrdinarySourceInput (familyRaw parities) :=
  ⟨(familyRaw_admissible parities).1, written, familyRaw_known_elements parities,
    familyRaw_all_single parities⟩

theorem family_normalized_parsed (parities : List TetrahedralInputParity) :
    (normalizeRawMolecule (familyRaw parities)).parsed = familyRaw parities :=
  familyRaw_normalize_eq parities

theorem family_normalized_mass_known (parities : List TetrahedralInputParity) :
    (normalizeRawMolecule (familyRaw parities)).parsed.Rule2MassesKnown := by
  rw [family_normalized_parsed]
  exact familyRaw_mass_known parities

theorem family_normalized_zero_demand (parities : List TetrahedralInputParity) :
    ZeroHydrogenDemand (normalizeRawMolecule (familyRaw parities)).parsed := by
  rw [family_normalized_parsed]
  exact familyRaw_zero_demand parities

theorem family_normalized_domain_of_records (parities : List TetrahedralInputParity)
    (positive : parities ≠ []) (physical : RemainingPhysicalRecords parities) :
    FirstZSeedDiscoveryRecoveryProofs.FirstZSeedDiscoveryRecovery.FirstZTagDomain
      (normalizeRawMolecule (familyRaw parities)).parsed := by
  rw [family_normalized_parsed]
  exact familyRaw_first_z_domain_of_records parities positive physical

theorem family_normalized_source_input_of_records (parities : List TetrahedralInputParity)
    (physical : RemainingPhysicalRecords parities) :
    NativeOrdinarySourceInputProofs.SourceInputPremiseRecovery.OrdinarySourceInput
      (normalizeRawMolecule (familyRaw parities)).parsed := by
  rw [family_normalized_parsed]
  exact familyRaw_ordinary_source_input_of_written parities physical.written

theorem family_normalized_stereo_admissible_of_records (parities : List TetrahedralInputParity)
    (physical : RemainingPhysicalRecords parities) :
    (normalizeRawMolecule (familyRaw parities)).parsed.StereochemicalAdmissible := by
  rw [family_normalized_parsed]
  exact ⟨familyRaw_admissible parities, physical.written⟩

/-- Explicit INTERMEDIATE composition:535 written adjacency and538 physical sites must still
inhabit RemainingPhysicalRecords internally. This is not claimed as unconditional family closure. -/
theorem pending_physical_whole_report_composition (parities : List TetrahedralInputParity)
    (positive : parities ≠ []) (physical : RemainingPhysicalRecords parities) :
    let result := normalizeRawMolecule (familyRaw parities)
    let fuel := analysisFuel (FirstZSeedDiscoveryRecoveryProofs.FirstZSeedDiscoveryRecovery.materialized result)
    analyzeNormalized result = ActualFamilyReportBridgeProofs.ActualFamilyReportBridge.fullRows result fuel ∧
      ((analyzeNormalized result).filter fun assignment => assignment.outcome.assigned) =
        ActualFamilyReportBridgeProofs.ActualFamilyReportBridge.tagRows result fuel ∧
      (ActualFamilyReportBridgeProofs.ActualFamilyReportBridge.tagRows result fuel).map StereoAssignment.unit =
        (rawAnnotatedCenters result).map StereoUnit.tetrahedral :=
  ActualFamilyReportBridgeProofs.ActualFamilyReportBridge.actual_normalized_whole_report (familyRaw parities)
    (family_normalized_domain_of_records parities positive physical)
    (family_normalized_source_input_of_records parities physical)
    (family_normalized_stereo_admissible_of_records parities physical)
    (family_normalized_mass_known parities)

theorem actual_family_string_normalization (parities : List TetrahedralInputParity) :
    parseAndNormalizeOpenSMILES (familyString parities) =
      Except.ok (normalizeRawMolecule (familyRaw parities)) := by
  unfold parseAndNormalizeOpenSMILES
  rw [parse_family_string]
  rfl



theorem pending_physical_whole_report_and_own_source (parities : List TetrahedralInputParity)
    (positive : parities ≠ []) (physical : RemainingPhysicalRecords parities) (carrierFuel : ℕ) :
    let result := normalizeRawMolecule (familyRaw parities)
    let domain := family_normalized_domain_of_records parities positive physical
    let input := family_normalized_source_input_of_records parities physical
    let fuel := analysisFuel (FirstZSeedDiscoveryRecoveryProofs.FirstZSeedDiscoveryRecovery.materialized result)
    analyzeNormalized result = ActualFamilyReportBridgeProofs.ActualFamilyReportBridge.fullRows result fuel ∧
      ((analyzeNormalized result).filter fun assignment => assignment.outcome.assigned) =
        ActualFamilyReportBridgeProofs.ActualFamilyReportBridge.tagRows result fuel ∧
      (ActualFamilyReportBridgeProofs.ActualFamilyReportBridge.tagRows result fuel).map StereoAssignment.unit =
        (rawAnnotatedCenters result).map StereoUnit.tetrahedral ∧
      (∀ assignment ∈ analyzeNormalized result, assignment.outcome.assigned = false →
        assignment.outcome = .refused .notSpecified ∨ assignment.outcome = .refused .rankingUnresolved) ∧
      (∀ index spec parity (observed : result.parsed.atomAt? index = some spec)
        (tagged : spec.tetrahedral? = some parity),
        FirstZSourceDiscoveryAlignmentProofs.FirstZSourceDiscoveryAlignment.ownState result domain
          (ActualFamilyReportBridgeProofs.ActualFamilyReportBridge.familySource result)
          (ActualFamilyReportBridgeProofs.ActualFamilyReportBridge.familyAgreement result domain input) carrierFuel
          ((ActualFamilyReportBridgeProofs.ActualFamilyReportBridge.familySource result).aromaticCanonicalFinalOccurrence
            carrierFuel (ActualFamilyReportBridgeProofs.ActualFamilyReportBridge.tagCenter result domain input index spec
              parity observed tagged)) = some (.chiral
                (FirstZSeedDiscoveryRecoveryProofs.FirstZSeedDiscoveryRecovery.seedDescriptor result fuel index parity))) :=
  ActualFamilyReportBridgeProofs.ActualFamilyReportBridge.actual_normalized_report_and_own_source (familyRaw parities)
    (family_normalized_domain_of_records parities positive physical)
    (family_normalized_source_input_of_records parities physical)
    (family_normalized_stereo_admissible_of_records parities physical)
    (family_normalized_mass_known parities) carrierFuel

/-- Explicit INTERMEDIATE authority wrapper: full written adjacency and physical valence still
must be derived for this family, not assumed to discharge an unconditional family claim. -/
def pendingCertifiedFromPhysicalRecords (parities : List TetrahedralInputParity)
    (physical : RemainingPhysicalRecords parities) (valence : (familyRaw parities).ValenceOK) :
    CertifiedChemistryNormalizationResult where
  result := normalizeRawMolecule (familyRaw parities)
  admissible := (family_normalized_stereo_admissible_of_records parities physical).1
  writtenNeighborExact := (family_normalized_stereo_admissible_of_records parities physical).2
  valenceOK := by rw [family_normalized_parsed]; exact valence
  rule2MassesKnown := family_normalized_mass_known parities

theorem pending_actual_certified_normalization (parities : List TetrahedralInputParity)
    (physical : RemainingPhysicalRecords parities) (valence : (familyRaw parities).ValenceOK) :
    normalizeRawMoleculeCertified? (familyRaw parities) =
      some (pendingCertifiedFromPhysicalRecords parities physical valence) := by
  have introduction :
      (normalizeRawMolecule (familyRaw parities)).parsed.introductionPredecessorsValid? = true := by
    rw [family_normalized_parsed]
    have valid := familyRaw_introduction_valid parities
    simp only [RawMolecule.parserIntroductionValid?, Bool.and_eq_true] at valid
    exact valid.2
  have admission : (normalizeRawMolecule (familyRaw parities)).parsed.admissible? = true :=
    (RawMolecule.admissible?_eq_true_iff _).mpr
      (family_normalized_stereo_admissible_of_records parities physical).1
  have written : (normalizeRawMolecule (familyRaw parities)).parsed.writtenNeighborExact? = true :=
    (RawMolecule.writtenNeighborExact?_eq_true_iff _).mpr
      (family_normalized_stereo_admissible_of_records parities physical).2
  have actualValence : (normalizeRawMolecule (familyRaw parities)).parsed.ValenceOK := by
    rw [family_normalized_parsed]
    exact valence
  have valenceCheck : (normalizeRawMolecule (familyRaw parities)).parsed.valenceOK? = true :=
    (RawMolecule.valenceOK?_eq_true_iff _).mpr actualValence
  have masses : (normalizeRawMolecule (familyRaw parities)).parsed.rule2MassesKnown? = true :=
    (RawMolecule.rule2MassesKnown?_eq_true_iff _).mpr (family_normalized_mass_known parities)
  unfold normalizeRawMoleculeCertified? ChemistryNormalizationResult.certify?
    pendingCertifiedFromPhysicalRecords
  rw [if_pos introduction, dif_pos admission, dif_pos written, dif_pos valenceCheck, dif_pos masses]

/-- Actual STRING certified intake composition, with precisely two independent physical
records and the encoded valence bound remaining. No caller intake/result equation is accepted. -/
theorem pending_actual_certified_string_intake (parities : List TetrahedralInputParity)
    (physical : RemainingPhysicalRecords parities) (valence : (familyRaw parities).ValenceOK) :
    parseAndNormalizeOpenSMILESCertified (familyString parities) =
      Except.ok (pendingCertifiedFromPhysicalRecords parities physical valence) := by
  unfold parseAndNormalizeOpenSMILESCertified
  rw [actual_family_string_normalization]
  have certified : (normalizeRawMolecule (familyRaw parities)).certify? =
      some (pendingCertifiedFromPhysicalRecords parities physical valence) :=
    pending_actual_certified_normalization parities physical valence
  change (match (normalizeRawMolecule (familyRaw parities)).certify? with
    | some output => Except.ok output
    | none => Except.error "normalized molecule failed structural, valence, or Rule-2 mass admission") = _
  rw [certified]

end TetraStereo.UniversalProof.ChronologicalFamilyRuntimeSourceBridge
