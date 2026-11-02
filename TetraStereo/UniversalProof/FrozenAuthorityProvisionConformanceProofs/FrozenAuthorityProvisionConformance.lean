import TetraStereo.UniversalProof.FrozenRule2DataSemanticsProofs.FrozenRule2DataSemantics
import TetraStereo.OneCenter.IUPACRemaining71P94AuthorityProductionAdapter
import TetraStereo.OneCenter.IUPACNormativeCoveragePartition

set_option autoImplicit false
set_option maxRecDepth 8192















































namespace TetraStereo.UniversalProof.FrozenAuthorityProvisionConformanceProofs.FrozenAuthorityProvisionConformance

open TetraStereo.OneCenter
open TetraStereo.OneCenter.IUPACNormativeProvision
open TetraStereo.OneCenter.CIPRule2MassData
open TetraStereo.UniversalProof.FrozenRule2DataSemanticsProofs.FrozenRule2DataSemantics

/-! ## New independent references over the actual observation types -/

/-- Independent periodic admission: the frozen 1--118 range law, not the generated lookup
membership.  Observation type is the actual `PeriodicAtomicNumberAuthorityObservation`. -/
def independentPeriodicAtomicNumbersReference : ProvisionReference where
  Observation := PeriodicAtomicNumberAuthorityObservation
  Applicable := fun _source =>
    ∃ observation : PeriodicAtomicNumberAuthorityObservation,
      PeriodicTableAdmits observation.atomicNumber
  Judges := fun _source observation => PeriodicTableAdmits observation.atomicNumber

/-- Independent CIAAW standard-weight admission: membership of the three-variant source record,
preserving interval, value-with-uncertainty and explicit unavailability.  This is *not* the
ordinary Rule-2 scalar policy. -/
def independentStandardAtomicWeightsReference : ProvisionReference where
  Observation := StandardAtomicWeightAuthorityObservation
  Applicable := fun _source =>
    ∃ observation : StandardAtomicWeightAuthorityObservation,
      (observation.atomicNumber, observation.entry) ∈ standardWeightRecords
  Judges := fun _source observation =>
    (observation.atomicNumber, observation.entry) ∈ standardWeightRecords

/-- The exact AME record named by an isotope observation. -/
def isotopeRecordOf (observation : IsotopeAtomicMassAuthorityObservation) :
    IsotopeMassRecord :=
  ⟨observation.atomicNumber, observation.massNumber, observation.massPico⟩

/-- Independent isotope admission: membership of the unique-key AME record table, not the composed
supported-nuclide/lookup pair. -/
def independentIsotopeAtomicMassesReference : ProvisionReference where
  Observation := IsotopeAtomicMassAuthorityObservation
  Applicable := fun _source =>
    ∃ observation : IsotopeAtomicMassAuthorityObservation,
      isotopeRecordOf observation ∈ isotopeRecords
  Judges := fun _source observation => isotopeRecordOf observation ∈ isotopeRecords

/-! ## Unrestricted production / independent-judgement bridges -/

/-- The independent range law is exactly current-domain membership. -/
theorem periodicAtomicNumber_production_iff_independent
    (source : AuthoritativeChemicalInput)
    (observation : PeriodicAtomicNumberAuthorityObservation) :
    PeriodicAtomicNumberProductionJudged observation ↔
      independentPeriodicAtomicNumbersReference.Judges source observation := by
  change PeriodicAtomicNumberProductionJudged observation ↔
    PeriodicTableAdmits observation.atomicNumber
  exact mem_currentAtomicNumbers_iff_admits observation.atomicNumber

/-! ### CIAAW domain derivation (no domain premise in the final equivalence)

`entry?` is the frozen 1--118 lookup.  Outside that domain it returns `none` on the first branch
(`z = 0`) and on the final catch-all.  The auxiliary `succN` makes the catch-all reduction explicit:
applying `Nat.succ` 119 times reaches the deepest default, which the kernel reduces to `none`. -/

private def succN : Nat → Nat → Nat
  | 0, m => m
  | Nat.succ n, m => Nat.succ (succN n m)

private theorem succN_eq_add (n m : Nat) : succN n m = n + m := by
  induction n generalizing m with
  | zero => simp [succN]
  | succ k inductionHypothesis =>
      show Nat.succ (succN k m) = Nat.succ k + m
      rw [inductionHypothesis]
      omega

private theorem entry?_succN_none (x : Nat) :
    CIAAWStandardAtomicWeights2021.entry? (succN 119 x) = none := rfl

/-- Out-of-domain failure: above the frozen range the lookup is `none`. -/
theorem entry?_eq_none_of_gt (z : Nat) (above : 118 < z) :
    CIAAWStandardAtomicWeights2021.entry? z = none := by
  have hz : z = succN 119 (z - 119) := by
    rw [succN_eq_add]
    omega
  rw [hz]
  exact entry?_succN_none (z - 119)

/-- Out-of-domain failure on any `z` outside the frozen current-atomic-number domain. -/
theorem entry?_eq_none_of_not_current (z : Nat) (absent : z ∉ currentAtomicNumbers) :
    CIAAWStandardAtomicWeights2021.entry? z = none := by
  have notAdmits : ¬ PeriodicTableAdmits z := by
    intro admitted
    exact absent ((mem_currentAtomicNumbers_iff_admits z).mpr admitted)
  have notRange : ¬ (1 ≤ z ∧ z ≤ 118) := by
    simpa [PeriodicTableAdmits] using notAdmits
  have below_or_above : z < 1 ∨ 118 < z := by omega
  rcases below_or_above with below | above
  · have zero : z = 0 := by omega
    subst z
    rfl
  · exact entry?_eq_none_of_gt z above

/-- Success implies domain: a successful CIAAW lookup forces the frozen current domain. -/
theorem entry?_isSome_domain (z : Nat)
    (success : (CIAAWStandardAtomicWeights2021.entry? z).isSome = true) :
    z ∈ currentAtomicNumbers := by
  by_contra absent
  rw [entry?_eq_none_of_not_current z absent] at success
  simp at success

/-- Unrestricted CIAAW standard-weight equivalence.  The frozen current domain is *derived*, not
assumed, so the equivalence holds for every atomic number and every entry. -/
theorem standardAtomicWeight_entry_iff (z : Nat)
    (entry : CIAAWStandardAtomicWeights2021.Entry) :
    CIAAWStandardAtomicWeights2021.entry? z = some entry ↔
      (z, entry) ∈ standardWeightRecords := by
  constructor
  · intro lookup
    have current := entry?_isSome_domain z (by rw [lookup]; rfl)
    exact (standardAtomicWeight_lookup_iff z entry current).mp lookup
  · intro member
    have checked : standardWeightRecords.all
        (fun record => decide (record.1 ∈ currentAtomicNumbers)) = true := by decide
    have current : z ∈ currentAtomicNumbers :=
      of_decide_eq_true (List.all_eq_true.mp checked (z, entry) member)
    exact (standardAtomicWeight_lookup_iff z entry current).mpr member

/-- Unrestricted production / independent-judgement bridge for CIAAW standard weights. -/
theorem standardAtomicWeight_production_iff_independent
    (source : AuthoritativeChemicalInput)
    (observation : StandardAtomicWeightAuthorityObservation) :
    StandardAtomicWeightProductionJudged observation ↔
      independentStandardAtomicWeightsReference.Judges source observation := by
  change StandardAtomicWeightProductionJudged observation ↔
    (observation.atomicNumber, observation.entry) ∈ standardWeightRecords
  exact standardAtomicWeight_entry_iff observation.atomicNumber observation.entry

/-- Unrestricted production / independent-judgement bridge for isotope atomic masses.  Membership
of `supportedNuclides` yields the current domain (via
`every_supported_nuclide_has_current_atomic_number`) and hence the record; record membership yields
the supported-nuclide key and the same mass lookup. -/
theorem isotopeAtomicMass_production_iff_record
    (observation : IsotopeAtomicMassAuthorityObservation) :
    IsotopeAtomicMassProductionJudged observation ↔
      isotopeRecordOf observation ∈ isotopeRecords := by
  constructor
  · rintro ⟨supported, lookup⟩
    have bounds := every_supported_nuclide_has_current_atomic_number
      (observation.atomicNumber, observation.massNumber) supported
    have current : observation.atomicNumber ∈ currentAtomicNumbers :=
      (mem_currentAtomicNumbers_iff_admits observation.atomicNumber).mpr
        ⟨by omega, bounds.2⟩
    exact (isotope_record_iff_lookup observation.atomicNumber observation.massNumber
      observation.massPico current).mpr lookup
  · intro member
    have unpacked := (mem_isotopeRecords_iff (isotopeRecordOf observation)).mp member
    have current : observation.atomicNumber ∈ currentAtomicNumbers := by
      simpa [isotopeRecordOf] using unpacked.1
    have lookup := (isotope_record_iff_lookup observation.atomicNumber observation.massNumber
      observation.massPico current).mp (by simpa [isotopeRecordOf] using member)
    refine ⟨?_, lookup⟩
    exact List.mem_flatMap.mpr
      ⟨observation.atomicNumber, current,
        List.mem_map.mpr
          ⟨(observation.massNumber, observation.massPico),
            by simpa [isotopeRecordOf] using unpacked.2, rfl⟩⟩

/-- Unrestricted production / independent-judgement bridge for isotope atomic masses, phrased over
the actual independent reference. -/
theorem isotopeAtomicMass_production_iff_independent
    (source : AuthoritativeChemicalInput)
    (observation : IsotopeAtomicMassAuthorityObservation) :
    IsotopeAtomicMassProductionJudged observation ↔
      independentIsotopeAtomicMassesReference.Judges source observation := by
  change IsotopeAtomicMassProductionJudged observation ↔
    isotopeRecordOf observation ∈ isotopeRecords
  exact isotopeAtomicMass_production_iff_record observation

/-! ## The separate ordinary Rule-2 policy is not CIAAW standard-weight coverage

`OrdinaryRule2Mass` composes the abridged periodic-table scalar with the explicit reference nuclide.
Hydrogen's CIAAW entry is the retained interval `[1.00784, 1.00811]`, while the ordinary Rule-2
scalar is the protium AME mass `1.007825031898`, strictly below the interval's lower endpoint. -/

/-- Concrete separation: the CIAAW hydrogen interval and the ordinary Rule-2 hydrogen scalar are
distinct quantities. -/
theorem ordinaryRule2Mass_separate_from_standardWeightAuthority :
    (1, CIAAWStandardAtomicWeights2021.Entry.interval 1007840000000 1008110000000) ∈
        standardWeightRecords ∧
      OrdinaryRule2Mass 1 1007825031898 ∧
      (1007825031898 : Nat) < 1007840000000 := by
  refine ⟨standardWeightRecords_three_variants.1, ?_, by decide⟩
  exact (ordinaryAtomicMassPico?_eq_some_iff 1 1007825031898 (by decide)).mp (by decide)

/-! ## Supplemental three-row candidate in the actual reviewed-batch interface -/

/-- The row-indexed independent reference. -/
def independentRowReference : Remaining71AuthorityDataRow → ProvisionReference
  | .periodicAtomicNumbers => independentPeriodicAtomicNumbersReference
  | .standardAtomicWeights => independentStandardAtomicWeightsReference
  | .isotopeAtomicMasses => independentIsotopeAtomicMassesReference

/-- One reviewed row carrying the new independent reference. -/
def independentRowSemantics (row : Remaining71AuthorityDataRow) : ReviewedProvisionSemantics where
  kind := row.kind
  sourceSuppliesRule := true
  reference := independentRowReference row

/-- Exact manifest provision/source mapping for each of the three rows. -/
theorem provisionSourceExact (row : Remaining71AuthorityDataRow) :
    IUPACNormativeProvision.source row.provision =
      (match row with
        | .periodicAtomicNumbers => IUPACNormativeSource.periodicTable2022
        | .standardAtomicWeights => IUPACNormativeSource.atomicWeights2021
        | .isotopeAtomicMasses => IUPACNormativeSource.atomicMasses2020) := by
  cases row <;> rfl

/-- The three frozen source digests, exactly as the manifest and the generated tables carry them.
Metadata strings only: this proves no external byte equality. -/
theorem frozenAuthorityData_source_digest_exact :
    IUPACNormativeSource.sha256? IUPACNormativeSource.periodicTable2022 =
        some CIPRule2MassData.periodicTable2022.sha256 ∧
      IUPACNormativeSource.sha256? IUPACNormativeSource.atomicWeights2021 =
        some CIAAWStandardAtomicWeights2021.sourceSha256 ∧
      IUPACNormativeSource.sha256? IUPACNormativeSource.atomicMasses2020 =
        some CIPRule2MassData.isotopeMasses2020.sha256 :=
  ⟨IUPACNormativeSource.periodic_table_digest_matches_rule2_mass_data,
    standardAtomicWeights2021_source_digest_exact,
    IUPACNormativeSource.isotope_mass_digest_matches_rule2_mass_data⟩

/-- Supplemental candidate reviewed batch: the actual `ReviewedProvisionBatch` interface over the
existing three-row scope, with the new independent references.  `sourceAudited` reuses
`remaining71AuthorityData_sourceAuditComplete` strictly as the existing manifest source-section
status. -/
noncomputable def supplementalAuthorityDataReviewedSemantics :
    Remaining71AuthorityDataReviewedSemanticsTable where
  reviewed :=
    { ChemicallyAdmitted := AuthoritativeChemicalInput.StructurallyWellFormed
      row := fun provision member =>
        independentRowSemantics
          (remaining71AuthorityDataRowOf provision (by simpa using member))
      sourceAudited := by
        intro provision member
        exact remaining71AuthorityData_sourceAuditComplete (by simpa using member) }
  classifier_exact := by
    intro provision member
    let row := remaining71AuthorityDataRowOf provision (by simpa using member)
    have rowProvision : row.provision = provision :=
      remaining71AuthorityDataRowOf_provision provision (by simpa using member)
    have classified := Remaining71AuthorityDataRow.classifier_exact row
    change row.kind = globalProvisionKind provision
    simpa [rowProvision] using classified.symm

/-- The supplemental batch's classifier is exactly the global kind, projection of the table. -/
theorem supplementalAuthorityDataReviewedSemantics_classifier_exact
    {provision : IUPACNormativeProvision}
    (member : provision ∈ authorityDataReviewedSemanticsSlice.toFinset) :
    (supplementalAuthorityDataReviewedSemantics.reviewed.row provision member).kind =
      globalProvisionKind provision :=
  supplementalAuthorityDataReviewedSemantics.classifier_exact member



theorem supplementalAuthorityDataReviewedSemantics_sourceAudited
    {provision : IUPACNormativeProvision}
    (member : provision ∈ authorityDataReviewedSemanticsSlice.toFinset) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source :=
  supplementalAuthorityDataReviewedSemantics.reviewed.sourceAudited member

/-! ## Concrete nonvacuity of the independent references -/

theorem independentPeriodicAtomicNumbersReference_nonvacuous :
    ∃ observation : PeriodicAtomicNumberAuthorityObservation,
      independentPeriodicAtomicNumbersReference.Judges
        Remaining71AuthorityDataRow.witnessInput observation := by
  refine ⟨⟨1⟩, ?_⟩
  change PeriodicTableAdmits 1
  exact ⟨by decide, by decide⟩

/-- Hydrogen's CIAAW interval is preserved verbatim; no ordinary Rule-2 substitution is made. -/
theorem supplemental_standardWeight_hydrogen_interval_preserved :
    (1, CIAAWStandardAtomicWeights2021.Entry.interval 1007840000000 1008110000000) ∈
      standardWeightRecords :=
  standardWeightRecords_three_variants.1

theorem independentStandardAtomicWeightsReference_nonvacuous :
    ∃ observation : StandardAtomicWeightAuthorityObservation,
      independentStandardAtomicWeightsReference.Judges
        Remaining71AuthorityDataRow.witnessInput observation := by
  refine ⟨⟨1, .interval 1007840000000 1008110000000⟩, ?_⟩
  change (1, CIAAWStandardAtomicWeights2021.Entry.interval 1007840000000 1008110000000) ∈
    standardWeightRecords
  exact supplemental_standardWeight_hydrogen_interval_preserved

theorem independentIsotopeAtomicMassesReference_nonvacuous :
    ∃ observation : IsotopeAtomicMassAuthorityObservation,
      independentIsotopeAtomicMassesReference.Judges
        Remaining71AuthorityDataRow.witnessInput observation := by
  refine ⟨⟨1, 1, 1007825031898⟩, ?_⟩
  change isotopeRecordOf ⟨1, 1, 1007825031898⟩ ∈ isotopeRecords
  exact (isotope_record_iff_lookup 1 1 1007825031898 (by decide)).mpr (by decide)

/-! ## Conformance certificate -/

/-- Supplemental conformance certificate, expressed in the actual normative interfaces: the
reviewed batch, the unrestricted all-observation production/independent bridges, the preserved
CIAAW hydrogen interval, the exact manifest provision/source mapping and the frozen source digests.
The fields are concrete witnesses, not an arbitrary renamed lookup. -/
structure SupplementalAuthorityDataConformanceCertificate where
  table : Remaining71AuthorityDataReviewedSemanticsTable
  table_exact : table = supplementalAuthorityDataReviewedSemantics
  periodic_bridge : ∀ (source : AuthoritativeChemicalInput)
      (observation : PeriodicAtomicNumberAuthorityObservation),
      PeriodicAtomicNumberProductionJudged observation ↔
        independentPeriodicAtomicNumbersReference.Judges source observation
  standard_bridge : ∀ (source : AuthoritativeChemicalInput)
      (observation : StandardAtomicWeightAuthorityObservation),
      StandardAtomicWeightProductionJudged observation ↔
        independentStandardAtomicWeightsReference.Judges source observation
  isotope_bridge : ∀ (source : AuthoritativeChemicalInput)
      (observation : IsotopeAtomicMassAuthorityObservation),
      IsotopeAtomicMassProductionJudged observation ↔
        independentIsotopeAtomicMassesReference.Judges source observation
  hydrogen_interval_preserved :
    (1, CIAAWStandardAtomicWeights2021.Entry.interval 1007840000000 1008110000000) ∈
      standardWeightRecords
  manifest_source_exact : ∀ row : Remaining71AuthorityDataRow,
    IUPACNormativeProvision.source row.provision =
      (match row with
        | .periodicAtomicNumbers => IUPACNormativeSource.periodicTable2022
        | .standardAtomicWeights => IUPACNormativeSource.atomicWeights2021
        | .isotopeAtomicMasses => IUPACNormativeSource.atomicMasses2020)
  metadata_exact :
    IUPACNormativeSource.sha256? IUPACNormativeSource.periodicTable2022 =
        some CIPRule2MassData.periodicTable2022.sha256 ∧
      IUPACNormativeSource.sha256? IUPACNormativeSource.atomicWeights2021 =
        some CIAAWStandardAtomicWeights2021.sourceSha256 ∧
      IUPACNormativeSource.sha256? IUPACNormativeSource.atomicMasses2020 =
        some CIPRule2MassData.isotopeMasses2020.sha256

noncomputable def supplementalAuthorityDataConformance :
    SupplementalAuthorityDataConformanceCertificate where
  table := supplementalAuthorityDataReviewedSemantics
  table_exact := rfl
  periodic_bridge := periodicAtomicNumber_production_iff_independent
  standard_bridge := standardAtomicWeight_production_iff_independent
  isotope_bridge := isotopeAtomicMass_production_iff_independent
  hydrogen_interval_preserved := supplemental_standardWeight_hydrogen_interval_preserved
  manifest_source_exact := provisionSourceExact
  metadata_exact := frozenAuthorityData_source_digest_exact

/-! ## Explicit hookup to the frozen corpus (faithfulness stays an explicit hypothesis) -/

/-- Given an explicit corpus/reviewed-batch faithfulness witness, the corpus reference for a member
of the three-row scope is the new independent reference.  The faithfulness predicate is supplied,
never synthesized here. -/
theorem supplementalCorpusReference_eq_of_member
    {corpus : FrozenProvisionCorpus}
    (faithful : ProvisionBatchReferenceFaithful
      supplementalAuthorityDataReviewedSemantics.reviewed corpus)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ authorityDataReviewedSemanticsSlice) :
    corpus.reference provision =
      (independentRowSemantics (remaining71AuthorityDataRowOf provision member)).reference := by
  have exactRow := faithful.exact (by simpa using member)
  simpa [supplementalAuthorityDataReviewedSemantics, independentRowSemantics]
    using exactRow.2.2

/-! ## Successor integration boundary (deliberately unproved)

Promoting the three rows requires a reviewed edit to `currentSemanticsMaturity`, an accompanying
synchronized semantics partition, and a downstream certificate binding the references to the
curated inventory. The separate 595-row non-descriptor source-meaning programme remains a full-project
obligation, not a prerequisite for these three rows. Implementation coverage and source adoption are
separate. This module states the integration obligation without pinning a mutable baseline maturity. -/

/-- The exact successor integration needed once the reviewed independent semantics is accepted. -/
def FrozenAuthorityDataSuccessorIntegrationRequired : Prop :=
  ∀ row : Remaining71AuthorityDataRow,
    IUPACNormativeProvision.currentSemanticsMaturity row.provision ≠ .absent


end TetraStereo.UniversalProof.FrozenAuthorityProvisionConformanceProofs.FrozenAuthorityProvisionConformance
