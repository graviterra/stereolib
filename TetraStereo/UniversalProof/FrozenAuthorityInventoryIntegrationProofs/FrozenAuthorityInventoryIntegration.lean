import TetraStereo.UniversalProof.FrozenAuthorityProvisionConformanceProofs.FrozenAuthorityProvisionConformance
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorSourceMeaningReadiness

set_option autoImplicit false















namespace TetraStereo.UniversalProof.FrozenAuthorityInventoryIntegrationProofs.FrozenAuthorityInventoryIntegration

open TetraStereo.OneCenter
open TetraStereo.OneCenter.IUPACNormativeProvision
open TetraStereo.UniversalProof.FrozenAuthorityProvisionConformanceProofs.FrozenAuthorityProvisionConformance

/-- Every row in the exact three-row authority family has partial independent semantics. -/
theorem authority_row_semantics_integrated (row : Remaining71AuthorityDataRow) :
    currentSemanticsMaturity row.provision = .partiallyFormalized := by
  cases row with
  | periodicAtomicNumbers => exact periodicAtomicNumbers_semantics_partiallyFormalized
  | standardAtomicWeights => exact standardAtomicWeights_semantics_partiallyFormalized
  | isotopeAtomicMasses => exact isotopeAtomicMasses_semantics_partiallyFormalized

theorem authority_semantics_integration_required_discharged :
    FrozenAuthorityDataSuccessorIntegrationRequired := by
  intro row
  rw [authority_row_semantics_integrated row]
  decide

/-- Semantics integration does not promote implementation maturity. -/
theorem authority_row_implementation_still_partial (row : Remaining71AuthorityDataRow) :
    currentMaturity row.provision = .partiallyCovered := by
  cases row <;> apply (currentMaturity_eq_partiallyCovered_iff _).mpr <;> decide

/-- The exact remaining absent set retains both Appendix-3 and carbohydrate obligations. -/
theorem absent_semantics_exact_non_descriptor_queue :
    currentAbsentSemanticsProvisions = globalNonDescriptorMissingSourceMeaningProvisions := rfl

theorem remaining_semantics_count : currentAbsentSemanticsProvisions.length = 595 :=
  currentAbsentSemanticsProvisionCount

/-- Existing production predicates, typed against the independent references. -/
def rowProductionJudges :
    (row : Remaining71AuthorityDataRow) → (independentRowReference row).Observation → Prop
  | .periodicAtomicNumbers => PeriodicAtomicNumberProductionJudged
  | .standardAtomicWeights => StandardAtomicWeightProductionJudged
  | .isotopeAtomicMasses => IsotopeAtomicMassProductionJudged

theorem row_production_iff_independent
    (row : Remaining71AuthorityDataRow) (source : AuthoritativeChemicalInput)
    (observation : (independentRowReference row).Observation) :
    rowProductionJudges row observation ↔
      (independentRowReference row).Judges source observation := by
  cases row with
  | periodicAtomicNumbers =>
      exact periodicAtomicNumber_production_iff_independent source observation
  | standardAtomicWeights =>
      exact standardAtomicWeight_production_iff_independent source observation
  | isotopeAtomicMasses =>
      exact isotopeAtomicMass_production_iff_independent source observation

theorem independent_row_applicable_of_judged
    (row : Remaining71AuthorityDataRow) (source : AuthoritativeChemicalInput)
    (observation : (independentRowReference row).Observation)
    (judged : (independentRowReference row).Judges source observation) :
    (independentRowReference row).Applicable source := by
  cases row <;> exact ⟨observation, judged⟩

/-- Fixed frozen-table production on the exact three-row scope; no reference judgment is used
as a production predicate. Reference faithfulness transports observation types only. -/
noncomputable def frozenAuthorityProductionInterpreter
    {corpus : FrozenProvisionCorpus}
    (faithful : ProvisionBatchReferenceFaithful
      supplementalAuthorityDataReviewedSemantics.reviewed corpus) : ProvisionInterpreter corpus where
  Produces := fun provision _source observation =>
    if member : provision ∈ authorityDataReviewedSemanticsSlice then
      let row := remaining71AuthorityDataRowOf provision member
      let referenceEq := supplementalCorpusReference_eq_of_member faithful provision member
      rowProductionJudges row
        (cast (congrArg ProvisionReference.Observation referenceEq) observation)
    else False

theorem frozenAuthorityProductionInterpreter_exact
    {corpus : FrozenProvisionCorpus}
    (faithful : ProvisionBatchReferenceFaithful
      supplementalAuthorityDataReviewedSemantics.reviewed corpus)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ authorityDataReviewedSemanticsSlice)
    (source : AuthoritativeChemicalInput)
    (observation : (corpus.reference provision).Observation) :
    (frozenAuthorityProductionInterpreter faithful).Produces provision source observation ↔
      rowProductionJudges (remaining71AuthorityDataRowOf provision member)
        (cast (congrArg ProvisionReference.Observation
          (supplementalCorpusReference_eq_of_member faithful provision member)) observation) := by
  simp only [frozenAuthorityProductionInterpreter, dif_pos member]

/-- An out-of-scope row has no output from this partial adapter. No global correctness claim
is made for those rows. -/
theorem frozenAuthorityProductionInterpreter_outside_scope
    {corpus : FrozenProvisionCorpus}
    (faithful : ProvisionBatchReferenceFaithful
      supplementalAuthorityDataReviewedSemantics.reviewed corpus)
    (provision : IUPACNormativeProvision)
    (absent : provision ∉ authorityDataReviewedSemanticsSlice)
    (source : AuthoritativeChemicalInput)
    (observation : (corpus.reference provision).Observation) :
    ¬ (frozenAuthorityProductionInterpreter faithful).Produces provision source observation := by
  simp only [frozenAuthorityProductionInterpreter, dif_neg absent, not_false_eq_true]

/-- The actual normative correctness interface, for every admitted input and observation in each
of the three authority rows. The explicit corpus-faithfulness hypothesis remains required. -/
theorem frozenAuthorityProductionInterpreter_provisionCorrect
    {corpus : FrozenProvisionCorpus}
    (faithful : ProvisionBatchReferenceFaithful
      supplementalAuthorityDataReviewedSemantics.reviewed corpus)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ authorityDataReviewedSemanticsSlice) :
    ProvisionCorrect corpus (frozenAuthorityProductionInterpreter faithful) provision := by
  intro source _admitted observation
  let row := remaining71AuthorityDataRowOf provision member
  let referenceEq := supplementalCorpusReference_eq_of_member faithful provision member
  let rowObservation : (independentRowReference row).Observation :=
    cast (congrArg ProvisionReference.Observation referenceEq) observation
  have judgment := row_production_iff_independent row source rowObservation
  have applicableTransport := ProvisionReference.applicable_congr referenceEq source
  have judgmentTransport := ProvisionReference.judges_cast_congr referenceEq source observation
  rw [frozenAuthorityProductionInterpreter_exact faithful provision member source observation]
  change rowProductionJudges row rowObservation ↔
    (corpus.reference provision).Applicable source ∧
      (corpus.reference provision).Judges source observation
  constructor
  · intro produced
    have judged := judgment.mp produced
    exact ⟨applicableTransport.mpr
      (independent_row_applicable_of_judged row source rowObservation judged),
      judgmentTransport.mpr judged⟩
  · rintro ⟨_applicable, judged⟩
    exact judgment.mpr (judgmentTransport.mp judged)

/-- A concrete certificate links independent production bridges to the curated partial inventory.
It deliberately contains no corpus-faithfulness, source-byte or human-adoption field. -/
structure CuratedFrozenAuthorityConformance where
  independent : SupplementalAuthorityDataConformanceCertificate
  independent_exact : independent = supplementalAuthorityDataConformance
  partial_semantics : ∀ row : Remaining71AuthorityDataRow,
    currentSemanticsMaturity row.provision = .partiallyFormalized
  partial_implementation : ∀ row : Remaining71AuthorityDataRow,
    currentMaturity row.provision = .partiallyCovered
  exact_remaining_queue :
    currentAbsentSemanticsProvisions = globalNonDescriptorMissingSourceMeaningProvisions

noncomputable def curatedFrozenAuthorityConformance : CuratedFrozenAuthorityConformance where
  independent := supplementalAuthorityDataConformance
  independent_exact := rfl
  partial_semantics := authority_row_semantics_integrated
  partial_implementation := authority_row_implementation_still_partial
  exact_remaining_queue := absent_semantics_exact_non_descriptor_queue

end TetraStereo.UniversalProof.FrozenAuthorityInventoryIntegrationProofs.FrozenAuthorityInventoryIntegration
