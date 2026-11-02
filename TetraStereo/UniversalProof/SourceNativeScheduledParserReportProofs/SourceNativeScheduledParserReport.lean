import TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserCausalModel

set_option autoImplicit false

namespace TetraStereo.UniversalProof.SourceNativeScheduledParserReportProofs.SourceNativeScheduledParserReport

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence
open TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserCausalModel





















structure ScheduledParserRow (source : AuthoritativeChemicalInput) where
  center : source.AromaticCanonicalTetrahedralCenter
  label : Option AromaticCanonicalAuxiliaryLabel
  deriving DecidableEq

variable (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
  (agreement : molecule.AuthoritativeStructureAgreement source)
  (writtenExact : molecule.WrittenNeighborExact) (carrierFuel ruleFuel : Nat)

noncomputable def scheduledParserLabel (center : source.AromaticCanonicalTetrahedralCenter) :
    Option AromaticCanonicalAuxiliaryLabel :=
  occurrenceParserRichScheduledState molecule source agreement writtenExact carrierFuel ruleFuel
    (source.aromaticCanonicalFinalOccurrence carrierFuel center)

/-- The internally scheduled label is the actual rich parser evaluator at the same final target. -/
theorem scheduledParserLabel_eq_actual_descriptor
    (center : source.AromaticCanonicalTetrahedralCenter) :
    scheduledParserLabel molecule source agreement writtenExact carrierFuel ruleFuel center =
      occurrenceParserRichDescriptor? molecule source agreement writtenExact
        (source.aromaticCanonicalFinalOccurrence carrierFuel center)
        (source.aromaticCanonicalDependencyView
          (occurrenceParserRichScheduledState molecule source agreement writtenExact
            carrierFuel ruleFuel)
          (source.aromaticCanonicalFinalOccurrence carrierFuel center)) ruleFuel :=
  (occurrenceParserRichModel_evaluates molecule source agreement writtenExact _
    (occurrenceParserRichScheduledState_cipModel molecule source agreement writtenExact
      carrierFuel ruleFuel) _).symm

noncomputable def scheduledParserReport : List (ScheduledParserRow source) :=
  source.aromaticCanonicalTetrahedralCenters.map fun center =>
    { center, label := scheduledParserLabel molecule source agreement writtenExact
        carrierFuel ruleFuel center }

theorem mem_scheduledParserReport_iff (row : ScheduledParserRow source) :
    row ∈ scheduledParserReport molecule source agreement writtenExact carrierFuel ruleFuel ↔
      row.label = scheduledParserLabel molecule source agreement writtenExact
        carrierFuel ruleFuel row.center := by
  constructor
  · intro present
    rcases List.mem_map.mp present with ⟨center, _, same⟩
    subst row
    rfl
  · intro same
    apply List.mem_map.mpr
    refine ⟨row.center,
      (source.mem_aromaticCanonicalTetrahedralCenters_iff row.center).mpr row.center.property, ?_⟩
    cases row with
    | mk center label =>
        change label = scheduledParserLabel molecule source agreement writtenExact
          carrierFuel ruleFuel center at same
        subst label
        rfl

theorem scheduledParserReport_centers :
    (scheduledParserReport molecule source agreement writtenExact carrierFuel ruleFuel).map
      ScheduledParserRow.center = source.aromaticCanonicalTetrahedralCenters := by
  unfold scheduledParserReport
  rw [List.map_map]
  change source.aromaticCanonicalTetrahedralCenters.map id =
    source.aromaticCanonicalTetrahedralCenters
  exact List.map_id _

theorem scheduledParserReport_length :
    (scheduledParserReport molecule source agreement writtenExact carrierFuel ruleFuel).length =
      source.aromaticCanonicalTetrahedralCenters.length := by
  simp [scheduledParserReport]

theorem scheduledParserReport_nodup :
    (scheduledParserReport molecule source agreement writtenExact carrierFuel ruleFuel).Nodup := by
  apply source.aromaticCanonicalTetrahedralCenters_nodup.map
  intro left right same
  exact congrArg ScheduledParserRow.center same

theorem scheduledParserReport_every_center (center : source.AromaticCanonicalTetrahedralCenter) :
    ∃! row, row ∈ scheduledParserReport molecule source agreement writtenExact carrierFuel ruleFuel ∧
      row.center = center := by
  refine ⟨⟨center, scheduledParserLabel molecule source agreement writtenExact
    carrierFuel ruleFuel center⟩, ?_, ?_⟩
  · exact ⟨(mem_scheduledParserReport_iff molecule source agreement writtenExact
      carrierFuel ruleFuel _).mpr rfl, rfl⟩
  · intro row present
    have labelEq := (mem_scheduledParserReport_iff molecule source agreement writtenExact
      carrierFuel ruleFuel row).mp present.1
    have centerEq := present.2
    cases row with
    | mk rowCenter rowLabel =>
        simp only at centerEq labelEq
        subst rowCenter
        subst rowLabel
        rfl

theorem scheduledParserReport_center_count_one (center : source.AromaticCanonicalTetrahedralCenter) :
    ((scheduledParserReport molecule source agreement writtenExact carrierFuel ruleFuel).map
      ScheduledParserRow.center).count center = 1 := by
  rw [scheduledParserReport_centers]
  exact List.count_eq_one_of_mem source.aromaticCanonicalTetrahedralCenters_nodup
    ((source.mem_aromaticCanonicalTetrahedralCenters_iff center).mpr center.property)

/-- Genuine parser model binding and independent meaning for every assigned row label. Absence
is retained by the model binding; no independent chemical completeness assertion is made. -/
def ScheduledParserRowMeaning (row : ScheduledParserRow source) : Prop :=
  ∃ state : source.AromaticCanonicalAuxiliaryState carrierFuel,
    (source.aromaticCanonicalOccurrenceSystem
      (occurrenceParserRichAuxiliarySemantics molecule source agreement writtenExact
        carrierFuel ruleFuel)).CIPModel state ∧
      state (source.aromaticCanonicalFinalOccurrence carrierFuel row.center) = row.label ∧
        ∀ descriptor, row.label = some descriptor →
          OccurrenceParserRichDescriptorMeaning molecule source agreement writtenExact
            (source.aromaticCanonicalFinalOccurrence carrierFuel row.center)
            (source.aromaticCanonicalDependencyView state
              (source.aromaticCanonicalFinalOccurrence carrierFuel row.center)) ruleFuel descriptor

theorem scheduledParserReport_member_sound (row : ScheduledParserRow source)
    (present : row ∈ scheduledParserReport molecule source agreement writtenExact
      carrierFuel ruleFuel) :
    ScheduledParserRowMeaning molecule source agreement writtenExact carrierFuel ruleFuel row := by
  have emitted := (mem_scheduledParserReport_iff molecule source agreement writtenExact
    carrierFuel ruleFuel row).mp present
  have model := occurrenceParserRichScheduledState_cipModel molecule source agreement writtenExact
    carrierFuel ruleFuel
  refine ⟨occurrenceParserRichScheduledState molecule source agreement writtenExact
    carrierFuel ruleFuel, model, emitted.symm, ?_⟩
  intro descriptor assigned
  exact occurrenceParserRichModel_output_sound molecule source agreement writtenExact _ model
    (source.aromaticCanonicalFinalOccurrence carrierFuel row.center) descriptor
    (emitted.symm.trans assigned)

namespace ClosedParserReport

open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment.ClosedParserWitness
open TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserCausalModel.ClosedParserModel

noncomputable def actualReport : List (ScheduledParserRow parserSource) :=
  scheduledParserReport annotatedRawCF parserSource parserSource_agreement
    parserSource_writtenExact 0 2

def actualRRow : ScheduledParserRow parserSource :=
  ⟨parserCenter, some (.chiral RS.R)⟩

theorem actual_R_row_mem : actualRRow ∈ actualReport := by
  apply (mem_scheduledParserReport_iff annotatedRawCF parserSource parserSource_agreement
    parserSource_writtenExact 0 2 actualRRow).mpr
  exact parser_scheduled_R.symm

theorem actual_R_center_count_one :
    (actualReport.map ScheduledParserRow.center).count parserCenter = 1 :=
  scheduledParserReport_center_count_one annotatedRawCF parserSource parserSource_agreement
    parserSource_writtenExact 0 2 parserCenter

theorem actual_R_row_meaning :
    ScheduledParserRowMeaning annotatedRawCF parserSource parserSource_agreement
      parserSource_writtenExact 0 2 actualRRow :=
  scheduledParserReport_member_sound annotatedRawCF parserSource parserSource_agreement
    parserSource_writtenExact 0 2 actualRRow actual_R_row_mem

end ClosedParserReport
end TetraStereo.UniversalProof.SourceNativeScheduledParserReportProofs.SourceNativeScheduledParserReport
