import TetraStereo.UniversalProof.PlanarAllCandidateConflictClosureProofs.PlanarAllCandidateConflictClosure
import TetraStereo.UniversalProof.SourceNativeMixedScheduledReportProofs.SourceNativeMixedScheduledReport
import TetraStereo.OneCenter.AuthoritativeMainGroupLewisGeneralHybridEvidence

set_option autoImplicit false

namespace TetraStereo.UniversalProof.PlanarNormalizedTransactionRecoveryProofs.PlanarNormalizedTransactionRecovery

open TetraStereo.OneCenter TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.UniversalProof.ScheduledDrawingSpatialEndToEndProofs.ScheduledDrawingSpatialIntegration
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
open TetraStereo.UniversalProof.SourceNativeMixedScheduledReportProofs.SourceNativeMixedScheduledReport (MixedScheduledRow)
open TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModel
















structure NormalizedPlanarRequest where
  originalRaw : RawMolecule
  normalized : CertifiedChemistryNormalizationResult
  normalizationEq : normalized.result = normalizeRawMolecule originalRaw
  source : AuthoritativeChemicalInput
  agreement : RawAnnotationAgreement normalized.result.parsed source
  carrierFuel : Nat
  ruleFuel : Nat

namespace NormalizedPlanarRequest

theorem normalization_binding (request : NormalizedPlanarRequest) :
    request.normalized.result = normalizeRawMolecule request.originalRaw := request.normalizationEq

noncomputable def accepted (request : NormalizedPlanarRequest) : Prop :=
  PlanarJointAuditObligation request.normalized.result.parsed request.source request.agreement
    request.normalized.writtenNeighborExact request.carrierFuel request.ruleFuel

noncomputable def label (request : NormalizedPlanarRequest)
    (center : request.source.AromaticCanonicalTetrahedralCenter) :
    Option AromaticCanonicalAuxiliaryLabel :=
  planarJointState request.normalized.result.parsed request.source request.agreement
    request.normalized.writtenNeighborExact request.carrierFuel request.ruleFuel
    (request.source.aromaticCanonicalFinalOccurrence request.carrierFuel center)

noncomputable def report (request : NormalizedPlanarRequest) : List (MixedScheduledRow request.source) :=
  request.source.aromaticCanonicalTetrahedralCenters.map fun center => ⟨center, request.label center⟩

noncomputable def guardedProduce (request : NormalizedPlanarRequest) :
    Option (List (MixedScheduledRow request.source)) := by
  classical
  exact if request.accepted then some request.report else none

theorem guardedProduce_eq_some_iff (request : NormalizedPlanarRequest)
    (rows : List (MixedScheduledRow request.source)) :
    request.guardedProduce = some rows ↔ request.accepted ∧ rows = request.report := by
  classical
  by_cases accepted : request.accepted
  · simp [guardedProduce, accepted, eq_comm]
  · simp [guardedProduce, accepted]

theorem guardedProduce_eq_none_iff (request : NormalizedPlanarRequest) :
    request.guardedProduce = none ↔ ¬ request.accepted := by
  classical
  by_cases accepted : request.accepted <;> simp [guardedProduce, accepted]

theorem mem_report_iff (request : NormalizedPlanarRequest) (row : MixedScheduledRow request.source) :
    row ∈ request.report ↔ row.label = request.label row.center := by
  constructor
  · intro present
    obtain ⟨center, _, rfl⟩ := List.mem_map.mp present
    rfl
  · intro same
    apply List.mem_map.mpr
    refine ⟨row.center, (request.source.mem_aromaticCanonicalTetrahedralCenters_iff row.center).mpr
      row.center.property, ?_⟩
    cases row with
    | mk center output =>
      change output = request.label center at same
      subst output
      rfl

theorem report_centers (request : NormalizedPlanarRequest) :
    request.report.map MixedScheduledRow.center = request.source.aromaticCanonicalTetrahedralCenters := by
  unfold report
  rw [List.map_map]
  change request.source.aromaticCanonicalTetrahedralCenters.map id = _
  exact List.map_id _

theorem report_center_count_one (request : NormalizedPlanarRequest)
    (center : request.source.AromaticCanonicalTetrahedralCenter) :
    (request.report.map MixedScheduledRow.center).count center = 1 := by
  rw [report_centers]
  exact List.count_eq_one_of_mem request.source.aromaticCanonicalTetrahedralCenters_nodup
    ((request.source.mem_aromaticCanonicalTetrahedralCenters_iff center).mpr center.property)

/-- Independent meaning binds the same source, occurrence, own model and own view. -/
def RowMeaning (request : NormalizedPlanarRequest) (row : MixedScheduledRow request.source) : Prop :=
  ∃ state : request.source.AromaticCanonicalAuxiliaryState request.carrierFuel,
    (request.source.aromaticCanonicalOccurrenceSystem
      (planarMixedAuxiliarySemantics request.normalized.result.parsed request.source request.agreement
        request.normalized.writtenNeighborExact request.carrierFuel request.ruleFuel)).CIPModel state ∧
    state (request.source.aromaticCanonicalFinalOccurrence request.carrierFuel row.center) = row.label ∧
    ∀ descriptor, row.label = some descriptor →
      PlanarMixedJointDescriptor request.normalized.result.parsed request.source request.agreement
        request.normalized.writtenNeighborExact
        (request.source.aromaticCanonicalFinalOccurrence request.carrierFuel row.center)
        (request.source.aromaticCanonicalDependencyView state
          (request.source.aromaticCanonicalFinalOccurrence request.carrierFuel row.center))
        request.ruleFuel descriptor

theorem report_member_sound (request : NormalizedPlanarRequest) (row : MixedScheduledRow request.source)
    (present : row ∈ request.report) : request.RowMeaning row := by
  have emitted := (mem_report_iff request row).mp present
  refine ⟨planarJointState _ _ _ _ _ _, planarMixedScheduledState_cipModel _ _ _ _ _ _,
    emitted.symm, ?_⟩
  intro descriptor assigned
  exact planarMixedModel_output_sound _ _ _ _ _
    (planarMixedScheduledState_cipModel _ _ _ _ _ _) _ descriptor (emitted.symm.trans assigned)

theorem guardedProduce_member_sound (request : NormalizedPlanarRequest)
    (rows : List (MixedScheduledRow request.source)) (produced : request.guardedProduce = some rows)
    (row : MixedScheduledRow request.source) (present : row ∈ rows) : request.RowMeaning row := by
  rw [((guardedProduce_eq_some_iff request rows).mp produced).2] at present
  exact report_member_sound request row present

theorem guardedProduce_conflict_free (request : NormalizedPlanarRequest)
    (rows : List (MixedScheduledRow request.source)) (produced : request.guardedProduce = some rows)
    (center : request.source.AromaticCanonicalTetrahedralCenter) :
    planarJointStatus request.normalized.result.parsed request.source request.agreement
      request.normalized.writtenNeighborExact request.carrierFuel request.ruleFuel
      (request.source.aromaticCanonicalFinalOccurrence request.carrierFuel center) ≠ .conflict := by
  have admitted := ((guardedProduce_eq_some_iff request rows).mp produced).1
  exact (planarGlobalConflictIssues_eq_nil_iff _ _ _ _ _ _).mp admitted.1 center
    ((request.source.mem_aromaticCanonicalTetrahedralCenters_iff center).mpr center.property)

end NormalizedPlanarRequest

namespace ClosedAnnotated

open TetraStereo.UniversalProof.SourceNativeAnnotatedPlanarParserWitnessProofs.SourceNativeAnnotatedPlanarParserWitness
open TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModelKernelCertificate.ClosedAnnotatedPlanarWitness
  (closedJointState_R)
open TetraStereo.UniversalProof.PlanarAllCandidateConflictClosureProofs.PlanarAllCandidateConflictClosure

local instance : NeZero source.molecule.atomCount := ⟨by change (9 : Nat) ≠ 0; decide⟩

def actualRequest : NormalizedPlanarRequest where
  originalRaw := annotatedRaw
  normalized := certified
  normalizationEq := rfl
  source := source
  agreement := actual_annotation_agreement
  carrierFuel := 1
  ruleFuel := 4

theorem actual_normalization_binding :
    actualRequest.normalized.result = normalizeRawMolecule actualRequest.originalRaw ∧
      actualRequest.normalized.result.parsed = annotatedRaw := ⟨rfl, rfl⟩

theorem actual_accepted : actualRequest.accepted := annotated_complete_audit

theorem actual_produce : actualRequest.guardedProduce = some actualRequest.report :=
  (NormalizedPlanarRequest.guardedProduce_eq_some_iff _ _).mpr ⟨actual_accepted, rfl⟩

noncomputable def actualRow : MixedScheduledRow source := ⟨center, some (.chiral RS.R)⟩

theorem actual_R_row : actualRow ∈ actualRequest.report := by
  apply (NormalizedPlanarRequest.mem_report_iff _ _).mpr
  exact closedJointState_R.symm

theorem actual_R_meaning : actualRequest.RowMeaning actualRow :=
  NormalizedPlanarRequest.guardedProduce_member_sound actualRequest actualRequest.report actual_produce
    actualRow actual_R_row

theorem actual_center_count_one : (actualRequest.report.map MixedScheduledRow.center).count center = 1 :=
  NormalizedPlanarRequest.report_center_count_one actualRequest center

/-- Both endpoint inventories are fully represented. No electronic count is guessed. -/
def zeroInventory : AromaticCanonicalRule3EndpointElectronicInventory := ⟨0, 0, 0, 0⟩

theorem left_neighbors : source.aromaticCanonicalNeighborFinset 1 = {0, 5, 6} := by
  ext atom
  rw [mem_aromaticCanonicalNeighborFinset_iff]
  unfold AromaticCanonicalAdjacent
  decide +revert +kernel

theorem right_neighbors : source.aromaticCanonicalNeighborFinset 5 = {1, 7, 8} := by
  ext atom
  rw [mem_aromaticCanonicalNeighborFinset_iff]
  unfold AromaticCanonicalAdjacent
  decide +revert +kernel

theorem left_inventory : source.MainGroupLewisGeneralEndpointInventory 1 5 zeroInventory := by
  constructor
  · unfold CanonicalAromaticCanonicalRule3EndpointElectronicInventory aromaticCanonicalRule3Substituents
    rw [left_neighbors]
    rw [Finset.length_sort]
    decide +kernel
  · refine ⟨4, by decide +kernel, ?_⟩
    unfold MainGroupLewisElectronBalance aromaticCanonicalRepresentedBondOrderSum
    rw [left_neighbors]
    decide +kernel

theorem right_inventory : source.MainGroupLewisGeneralEndpointInventory 5 1 zeroInventory := by
  constructor
  · unfold CanonicalAromaticCanonicalRule3EndpointElectronicInventory aromaticCanonicalRule3Substituents
    rw [right_neighbors]
    rw [Finset.length_sort]
    decide +kernel
  · refine ⟨4, by decide +kernel, ?_⟩
    unfold MainGroupLewisElectronBalance aromaticCanonicalRepresentedBondOrderSum
    rw [right_neighbors]
    decide +kernel

theorem only_ordinary_double_bond (endpoint partner : source.AromaticCanonicalAtom) :
    source.AromaticCanonicalOrdinaryDoubleBond endpoint partner →
      (endpoint = 1 ∧ partner = 5) ∨ (endpoint = 5 ∧ partner = 1) := by
  unfold AromaticCanonicalOrdinaryDoubleBond AromaticCanonicalAdjacent
  decide +revert +kernel

/-- General inventory uniqueness follows already from the two represented-position equation. -/
theorem represented_inventory_unique (endpoint partner : source.AromaticCanonicalAtom)
    (count : (source.aromaticCanonicalRule3Substituents endpoint partner).length = 2)
    (other : AromaticCanonicalRule3EndpointElectronicInventory)
    (valid : source.MainGroupLewisGeneralEndpointInventory endpoint partner other) :
    other = zeroInventory := by
  have positions := valid.1.1
  rw [count] at positions
  rcases other with ⟨hydrogens, pairs, vacancies, radicals⟩
  unfold AromaticCanonicalRule3EndpointElectronicInventory.totalNonrepresentedPositions at positions
  change 2 + (hydrogens + pairs + vacancies + radicals) = 2 at positions
  have h : hydrogens = 0 := by omega
  have p : pairs = 0 := by omega
  have v : vacancies = 0 := by omega
  have r : radicals = 0 := by omega
  subst hydrogens; subst pairs; subst vacancies; subst radicals
  rfl

theorem actual_empty_electronic_ready : source.MainGroupLewisGeneralHybridCertificationReady [] := by
  refine ⟨(source.structurallyWellFormed?_eq_true_iff).mp (by decide +kernel), ⟨by simp, by simp⟩, ?_⟩
  intro endpoint partner directed
  have ordinary := source.aromaticCanonicalOrdinaryDoubleBond_of_directedEndpoint directed
  have shape := only_ordinary_double_bond endpoint partner ordinary
  have lewis : source.MainGroupLewisGeneralEndpointInventory endpoint partner zeroInventory := by
    rcases shape with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact left_inventory
    · exact right_inventory
  have count : (source.aromaticCanonicalRule3Substituents endpoint partner).length = 2 := by
    have canonical := lewis.1.1
    simpa [zeroInventory, AromaticCanonicalRule3EndpointElectronicInventory.totalNonrepresentedPositions]
      using canonical
  refine ⟨zeroInventory, Or.inr ⟨rfl, ?_, ?_⟩⟩
  · exact (source.mainGroupLewisGeneralAtomInventory_iff_endpoint endpoint partner directed _).mpr lewis
  · intro other atomMeaning
    exact represented_inventory_unique endpoint partner count other
      ((source.mainGroupLewisGeneralAtomInventory_iff_endpoint endpoint partner directed _).mp atomMeaning)

end ClosedAnnotated
end TetraStereo.UniversalProof.PlanarNormalizedTransactionRecoveryProofs.PlanarNormalizedTransactionRecovery
