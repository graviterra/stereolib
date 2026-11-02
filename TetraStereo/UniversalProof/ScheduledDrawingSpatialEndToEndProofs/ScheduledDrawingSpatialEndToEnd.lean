import TetraStereo.UniversalProof.ScheduledDrawingSpatialEndToEndProofs.ScheduledDrawingSpatialWholeMolecule
import TetraStereo.OneCenter.AuthoritativeSingleWedgeExactPriorityDescriptor
import TetraStereo.OneCenter.AuthoritativeSingleWedgeAuxiliaryIndependence

set_option autoImplicit false

namespace TetraStereo.UniversalProof.ScheduledDrawingSpatialEndToEndProofs.ScheduledDrawingSpatialEndToEnd

open TetraStereo.OneCenter TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open SingleWedgeOccurrenceAlignmentRegression SingleWedgeAtomicPriorityBridgeRegression
open SingleWedgeExactPriorityDescriptorRegression
open ScheduledDrawingSpatialIntegration ScheduledDrawingSpatialWholeMolecule

/-! Literal source-only scheduled assignments and whole-molecule rows. Supplied semantics stays
explicit; the final closed reports instantiate the existing concrete evaluator semantics and
prove its internally scheduled CIP model. No scientific approval or inventory readiness follows.

The tetrahedral calibration is the corrected one: a negative priority-ordered oriented volume is
`R` (clockwise when the lowest-priority point is remote) and a positive one is `S`.  The solid
CFClBrI written frame (determinant `-3`) therefore produces `R`, and the hashed frame
(determinant `+3`) produces `S`.

Historical API policy: `cfclbri_solid_scheduled_S` and `cfclbri_hashed_scheduled_R` are
kernel-certificate-pinned identifiers retained from before the calibration repair.  Their
statements now carry the corrected labels `R` and `S`; accurately named aliases
`cfclbri_solid_scheduled_R` and `cfclbri_hashed_scheduled_S` are provided for new code. -/

private theorem status_of_exact_empty (source : AuthoritativeChemicalInput)
    (semantics : source.AromaticCanonicalRuleSemantics 0)
    (center : source.AromaticCanonicalTetrahedralCenter) (drawing : SingleWedgeSource.Frame)
    (bound : SourceFrame source center.1.val drawing)
    (separated : SourceEndpointAtomicSeparation source drawing) (noSpatial : source.spatial? = none)
    (raw : RS) (empty : ordinaryEmptyAuxiliaryDescriptor? source 0 2 center = some (.chiral raw)) :
    scheduledDrawingSpatialStatus source semantics 2 center = .assigned (.chiral raw) := by
  have drawingComputed := (ordinaryDescriptor?_eq_empty_auxiliary_zero_carrier source center
    drawing bound separated (scheduledDrawingView source semantics center)).trans empty
  have ordinaryNone := aromaticCanonicalOccurrenceRule3Through5Descriptor?_eq_none_of_spatial_none
    source noSpatial (source.aromaticCanonicalFinalOccurrence 0 center)
    (scheduledDrawingView source semantics center) 2
  have tieNone := aromaticCanonicalScheduledRule3Through6RSPseudoDescriptor?_eq_none_of_spatial_none
    source noSpatial semantics 2 center
  unfold scheduledDrawingSpatialStatus scheduledDrawingOutputs
  rw [drawingComputed, ordinaryNone, tieNone]
  rfl

/-- **Solid CFClBrI drawing, historical API key.**  The old suffix says `S`; under the corrected
calibration the negative priority-ordered determinant is `R`.  Use `cfclbri_solid_scheduled_R`
for new code. -/
theorem cfclbri_solid_scheduled_S
    (semantics : SingleWedgeSourceRegression.source.AromaticCanonicalRuleSemantics 0) :
    scheduledDrawingSpatialStatus SingleWedgeSourceRegression.source semantics 2 cfclbriProductionCenter =
      .assigned (.chiral RS.R) := by
  obtain ⟨aligned, computed⟩ := cfclbri_constructed_center_alignment 0
  have bound := (occurrenceAlignment?_sound SingleWedgeSourceRegression.source 0
    cfclbriProductionCenter aligned.1 aligned.2 computed).1
  exact status_of_exact_empty _ semantics _ aligned.1 bound
    (cfclbri_source_endpoint_atomic_separation aligned.1) rfl RS.R cfclbri_full_production_solid_descriptor

/-- Accurate-name alias for the solid CFClBrI scheduled assignment. -/
theorem cfclbri_solid_scheduled_R
    (semantics : SingleWedgeSourceRegression.source.AromaticCanonicalRuleSemantics 0) :
    scheduledDrawingSpatialStatus SingleWedgeSourceRegression.source semantics 2 cfclbriProductionCenter =
      .assigned (.chiral RS.R) :=
  cfclbri_solid_scheduled_S semantics

set_option maxHeartbeats 800000 in
/-- **Hashed CFClBrI drawing, historical API key.**  The old suffix says `R`; under the corrected
calibration the positive priority-ordered determinant is `S`.  Use `cfclbri_hashed_scheduled_S`
for new code. -/
theorem cfclbri_hashed_scheduled_R
    (semantics : (SingleWedgeSourceRegression.sourceWithStyle .hashedWedge).AromaticCanonicalRuleSemantics 0) :
    scheduledDrawingSpatialStatus (SingleWedgeSourceRegression.sourceWithStyle .hashedWedge)
      semantics 2 hashedProductionCenter = .assigned (.chiral RS.S) := by
  obtain ⟨drawing, extracted⟩ := Option.isSome_iff_exists.mp SingleWedgeSourceRegression.hashed_source_recognized
  have bound : SourceFrame (SingleWedgeSourceRegression.sourceWithStyle .hashedWedge)
      hashedProductionCenter.1.val drawing := (extract?_eq_some_iff _ _ drawing).mp extracted
  have separated : SourceEndpointAtomicSeparation (SingleWedgeSourceRegression.sourceWithStyle .hashedWedge)
      drawing := by
    intro left right _ _ same
    exact cfclbri_source_atomZ_injective same
  exact status_of_exact_empty _ semantics _ drawing bound separated rfl RS.S
    cfclbri_full_production_hashed_descriptor

/-- Accurate-name alias for the hashed CFClBrI scheduled assignment. -/
theorem cfclbri_hashed_scheduled_S
    (semantics : (SingleWedgeSourceRegression.sourceWithStyle .hashedWedge).AromaticCanonicalRuleSemantics 0) :
    scheduledDrawingSpatialStatus (SingleWedgeSourceRegression.sourceWithStyle .hashedWedge)
      semantics 2 hashedProductionCenter = .assigned (.chiral RS.S) :=
  cfclbri_hashed_scheduled_R semantics

theorem cfclbri_solid_scheduled_report_member
    (semantics : SingleWedgeSourceRegression.source.AromaticCanonicalRuleSemantics 0) :
    (⟨cfclbriProductionCenter, .assigned (.chiral RS.R)⟩ : TetrahedralStatusRow SingleWedgeSourceRegression.source) ∈
      scheduledTetrahedralReport SingleWedgeSourceRegression.source semantics 2 :=
  (mem_scheduledTetrahedralReport_iff _ semantics 2 _).mpr (cfclbri_solid_scheduled_S semantics).symm

theorem cfclbri_hashed_scheduled_report_member
    (semantics : (SingleWedgeSourceRegression.sourceWithStyle .hashedWedge).AromaticCanonicalRuleSemantics 0) :
    (⟨hashedProductionCenter, .assigned (.chiral RS.S)⟩ :
      TetrahedralStatusRow (SingleWedgeSourceRegression.sourceWithStyle .hashedWedge)) ∈
      scheduledTetrahedralReport (SingleWedgeSourceRegression.sourceWithStyle .hashedWedge) semantics 2 :=
  (mem_scheduledTetrahedralReport_iff _ semantics 2 _).mpr (cfclbri_hashed_scheduled_R semantics).symm

noncomputable def solidConcreteSemantics :=
  SingleWedgeSourceRegression.source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics 0 2

noncomputable def hashedConcreteSemantics :=
  (SingleWedgeSourceRegression.sourceWithStyle .hashedWedge).aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics 0 2

theorem cfclbri_solid_concrete_report_and_model :
    (⟨cfclbriProductionCenter, .assigned (.chiral RS.R)⟩ : TetrahedralStatusRow SingleWedgeSourceRegression.source) ∈
        scheduledTetrahedralReport SingleWedgeSourceRegression.source solidConcreteSemantics 2 ∧
      ((scheduledTetrahedralReport SingleWedgeSourceRegression.source solidConcreteSemantics 2).map
        TetrahedralStatusRow.center).count cfclbriProductionCenter = 1 ∧
      (SingleWedgeSourceRegression.source.aromaticCanonicalOccurrenceSystem solidConcreteSemantics).CIPModel
        (SingleWedgeSourceRegression.source.aromaticCanonicalScheduledAuxiliaryState solidConcreteSemantics) :=
  ⟨cfclbri_solid_scheduled_report_member _, scheduledTetrahedralReport_center_count_one _ _ 2 _,
    SingleWedgeSourceRegression.source.aromaticCanonicalScheduledAuxiliaryState_cipModel _⟩

theorem cfclbri_hashed_concrete_report_and_model :
    (⟨hashedProductionCenter, .assigned (.chiral RS.S)⟩ :
      TetrahedralStatusRow (SingleWedgeSourceRegression.sourceWithStyle .hashedWedge)) ∈
        scheduledTetrahedralReport (SingleWedgeSourceRegression.sourceWithStyle .hashedWedge) hashedConcreteSemantics 2 ∧
      ((scheduledTetrahedralReport (SingleWedgeSourceRegression.sourceWithStyle .hashedWedge) hashedConcreteSemantics 2).map
        TetrahedralStatusRow.center).count hashedProductionCenter = 1 ∧
      ((SingleWedgeSourceRegression.sourceWithStyle .hashedWedge).aromaticCanonicalOccurrenceSystem hashedConcreteSemantics).CIPModel
        ((SingleWedgeSourceRegression.sourceWithStyle .hashedWedge).aromaticCanonicalScheduledAuxiliaryState hashedConcreteSemantics) :=
  ⟨cfclbri_hashed_scheduled_report_member _, scheduledTetrahedralReport_center_count_one _ _ 2 _,
    (SingleWedgeSourceRegression.sourceWithStyle .hashedWedge).aromaticCanonicalScheduledAuxiliaryState_cipModel _⟩

end TetraStereo.UniversalProof.ScheduledDrawingSpatialEndToEndProofs.ScheduledDrawingSpatialEndToEnd
