import TetraStereo.UniversalProof.CentralDrawingRule3TieProofs.CentralDrawingPseudoDescriptor
import TetraStereo.UniversalProof.ScheduledDrawingSpatialEndToEndProofs.ScheduledDrawingSpatialWholeMolecule

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

namespace TetraStereo.UniversalProof.ThreeCenterWholeMoleculeDrawingProofs.ThreeCenterWholeMoleculeDrawing

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.UniversalProof.ThreeCenterDrawingSourceProofs.ThreeCenterDrawingSource
open TetraStereo.UniversalProof.ScheduledDrawingSpatialEndToEndProofs.ScheduledDrawingSpatialIntegration
open TetraStereo.UniversalProof.ScheduledDrawingSpatialEndToEndProofs.ScheduledDrawingSpatialWholeMolecule
open TetraStereo.UniversalProof.CentralDrawingRule3TieProofs.CentralDrawingRule45Comparison






























/-! ## Selected semantics schedules the actual drawing model -/

/-- The selected ordinary occurrence semantics, at carrier fuel `1` and rule fuel `4`. -/
noncomputable def selectedSemantics : source.AromaticCanonicalRuleSemantics branchCarrierFuel :=
  occurrenceOrdinaryAuxiliarySemantics source branchCarrierFuel 4

/-- The selected semantics' causal scheduled state is the drawing model state, by occurrence-system
uniqueness — not by a seed, a report expectation or a supplied label. -/
theorem selectedScheduledState_eq_drawingScheduledState :
    source.aromaticCanonicalScheduledAuxiliaryState selectedSemantics = drawingScheduledState :=
  (source.aromaticCanonicalOccurrenceSystem selectedSemantics).cipModel_unique_of_wellFounded
    (source.aromaticCanonicalDerivationStepCorrespondence selectedSemantics)
    (@source.AromaticCanonicalDepthDependency branchCarrierFuel)
    (source.aromaticCanonicalDepthDependency_wellFounded branchCarrierFuel)
    (source.aromaticCanonicalEvaluatorLocal selectedSemantics)
    _ _
    (source.aromaticCanonicalScheduledAuxiliaryState_cipModel selectedSemantics)
    (by simpa only [selectedSemantics] using drawingScheduledState_cipModel)

/-- The whole-molecule adapter's scheduled view at any center is the drawing model's view. -/
theorem selectedScheduledView_eq_drawingView
    (center : source.AromaticCanonicalTetrahedralCenter) :
    scheduledDrawingView source selectedSemantics center =
      source.aromaticCanonicalDependencyView drawingScheduledState
        (source.aromaticCanonicalFinalOccurrence branchCarrierFuel center) := by
  unfold scheduledDrawingView
  rw [selectedScheduledState_eq_drawingScheduledState]

/-! ## Final daughter occurrences rooted at atoms `3` and `6` -/

noncomputable def leftFinalRoots : List (source.AromaticCanonicalRerootCursor branchCarrierFuel) :=
  finalOccurrenceRoots source branchCarrierFuel leftPerceivedCenter

noncomputable def rightFinalRoots : List (source.AromaticCanonicalRerootCursor branchCarrierFuel) :=
  finalOccurrenceRoots source branchCarrierFuel rightPerceivedCenter

/-- Both final cursor-ID lists are permutations of the actual written endpoint lists. -/
theorem daughterFinalRootIDs_sameIDs :
    (leftFinalRoots.map (cursorAtomID source)).Perm (leftFrame.endpoints.map some) ∧
      (rightFinalRoots.map (cursorAtomID source)).Perm (rightFrame.endpoints.map some) := by
  constructor
  · have official : (officialRootIDs source leftPerceivedCenter.1).Perm
        (leftFrame.endpoints.map some) := by
      rw [actual_endpoint_orders.2.1]
      decide +kernel
    have transport := (finalOccurrenceRootIDs_perm_officialRootIDs source branchCarrierFuel
      leftPerceivedCenter).trans official
    simpa [finalOccurrenceRootIDs, leftFinalRoots] using transport
  · have official : (officialRootIDs source rightPerceivedCenter.1).Perm
        (rightFrame.endpoints.map some) := by
      rw [actual_endpoint_orders.2.2]
      decide +kernel
    have transport := (finalOccurrenceRootIDs_perm_officialRootIDs source branchCarrierFuel
      rightPerceivedCenter).trans official
    simpa [finalOccurrenceRootIDs, rightFinalRoots] using transport

theorem daughterFinalRoots_length :
    leftFinalRoots.length = 4 ∧ rightFinalRoots.length = 4 := by
  constructor
  · have transfer := daughterFinalRootIDs_sameIDs.1
    rw [actual_endpoint_orders.2.1] at transfer
    simpa using transfer.length_eq
  · have transfer := daughterFinalRootIDs_sameIDs.2
    rw [actual_endpoint_orders.2.2] at transfer
    simpa using transfer.length_eq

/-- The actual final left daughter four-ligand frame, built from the returned cursor list. -/
noncomputable def leftFinalFrame : source.AromaticCanonicalOccurrenceFourLigandFrame branchCarrierFuel :=
  { roots := leftFinalRoots, rootsLength := daughterFinalRoots_length.1 }

/-- The actual final right daughter four-ligand frame, built from the returned cursor list. -/
noncomputable def rightFinalFrame : source.AromaticCanonicalOccurrenceFourLigandFrame branchCarrierFuel :=
  { roots := rightFinalRoots, rootsLength := daughterFinalRoots_length.2 }

theorem daughterFinalFrames_real :
    OccurrenceRootsReal source leftFinalFrame ∧ OccurrenceRootsReal source rightFinalFrame := by
  constructor
  · intro slot
    fin_cases slot <;> exact ⟨_, rfl, rfl⟩
  · intro slot
    fin_cases slot <;> exact ⟨_, rfl, rfl⟩

/-! ## Final daughter descriptors from the actual returned roots and source geometry -/

/-- The **final** left occurrence, rooted at atom `3` with empty address, produces drawing `S`
for every restricted view from the actual returned roots, atomic separation and no-double, under
the corrected geometry calibration.  The declaration name `_R` is the historical kernel key; the
accurately named sibling is `left_final_occurrence_descriptor_S`. -/
theorem left_final_occurrence_descriptor_R
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence branchCarrierFuel leftPerceivedCenter)) :
    occurrenceOrdinaryDescriptor? source
        (source.aromaticCanonicalFinalOccurrence branchCarrierFuel leftPerceivedCenter) view 4 =
      some (.chiral RS.S) := by
  have computed := occurrenceOrdinaryDescriptor?_eq_chiral_of_written_priority source
    (source.aromaticCanonicalFinalOccurrence branchCarrierFuel leftPerceivedCenter) view
    leftPerceivedCenter
    (occurrenceTetrahedralCenter?_final source branchCarrierFuel leftPerceivedCenter)
    leftFinalFrame
    (finalOccurrenceRoots_are_returned source branchCarrierFuel leftPerceivedCenter)
    leftFrame
    (show SourceFrame source leftPerceivedCenter.1.val leftFrame from left_source_frame)
    daughterFinalFrames_real.1 daughterFinalRootIDs_sameIDs.1
    left_endpoint_atomic_separation source_no_ordinary_double_bond
    writtenPriorityOrder written_priority_is_actual_atomic_order.1
    written_priority_is_actual_atomic_order.2.1 RS.S actual_sorted_source_geometry.1
  simpa [branchCarrierFuel] using computed

/-- Accurately named sibling of the historical `left_final_occurrence_descriptor_R` key. -/
theorem left_final_occurrence_descriptor_S
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence branchCarrierFuel leftPerceivedCenter)) :
    occurrenceOrdinaryDescriptor? source
        (source.aromaticCanonicalFinalOccurrence branchCarrierFuel leftPerceivedCenter) view 4 =
      some (.chiral RS.S) :=
  left_final_occurrence_descriptor_R view

/-- The **final** right occurrence, rooted at atom `6` with empty address, produces drawing `R`
for every restricted view from the actual returned roots, atomic separation and no-double, under
the corrected geometry calibration.  The declaration name `_S` is the historical kernel key; the
accurately named sibling is `right_final_occurrence_descriptor_R`. -/
theorem right_final_occurrence_descriptor_S
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence branchCarrierFuel rightPerceivedCenter)) :
    occurrenceOrdinaryDescriptor? source
        (source.aromaticCanonicalFinalOccurrence branchCarrierFuel rightPerceivedCenter) view 4 =
      some (.chiral RS.R) := by
  have computed := occurrenceOrdinaryDescriptor?_eq_chiral_of_written_priority source
    (source.aromaticCanonicalFinalOccurrence branchCarrierFuel rightPerceivedCenter) view
    rightPerceivedCenter
    (occurrenceTetrahedralCenter?_final source branchCarrierFuel rightPerceivedCenter)
    rightFinalFrame
    (finalOccurrenceRoots_are_returned source branchCarrierFuel rightPerceivedCenter)
    rightFrame
    (show SourceFrame source rightPerceivedCenter.1.val rightFrame from right_source_frame)
    daughterFinalFrames_real.2 daughterFinalRootIDs_sameIDs.2
    right_endpoint_atomic_separation source_no_ordinary_double_bond
    writtenPriorityOrder written_priority_is_actual_atomic_order.1
    written_priority_is_actual_atomic_order.2.2 RS.R actual_sorted_source_geometry.2
  simpa [branchCarrierFuel] using computed

/-- Accurately named sibling of the historical `right_final_occurrence_descriptor_S` key. -/
theorem right_final_occurrence_descriptor_R
    (view : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalFinalOccurrence branchCarrierFuel rightPerceivedCenter)) :
    occurrenceOrdinaryDescriptor? source
        (source.aromaticCanonicalFinalOccurrence branchCarrierFuel rightPerceivedCenter) view 4 =
      some (.chiral RS.R) :=
  right_final_occurrence_descriptor_S view

/-- The center adapter reads the final daughter labels through the common scheduled view. -/
theorem left_selected_ordinary_descriptor :
    ordinaryDescriptor? source branchCarrierFuel leftPerceivedCenter
        (scheduledDrawingView source selectedSemantics leftPerceivedCenter) 4 =
      some (.chiral RS.S) := by
  rw [← occurrenceOrdinaryDescriptor?_final_eq source branchCarrierFuel leftPerceivedCenter
    (scheduledDrawingView source selectedSemantics leftPerceivedCenter) 4]
  exact left_final_occurrence_descriptor_R _

theorem right_selected_ordinary_descriptor :
    ordinaryDescriptor? source branchCarrierFuel rightPerceivedCenter
        (scheduledDrawingView source selectedSemantics rightPerceivedCenter) 4 =
      some (.chiral RS.R) := by
  rw [← occurrenceOrdinaryDescriptor?_final_eq source branchCarrierFuel rightPerceivedCenter
    (scheduledDrawingView source selectedSemantics rightPerceivedCenter) 4]
  exact right_final_occurrence_descriptor_S _

/-- The central adapter reads the actual geometry-derived pseudoasymmetric `r` at the same view. -/
theorem central_selected_ordinary_descriptor :
    ordinaryDescriptor? source branchCarrierFuel centralPerceivedCenter
        (scheduledDrawingView source selectedSemantics centralPerceivedCenter) 4 =
      some (.pseudoasymmetric .r) := by
  rw [selectedScheduledView_eq_drawingView]
  simpa [centralView, centralTarget] using central_actual_final_descriptor_pseudo_r

/-! ## Channel status of each center: spatial absence is neutral -/

/-- In the selected semantics, each center's whole-molecule status is the sole ordinary drawing
label; both spatial channels are absent and stay neutral.  Under the corrected calibration the
final daughter labels are left `S` and right `R`; the central pseudoasymmetric label remains `r`. -/
theorem three_center_selected_status :
    scheduledDrawingSpatialStatus source selectedSemantics 4 centralPerceivedCenter =
        .assigned (.pseudoasymmetric .r) ∧
      scheduledDrawingSpatialStatus source selectedSemantics 4 leftPerceivedCenter =
        .assigned (.chiral RS.S) ∧
      scheduledDrawingSpatialStatus source selectedSemantics 4 rightPerceivedCenter =
        .assigned (.chiral RS.R) := by
  have noSpatial : source.spatial? = none := source_has_only_drawing_configuration.1
  have centralDirect := aromaticCanonicalOccurrenceRule3Through5Descriptor?_eq_none_of_spatial_none
    source noSpatial
    (source.aromaticCanonicalFinalOccurrence branchCarrierFuel centralPerceivedCenter)
    (scheduledDrawingView source selectedSemantics centralPerceivedCenter) 4
  have centralTie := aromaticCanonicalScheduledRule3Through6RSPseudoDescriptor?_eq_none_of_spatial_none
    source noSpatial selectedSemantics 4 centralPerceivedCenter
  have leftDirect := aromaticCanonicalOccurrenceRule3Through5Descriptor?_eq_none_of_spatial_none
    source noSpatial
    (source.aromaticCanonicalFinalOccurrence branchCarrierFuel leftPerceivedCenter)
    (scheduledDrawingView source selectedSemantics leftPerceivedCenter) 4
  have leftTie := aromaticCanonicalScheduledRule3Through6RSPseudoDescriptor?_eq_none_of_spatial_none
    source noSpatial selectedSemantics 4 leftPerceivedCenter
  have rightDirect := aromaticCanonicalOccurrenceRule3Through5Descriptor?_eq_none_of_spatial_none
    source noSpatial
    (source.aromaticCanonicalFinalOccurrence branchCarrierFuel rightPerceivedCenter)
    (scheduledDrawingView source selectedSemantics rightPerceivedCenter) 4
  have rightTie := aromaticCanonicalScheduledRule3Through6RSPseudoDescriptor?_eq_none_of_spatial_none
    source noSpatial selectedSemantics 4 rightPerceivedCenter
  refine ⟨?_, ?_, ?_⟩
  · unfold scheduledDrawingSpatialStatus scheduledDrawingOutputs
    rw [central_selected_ordinary_descriptor, centralDirect, centralTie]
    exact foldStatus_some_none_none _
  · unfold scheduledDrawingSpatialStatus scheduledDrawingOutputs
    rw [left_selected_ordinary_descriptor, leftDirect, leftTie]
    exact foldStatus_some_none_none _
  · unfold scheduledDrawingSpatialStatus scheduledDrawingOutputs
    rw [right_selected_ordinary_descriptor, rightDirect, rightTie]
    exact foldStatus_some_none_none _

/-! ## One actual row per center, inside the same whole-molecule report -/

def centralReportRow : TetrahedralStatusRow source :=
  { center := centralPerceivedCenter, status := .assigned (.pseudoasymmetric .r) }

def leftReportRow : TetrahedralStatusRow source :=
  { center := leftPerceivedCenter, status := .assigned (.chiral RS.S) }

def rightReportRow : TetrahedralStatusRow source :=
  { center := rightPerceivedCenter, status := .assigned (.chiral RS.R) }

theorem three_center_report_rows_mem :
    centralReportRow ∈ scheduledTetrahedralReport source selectedSemantics 4 ∧
      leftReportRow ∈ scheduledTetrahedralReport source selectedSemantics 4 ∧
      rightReportRow ∈ scheduledTetrahedralReport source selectedSemantics 4 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_scheduledTetrahedralReport_iff source selectedSemantics 4 centralReportRow]
    exact three_center_selected_status.1.symm
  · rw [mem_scheduledTetrahedralReport_iff source selectedSemantics 4 leftReportRow]
    exact three_center_selected_status.2.1.symm
  · rw [mem_scheduledTetrahedralReport_iff source selectedSemantics 4 rightReportRow]
    exact three_center_selected_status.2.2.symm

theorem three_center_report_center_count_one :
    ((scheduledTetrahedralReport source selectedSemantics 4).map
        TetrahedralStatusRow.center).count centralPerceivedCenter = 1 ∧
      ((scheduledTetrahedralReport source selectedSemantics 4).map
        TetrahedralStatusRow.center).count leftPerceivedCenter = 1 ∧
      ((scheduledTetrahedralReport source selectedSemantics 4).map
        TetrahedralStatusRow.center).count rightPerceivedCenter = 1 :=
  ⟨scheduledTetrahedralReport_center_count_one source selectedSemantics 4 centralPerceivedCenter,
   scheduledTetrahedralReport_center_count_one source selectedSemantics 4 leftPerceivedCenter,
   scheduledTetrahedralReport_center_count_one source selectedSemantics 4 rightPerceivedCenter⟩

theorem three_center_values :
    centralPerceivedCenter.1.val = 1 ∧ leftPerceivedCenter.1.val = 3 ∧
      rightPerceivedCenter.1.val = 6 :=
  ⟨rfl, rfl, rfl⟩

theorem three_center_centers_distinct :
    centralPerceivedCenter ≠ leftPerceivedCenter ∧
      centralPerceivedCenter ≠ rightPerceivedCenter ∧
      leftPerceivedCenter ≠ rightPerceivedCenter := by
  refine ⟨?_, ?_, ?_⟩
  · intro same
    have vals : centralPerceivedCenter.1.val = leftPerceivedCenter.1.val :=
      congrArg (fun center : source.AromaticCanonicalTetrahedralCenter => center.1.val) same
    rw [three_center_values.1, three_center_values.2.1] at vals
    exact absurd vals (by decide)
  · intro same
    have vals : centralPerceivedCenter.1.val = rightPerceivedCenter.1.val :=
      congrArg (fun center : source.AromaticCanonicalTetrahedralCenter => center.1.val) same
    rw [three_center_values.1, three_center_values.2.2] at vals
    exact absurd vals (by decide)
  · intro same
    have vals : leftPerceivedCenter.1.val = rightPerceivedCenter.1.val :=
      congrArg (fun center : source.AromaticCanonicalTetrahedralCenter => center.1.val) same
    rw [three_center_values.2.1, three_center_values.2.2] at vals
    exact absurd vals (by decide)

/-- **Actual whole-molecule drawing report.** In one drawing model/semantics, the whole-molecule
tetrahedral report contains exactly one row for each of the three actual centers — central
pseudoasymmetric `r`, final left daughter `S`, final right daughter `R` — and no spatial channel
contributes a label. -/
theorem actual_three_center_whole_molecule_drawing :
    source.aromaticCanonicalScheduledAuxiliaryState selectedSemantics = drawingScheduledState ∧
      centralReportRow ∈ scheduledTetrahedralReport source selectedSemantics 4 ∧
      leftReportRow ∈ scheduledTetrahedralReport source selectedSemantics 4 ∧
      rightReportRow ∈ scheduledTetrahedralReport source selectedSemantics 4 ∧
      scheduledDrawingSpatialStatus source selectedSemantics 4 centralPerceivedCenter =
        .assigned (.pseudoasymmetric .r) ∧
      scheduledDrawingSpatialStatus source selectedSemantics 4 leftPerceivedCenter =
        .assigned (.chiral RS.S) ∧
      scheduledDrawingSpatialStatus source selectedSemantics 4 rightPerceivedCenter =
        .assigned (.chiral RS.R) :=
  ⟨selectedScheduledState_eq_drawingScheduledState,
   three_center_report_rows_mem.1, three_center_report_rows_mem.2.1,
   three_center_report_rows_mem.2.2,
   three_center_selected_status.1, three_center_selected_status.2.1,
   three_center_selected_status.2.2⟩

end TetraStereo.UniversalProof.ThreeCenterWholeMoleculeDrawingProofs.ThreeCenterWholeMoleculeDrawing
