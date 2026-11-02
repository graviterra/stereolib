import TetraStereo.UniversalProof.CentralDrawingRule3TieProofs.CentralDrawingTrackedSort

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace TetraStereo.UniversalProof.CentralDrawingRule3TieProofs.CentralDrawingRule45Comparison

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.OneCenter.RationalTetrahedralPermutation
open TetraStereo.UniversalProof.ThreeCenterDrawingSourceProofs.ThreeCenterDrawingSource

























def centralPriorityPoints : List CartesianPoint3 :=
  centralHypotheticalOrderRightFirst.map
    (pointVector centralFrame.first centralFrame.second centralFrame.third centralFrame.fourth)

theorem central_actual_slot_alignment :
    findSlotAlignment? centralFrame.endpoints (centralRoots.map (cursorAtomID source)) =
      some [0, 1, 2, 3] := by
  rw [actual_endpoint_orders.1, central_root_ids]
  decide +kernel

theorem central_actual_priority_point_lookup :
    centralTrackedOrder.highestFirst.mapM
      (drawingPointForOccurrenceSlot? centralFrame [0, 1, 2, 3]) =
      some centralPriorityPoints := by
  rfl

/-- The actual production tracked order is the right-first order; at that order the exact
geometry is uppercase `R` (negative oriented volume).  The definition of the point list and this
coupling to `centralTrackedOrder` are the corrected-calibration replacements for the historical
left-first order. -/
theorem central_actual_priority_geometry_R :
    descriptorOfPriorityOrderedPoints? centralPriorityPoints = some RS.R :=
  central_geometry_hypothetical_right_first

noncomputable def centralPriorityEvidence : OrdinaryPriorityEvidence source branchCarrierFuel :=
  { drawing := centralFrame
    slots := [0, 1, 2, 3]
    keys := centralKeyFrame
    tracked := centralTrackedOrder
    points := centralPriorityPoints }

theorem central_actual_priority_evidence_computed :
    occurrenceOrdinaryPriorityEvidence? source centralTarget centralView 4 =
      some centralPriorityEvidence := by
  have drawing : extract? source centralPerceivedCenter.1 = some centralFrame :=
    central_extractor_returns_actual_frame
  have keysComputed :
      source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame? centralTarget centralView
        4 centralRoots = some centralKeyFrame := centralKeyFrame_computed
  simp [occurrenceOrdinaryPriorityEvidence?, central_perceived_center_recovered,
    drawing, actual_ligand_frames.1, central_actual_slot_alignment,
    keysComputed, central_actual_safe_tracked_order_computed,
    central_actual_priority_point_lookup, centralPriorityEvidence]

theorem central_actual_priority_evidence_meaning :
    OccurrenceOrdinaryPriorityEvidenceMeaning source centralTarget centralView 4
      centralPriorityEvidence :=
  occurrenceOrdinaryPriorityEvidence?_sound source centralTarget centralView 4
    centralPriorityEvidence central_actual_priority_evidence_computed

/-- Complete production descriptor at the original target, without execution premises. -/
theorem central_actual_occurrence_descriptor_pseudo_r :
    occurrenceOrdinaryDescriptor? source centralTarget centralView 4 =
      some (.pseudoasymmetric .r) := by
  simp only [occurrenceOrdinaryDescriptor?, central_actual_priority_evidence_computed]
  change (descriptorOfPriorityOrderedPoints? centralPriorityPoints).bind
    (fun raw => some (classifyTetrahedralRSPseudo raw centralTrackedOrder.pseudoComparisons)) = _
  rw [central_actual_priority_geometry_R]
  rfl

theorem central_actual_occurrence_descriptor_meaning :
    OccurrenceOrdinaryDescriptorMeaning source centralTarget centralView 4
      (.pseudoasymmetric .r) :=
  occurrenceOrdinaryDescriptor?_sound source centralTarget centralView 4
    (.pseudoasymmetric .r) central_actual_occurrence_descriptor_pseudo_r

theorem central_scheduled_drawing_pseudo_r :
    drawingScheduledState centralTarget = some (.pseudoasymmetric .r) := by
  rw [← occurrenceOrdinaryModel_evaluates source drawingScheduledState
    drawingScheduledState_cipModel centralTarget]
  exact central_actual_occurrence_descriptor_pseudo_r

/-- Central and daughter labels belong to one inhabited, causally evaluated occurrence model.
Under the corrected calibration the daughters are `S` (left, historical key
`left_scheduled_drawing_R`) and `R` (right, historical key `right_scheduled_drawing_S`), while the
central descriptor remains lowercase `r` because the tracked order flips together with the
labels and the geometry at the new order is again `R`. -/
theorem actual_three_center_scheduled_drawing_labels :
    drawingScheduledState centralTarget = some (.pseudoasymmetric .r) ∧
      drawingScheduledState leftOccurrence = some (.chiral RS.S) ∧
      drawingScheduledState rightOccurrence = some (.chiral RS.R) :=
  ⟨central_scheduled_drawing_pseudo_r, left_scheduled_drawing_R, right_scheduled_drawing_S⟩

theorem central_actual_final_descriptor_pseudo_r :
    ordinaryDescriptor? source branchCarrierFuel centralPerceivedCenter centralView 4 =
      some (.pseudoasymmetric .r) := by
  rw [← occurrenceOrdinaryDescriptor?_final_eq source branchCarrierFuel
    centralPerceivedCenter centralView 4]
  exact central_actual_occurrence_descriptor_pseudo_r

end TetraStereo.UniversalProof.CentralDrawingRule3TieProofs.CentralDrawingRule45Comparison
