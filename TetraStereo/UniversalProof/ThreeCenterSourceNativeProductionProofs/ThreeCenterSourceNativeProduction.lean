import TetraStereo.UniversalProof.ThreeCenterSourceNativeProductionProofs.ThreeCenterNormalizedSourceAdmission
import TetraStereo.UniversalProof.ThreeCenterWholeMoleculeDrawingProofs.ThreeCenterWholeMoleculeDrawing
import TetraStereo.UniversalProof.SourceNativeRawAnnotationGuardProofs.SourceNativeRawAnnotationGuard

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1600000

namespace TetraStereo.UniversalProof.ThreeCenterSourceNativeProductionProofs.ThreeCenterSourceNativeProduction

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.UniversalProof.ThreeCenterDrawingSourceProofs.ThreeCenterDrawingSource
open TetraStereo.UniversalProof.ThreeCenterWholeMoleculeDrawingProofs.ThreeCenterWholeMoleculeDrawing
open TetraStereo.UniversalProof.ScheduledDrawingSpatialEndToEndProofs.ScheduledDrawingSpatialIntegration
open TetraStereo.UniversalProof.ScheduledDrawingSpatialEndToEndProofs.ScheduledDrawingSpatialWholeMolecule
open TetraStereo.UniversalProof.SourceNativeRawAnnotationGuardProofs.SourceNativeDevelopmentTransaction
open TetraStereo.UniversalProof.SourceNativeRawAnnotationGuardProofs.SourceNativeRawAnnotationGuard
open TetraStereo.UniversalProof.ThreeCenterSourceNativeProductionProofs.ThreeCenterNormalizedSourceAdmission
















/-- Every one of the ten actual diagram records has a real binary semantic partner. -/
theorem actual_all_diagram_bonds_backed :
    ∀ bond ∈ diagram.bonds, hasActualBinaryBond? targetSource bond = true := by
  decide +kernel

/-- Recognition and canonical perception hold for every actual wedge record. -/
theorem actual_all_wedges_recognized_and_perceived :
    ∀ bond ∈ diagram.bonds,
      bond.style = .solidWedge ∨ bond.style = .hashedWedge →
        wedgeCenterRecognized? targetSource bond = true ∧
          wedgeSourcePerceived? targetSource bond = true := by
  decide +kernel

/-- The actual annotation list contains precisely the three drawn source atoms. -/
theorem actual_annotated_atoms : annotatedAtoms targetSource = [1, 3, 6] := by
  decide +kernel


theorem actual_diagram_audit_nil : diagramAuditIssues targetSource = [] := by
  decide +kernel

/-- Only the three actual carbon atoms are eligible connectivity-only tetrahedral elements. -/
theorem actual_eligible_atom_values :
    ∀ atom : targetSource.AromaticCanonicalAtom,
      targetSource.ConnectivityOnlyTetrahedralCenterAtom atom →
        atom.val = 1 ∨ atom.val = 3 ∨ atom.val = 6 := by
  unfold ConnectivityOnlyTetrahedralCenterAtom ConnectivityOnlyTetrahedralPeriodicElement
  decide +kernel

/-- Every perceived center is one of the three checked drawing centers. The converse is witnessed
by the three actual perceived-center values themselves, not by a detached atom list. -/
theorem actual_perceived_center_cases
    (center : targetSource.AromaticCanonicalTetrahedralCenter) :
    center = centralPerceivedCenter ∨ center = leftPerceivedCenter ∨
      center = rightPerceivedCenter := by
  have eligible := (targetSource.mem_aromaticCanonicalTetrahedralCenterSet_iff center.1).mp
    center.2 |>.1
  rcases actual_eligible_atom_values center.1 eligible with central | left | right
  · exact Or.inl (Subtype.ext (Fin.ext central))
  · exact Or.inr (Or.inl (Subtype.ext (Fin.ext left)))
  · exact Or.inr (Or.inr (Subtype.ext (Fin.ext right)))

/-- All perceived centers are assigned in the request's actual selected occurrence semantics. -/
theorem actual_all_perceived_centers_assigned :
    ∀ center : admissionRequest.source.AromaticCanonicalTetrahedralCenter,
      ∃ label, scheduledDrawingSpatialStatus admissionRequest.source
        admissionRequest.semantics admissionRequest.ruleFuel center = .assigned label := by
  intro center
  rcases actual_perceived_center_cases center with central | left | right
  · subst center
    exact ⟨_, three_center_selected_status.1⟩
  · subst center
    exact ⟨_, three_center_selected_status.2.1⟩
  · subst center
    exact ⟨_, three_center_selected_status.2.2⟩


theorem actual_tetrahedral_audit_nil :
    tetrahedralAuditIssues admissionRequest.source admissionRequest.semantics
      admissionRequest.ruleFuel = [] :=
  ClosedSource.tetrahedralAuditIssues_eq_nil_of_all_assigned _ _ _
    actual_all_perceived_centers_assigned


theorem actual_request_audit_nil : admissionRequest.auditIssues = [] := by
  change diagramAuditIssues admissionRequest.source ++
    tetrahedralAuditIssues admissionRequest.source admissionRequest.semantics
      admissionRequest.ruleFuel = []
  have diagramEmpty : diagramAuditIssues admissionRequest.source = [] :=
    actual_diagram_audit_nil
  rw [diagramEmpty, actual_tetrahedral_audit_nil]
  rfl

/-- The real annotation-free normalized request returns its actual analyzer payload. -/
theorem actual_guarded_production :
    guardedProduce admissionRequest = some admissionRequest.report :=
  (guardedProduce_eq_some_iff admissionRequest admissionRequest.report).mpr
    ⟨admissionRequest_annotationFree, admissionRequest_constitutionalAgreement,
      actual_request_audit_nil, rfl⟩

/-- The actual five-family payload contains central r and the final daughter R/S rows. -/
theorem actual_payload_three_rows :
    ScheduledHybridRepresentedResult.tetrahedral centralReportRow ∈ admissionRequest.report ∧
      ScheduledHybridRepresentedResult.tetrahedral leftReportRow ∈ admissionRequest.report ∧
      ScheduledHybridRepresentedResult.tetrahedral rightReportRow ∈ admissionRequest.report := by
  refine ⟨?_, ?_, ?_⟩
  · apply (mem_analyzeScheduledHybridRepresentedOfReady_iff admissionRequest.source
      admissionRequest.supplied admissionRequest.electronicReady admissionRequest.semantics
      admissionRequest.ruleFuel (.tetrahedral centralReportRow)).mpr
    exact three_center_selected_status.1.symm
  · apply (mem_analyzeScheduledHybridRepresentedOfReady_iff admissionRequest.source
      admissionRequest.supplied admissionRequest.electronicReady admissionRequest.semantics
      admissionRequest.ruleFuel (.tetrahedral leftReportRow)).mpr
    exact three_center_selected_status.2.1.symm
  · apply (mem_analyzeScheduledHybridRepresentedOfReady_iff admissionRequest.source
      admissionRequest.supplied admissionRequest.electronicReady admissionRequest.semantics
      admissionRequest.ruleFuel (.tetrahedral rightReportRow)).mpr
    exact three_center_selected_status.2.2.symm

/-- Inspect the tetrahedral centers of a mixed payload without conflating its other four families. -/
def tetrahedralCenterOfResult (result : ScheduledHybridRepresentedResult targetSource) :
    Option targetSource.AromaticCanonicalTetrahedralCenter :=
  match result with
  | .tetrahedral row => some row.center
  | .ordinaryDoubleBond _ | .oddOpenCumulene _ | .evenOpenCumulene _ |
      .fullyCyclicCumuleneParent _ => none

/-- Projecting the actual mixed payload recovers precisely the actual tetrahedral center report. -/
theorem actual_payload_tetrahedral_centers :
    admissionRequest.report.filterMap tetrahedralCenterOfResult =
      (scheduledTetrahedralReport admissionRequest.source admissionRequest.semantics
        admissionRequest.ruleFuel).map TetrahedralStatusRow.center := by
  have dropNone {α : Type} (items : List α) :
      items.filterMap (fun _ => (none : Option targetSource.AromaticCanonicalTetrahedralCenter)) =
        [] := by
    rw [List.filterMap_eq_nil_iff]
    intro _ _
    rfl
  unfold SourceNativeDevelopmentRequest.report analyzeScheduledHybridRepresentedOfReady
  simp only [List.filterMap_append, List.filterMap_map]
  simp [tetrahedralCenterOfResult, Function.comp_def, dropNone]

/-- Each actual center occurs once even after projection from the full five-family payload. -/
theorem actual_payload_center_counts_one :
    (admissionRequest.report.filterMap tetrahedralCenterOfResult).count centralPerceivedCenter = 1 ∧
      (admissionRequest.report.filterMap tetrahedralCenterOfResult).count leftPerceivedCenter = 1 ∧
      (admissionRequest.report.filterMap tetrahedralCenterOfResult).count rightPerceivedCenter = 1 := by
  simp only [actual_payload_tetrahedral_centers]
  exact three_center_report_center_count_one

/-- The three produced rows satisfy the existing independent represented-meaning relations. -/
theorem actual_produced_rows_meaning :
    ScheduledHybridRepresentedMeaning admissionRequest.source admissionRequest.supplied
        admissionRequest.electronicReady admissionRequest.semantics admissionRequest.ruleFuel
        (.tetrahedral centralReportRow) ∧
      ScheduledHybridRepresentedMeaning admissionRequest.source admissionRequest.supplied
        admissionRequest.electronicReady admissionRequest.semantics admissionRequest.ruleFuel
        (.tetrahedral leftReportRow) ∧
      ScheduledHybridRepresentedMeaning admissionRequest.source admissionRequest.supplied
        admissionRequest.electronicReady admissionRequest.semantics admissionRequest.ruleFuel
        (.tetrahedral rightReportRow) :=
  ⟨guardedProduce_member_sound admissionRequest admissionRequest.report actual_guarded_production
      _ actual_payload_three_rows.1,
    guardedProduce_member_sound admissionRequest admissionRequest.report actual_guarded_production
      _ actual_payload_three_rows.2.1,
    guardedProduce_member_sound admissionRequest admissionRequest.report actual_guarded_production
      _ actual_payload_three_rows.2.2⟩

/-- A closed successful development transaction with actual central r and final daughter R/S,
without an expected-label input, assumed callback, or assumed production success. -/
theorem actual_three_center_source_native_production :
    ∃ rows : List (ScheduledHybridRepresentedResult admissionRequest.source),
      guardedProduce admissionRequest = some rows ∧
        rows = admissionRequest.report ∧
        ScheduledHybridRepresentedResult.tetrahedral centralReportRow ∈ rows ∧
        ScheduledHybridRepresentedResult.tetrahedral leftReportRow ∈ rows ∧
        ScheduledHybridRepresentedResult.tetrahedral rightReportRow ∈ rows :=
  ⟨admissionRequest.report, actual_guarded_production, rfl,
    actual_payload_three_rows.1, actual_payload_three_rows.2.1, actual_payload_three_rows.2.2⟩

end TetraStereo.UniversalProof.ThreeCenterSourceNativeProductionProofs.ThreeCenterSourceNativeProduction
