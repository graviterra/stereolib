import TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofsLibrary.MixedPlanarCausalRecoveryKernelCertificate

set_option autoImplicit false

namespace TetraStereo.UniversalProof.PlanarAllCandidateConflictClosureProofs.PlanarAllCandidateConflictClosure

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.ScheduledDrawingSpatialEndToEndProofs.ScheduledDrawingSpatialIntegration
open TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModel
open TetraStereo.UniversalProof.MixedPlanarCausalRecoveryProofs.SourceNativeMixedPlanarCausalModelKernelCertificate.ClosedAnnotatedPlanarWitness










theorem wedgeRecords_incident_eq_nil_of_plain
    (diagram : DiagramConfiguration)
    (plain : ∀ bond ∈ diagram.bonds, bond.style = .plain) (center : Nat) :
    wedgeRecords (incidentRecords diagram center) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro bond member
  have original : bond ∈ diagram.bonds := (List.mem_filter.mp member).1
  simp [isWedge, plain bond original]

theorem extract_none_of_plain_diagram
    (source : AuthoritativeChemicalInput) (diagram : DiagramConfiguration)
    (observed : source.diagram? = some diagram)
    (plain : ∀ bond ∈ diagram.bonds, bond.style = .plain)
    (center : Fin source.molecule.atomCount) :
    extract? source center = none := by
  rw [extract?_eq_none_iff_not_recognized]
  rintro ⟨diagram', positions, diagramEq, _positionsEq, admitted⟩
  have same : diagram' = diagram := Option.some.inj (diagramEq.symm.trans observed)
  rw [same] at admitted
  obtain ⟨_, _, _, _, _, _, _, _, _, count, _⟩ := admitted
  rw [wedgeRecords_incident_eq_nil_of_plain diagram plain center.val] at count
  exact Nat.zero_ne_one count

theorem annotated_all_bonds_plain :
    ∀ bond ∈ annotatedDiagram.bonds, bond.style = .plain := by decide +kernel

theorem annotated_extract_none_all_atoms (center : Fin annotatedSource.molecule.atomCount) :
    extract? annotatedSource center = none :=
  extract_none_of_plain_diagram annotatedSource annotatedDiagram rfl
    annotated_all_bonds_plain center

theorem annotated_drawing_absent_all_occurrences {carrierFuel : Nat}
    (target : annotatedSource.AromaticCanonicalOccurrence carrierFuel)
    (view : annotatedSource.AromaticCanonicalDependencyView target) (ruleFuel : Nat) :
    occurrenceOrdinaryDescriptor? annotatedSource target view ruleFuel = none :=
  occurrenceOrdinaryDescriptor?_eq_none_of_recovered_extract_none annotatedSource target view
    ruleFuel (fun center _ => annotated_extract_none_all_atoms center.1)

theorem absent_first_channel_not_conflict {Label : Type*} [DecidableEq Label]
    (output : Option Label) : foldStatus [none, output] ≠ .conflict := by
  cases output <;> simp [foldStatus, mergeChannel]

theorem annotated_all_own_joint_statuses_not_conflict (carrierFuel ruleFuel : Nat)
    (target : annotatedSource.AromaticCanonicalOccurrence carrierFuel) :
    planarJointStatus annotatedRaw annotatedSource annotatedAgreement annotatedWrittenExact
      carrierFuel ruleFuel target ≠ .conflict := by
  rw [planarJointStatus_eq_fold]
  have absent :
      planarJointDrawingDescriptor? annotatedRaw annotatedSource annotatedAgreement
        annotatedWrittenExact carrierFuel ruleFuel target = none :=
    annotated_drawing_absent_all_occurrences target
      (planarJointView annotatedRaw annotatedSource annotatedAgreement annotatedWrittenExact
        carrierFuel ruleFuel target) ruleFuel
  rw [absent]
  exact absent_first_channel_not_conflict _

theorem annotated_global_conflict_free (carrierFuel ruleFuel : Nat) :
    PlanarGlobalConflictFree annotatedRaw annotatedSource annotatedAgreement annotatedWrittenExact
      carrierFuel ruleFuel := by
  apply (planarGlobalConflictIssues_eq_nil_iff annotatedRaw annotatedSource annotatedAgreement
    annotatedWrittenExact carrierFuel ruleFuel).mpr
  intro center _
  exact annotated_all_own_joint_statuses_not_conflict carrierFuel ruleFuel
    (annotatedSource.aromaticCanonicalFinalOccurrence carrierFuel center)

theorem annotated_complete_audit :
    PlanarJointAuditObligation annotatedRaw annotatedSource annotatedAgreement annotatedWrittenExact
      1 4 :=
  ⟨annotated_global_conflict_free 1 4, annotated_partialAudit⟩

end TetraStereo.UniversalProof.PlanarAllCandidateConflictClosureProofs.PlanarAllCandidateConflictClosure
