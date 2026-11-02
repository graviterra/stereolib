import TetraStereo.UniversalProof.SourceNativeRawAnnotationGuardProofs.SourceNativeDevelopmentTransaction

set_option autoImplicit false

namespace TetraStereo.UniversalProof.SourceNativeRawAnnotationGuardProofs.SourceNativeAnnotationAuditSoundness

open TetraStereo.OneCenter TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open ScheduledDrawingSpatialEndToEndProofs.ScheduledDrawingSpatialIntegration ScheduledDrawingSpatialEndToEndProofs.ScheduledDrawingSpatialWholeMolecule
open SourceNativeDevelopmentTransaction








def ActualBinaryPartner (source : AuthoritativeChemicalInput) (bond : DiagramBond) : Prop :=
  ∃ interaction ∈ source.molecule.interactions, IsActualBinaryBond interaction ∧
    (interaction.participants = [bond.source, bond.target] ∨
      interaction.participants = [bond.target, bond.source])

def WedgeAnnotationAccepted (source : AuthoritativeChemicalInput) (bond : DiagramBond) : Prop :=
  ∃ bound : bond.source < source.molecule.atomCount, Recognized source bond.source ∧
    (⟨bond.source, bound⟩ : source.AromaticCanonicalAtom) ∈ source.aromaticCanonicalTetrahedralCenterSet

def BondAnnotationAccepted (source : AuthoritativeChemicalInput) (bond : DiagramBond) : Prop :=
  bond.scope = .absolute ∧ ActualBinaryPartner source bond ∧
    (bond.style = .plain ∨
      ((bond.style = .solidWedge ∨ bond.style = .hashedWedge) ∧ WedgeAnnotationAccepted source bond))

theorem wedge_checks_iff_accepted (source : AuthoritativeChemicalInput) (bond : DiagramBond) :
    (wedgeCenterRecognized? source bond = true ∧ wedgeSourcePerceived? source bond = true) ↔
      WedgeAnnotationAccepted source bond := by
  rw [wedgeCenterRecognized?_eq_true_iff, wedgeSourcePerceived?_eq_true_iff]
  constructor
  · rintro ⟨⟨_, recognized⟩, ⟨bound, perceived⟩⟩
    exact ⟨bound, recognized, perceived⟩
  · rintro ⟨bound, recognized, perceived⟩
    exact ⟨⟨bound, recognized⟩, ⟨bound, perceived⟩⟩

private theorem guarded_issue_nil_iff {Issue : Type} (condition : Prop) [Decidable condition]
    (issue : Issue) : (if condition then [] else [issue]) = [] ↔ condition := by
  by_cases accepted : condition <;> simp [accepted]

theorem bondAuditIssues_eq_nil_iff (source : AuthoritativeChemicalInput) (bond : DiagramBond) :
    bondAuditIssues source bond = [] ↔ BondAnnotationAccepted source bond := by
  unfold BondAnnotationAccepted ActualBinaryPartner
  rw [← hasActualBinaryBond?_eq_true_iff, ← wedge_checks_iff_accepted]
  cases style : bond.style <;>
    simp [bondAuditIssues, style, List.append_eq_nil_iff]

def DiagramAnnotationAccepted (source : AuthoritativeChemicalInput) : Prop :=
  match source.diagram? with
  | none => True
  | some diagram => diagram.atomConfigurations = [] ∧
      ∀ bond ∈ diagram.bonds, BondAnnotationAccepted source bond

theorem diagramAuditIssues_eq_nil_iff (source : AuthoritativeChemicalInput) :
    diagramAuditIssues source = [] ↔ DiagramAnnotationAccepted source := by
  cases observed : source.diagram? with
  | none => simp [diagramAuditIssues, DiagramAnnotationAccepted, observed]
  | some diagram =>
      simp [diagramAuditIssues, DiagramAnnotationAccepted, observed, List.append_eq_nil_iff,
        List.flatMap_eq_nil_iff, bondAuditIssues_eq_nil_iff]

theorem no_diagram_is_annotation_accepted (source : AuthoritativeChemicalInput)
    (absent : source.diagram? = none) : DiagramAnnotationAccepted source := by
  simp [DiagramAnnotationAccepted, absent]

def StatusAnnotationAccepted (source : AuthoritativeChemicalInput)
    (center : source.AromaticCanonicalAtom) (status : ChannelStatus AromaticCanonicalAuxiliaryLabel) : Prop :=
  status ≠ .conflict ∧ (center.val ∈ annotatedAtoms source → ∃ label, status = .assigned label)

private theorem status_issue_none_iff (source : AuthoritativeChemicalInput)
    (center : source.AromaticCanonicalAtom) (status : ChannelStatus AromaticCanonicalAuxiliaryLabel) :
    (match status with
    | .conflict => some (AnnotationIssue.tetrahedralStatusConflict center)
    | .unassigned => if center.val ∈ annotatedAtoms source then
        some (AnnotationIssue.annotatedCenterUnassigned center) else none
    | .assigned _ => none) = none ↔ StatusAnnotationAccepted source center status := by
  cases status <;> simp [StatusAnnotationAccepted]

def TetrahedralAnnotationAccepted (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel) (ruleFuel : Nat) : Prop :=
  ∀ center : source.AromaticCanonicalTetrahedralCenter,
    StatusAnnotationAccepted source center.1 (scheduledDrawingSpatialStatus source semantics ruleFuel center)

theorem tetrahedralAuditIssues_eq_nil_iff (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel) (ruleFuel : Nat) :
    tetrahedralAuditIssues source semantics ruleFuel = [] ↔
      TetrahedralAnnotationAccepted source semantics ruleFuel := by
  unfold tetrahedralAuditIssues
  rw [List.filterMap_eq_nil_iff]
  constructor
  · intro accepted center
    have raw := accepted ⟨center, scheduledDrawingSpatialStatus source semantics ruleFuel center⟩
      ((mem_scheduledTetrahedralReport_iff source semantics ruleFuel _).mpr rfl)
    exact (status_issue_none_iff source center.1
      (scheduledDrawingSpatialStatus source semantics ruleFuel center)).mp raw
  · intro accepted row present
    have status := (mem_scheduledTetrahedralReport_iff source semantics ruleFuel row).mp present
    apply (status_issue_none_iff source row.center.1 row.status).mpr
    rw [status]
    exact accepted row.center

theorem successfulProduction_annotation_policy (request : SourceNativeDevelopmentRequest)
    (rows : List (ScheduledHybridRepresentedResult request.source))
    (produced : request.produce = some rows) :
    DiagramAnnotationAccepted request.source ∧
      TetrahedralAnnotationAccepted request.source request.semantics request.ruleFuel := by
  have empty := (SourceNativeDevelopmentRequest.produce_eq_some_iff request rows).mp produced
  have emptyParts := List.append_eq_nil_iff.mp empty.2.1
  exact ⟨(diagramAuditIssues_eq_nil_iff request.source).mp emptyParts.1,
    (tetrahedralAuditIssues_eq_nil_iff request.source request.semantics request.ruleFuel).mp emptyParts.2⟩

/-- Every successful development transaction represents each actual wedge source by an assigned
scheduled row, with source recognition and actual perceived-center membership constructed. -/
theorem successfulProduction_every_wedge_assigned (request : SourceNativeDevelopmentRequest)
    (rows : List (ScheduledHybridRepresentedResult request.source))
    (produced : request.produce = some rows) (diagram : DiagramConfiguration)
    (observed : request.source.diagram? = some diagram) (bond : DiagramBond)
    (present : bond ∈ diagram.bonds) (wedge : bond.style = .solidWedge ∨ bond.style = .hashedWedge) :
    ∃ center : request.source.AromaticCanonicalTetrahedralCenter, ∃ label,
      center.1.val = bond.source ∧ Recognized request.source bond.source ∧
        scheduledDrawingSpatialStatus request.source request.semantics request.ruleFuel center = .assigned label ∧
        (⟨center, .assigned label⟩ : TetrahedralStatusRow request.source) ∈
          scheduledTetrahedralReport request.source request.semantics request.ruleFuel := by
  have policies := successfulProduction_annotation_policy request rows produced
  have diagramPolicy : diagram.atomConfigurations = [] ∧
      ∀ value ∈ diagram.bonds, BondAnnotationAccepted request.source value := by
    simpa only [DiagramAnnotationAccepted, observed] using policies.1
  have notPlain : bond.style ≠ .plain := by
    rcases wedge with style | style <;> simp [style]
  have wedgePolicy := ((diagramPolicy.2 bond present).2.2.resolve_left notPlain).2
  obtain ⟨bound, recognized, perceived⟩ := wedgePolicy
  let center : request.source.AromaticCanonicalTetrahedralCenter := ⟨⟨bond.source, bound⟩, perceived⟩
  have annotated : center.1.val ∈ annotatedAtoms request.source :=
    wedge_source_mem_annotatedAtoms request.source diagram observed bond present wedge
  obtain ⟨label, assigned⟩ := (policies.2 center).2 annotated
  exact ⟨center, label, rfl, recognized, assigned,
    (mem_scheduledTetrahedralReport_iff request.source request.semantics request.ruleFuel _).mpr assigned.symm⟩

theorem successfulProduction_no_tetrahedral_conflicts (request : SourceNativeDevelopmentRequest)
    (rows : List (ScheduledHybridRepresentedResult request.source))
    (produced : request.produce = some rows) (center : request.source.AromaticCanonicalTetrahedralCenter) :
    scheduledDrawingSpatialStatus request.source request.semantics request.ruleFuel center ≠ .conflict :=
  (successfulProduction_annotation_policy request rows produced).2 center |>.1

theorem actual_closed_development_request_satisfies_policy :
    DiagramAnnotationAccepted ClosedSource.closedRequest.source ∧
      TetrahedralAnnotationAccepted ClosedSource.closedRequest.source
        ClosedSource.closedRequest.semantics ClosedSource.closedRequest.ruleFuel :=
  successfulProduction_annotation_policy ClosedSource.closedRequest ClosedSource.closedRequest.report
    ClosedSource.closed_produce_eq_some

end TetraStereo.UniversalProof.SourceNativeRawAnnotationGuardProofs.SourceNativeAnnotationAuditSoundness
