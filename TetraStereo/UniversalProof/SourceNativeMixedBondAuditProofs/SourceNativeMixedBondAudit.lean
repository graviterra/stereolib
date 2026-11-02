import TetraStereo.UniversalProof.SourceNativeRawAnnotationGuardProofs.SourceNativeAnnotationAuditSoundness

set_option autoImplicit false

namespace TetraStereo.UniversalProof.SourceNativeMixedBondAuditProofs.SourceNativeMixedBondAudit

open TetraStereo.OneCenter TetraStereo.OneCenter.AuthoritativeChemicalInput
open SourceNativeRawAnnotationGuardProofs.SourceNativeDevelopmentTransaction
open SourceNativeRawAnnotationGuardProofs.SourceNativeAnnotationAuditSoundness

















def sourceBondAuditIssues (source : AuthoritativeChemicalInput) : List (AnnotationIssue source) :=
  match source.diagram? with
  | none => []
  | some diagram => diagram.bonds.flatMap (bondAuditIssues source)

def SourceBondAnnotationsAccepted (source : AuthoritativeChemicalInput) : Prop :=
  match source.diagram? with
  | none => True
  | some diagram => ∀ bond ∈ diagram.bonds, BondAnnotationAccepted source bond

theorem sourceBondAuditIssues_eq_nil_iff (source : AuthoritativeChemicalInput) :
    sourceBondAuditIssues source = [] ↔ SourceBondAnnotationsAccepted source := by
  cases observed : source.diagram? with
  | none => simp [sourceBondAuditIssues, SourceBondAnnotationsAccepted, observed]
  | some diagram =>
      simp [sourceBondAuditIssues, SourceBondAnnotationsAccepted, observed,
        List.flatMap_eq_nil_iff, bondAuditIssues_eq_nil_iff]

theorem bond_issue_retained (source : AuthoritativeChemicalInput)
    (diagram : DiagramConfiguration) (observed : source.diagram? = some diagram)
    (bond : DiagramBond) (present : bond ∈ diagram.bonds)
    (issue : AnnotationIssue source) (raised : issue ∈ bondAuditIssues source bond) :
    issue ∈ sourceBondAuditIssues source := by
  unfold sourceBondAuditIssues
  rw [observed]
  exact List.mem_flatMap.mpr ⟨bond, present, raised⟩

inductive RecordUniquenessIssue where
  | duplicateBondRecords
  | duplicateAtomConfigurationRecords
  deriving DecidableEq

def sourceRecordUniquenessIssues (source : AuthoritativeChemicalInput) :
    List RecordUniquenessIssue :=
  match source.diagram? with
  | none => []
  | some diagram =>
      (if diagram.bonds.Nodup then [] else [.duplicateBondRecords]) ++
        (if diagram.atomConfigurations.Nodup then [] else [.duplicateAtomConfigurationRecords])

def SourceRecordsUnique (source : AuthoritativeChemicalInput) : Prop :=
  match source.diagram? with
  | none => True
  | some diagram => diagram.bonds.Nodup ∧ diagram.atomConfigurations.Nodup

theorem sourceRecordUniquenessIssues_eq_nil_iff (source : AuthoritativeChemicalInput) :
    sourceRecordUniquenessIssues source = [] ↔ SourceRecordsUnique source := by
  cases observed : source.diagram? with
  | none => simp [sourceRecordUniquenessIssues, SourceRecordsUnique, observed]
  | some diagram =>
      by_cases bonds : diagram.bonds.Nodup <;>
        by_cases configurations : diagram.atomConfigurations.Nodup <;>
        simp [sourceRecordUniquenessIssues, SourceRecordsUnique, observed, bonds, configurations]

theorem duplicate_bonds_raise_issue (source : AuthoritativeChemicalInput)
    (diagram : DiagramConfiguration) (observed : source.diagram? = some diagram)
    (repeated : ¬ diagram.bonds.Nodup) :
    .duplicateBondRecords ∈ sourceRecordUniquenessIssues source := by
  simp [sourceRecordUniquenessIssues, observed, repeated]

theorem duplicate_atom_configurations_raise_issue (source : AuthoritativeChemicalInput)
    (diagram : DiagramConfiguration) (observed : source.diagram? = some diagram)
    (repeated : ¬ diagram.atomConfigurations.Nodup) :
    .duplicateAtomConfigurationRecords ∈ sourceRecordUniquenessIssues source := by
  simp [sourceRecordUniquenessIssues, observed, repeated]

inductive MixedBondAuditIssue (source : AuthoritativeChemicalInput) where
  | bond (issue : AnnotationIssue source)
  | recordUniqueness (issue : RecordUniquenessIssue)
  deriving DecidableEq

def mixedBondAuditIssues (source : AuthoritativeChemicalInput) : List (MixedBondAuditIssue source) :=
  (sourceBondAuditIssues source).map MixedBondAuditIssue.bond ++
    (sourceRecordUniquenessIssues source).map MixedBondAuditIssue.recordUniqueness

def MixedBondAnnotationsAccepted (source : AuthoritativeChemicalInput) : Prop :=
  SourceBondAnnotationsAccepted source ∧ SourceRecordsUnique source

theorem mixedBondAuditIssues_eq_nil_iff (source : AuthoritativeChemicalInput) :
    mixedBondAuditIssues source = [] ↔ MixedBondAnnotationsAccepted source := by
  simp [mixedBondAuditIssues, MixedBondAnnotationsAccepted, List.append_eq_nil_iff,
    sourceBondAuditIssues_eq_nil_iff, sourceRecordUniquenessIssues_eq_nil_iff]

namespace ClosedMixedSources

/-- The preserved solid-wedge source has all four actual bond records and a clockwise parser
configuration. Bond acceptance does not establish agreement of their interpretations. -/
abbrev solidSource : AuthoritativeChemicalInput := Counterexamples.annotatedSource

/-- Same actual constitution, coordinates and clockwise atom configuration, changing only the
fourth bond from solid to hashed wedge. -/
def hashedDiagram : DiagramConfiguration :=
  { SingleWedgeSourceRegression.diagramWithStyle .hashedWedge with
    atomConfigurations := Counterexamples.annotatedDiagram.atomConfigurations }

def hashedSource : AuthoritativeChemicalInput :=
  { SingleWedgeSourceRegression.source with diagram? := some hashedDiagram }

theorem solid_bonds_only_clean : sourceBondAuditIssues solidSource = [] := by
  decide +kernel

theorem hashed_bonds_only_clean : sourceBondAuditIssues hashedSource = [] := by
  decide +kernel

theorem solid_preliminary_audit_clean : mixedBondAuditIssues solidSource = [] := by
  decide +kernel

theorem hashed_preliminary_audit_clean : mixedBondAuditIssues hashedSource = [] := by
  decide +kernel



theorem old_full_audit_still_refuses :
    diagramAuditIssues solidSource ≠ [] ∧ diagramAuditIssues hashedSource ≠ [] := by
  refine ⟨Counterexamples.annotated_audit_ne_nil, ?_⟩
  intro empty
  have member := Counterexamples.unsupportedAtomConfiguration_mem hashedSource hashedDiagram rfl
    ⟨0, .clockwise, .absolute⟩ (by simp [hashedDiagram, Counterexamples.annotatedDiagram])
  rw [empty] at member
  exact List.not_mem_nil member

/-- A duplicated plain record has an actual semantic partner and bypasses local wedge checks;
the separate uniqueness guard therefore addresses an observable per-bond policy gap. -/
def duplicatePlainDiagram : DiagramConfiguration :=
  { SingleWedgeSourceRegression.diagramWithStyle .plain with
    bonds := (SingleWedgeSourceRegression.diagramWithStyle .plain).bonds ++
      [⟨0, 1, .plain, .absolute⟩]
    atomConfigurations := Counterexamples.annotatedDiagram.atomConfigurations }

def duplicatePlainSource : AuthoritativeChemicalInput :=
  { SingleWedgeSourceRegression.source with diagram? := some duplicatePlainDiagram }

theorem duplicate_plain_record_refused :
    sourceBondAuditIssues duplicatePlainSource = [] ∧
      mixedBondAuditIssues duplicatePlainSource ≠ [] := by
  decide +kernel

end ClosedMixedSources
end TetraStereo.UniversalProof.SourceNativeMixedBondAuditProofs.SourceNativeMixedBondAudit
