import TetraStereo.OneCenter.IUPACRemaining71ProvisionInventory
import TetraStereo.OneCenter.CIPRule2MassData
import TetraStereo.OneCenter.CIAAWStandardAtomicWeights2021Generated

set_option autoImplicit false

/-!
# Reviewed three-row descriptor authority-data family

These rows expose exact lookups into byte-verified authority tables.  Atomic numbers are the
frozen 1--118 periodic-table domain.  Standard atomic weights reproduce CIAAW 2021 Table 1 as
14 intervals, 70 value/uncertainty records, and 34 explicit unavailable records.  Explicit
nuclides use the frozen CIAAW AME records through AME-2020.  No floating-point value or
caller-supplied data relation appears at this boundary.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

structure PeriodicAtomicNumberAuthorityObservation where
  atomicNumber : Nat
  deriving DecidableEq, Repr

def PeriodicAtomicNumberAuthorityObservation.Valid
    (observation : PeriodicAtomicNumberAuthorityObservation) : Prop :=
  observation.atomicNumber ∈ CIPRule2MassData.currentAtomicNumbers

structure StandardAtomicWeightAuthorityObservation where
  atomicNumber : Nat
  entry : CIAAWStandardAtomicWeights2021.Entry
  deriving DecidableEq, Repr

def StandardAtomicWeightAuthorityObservation.Valid
    (observation : StandardAtomicWeightAuthorityObservation) : Prop :=
  CIAAWStandardAtomicWeights2021.entry? observation.atomicNumber =
    some observation.entry

/-- The reviewed table and manifest name the identical publisher-version report bytes. -/
@[simp] theorem standardAtomicWeights2021_source_digest_exact :
    IUPACNormativeSource.sha256? .atomicWeights2021 =
      some CIAAWStandardAtomicWeights2021.sourceSha256 := by
  rfl

structure IsotopeAtomicMassAuthorityObservation where
  atomicNumber : Nat
  massNumber : Nat
  massPico : CIPRule2MassData.MassPico
  deriving DecidableEq, Repr

def IsotopeAtomicMassAuthorityObservation.Valid
    (observation : IsotopeAtomicMassAuthorityObservation) : Prop :=
  (observation.atomicNumber, observation.massNumber) ∈
      CIPRule2MassData.supportedNuclides ∧
    CIPRule2MassData.isotopeAtomicMassPico?
      observation.atomicNumber observation.massNumber = some observation.massPico

def periodicAtomicNumbersReference : ProvisionReference where
  Observation := PeriodicAtomicNumberAuthorityObservation
  Applicable := fun _source =>
    ∃ observation : PeriodicAtomicNumberAuthorityObservation, observation.Valid
  Judges := fun _source observation => observation.Valid

def standardAtomicWeightsReference : ProvisionReference where
  Observation := StandardAtomicWeightAuthorityObservation
  Applicable := fun _source =>
    ∃ observation : StandardAtomicWeightAuthorityObservation, observation.Valid
  Judges := fun _source observation => observation.Valid

def isotopeAtomicMassesReference : ProvisionReference where
  Observation := IsotopeAtomicMassAuthorityObservation
  Applicable := fun _source =>
    ∃ observation : IsotopeAtomicMassAuthorityObservation, observation.Valid
  Judges := fun _source observation => observation.Valid

inductive Remaining71AuthorityDataRow where
  | periodicAtomicNumbers
  | standardAtomicWeights
  | isotopeAtomicMasses
  deriving DecidableEq, Repr

namespace Remaining71AuthorityDataRow

def all : List Remaining71AuthorityDataRow :=
  [.periodicAtomicNumbers, .standardAtomicWeights, .isotopeAtomicMasses]

def provision : Remaining71AuthorityDataRow → IUPACNormativeProvision
  | .periodicAtomicNumbers => .periodicAtomicNumbers
  | .standardAtomicWeights => .standardAtomicWeights
  | .isotopeAtomicMasses => .isotopeAtomicMasses

def kind (_row : Remaining71AuthorityDataRow) : ProvisionKind :=
  .authorityData

def reference : Remaining71AuthorityDataRow → ProvisionReference
  | .periodicAtomicNumbers => periodicAtomicNumbersReference
  | .standardAtomicWeights => standardAtomicWeightsReference
  | .isotopeAtomicMasses => isotopeAtomicMassesReference

def semantics (row : Remaining71AuthorityDataRow) : ReviewedProvisionSemantics where
  kind := row.kind
  sourceSuppliesRule := true
  reference := row.reference

@[simp] theorem all_length : all.length = 3 := by
  rfl

theorem all_nodup : all.Nodup := by
  decide

@[simp] theorem all_provisions_exact :
    all.map provision = descriptorAssignmentAuthorityDataProvisions := by
  rfl

set_option maxRecDepth 16384 in
@[simp] theorem classifier_exact (row : Remaining71AuthorityDataRow) :
    globalProvisionKind row.provision = row.kind := by
  cases row <;> decide

/-! ## Frozen-table nonvacuity -/

def witnessInput : AuthoritativeChemicalInput where
  molecule := { atoms := [], interactions := [] }

@[simp] theorem witnessInput_structurallyWellFormed :
    witnessInput.StructurallyWellFormed := by
  simp [witnessInput, AuthoritativeChemicalInput.StructurallyWellFormed,
    SemanticMolecule.StructurallyWellFormed,
    AuthoritativeChemicalInput.SpatialIndicesWellFormed,
    AuthoritativeChemicalInput.DiagramIndicesWellFormed]

/-- Every authority-data row has a concrete witness read from the frozen periodic, CIAAW-2021,
and AME-2020 tables. -/
theorem reference_nonvacuous (row : Remaining71AuthorityDataRow) :
    ∃ observation,
      row.reference.Applicable witnessInput ∧
        row.reference.Judges witnessInput observation := by
  cases row with
  | periodicAtomicNumbers =>
      let observation : PeriodicAtomicNumberAuthorityObservation :=
        { atomicNumber := 1 }
      have valid : observation.Valid := by
        simp [PeriodicAtomicNumberAuthorityObservation.Valid, observation,
          CIPRule2MassData.currentAtomicNumbers]
      exact ⟨observation, ⟨observation, valid⟩, valid⟩
  | standardAtomicWeights =>
      let observation : StandardAtomicWeightAuthorityObservation :=
        { atomicNumber := 1
          entry := .interval 1007840000000 1008110000000 }
      have valid : observation.Valid := by
        rfl
      exact ⟨observation, ⟨observation, valid⟩, valid⟩
  | isotopeAtomicMasses =>
      let observation : IsotopeAtomicMassAuthorityObservation :=
        { atomicNumber := 1
          massNumber := 1
          massPico := 1007825031898 }
      have valid : observation.Valid := by
        simp [IsotopeAtomicMassAuthorityObservation.Valid, observation,
          CIPRule2MassData.supportedNuclides, CIPRule2MassData.currentAtomicNumbers,
          CIPRule2MassData.isotopeAtomicMassPico?, CIPRule2MassData.lookupMassNumber?,
          CIPRule2MassData.Generated.isotopeMassesPico]
      exact ⟨observation, ⟨observation, valid⟩, valid⟩

end Remaining71AuthorityDataRow

def authorityDataReviewedSemanticsSlice : List IUPACNormativeProvision :=
  Remaining71AuthorityDataRow.all.map Remaining71AuthorityDataRow.provision

@[simp] theorem authorityDataReviewedSemanticsSlice_length :
    authorityDataReviewedSemanticsSlice.length = 3 := by
  rfl

@[simp] theorem authorityDataReviewedSemanticsSlice_exact :
    authorityDataReviewedSemanticsSlice = descriptorAssignmentAuthorityDataProvisions := by
  rfl

theorem remaining71AuthorityData_sourceAuditComplete
    {provision : IUPACNormativeProvision}
    (member : provision ∈ authorityDataReviewedSemanticsSlice) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  have sourceNotIncomplete :
      provision.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources := by
    have everySourceClosed : authorityDataReviewedSemanticsSlice.Forall (fun row =>
        row.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources) := by
      decide
    exact (List.forall_iff_forall_mem.mp everySourceClosed) provision member
  apply Classical.byContradiction
  intro auditIncomplete
  exact sourceNotIncomplete
    ((IUPACNormativeSource.mem_currentIncompleteProvisionAuditSources_iff
      provision.source).2 auditIncomplete)

theorem exists_remaining71AuthorityDataRow
    {provision : IUPACNormativeProvision}
    (member : provision ∈ authorityDataReviewedSemanticsSlice) :
    ∃ row, row ∈ Remaining71AuthorityDataRow.all ∧ row.provision = provision := by
  change provision ∈
    Remaining71AuthorityDataRow.all.map Remaining71AuthorityDataRow.provision at member
  simpa only [List.mem_map] using member

noncomputable def remaining71AuthorityDataRowOf
    (provision : IUPACNormativeProvision)
    (member : provision ∈ authorityDataReviewedSemanticsSlice) :
    Remaining71AuthorityDataRow :=
  Classical.choose (exists_remaining71AuthorityDataRow member)

theorem remaining71AuthorityDataRowOf_provision
    (provision : IUPACNormativeProvision)
    (member : provision ∈ authorityDataReviewedSemanticsSlice) :
    (remaining71AuthorityDataRowOf provision member).provision = provision :=
  (Classical.choose_spec (exists_remaining71AuthorityDataRow member)).2

structure Remaining71AuthorityDataReviewedSemanticsTable where
  reviewed : ReviewedProvisionBatch authorityDataReviewedSemanticsSlice.toFinset
  classifier_exact : ∀ {provision : IUPACNormativeProvision}
    (member : provision ∈ authorityDataReviewedSemanticsSlice.toFinset),
      (reviewed.row provision member).kind = globalProvisionKind provision

noncomputable def remaining71AuthorityDataReviewedSemantics :
    Remaining71AuthorityDataReviewedSemanticsTable where
  reviewed :=
    { ChemicallyAdmitted := AuthoritativeChemicalInput.StructurallyWellFormed
      row := fun provision member =>
        Remaining71AuthorityDataRow.semantics
          (remaining71AuthorityDataRowOf provision (by simpa using member))
      sourceAudited := by
        intro provision member
        exact remaining71AuthorityData_sourceAuditComplete (by simpa using member) }
  classifier_exact := by
    intro provision member
    let row := remaining71AuthorityDataRowOf provision (by simpa using member)
    have rowProvision : row.provision = provision :=
      remaining71AuthorityDataRowOf_provision provision (by simpa using member)
    have classified := Remaining71AuthorityDataRow.classifier_exact row
    change row.kind = globalProvisionKind provision
    simpa [rowProvision] using classified.symm

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71AuthorityDataRow.all_length
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71AuthorityDataRow.all_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.remaining71AuthorityData_sourceAuditComplete
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71AuthorityDataRow.reference_nonvacuous
