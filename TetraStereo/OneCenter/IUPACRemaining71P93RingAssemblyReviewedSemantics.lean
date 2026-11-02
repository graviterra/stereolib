import TetraStereo.OneCenter.IUPACRemaining71P93CyclicFamilyPartition
import TetraStereo.OneCenter.IUPACP93RingAssemblyAuthorityCarrier

set_option autoImplicit false

/-!
# Reviewed three-row ring-assembly P-93 authority family

The three P-93.5.7 rows share one checked ring-assembly graph while retaining distinct exact
observation types for stereogenic axes, centers, and unsaturated-ring double bonds.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

def P93RingAssemblyAxesApplicable
    (policy : P93RingAssemblyAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93RingAssemblyAxesAuthorityObservation policy,
    observation.ValidFor policy source

def P93RingAssemblyCentersApplicable
    (policy : P93RingAssemblyAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93RingAssemblyCentersAuthorityObservation policy,
    observation.ValidFor policy source

def P93RingAssemblyDoubleBondsApplicable
    (policy : P93RingAssemblyAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93RingAssemblyDoubleBondsAuthorityObservation policy,
    observation.ValidFor policy source

def p93RingAssemblyAxesReference
    (policy : P93RingAssemblyAuthorityPolicy) : ProvisionReference where
  Observation := P93RingAssemblyAxesAuthorityObservation policy
  Applicable := P93RingAssemblyAxesApplicable policy
  Judges := fun source observation => observation.ValidFor policy source

def p93RingAssemblyCentersReference
    (policy : P93RingAssemblyAuthorityPolicy) : ProvisionReference where
  Observation := P93RingAssemblyCentersAuthorityObservation policy
  Applicable := P93RingAssemblyCentersApplicable policy
  Judges := fun source observation => observation.ValidFor policy source

def p93RingAssemblyDoubleBondsReference
    (policy : P93RingAssemblyAuthorityPolicy) : ProvisionReference where
  Observation := P93RingAssemblyDoubleBondsAuthorityObservation policy
  Applicable := P93RingAssemblyDoubleBondsApplicable policy
  Judges := fun source observation => observation.ValidFor policy source

inductive Remaining71P93RingAssemblyAuthorityRow where
  | axes
  | centers
  | doubleBonds
  deriving DecidableEq, Repr

namespace Remaining71P93RingAssemblyAuthorityRow

def all : List Remaining71P93RingAssemblyAuthorityRow :=
  [.axes, .centers, .doubleBonds]

def provision : Remaining71P93RingAssemblyAuthorityRow → IUPACNormativeProvision
  | .axes => .p93RingAssemblyAxes
  | .centers => .p93RingAssemblyCenters
  | .doubleBonds => .p93RingAssemblyDoubleBonds

def kind (_row : Remaining71P93RingAssemblyAuthorityRow) : ProvisionKind :=
  .spatialDescriptor

def reference
    (policy : P93RingAssemblyAuthorityPolicy) :
    Remaining71P93RingAssemblyAuthorityRow → ProvisionReference
  | .axes => p93RingAssemblyAxesReference policy
  | .centers => p93RingAssemblyCentersReference policy
  | .doubleBonds => p93RingAssemblyDoubleBondsReference policy

def semantics
    (policy : P93RingAssemblyAuthorityPolicy)
    (row : Remaining71P93RingAssemblyAuthorityRow) : ReviewedProvisionSemantics where
  kind := row.kind
  sourceSuppliesRule := true
  reference := row.reference policy

@[simp] theorem all_length : all.length = 3 := by
  rfl

theorem all_nodup : all.Nodup := by
  decide

@[simp] theorem all_provisions_exact :
    all.map provision =
      Remaining71P93CyclicAuthorityRow.ringAssemblyRows.map
        Remaining71P93CyclicAuthorityRow.provision := by
  rfl

set_option maxRecDepth 16384 in
@[simp] theorem classifier_exact
    (row : Remaining71P93RingAssemblyAuthorityRow) :
    globalProvisionKind row.provision = row.kind := by
  cases row <;> decide

end Remaining71P93RingAssemblyAuthorityRow

def p93RingAssemblySemanticsSlice : List IUPACNormativeProvision :=
  Remaining71P93RingAssemblyAuthorityRow.all.map
    Remaining71P93RingAssemblyAuthorityRow.provision

@[simp] theorem p93RingAssemblySemanticsSlice_length :
    p93RingAssemblySemanticsSlice.length = 3 := by
  rfl

@[simp] theorem p93RingAssemblySemanticsSlice_exact :
    p93RingAssemblySemanticsSlice =
      Remaining71P93CyclicAuthorityRow.ringAssemblyRows.map
        Remaining71P93CyclicAuthorityRow.provision := by
  rfl

theorem remaining71P93RingAssembly_sourceAuditComplete
    {provision : IUPACNormativeProvision}
    (member : provision ∈ p93RingAssemblySemanticsSlice) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  have sourceNotIncomplete :
      provision.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources := by
    have everySourceClosed : p93RingAssemblySemanticsSlice.Forall (fun row =>
        row.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources) := by
      decide
    exact (List.forall_iff_forall_mem.mp everySourceClosed) provision member
  apply Classical.byContradiction
  intro auditIncomplete
  exact sourceNotIncomplete
    ((IUPACNormativeSource.mem_currentIncompleteProvisionAuditSources_iff
      provision.source).2 auditIncomplete)

theorem exists_remaining71P93RingAssemblyAuthorityRow
    {provision : IUPACNormativeProvision}
    (member : provision ∈ p93RingAssemblySemanticsSlice) :
    ∃ row, row ∈ Remaining71P93RingAssemblyAuthorityRow.all ∧
      row.provision = provision := by
  change provision ∈
    Remaining71P93RingAssemblyAuthorityRow.all.map
      Remaining71P93RingAssemblyAuthorityRow.provision at member
  simpa only [List.mem_map] using member

noncomputable def remaining71P93RingAssemblyAuthorityRowOf
    (provision : IUPACNormativeProvision)
    (member : provision ∈ p93RingAssemblySemanticsSlice) :
    Remaining71P93RingAssemblyAuthorityRow :=
  Classical.choose (exists_remaining71P93RingAssemblyAuthorityRow member)

theorem remaining71P93RingAssemblyAuthorityRowOf_provision
    (provision : IUPACNormativeProvision)
    (member : provision ∈ p93RingAssemblySemanticsSlice) :
    (remaining71P93RingAssemblyAuthorityRowOf provision member).provision = provision :=
  (Classical.choose_spec
    (exists_remaining71P93RingAssemblyAuthorityRow member)).2

structure Remaining71P93RingAssemblyReviewedSemanticsTable where
  reviewed : ReviewedProvisionBatch p93RingAssemblySemanticsSlice.toFinset
  classifier_exact : ∀ {provision : IUPACNormativeProvision}
    (member : provision ∈ p93RingAssemblySemanticsSlice.toFinset),
      (reviewed.row provision member).kind = globalProvisionKind provision

noncomputable def remaining71P93RingAssemblyReviewedSemantics
    (policy : P93RingAssemblyAuthorityPolicy) :
    Remaining71P93RingAssemblyReviewedSemanticsTable where
  reviewed :=
    { ChemicallyAdmitted := AuthoritativeChemicalInput.StructurallyWellFormed
      row := fun provision member =>
        Remaining71P93RingAssemblyAuthorityRow.semantics policy
          (remaining71P93RingAssemblyAuthorityRowOf provision (by simpa using member))
      sourceAudited := by
        intro provision member
        exact remaining71P93RingAssembly_sourceAuditComplete (by simpa using member) }
  classifier_exact := by
    intro provision member
    let row := remaining71P93RingAssemblyAuthorityRowOf provision (by simpa using member)
    have rowProvision : row.provision = provision :=
      remaining71P93RingAssemblyAuthorityRowOf_provision provision (by simpa using member)
    have classified := Remaining71P93RingAssemblyAuthorityRow.classifier_exact row
    change row.kind = globalProvisionKind provision
    simpa [rowProvision] using classified.symm

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93RingAssemblyAuthorityRow.all_length
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93RingAssemblyAuthorityRow.all_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.remaining71P93RingAssembly_sourceAuditComplete
