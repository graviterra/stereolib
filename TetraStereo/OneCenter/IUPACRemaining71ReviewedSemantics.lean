import TetraStereo.OneCenter.IUPACRemaining71P93GeneralReviewedSemantics
import TetraStereo.OneCenter.IUPACRemaining71P93NoncarbonReviewedSemantics
import TetraStereo.OneCenter.IUPACRemaining71P93AcyclicReviewedSemantics
import TetraStereo.OneCenter.IUPACRemaining71P93CyclicReviewedSemantics
import TetraStereo.OneCenter.IUPACRemaining71P94ReviewedSemantics
import TetraStereo.OneCenter.IUPACRemaining71AuthorityDataReviewedSemantics

set_option autoImplicit false

/-!
# Exhaustive reviewed remaining-71 compiler

The remaining positive queue is one sum-typed program over six already reviewed semantic
families.  Its exact provision projection is the frozen `remaining71DescriptorBearingProvisions`
list, so no row can be added, omitted, or routed through a fallback reference.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

structure Remaining71ReviewedPolicies where
  p93General : P93GeneralAuthorityPolicy
  p93Noncarbon : P93NoncarbonTetrahedralAuthorityPolicy
  p93Acyclic : P93AcyclicAuthorityPolicy
  p93Cyclic : P93CyclicReviewedPolicies
  p94 : P94AuthorityPolicy

inductive Remaining71ReviewedRow where
  | p93General (row : Remaining71P93GeneralAuthorityRow)
  | p93Noncarbon (row : Remaining71P93NoncarbonAuthorityRow)
  | p93Acyclic (row : Remaining71P93AcyclicAuthorityRow)
  | p93Cyclic (row : Remaining71P93CyclicAuthorityRow)
  | p94 (row : Remaining71P94AuthorityRow)
  | authorityData (row : Remaining71AuthorityDataRow)
  deriving DecidableEq, Repr

namespace Remaining71ReviewedRow

def generalRows : List Remaining71ReviewedRow :=
  Remaining71P93GeneralAuthorityRow.all.map .p93General

def noncarbonRows : List Remaining71ReviewedRow :=
  Remaining71P93NoncarbonAuthorityRow.all.map .p93Noncarbon

def acyclicRows : List Remaining71ReviewedRow :=
  Remaining71P93AcyclicAuthorityRow.all.map .p93Acyclic

def cyclicRows : List Remaining71ReviewedRow :=
  Remaining71P93CyclicAuthorityRow.all.map .p93Cyclic

def p94Rows : List Remaining71ReviewedRow :=
  Remaining71P94AuthorityRow.all.map .p94

def authorityDataRows : List Remaining71ReviewedRow :=
  Remaining71AuthorityDataRow.all.map .authorityData

def all : List Remaining71ReviewedRow :=
  generalRows ++ noncarbonRows ++ acyclicRows ++ cyclicRows ++ p94Rows ++ authorityDataRows

def provision : Remaining71ReviewedRow → IUPACNormativeProvision
  | .p93General row => row.provision
  | .p93Noncarbon row => row.provision
  | .p93Acyclic row => row.provision
  | .p93Cyclic row => row.provision
  | .p94 row => row.provision
  | .authorityData row => row.provision

def kind : Remaining71ReviewedRow → ProvisionKind
  | .p93General row => row.kind
  | .p93Noncarbon row => row.kind
  | .p93Acyclic row => row.kind
  | .p93Cyclic row => row.kind
  | .p94 row => row.kind
  | .authorityData row => row.kind

def reference
    (policies : Remaining71ReviewedPolicies) :
    Remaining71ReviewedRow → ProvisionReference
  | .p93General row => row.reference policies.p93General
  | .p93Noncarbon row => row.reference policies.p93Noncarbon
  | .p93Acyclic row => row.reference policies.p93Acyclic
  | .p93Cyclic row => row.reference policies.p93Cyclic
  | .p94 row => row.reference policies.p94
  | .authorityData row => row.reference

def semantics
    (policies : Remaining71ReviewedPolicies)
    (row : Remaining71ReviewedRow) : ReviewedProvisionSemantics where
  kind := row.kind
  sourceSuppliesRule := true
  reference := row.reference policies

@[simp] theorem all_length : all.length = 71 := by
  simp [all, generalRows, noncarbonRows, acyclicRows, cyclicRows, p94Rows,
    authorityDataRows]

set_option maxRecDepth 16384 in
theorem all_nodup : all.Nodup := by
  decide

@[simp] theorem all_provisions_exact :
    all.map provision = remaining71DescriptorBearingProvisions := by
  have generalExact : generalRows.map provision = p93GeneralSemanticsSlice := by
    rw [generalRows, List.map_map]
    exact Remaining71P93GeneralAuthorityRow.all_provisions_exact
  have noncarbonExact :
      noncarbonRows.map provision = p93NoncarbonTetrahedraSemanticsSlice := by
    rw [noncarbonRows, List.map_map]
    exact Remaining71P93NoncarbonAuthorityRow.all_provisions_exact
  have acyclicExact : acyclicRows.map provision = p93AcyclicSemanticsSlice := by
    rw [acyclicRows, List.map_map]
    exact Remaining71P93AcyclicAuthorityRow.all_provisions_exact
  have cyclicExact : cyclicRows.map provision = p93CyclicSemanticsSlice := by
    rw [cyclicRows, List.map_map]
    exact Remaining71P93CyclicAuthorityRow.all_provisions_exact
  have p94Exact : p94Rows.map provision = p94SemanticsSlice := by
    rw [p94Rows, List.map_map]
    exact Remaining71P94AuthorityRow.all_provisions_exact
  have authorityDataExact :
      authorityDataRows.map provision = descriptorAssignmentAuthorityDataProvisions := by
    rw [authorityDataRows, List.map_map]
    exact Remaining71AuthorityDataRow.all_provisions_exact
  simp only [all, List.map_append, generalExact, noncarbonExact, acyclicExact,
    cyclicExact, p94Exact, authorityDataExact, remaining71DescriptorBearingProvisions,
    remainingP93DescriptorProvisions]

@[simp] theorem classifier_exact (row : Remaining71ReviewedRow) :
    globalProvisionKind row.provision = row.kind := by
  cases row with
  | p93General child => exact Remaining71P93GeneralAuthorityRow.classifier_exact child
  | p93Noncarbon child => exact Remaining71P93NoncarbonAuthorityRow.classifier_exact child
  | p93Acyclic child => exact Remaining71P93AcyclicAuthorityRow.classifier_exact child
  | p93Cyclic child => exact Remaining71P93CyclicAuthorityRow.classifier_exact child
  | p94 child => exact Remaining71P94AuthorityRow.classifier_exact child
  | authorityData child => exact Remaining71AuthorityDataRow.classifier_exact child

end Remaining71ReviewedRow

def remaining71ReviewedSemanticsSlice : List IUPACNormativeProvision :=
  Remaining71ReviewedRow.all.map Remaining71ReviewedRow.provision

@[simp] theorem remaining71ReviewedSemanticsSlice_length :
    remaining71ReviewedSemanticsSlice.length = 71 := by
  simp [remaining71ReviewedSemanticsSlice]

@[simp] theorem remaining71ReviewedSemanticsSlice_exact :
    remaining71ReviewedSemanticsSlice = remaining71DescriptorBearingProvisions := by
  exact Remaining71ReviewedRow.all_provisions_exact

set_option maxRecDepth 16384 in
theorem remaining71_sourceAuditComplete
    {provision : IUPACNormativeProvision}
    (member : provision ∈ remaining71ReviewedSemanticsSlice) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  have sourceNotIncomplete :
      provision.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources := by
    have everySourceClosed : remaining71ReviewedSemanticsSlice.Forall (fun row =>
        row.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources) := by
      decide
    exact (List.forall_iff_forall_mem.mp everySourceClosed) provision member
  apply Classical.byContradiction
  intro auditIncomplete
  exact sourceNotIncomplete
    ((IUPACNormativeSource.mem_currentIncompleteProvisionAuditSources_iff
      provision.source).2 auditIncomplete)

theorem exists_remaining71ReviewedRow
    {provision : IUPACNormativeProvision}
    (member : provision ∈ remaining71ReviewedSemanticsSlice) :
    ∃ row, row ∈ Remaining71ReviewedRow.all ∧ row.provision = provision := by
  change provision ∈
    Remaining71ReviewedRow.all.map Remaining71ReviewedRow.provision at member
  simpa only [List.mem_map] using member

noncomputable def remaining71ReviewedRowOf
    (provision : IUPACNormativeProvision)
    (member : provision ∈ remaining71ReviewedSemanticsSlice) : Remaining71ReviewedRow :=
  Classical.choose (exists_remaining71ReviewedRow member)

theorem remaining71ReviewedRowOf_provision
    (provision : IUPACNormativeProvision)
    (member : provision ∈ remaining71ReviewedSemanticsSlice) :
    (remaining71ReviewedRowOf provision member).provision = provision :=
  (Classical.choose_spec (exists_remaining71ReviewedRow member)).2

structure Remaining71ReviewedSemanticsTable where
  reviewed : ReviewedProvisionBatch remaining71ReviewedSemanticsSlice.toFinset
  classifier_exact : ∀ {provision : IUPACNormativeProvision}
    (member : provision ∈ remaining71ReviewedSemanticsSlice.toFinset),
      (reviewed.row provision member).kind = globalProvisionKind provision

noncomputable def remaining71ReviewedSemantics
    (policies : Remaining71ReviewedPolicies) : Remaining71ReviewedSemanticsTable where
  reviewed :=
    { ChemicallyAdmitted := AuthoritativeChemicalInput.StructurallyWellFormed
      row := fun provision member =>
        Remaining71ReviewedRow.semantics policies
          (remaining71ReviewedRowOf provision (by simpa using member))
      sourceAudited := by
        intro provision member
        exact remaining71_sourceAuditComplete (by simpa using member) }
  classifier_exact := by
    intro provision member
    let row := remaining71ReviewedRowOf provision (by simpa using member)
    have rowProvision : row.provision = provision :=
      remaining71ReviewedRowOf_provision provision (by simpa using member)
    have classified := Remaining71ReviewedRow.classifier_exact row
    change row.kind = globalProvisionKind provision
    simpa [rowProvision] using classified.symm

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71ReviewedRow.all_length
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71ReviewedRow.all_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.remaining71_sourceAuditComplete
