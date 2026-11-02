import TetraStereo.OneCenter.IUPACRemaining71P93CyclicFamilyPartition
import TetraStereo.OneCenter.IUPACP93CoupledRingChainAuthorityCarrier

set_option autoImplicit false

/-!
# Reviewed one-row coupled ring/chain P-93 authority family

The P-93.6 row is judged by one checked observation that first fixes the P-1 through P-8
base name, then transports reviewed stereodescriptors onto that numbering.  Multiplicative
naming is accepted only when repeated components, their owned assignments, boundary
interactions, and transported descriptors are symmetric.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

def P93CoupledRingChainApplicable
    (policy : P93CoupledRingChainAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93CoupledRingChainAuthorityObservation policy,
    observation.ValidFor policy source

def p93CoupledRingChainReference
    (policy : P93CoupledRingChainAuthorityPolicy) : ProvisionReference where
  Observation := P93CoupledRingChainAuthorityObservation policy
  Applicable := P93CoupledRingChainApplicable policy
  Judges := fun source observation => observation.ValidFor policy source

inductive Remaining71P93CoupledRingChainAuthorityRow where
  | configurations
  deriving DecidableEq, Repr

namespace Remaining71P93CoupledRingChainAuthorityRow

def all : List Remaining71P93CoupledRingChainAuthorityRow :=
  [.configurations]

def provision :
    Remaining71P93CoupledRingChainAuthorityRow → IUPACNormativeProvision
  | .configurations => .p93CoupledRingChainConfigurations

def kind (_row : Remaining71P93CoupledRingChainAuthorityRow) : ProvisionKind :=
  .spatialDescriptor

def reference
    (policy : P93CoupledRingChainAuthorityPolicy) :
    Remaining71P93CoupledRingChainAuthorityRow → ProvisionReference
  | .configurations => p93CoupledRingChainReference policy

def semantics
    (policy : P93CoupledRingChainAuthorityPolicy)
    (row : Remaining71P93CoupledRingChainAuthorityRow) :
    ReviewedProvisionSemantics where
  kind := row.kind
  sourceSuppliesRule := true
  reference := row.reference policy

@[simp] theorem all_length : all.length = 1 := by
  rfl

theorem all_nodup : all.Nodup := by
  decide

@[simp] theorem all_provisions_exact :
    all.map provision =
      Remaining71P93CyclicAuthorityRow.coupledRingChainRows.map
        Remaining71P93CyclicAuthorityRow.provision := by
  rfl

set_option maxRecDepth 16384 in
@[simp] theorem classifier_exact
    (row : Remaining71P93CoupledRingChainAuthorityRow) :
    globalProvisionKind row.provision = row.kind := by
  cases row ; decide

end Remaining71P93CoupledRingChainAuthorityRow

def p93CoupledRingChainSemanticsSlice : List IUPACNormativeProvision :=
  Remaining71P93CoupledRingChainAuthorityRow.all.map
    Remaining71P93CoupledRingChainAuthorityRow.provision

@[simp] theorem p93CoupledRingChainSemanticsSlice_length :
    p93CoupledRingChainSemanticsSlice.length = 1 := by
  rfl

@[simp] theorem p93CoupledRingChainSemanticsSlice_exact :
    p93CoupledRingChainSemanticsSlice =
      Remaining71P93CyclicAuthorityRow.coupledRingChainRows.map
        Remaining71P93CyclicAuthorityRow.provision := by
  rfl

theorem remaining71P93CoupledRingChain_sourceAuditComplete
    {provision : IUPACNormativeProvision}
    (member : provision ∈ p93CoupledRingChainSemanticsSlice) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  have sourceNotIncomplete :
      provision.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources := by
    have everySourceClosed : p93CoupledRingChainSemanticsSlice.Forall (fun row =>
        row.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources) := by
      decide
    exact (List.forall_iff_forall_mem.mp everySourceClosed) provision member
  apply Classical.byContradiction
  intro auditIncomplete
  exact sourceNotIncomplete
    ((IUPACNormativeSource.mem_currentIncompleteProvisionAuditSources_iff
      provision.source).2 auditIncomplete)

theorem exists_remaining71P93CoupledRingChainAuthorityRow
    {provision : IUPACNormativeProvision}
    (member : provision ∈ p93CoupledRingChainSemanticsSlice) :
    ∃ row, row ∈ Remaining71P93CoupledRingChainAuthorityRow.all ∧
      row.provision = provision := by
  change provision ∈
    Remaining71P93CoupledRingChainAuthorityRow.all.map
      Remaining71P93CoupledRingChainAuthorityRow.provision at member
  simpa only [List.mem_map] using member

noncomputable def remaining71P93CoupledRingChainAuthorityRowOf
    (provision : IUPACNormativeProvision)
    (member : provision ∈ p93CoupledRingChainSemanticsSlice) :
    Remaining71P93CoupledRingChainAuthorityRow :=
  Classical.choose (exists_remaining71P93CoupledRingChainAuthorityRow member)

theorem remaining71P93CoupledRingChainAuthorityRowOf_provision
    (provision : IUPACNormativeProvision)
    (member : provision ∈ p93CoupledRingChainSemanticsSlice) :
    (remaining71P93CoupledRingChainAuthorityRowOf provision member).provision =
      provision :=
  (Classical.choose_spec
    (exists_remaining71P93CoupledRingChainAuthorityRow member)).2

structure Remaining71P93CoupledRingChainReviewedSemanticsTable where
  reviewed : ReviewedProvisionBatch p93CoupledRingChainSemanticsSlice.toFinset
  classifier_exact : ∀ {provision : IUPACNormativeProvision}
    (member : provision ∈ p93CoupledRingChainSemanticsSlice.toFinset),
      (reviewed.row provision member).kind = globalProvisionKind provision

noncomputable def remaining71P93CoupledRingChainReviewedSemantics
    (policy : P93CoupledRingChainAuthorityPolicy) :
    Remaining71P93CoupledRingChainReviewedSemanticsTable where
  reviewed :=
    { ChemicallyAdmitted := AuthoritativeChemicalInput.StructurallyWellFormed
      row := fun provision member =>
        Remaining71P93CoupledRingChainAuthorityRow.semantics policy
          (remaining71P93CoupledRingChainAuthorityRowOf provision (by simpa using member))
      sourceAudited := by
        intro provision member
        exact remaining71P93CoupledRingChain_sourceAuditComplete (by simpa using member) }
  classifier_exact := by
    intro provision member
    let row := remaining71P93CoupledRingChainAuthorityRowOf provision (by simpa using member)
    have rowProvision : row.provision = provision :=
      remaining71P93CoupledRingChainAuthorityRowOf_provision provision (by simpa using member)
    have classified := Remaining71P93CoupledRingChainAuthorityRow.classifier_exact row
    change row.kind = globalProvisionKind provision
    simpa [rowProvision] using classified.symm

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93CoupledRingChainAuthorityRow.all_length
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93CoupledRingChainAuthorityRow.all_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.remaining71P93CoupledRingChain_sourceAuditComplete
