import TetraStereo.OneCenter.IUPACRemaining71P93CyclicFamilyPartition
import TetraStereo.OneCenter.IUPACP93VonBaeyerAuthorityCarrier

set_option autoImplicit false

/-!
# Reviewed four-row von Baeyer P-93 authority family

The four P-93.5.2 provisions are exact projections of one graph-bearing von Baeyer carrier.
Absolute CIP centers, the restricted endo/exo/syn/anti vocabulary, bridgehead-relative notation,
and ordinary/cumulene unsaturation are separate reference judgments; no row can fall through to a
generic cyclic default.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

def P93VonBaeyerCIPCenterJudged
    (policy : P93VonBaeyerAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93VonBaeyerCenterAuthorityObservation policy) : Prop :=
  observation.ValidFor policy source ∧
    observation.knowledge = .absolute

def P93VonBaeyerCIPCenterApplicable
    (policy : P93VonBaeyerAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93VonBaeyerCenterAuthorityObservation policy,
    P93VonBaeyerCIPCenterJudged policy source observation

def P93VonBaeyerBridgeOrientationApplicable
    (policy : P93VonBaeyerAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93VonBaeyerBridgeOrientationAuthorityObservation policy,
    observation.ValidFor policy source

def P93VonBaeyerBridgeheadRelativeApplicable
    (policy : P93VonBaeyerAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93VonBaeyerBridgeheadRelativeAuthorityObservation policy,
    observation.ValidFor policy source

def P93VonBaeyerUnsaturationApplicable
    (policy : P93VonBaeyerAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93VonBaeyerUnsaturationAuthorityObservation policy,
    observation.ValidFor policy source

def p93VonBaeyerCIPCentersReference
    (policy : P93VonBaeyerAuthorityPolicy) : ProvisionReference where
  Observation := P93VonBaeyerCenterAuthorityObservation policy
  Applicable := P93VonBaeyerCIPCenterApplicable policy
  Judges := P93VonBaeyerCIPCenterJudged policy

def p93VonBaeyerEndoExoSynAntiReference
    (policy : P93VonBaeyerAuthorityPolicy) : ProvisionReference where
  Observation := P93VonBaeyerBridgeOrientationAuthorityObservation policy
  Applicable := P93VonBaeyerBridgeOrientationApplicable policy
  Judges := fun source observation => observation.ValidFor policy source

def p93VonBaeyerCisTransReference
    (policy : P93VonBaeyerAuthorityPolicy) : ProvisionReference where
  Observation := P93VonBaeyerBridgeheadRelativeAuthorityObservation policy
  Applicable := P93VonBaeyerBridgeheadRelativeApplicable policy
  Judges := fun source observation => observation.ValidFor policy source

def p93VonBaeyerDoubleBondsReference
    (policy : P93VonBaeyerAuthorityPolicy) : ProvisionReference where
  Observation := P93VonBaeyerUnsaturationAuthorityObservation policy
  Applicable := P93VonBaeyerUnsaturationApplicable policy
  Judges := fun source observation => observation.ValidFor policy source

inductive Remaining71P93VonBaeyerAuthorityRow where
  | vonBaeyerCIPCenters
  | vonBaeyerEndoExoSynAnti
  | vonBaeyerCisTrans
  | vonBaeyerDoubleBonds
  deriving DecidableEq, Repr

namespace Remaining71P93VonBaeyerAuthorityRow

def all : List Remaining71P93VonBaeyerAuthorityRow :=
  [ .vonBaeyerCIPCenters
  , .vonBaeyerEndoExoSynAnti
  , .vonBaeyerCisTrans
  , .vonBaeyerDoubleBonds
  ]

def provision : Remaining71P93VonBaeyerAuthorityRow → IUPACNormativeProvision
  | .vonBaeyerCIPCenters => .p93VonBaeyerCIPCenters
  | .vonBaeyerEndoExoSynAnti => .p93VonBaeyerEndoExoSynAnti
  | .vonBaeyerCisTrans => .p93VonBaeyerCisTrans
  | .vonBaeyerDoubleBonds => .p93VonBaeyerDoubleBonds

def kind (_row : Remaining71P93VonBaeyerAuthorityRow) : ProvisionKind :=
  .spatialDescriptor

def reference (policy : P93VonBaeyerAuthorityPolicy) :
    Remaining71P93VonBaeyerAuthorityRow → ProvisionReference
  | .vonBaeyerCIPCenters => p93VonBaeyerCIPCentersReference policy
  | .vonBaeyerEndoExoSynAnti => p93VonBaeyerEndoExoSynAntiReference policy
  | .vonBaeyerCisTrans => p93VonBaeyerCisTransReference policy
  | .vonBaeyerDoubleBonds => p93VonBaeyerDoubleBondsReference policy

def semantics (policy : P93VonBaeyerAuthorityPolicy)
    (row : Remaining71P93VonBaeyerAuthorityRow) : ReviewedProvisionSemantics where
  kind := row.kind
  sourceSuppliesRule := true
  reference := reference policy row

@[simp] theorem all_length : all.length = 4 := by
  rfl

theorem all_nodup : all.Nodup := by
  decide

@[simp] theorem all_provisions_exact :
    all.map provision =
      Remaining71P93CyclicAuthorityRow.vonBaeyerRows.map
        Remaining71P93CyclicAuthorityRow.provision := by
  rfl

set_option maxRecDepth 16384 in
@[simp] theorem classifier_exact (row : Remaining71P93VonBaeyerAuthorityRow) :
    globalProvisionKind row.provision = row.kind := by
  cases row <;> decide

end Remaining71P93VonBaeyerAuthorityRow

def p93VonBaeyerSemanticsSlice : List IUPACNormativeProvision :=
  Remaining71P93VonBaeyerAuthorityRow.all.map
    Remaining71P93VonBaeyerAuthorityRow.provision

@[simp] theorem p93VonBaeyerSemanticsSlice_length :
    p93VonBaeyerSemanticsSlice.length = 4 := by
  rfl

@[simp] theorem p93VonBaeyerSemanticsSlice_exact :
    p93VonBaeyerSemanticsSlice =
      Remaining71P93CyclicAuthorityRow.vonBaeyerRows.map
        Remaining71P93CyclicAuthorityRow.provision := by
  rfl

theorem remaining71P93VonBaeyer_sourceAuditComplete
    {provision : IUPACNormativeProvision}
    (member : provision ∈ p93VonBaeyerSemanticsSlice) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  have sourceNotIncomplete :
      provision.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources := by
    have everySourceClosed : p93VonBaeyerSemanticsSlice.Forall (fun row =>
        row.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources) := by
      decide
    exact (List.forall_iff_forall_mem.mp everySourceClosed) provision member
  apply Classical.byContradiction
  intro auditIncomplete
  exact sourceNotIncomplete
    ((IUPACNormativeSource.mem_currentIncompleteProvisionAuditSources_iff
      provision.source).2 auditIncomplete)

theorem exists_remaining71P93VonBaeyerAuthorityRow
    {provision : IUPACNormativeProvision}
    (member : provision ∈ p93VonBaeyerSemanticsSlice) :
    ∃ row, row ∈ Remaining71P93VonBaeyerAuthorityRow.all ∧
      row.provision = provision := by
  change provision ∈
    Remaining71P93VonBaeyerAuthorityRow.all.map
      Remaining71P93VonBaeyerAuthorityRow.provision at member
  simpa only [List.mem_map] using member

noncomputable def remaining71P93VonBaeyerAuthorityRowOf
    (provision : IUPACNormativeProvision)
    (member : provision ∈ p93VonBaeyerSemanticsSlice) :
    Remaining71P93VonBaeyerAuthorityRow :=
  Classical.choose (exists_remaining71P93VonBaeyerAuthorityRow member)

theorem remaining71P93VonBaeyerAuthorityRowOf_provision
    (provision : IUPACNormativeProvision)
    (member : provision ∈ p93VonBaeyerSemanticsSlice) :
    (remaining71P93VonBaeyerAuthorityRowOf provision member).provision = provision :=
  (Classical.choose_spec (exists_remaining71P93VonBaeyerAuthorityRow member)).2

structure Remaining71P93VonBaeyerReviewedSemanticsTable where
  reviewed : ReviewedProvisionBatch p93VonBaeyerSemanticsSlice.toFinset
  classifier_exact : ∀ {provision : IUPACNormativeProvision}
    (member : provision ∈ p93VonBaeyerSemanticsSlice.toFinset),
      (reviewed.row provision member).kind = globalProvisionKind provision

noncomputable def remaining71P93VonBaeyerReviewedSemantics
    (policy : P93VonBaeyerAuthorityPolicy) :
    Remaining71P93VonBaeyerReviewedSemanticsTable where
  reviewed :=
    { ChemicallyAdmitted := AuthoritativeChemicalInput.StructurallyWellFormed
      row := fun provision member =>
        Remaining71P93VonBaeyerAuthorityRow.semantics policy
          (remaining71P93VonBaeyerAuthorityRowOf provision (by simpa using member))
      sourceAudited := by
        intro provision member
        exact remaining71P93VonBaeyer_sourceAuditComplete (by simpa using member) }
  classifier_exact := by
    intro provision member
    let row := remaining71P93VonBaeyerAuthorityRowOf provision (by simpa using member)
    have rowProvision : row.provision = provision :=
      remaining71P93VonBaeyerAuthorityRowOf_provision provision (by simpa using member)
    have classified := Remaining71P93VonBaeyerAuthorityRow.classifier_exact row
    change row.kind = globalProvisionKind provision
    simpa [rowProvision] using classified.symm

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93VonBaeyerAuthorityRow.all_length
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93VonBaeyerAuthorityRow.all_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.remaining71P93VonBaeyer_sourceAuditComplete
