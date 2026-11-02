import TetraStereo.OneCenter.IUPACRemaining71P93CyclicFamilyPartition
import TetraStereo.OneCenter.IUPACP93FusedAuthorityCarrier
import TetraStereo.OneCenter.IUPACP93CyclophaneAuthorityCarrier

set_option autoImplicit false

/-!
# Reviewed five-row fused/cyclophane P-93 authority family

The P-93.5.4 fused rows and P-93.5.5 cyclophane rows share one manifest family but retain separate
physical carriers.  Exact row routing prevents fused axes or junction relations from standing in
for cyclophane planes, centers, or node-threshold double bonds.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

def P93FusedCIPApplicable
    (policy : P93FusedAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93FusedCIPAuthorityObservation policy,
    observation.ValidFor policy source

def P93FusedRelationApplicable
    (policy : P93FusedAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93FusedRelationAuthorityObservation policy,
    observation.ValidFor policy source

def P93CyclophanePlaneApplicable
    (policy : P93CyclophaneAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93CyclophanePlaneAuthorityObservation policy,
    observation.ValidFor policy source

def P93CyclophaneCenterApplicable
    (policy : P93CyclophaneAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93CyclophaneCenterAuthorityObservation policy,
    observation.ValidFor policy source

def P93CyclophaneDoubleBondApplicable
    (policy : P93CyclophaneAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93CyclophaneDoubleBondAuthorityObservation policy,
    observation.ValidFor policy source

def p93FusedBridgedCIPReference
    (policy : P93FusedAuthorityPolicy) : ProvisionReference where
  Observation := P93FusedCIPAuthorityObservation policy
  Applicable := P93FusedCIPApplicable policy
  Judges := fun source observation => observation.ValidFor policy source

def p93CisoidTransoidReference
    (policy : P93FusedAuthorityPolicy) : ProvisionReference where
  Observation := P93FusedRelationAuthorityObservation policy
  Applicable := P93FusedRelationApplicable policy
  Judges := fun source observation => observation.ValidFor policy source

def p93CyclophanePlanesReference
    (policy : P93CyclophaneAuthorityPolicy) : ProvisionReference where
  Observation := P93CyclophanePlaneAuthorityObservation policy
  Applicable := P93CyclophanePlaneApplicable policy
  Judges := fun source observation => observation.ValidFor policy source

def p93CyclophaneCentersReference
    (policy : P93CyclophaneAuthorityPolicy) : ProvisionReference where
  Observation := P93CyclophaneCenterAuthorityObservation policy
  Applicable := P93CyclophaneCenterApplicable policy
  Judges := fun source observation => observation.ValidFor policy source

def p93CyclophaneDoubleBondsReference
    (policy : P93CyclophaneAuthorityPolicy) : ProvisionReference where
  Observation := P93CyclophaneDoubleBondAuthorityObservation policy
  Applicable := P93CyclophaneDoubleBondApplicable policy
  Judges := fun source observation => observation.ValidFor policy source

inductive Remaining71P93FusedCyclophaneAuthorityRow where
  | fusedBridgedCIP
  | cisoidTransoid
  | cyclophanePlanes
  | cyclophaneCenters
  | cyclophaneDoubleBonds
  deriving DecidableEq, Repr

namespace Remaining71P93FusedCyclophaneAuthorityRow

def all : List Remaining71P93FusedCyclophaneAuthorityRow :=
  [ .fusedBridgedCIP
  , .cisoidTransoid
  , .cyclophanePlanes
  , .cyclophaneCenters
  , .cyclophaneDoubleBonds
  ]

def provision : Remaining71P93FusedCyclophaneAuthorityRow → IUPACNormativeProvision
  | .fusedBridgedCIP => .p93FusedBridgedCIP
  | .cisoidTransoid => .p93CisoidTransoid
  | .cyclophanePlanes => .p93CyclophanePlanes
  | .cyclophaneCenters => .p93CyclophaneCenters
  | .cyclophaneDoubleBonds => .p93CyclophaneDoubleBonds

def kind (_row : Remaining71P93FusedCyclophaneAuthorityRow) : ProvisionKind :=
  .spatialDescriptor

def reference
    (fusedPolicy : P93FusedAuthorityPolicy)
    (cyclophanePolicy : P93CyclophaneAuthorityPolicy) :
    Remaining71P93FusedCyclophaneAuthorityRow → ProvisionReference
  | .fusedBridgedCIP => p93FusedBridgedCIPReference fusedPolicy
  | .cisoidTransoid => p93CisoidTransoidReference fusedPolicy
  | .cyclophanePlanes => p93CyclophanePlanesReference cyclophanePolicy
  | .cyclophaneCenters => p93CyclophaneCentersReference cyclophanePolicy
  | .cyclophaneDoubleBonds => p93CyclophaneDoubleBondsReference cyclophanePolicy

def semantics
    (fusedPolicy : P93FusedAuthorityPolicy)
    (cyclophanePolicy : P93CyclophaneAuthorityPolicy)
    (row : Remaining71P93FusedCyclophaneAuthorityRow) :
    ReviewedProvisionSemantics where
  kind := row.kind
  sourceSuppliesRule := true
  reference := reference fusedPolicy cyclophanePolicy row

@[simp] theorem all_length : all.length = 5 := by
  rfl

theorem all_nodup : all.Nodup := by
  decide

@[simp] theorem all_provisions_exact :
    all.map provision =
      Remaining71P93CyclicAuthorityRow.fusedAndCyclophaneRows.map
        Remaining71P93CyclicAuthorityRow.provision := by
  rfl

set_option maxRecDepth 16384 in
@[simp] theorem classifier_exact
    (row : Remaining71P93FusedCyclophaneAuthorityRow) :
    globalProvisionKind row.provision = row.kind := by
  cases row <;> decide

end Remaining71P93FusedCyclophaneAuthorityRow

def p93FusedCyclophaneSemanticsSlice : List IUPACNormativeProvision :=
  Remaining71P93FusedCyclophaneAuthorityRow.all.map
    Remaining71P93FusedCyclophaneAuthorityRow.provision

@[simp] theorem p93FusedCyclophaneSemanticsSlice_length :
    p93FusedCyclophaneSemanticsSlice.length = 5 := by
  rfl

@[simp] theorem p93FusedCyclophaneSemanticsSlice_exact :
    p93FusedCyclophaneSemanticsSlice =
      Remaining71P93CyclicAuthorityRow.fusedAndCyclophaneRows.map
        Remaining71P93CyclicAuthorityRow.provision := by
  rfl

theorem remaining71P93FusedCyclophane_sourceAuditComplete
    {provision : IUPACNormativeProvision}
    (member : provision ∈ p93FusedCyclophaneSemanticsSlice) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  have sourceNotIncomplete :
      provision.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources := by
    have everySourceClosed : p93FusedCyclophaneSemanticsSlice.Forall (fun row =>
        row.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources) := by
      decide
    exact (List.forall_iff_forall_mem.mp everySourceClosed) provision member
  apply Classical.byContradiction
  intro auditIncomplete
  exact sourceNotIncomplete
    ((IUPACNormativeSource.mem_currentIncompleteProvisionAuditSources_iff
      provision.source).2 auditIncomplete)

theorem exists_remaining71P93FusedCyclophaneAuthorityRow
    {provision : IUPACNormativeProvision}
    (member : provision ∈ p93FusedCyclophaneSemanticsSlice) :
    ∃ row, row ∈ Remaining71P93FusedCyclophaneAuthorityRow.all ∧
      row.provision = provision := by
  change provision ∈
    Remaining71P93FusedCyclophaneAuthorityRow.all.map
      Remaining71P93FusedCyclophaneAuthorityRow.provision at member
  simpa only [List.mem_map] using member

noncomputable def remaining71P93FusedCyclophaneAuthorityRowOf
    (provision : IUPACNormativeProvision)
    (member : provision ∈ p93FusedCyclophaneSemanticsSlice) :
    Remaining71P93FusedCyclophaneAuthorityRow :=
  Classical.choose (exists_remaining71P93FusedCyclophaneAuthorityRow member)

theorem remaining71P93FusedCyclophaneAuthorityRowOf_provision
    (provision : IUPACNormativeProvision)
    (member : provision ∈ p93FusedCyclophaneSemanticsSlice) :
    (remaining71P93FusedCyclophaneAuthorityRowOf provision member).provision = provision :=
  (Classical.choose_spec
    (exists_remaining71P93FusedCyclophaneAuthorityRow member)).2

structure Remaining71P93FusedCyclophaneReviewedSemanticsTable where
  reviewed : ReviewedProvisionBatch p93FusedCyclophaneSemanticsSlice.toFinset
  classifier_exact : ∀ {provision : IUPACNormativeProvision}
    (member : provision ∈ p93FusedCyclophaneSemanticsSlice.toFinset),
      (reviewed.row provision member).kind = globalProvisionKind provision

noncomputable def remaining71P93FusedCyclophaneReviewedSemantics
    (fusedPolicy : P93FusedAuthorityPolicy)
    (cyclophanePolicy : P93CyclophaneAuthorityPolicy) :
    Remaining71P93FusedCyclophaneReviewedSemanticsTable where
  reviewed :=
    { ChemicallyAdmitted := AuthoritativeChemicalInput.StructurallyWellFormed
      row := fun provision member =>
        Remaining71P93FusedCyclophaneAuthorityRow.semantics
          fusedPolicy cyclophanePolicy
          (remaining71P93FusedCyclophaneAuthorityRowOf provision (by simpa using member))
      sourceAudited := by
        intro provision member
        exact remaining71P93FusedCyclophane_sourceAuditComplete (by simpa using member) }
  classifier_exact := by
    intro provision member
    let row := remaining71P93FusedCyclophaneAuthorityRowOf provision (by simpa using member)
    have rowProvision : row.provision = provision :=
      remaining71P93FusedCyclophaneAuthorityRowOf_provision provision (by simpa using member)
    have classified := Remaining71P93FusedCyclophaneAuthorityRow.classifier_exact row
    change row.kind = globalProvisionKind provision
    simpa [rowProvision] using classified.symm

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93FusedCyclophaneAuthorityRow.all_length
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93FusedCyclophaneAuthorityRow.all_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.remaining71P93FusedCyclophane_sourceAuditComplete
