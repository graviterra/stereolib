import TetraStereo.OneCenter.IUPACRemaining71P93CyclicFamilyPartition
import TetraStereo.OneCenter.IUPACP93SpiroAuthorityCarrier

set_option autoImplicit false

/-!
# Reviewed five-row spiro P-93 authority family

Each P-93.5.3 row receives its own observation type over the shared source-bound spiro frame.
`Xabcd`, occurrence-sensitive `Xabab`, ring-size-controlled double bonds, nontetrahedral `A/C`, and
the permitted `Xaabb` axial alternative therefore cannot be accepted through one another.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

def P93SpiroXabcdApplicable
    (policy : P93SpiroAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93SpiroXabcdAuthorityObservation policy,
    observation.ValidFor policy source

def P93SpiroXababApplicable
    (policy : P93SpiroAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93SpiroXababAuthorityObservation policy,
    observation.ValidFor policy source

def P93SpiroDoubleBondApplicable
    (policy : P93SpiroAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93SpiroDoubleBondAuthorityObservation policy,
    observation.ValidFor policy source

def P93SpiroPolyhedralApplicable
    (policy : P93SpiroAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93SpiroPolyhedralAuthorityObservation policy,
    observation.ValidFor policy source

def P93SpiroAxialApplicable
    (policy : P93SpiroAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93SpiroAxialAuthorityObservation policy,
    observation.ValidFor policy source

def p93SpiroXabcdReference
    (policy : P93SpiroAuthorityPolicy) : ProvisionReference where
  Observation := P93SpiroXabcdAuthorityObservation policy
  Applicable := P93SpiroXabcdApplicable policy
  Judges := fun source observation => observation.ValidFor policy source

def p93SpiroXababReference
    (policy : P93SpiroAuthorityPolicy) : ProvisionReference where
  Observation := P93SpiroXababAuthorityObservation policy
  Applicable := P93SpiroXababApplicable policy
  Judges := fun source observation => observation.ValidFor policy source

def p93SpiroDoubleBondsReference
    (policy : P93SpiroAuthorityPolicy) : ProvisionReference where
  Observation := P93SpiroDoubleBondAuthorityObservation policy
  Applicable := P93SpiroDoubleBondApplicable policy
  Judges := fun source observation => observation.ValidFor policy source

def p93SpiroNontetrahedralCentersReference
    (policy : P93SpiroAuthorityPolicy) : ProvisionReference where
  Observation := P93SpiroPolyhedralAuthorityObservation policy
  Applicable := P93SpiroPolyhedralApplicable policy
  Judges := fun source observation => observation.ValidFor policy source

def p93SpiroAxialChiralityReference
    (policy : P93SpiroAuthorityPolicy) : ProvisionReference where
  Observation := P93SpiroAxialAuthorityObservation policy
  Applicable := P93SpiroAxialApplicable policy
  Judges := fun source observation => observation.ValidFor policy source

inductive Remaining71P93SpiroAuthorityRow where
  | spiroXabcd
  | spiroXabab
  | spiroDoubleBonds
  | spiroNontetrahedralCenters
  | spiroAxialChirality
  deriving DecidableEq, Repr

namespace Remaining71P93SpiroAuthorityRow

def all : List Remaining71P93SpiroAuthorityRow :=
  [ .spiroXabcd
  , .spiroXabab
  , .spiroDoubleBonds
  , .spiroNontetrahedralCenters
  , .spiroAxialChirality
  ]

def provision : Remaining71P93SpiroAuthorityRow → IUPACNormativeProvision
  | .spiroXabcd => .p93SpiroXabcd
  | .spiroXabab => .p93SpiroXabab
  | .spiroDoubleBonds => .p93SpiroDoubleBonds
  | .spiroNontetrahedralCenters => .p93SpiroNontetrahedralCenters
  | .spiroAxialChirality => .p93SpiroAxialChirality

def kind (_row : Remaining71P93SpiroAuthorityRow) : ProvisionKind :=
  .spatialDescriptor

def reference (policy : P93SpiroAuthorityPolicy) :
    Remaining71P93SpiroAuthorityRow → ProvisionReference
  | .spiroXabcd => p93SpiroXabcdReference policy
  | .spiroXabab => p93SpiroXababReference policy
  | .spiroDoubleBonds => p93SpiroDoubleBondsReference policy
  | .spiroNontetrahedralCenters => p93SpiroNontetrahedralCentersReference policy
  | .spiroAxialChirality => p93SpiroAxialChiralityReference policy

def semantics (policy : P93SpiroAuthorityPolicy)
    (row : Remaining71P93SpiroAuthorityRow) : ReviewedProvisionSemantics where
  kind := row.kind
  sourceSuppliesRule := true
  reference := reference policy row

@[simp] theorem all_length : all.length = 5 := by
  rfl

theorem all_nodup : all.Nodup := by
  decide

@[simp] theorem all_provisions_exact :
    all.map provision =
      Remaining71P93CyclicAuthorityRow.spiroRows.map
        Remaining71P93CyclicAuthorityRow.provision := by
  rfl

set_option maxRecDepth 16384 in
@[simp] theorem classifier_exact (row : Remaining71P93SpiroAuthorityRow) :
    globalProvisionKind row.provision = row.kind := by
  cases row <;> decide

end Remaining71P93SpiroAuthorityRow

def p93SpiroSemanticsSlice : List IUPACNormativeProvision :=
  Remaining71P93SpiroAuthorityRow.all.map
    Remaining71P93SpiroAuthorityRow.provision

@[simp] theorem p93SpiroSemanticsSlice_length :
    p93SpiroSemanticsSlice.length = 5 := by
  rfl

@[simp] theorem p93SpiroSemanticsSlice_exact :
    p93SpiroSemanticsSlice =
      Remaining71P93CyclicAuthorityRow.spiroRows.map
        Remaining71P93CyclicAuthorityRow.provision := by
  rfl

theorem remaining71P93Spiro_sourceAuditComplete
    {provision : IUPACNormativeProvision}
    (member : provision ∈ p93SpiroSemanticsSlice) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  have sourceNotIncomplete :
      provision.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources := by
    have everySourceClosed : p93SpiroSemanticsSlice.Forall (fun row =>
        row.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources) := by
      decide
    exact (List.forall_iff_forall_mem.mp everySourceClosed) provision member
  apply Classical.byContradiction
  intro auditIncomplete
  exact sourceNotIncomplete
    ((IUPACNormativeSource.mem_currentIncompleteProvisionAuditSources_iff
      provision.source).2 auditIncomplete)

theorem exists_remaining71P93SpiroAuthorityRow
    {provision : IUPACNormativeProvision}
    (member : provision ∈ p93SpiroSemanticsSlice) :
    ∃ row, row ∈ Remaining71P93SpiroAuthorityRow.all ∧
      row.provision = provision := by
  change provision ∈
    Remaining71P93SpiroAuthorityRow.all.map
      Remaining71P93SpiroAuthorityRow.provision at member
  simpa only [List.mem_map] using member

noncomputable def remaining71P93SpiroAuthorityRowOf
    (provision : IUPACNormativeProvision)
    (member : provision ∈ p93SpiroSemanticsSlice) :
    Remaining71P93SpiroAuthorityRow :=
  Classical.choose (exists_remaining71P93SpiroAuthorityRow member)

theorem remaining71P93SpiroAuthorityRowOf_provision
    (provision : IUPACNormativeProvision)
    (member : provision ∈ p93SpiroSemanticsSlice) :
    (remaining71P93SpiroAuthorityRowOf provision member).provision = provision :=
  (Classical.choose_spec (exists_remaining71P93SpiroAuthorityRow member)).2

structure Remaining71P93SpiroReviewedSemanticsTable where
  reviewed : ReviewedProvisionBatch p93SpiroSemanticsSlice.toFinset
  classifier_exact : ∀ {provision : IUPACNormativeProvision}
    (member : provision ∈ p93SpiroSemanticsSlice.toFinset),
      (reviewed.row provision member).kind = globalProvisionKind provision

noncomputable def remaining71P93SpiroReviewedSemantics
    (policy : P93SpiroAuthorityPolicy) :
    Remaining71P93SpiroReviewedSemanticsTable where
  reviewed :=
    { ChemicallyAdmitted := AuthoritativeChemicalInput.StructurallyWellFormed
      row := fun provision member =>
        Remaining71P93SpiroAuthorityRow.semantics policy
          (remaining71P93SpiroAuthorityRowOf provision (by simpa using member))
      sourceAudited := by
        intro provision member
        exact remaining71P93Spiro_sourceAuditComplete (by simpa using member) }
  classifier_exact := by
    intro provision member
    let row := remaining71P93SpiroAuthorityRowOf provision (by simpa using member)
    have rowProvision : row.provision = provision :=
      remaining71P93SpiroAuthorityRowOf_provision provision (by simpa using member)
    have classified := Remaining71P93SpiroAuthorityRow.classifier_exact row
    change row.kind = globalProvisionKind provision
    simpa [rowProvision] using classified.symm

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93SpiroAuthorityRow.all_length
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93SpiroAuthorityRow.all_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.remaining71P93Spiro_sourceAuditComplete
