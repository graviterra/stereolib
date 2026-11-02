import TetraStereo.OneCenter.IUPACRemaining71ProvisionInventory
import TetraStereo.OneCenter.IUPACP94AuthorityCarrier

set_option autoImplicit false

/-!
# Exhaustive reviewed twelve-row P-94 semantics

All P-94 rows project from the shared typed authority language.  Each reference restricts the
claim to its exact manifest provision; no per-row descriptor oracle or fallback reference exists.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

def P94ProvisionApplicable
    (policy : P94AuthorityPolicy)
    (provision : IUPACNormativeProvision)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P94AuthorityObservation policy,
    observation.ValidForProvision policy provision source

def p94ProvisionReference
    (policy : P94AuthorityPolicy)
    (provision : IUPACNormativeProvision) : ProvisionReference where
  Observation := P94AuthorityObservation policy
  Applicable := P94ProvisionApplicable policy provision
  Judges := fun source observation =>
    observation.ValidForProvision policy provision source

inductive Remaining71P94AuthorityRow where
  | conformationDefinition
  | torsionAngle
  | torsionLonePairs
  | eclipsedStaggeredGauche
  | trigonalConformations
  | sCisSTrans
  | envelope
  | chairBoatTwist
  | halfChair
  | crown
  | tub
  | inOut
  deriving DecidableEq, Repr

namespace Remaining71P94AuthorityRow

def all : List Remaining71P94AuthorityRow :=
  [ .conformationDefinition
  , .torsionAngle
  , .torsionLonePairs
  , .eclipsedStaggeredGauche
  , .trigonalConformations
  , .sCisSTrans
  , .envelope
  , .chairBoatTwist
  , .halfChair
  , .crown
  , .tub
  , .inOut
  ]

def provision : Remaining71P94AuthorityRow → IUPACNormativeProvision
  | .conformationDefinition => .p94ConformationDefinition
  | .torsionAngle => .p94TorsionAngle
  | .torsionLonePairs => .p94TorsionLonePairs
  | .eclipsedStaggeredGauche => .p94EclipsedStaggeredGauche
  | .trigonalConformations => .p94TrigonalConformations
  | .sCisSTrans => .p94SCisSTrans
  | .envelope => .p94Envelope
  | .chairBoatTwist => .p94ChairBoatTwist
  | .halfChair => .p94HalfChair
  | .crown => .p94Crown
  | .tub => .p94Tub
  | .inOut => .p94InOut

def kind (_row : Remaining71P94AuthorityRow) : ProvisionKind :=
  .spatialDescriptor

def reference
    (policy : P94AuthorityPolicy)
    (row : Remaining71P94AuthorityRow) : ProvisionReference :=
  p94ProvisionReference policy row.provision

def semantics
    (policy : P94AuthorityPolicy)
    (row : Remaining71P94AuthorityRow) : ReviewedProvisionSemantics where
  kind := row.kind
  sourceSuppliesRule := true
  reference := row.reference policy

@[simp] theorem all_length : all.length = 12 := by
  rfl

theorem all_nodup : all.Nodup := by
  decide

@[simp] theorem all_provisions_exact : all.map provision = p94SemanticsSlice := by
  rfl

set_option maxRecDepth 16384 in
@[simp] theorem classifier_exact (row : Remaining71P94AuthorityRow) :
    globalProvisionKind row.provision = row.kind := by
  cases row <;> decide

end Remaining71P94AuthorityRow

def p94ReviewedSemanticsSlice : List IUPACNormativeProvision :=
  Remaining71P94AuthorityRow.all.map Remaining71P94AuthorityRow.provision

@[simp] theorem p94ReviewedSemanticsSlice_length :
    p94ReviewedSemanticsSlice.length = 12 := by
  rfl

@[simp] theorem p94ReviewedSemanticsSlice_exact :
    p94ReviewedSemanticsSlice = p94SemanticsSlice := by
  rfl

set_option maxRecDepth 16384 in
theorem remaining71P94_sourceAuditComplete
    {provision : IUPACNormativeProvision}
    (member : provision ∈ p94ReviewedSemanticsSlice) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  have sourceNotIncomplete :
      provision.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources := by
    have everySourceClosed : p94ReviewedSemanticsSlice.Forall (fun row =>
        row.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources) := by
      decide
    exact (List.forall_iff_forall_mem.mp everySourceClosed) provision member
  apply Classical.byContradiction
  intro auditIncomplete
  exact sourceNotIncomplete
    ((IUPACNormativeSource.mem_currentIncompleteProvisionAuditSources_iff
      provision.source).2 auditIncomplete)

theorem exists_remaining71P94AuthorityRow
    {provision : IUPACNormativeProvision}
    (member : provision ∈ p94ReviewedSemanticsSlice) :
    ∃ row, row ∈ Remaining71P94AuthorityRow.all ∧ row.provision = provision := by
  change provision ∈
    Remaining71P94AuthorityRow.all.map Remaining71P94AuthorityRow.provision at member
  simpa only [List.mem_map] using member

noncomputable def remaining71P94AuthorityRowOf
    (provision : IUPACNormativeProvision)
    (member : provision ∈ p94ReviewedSemanticsSlice) : Remaining71P94AuthorityRow :=
  Classical.choose (exists_remaining71P94AuthorityRow member)

theorem remaining71P94AuthorityRowOf_provision
    (provision : IUPACNormativeProvision)
    (member : provision ∈ p94ReviewedSemanticsSlice) :
    (remaining71P94AuthorityRowOf provision member).provision = provision :=
  (Classical.choose_spec (exists_remaining71P94AuthorityRow member)).2

structure Remaining71P94ReviewedSemanticsTable where
  reviewed : ReviewedProvisionBatch p94ReviewedSemanticsSlice.toFinset
  classifier_exact : ∀ {provision : IUPACNormativeProvision}
    (member : provision ∈ p94ReviewedSemanticsSlice.toFinset),
      (reviewed.row provision member).kind = globalProvisionKind provision

noncomputable def remaining71P94ReviewedSemantics
    (policy : P94AuthorityPolicy) : Remaining71P94ReviewedSemanticsTable where
  reviewed :=
    { ChemicallyAdmitted := AuthoritativeChemicalInput.StructurallyWellFormed
      row := fun provision member =>
        Remaining71P94AuthorityRow.semantics policy
          (remaining71P94AuthorityRowOf provision (by simpa using member))
      sourceAudited := by
        intro provision member
        exact remaining71P94_sourceAuditComplete (by simpa using member) }
  classifier_exact := by
    intro provision member
    let row := remaining71P94AuthorityRowOf provision (by simpa using member)
    have rowProvision : row.provision = provision :=
      remaining71P94AuthorityRowOf_provision provision (by simpa using member)
    have classified := Remaining71P94AuthorityRow.classifier_exact row
    change row.kind = globalProvisionKind provision
    simpa [rowProvision] using classified.symm

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P94AuthorityRow.all_length
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P94AuthorityRow.all_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.remaining71P94_sourceAuditComplete
