import TetraStereo.OneCenter.IUPACRemaining71ProvisionInventory
import TetraStereo.OneCenter.IUPACP93NoncarbonTetrahedralAuthorityCarrier

set_option autoImplicit false

/-!
# Reviewed seven-row P-93.2 authority family

All seven noncarbon-tetrahedral provisions are projections of one source-bound authority carrier.
The family retains exact element routing and the source-mandated oxide/oxo representation quotient;
it does not read a production descriptor list or parser element whitelist.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

open BlueBookP93.NoncarbonTetrahedra

def P93NoncarbonTetrahedralApplicable
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93NoncarbonTetrahedralAssignment policy,
    observation.ValidFor policy source

def P93NoncarbonTetrahedralJudged
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93NoncarbonTetrahedralAssignment policy) : Prop :=
  observation.ValidFor policy source

def P93NoncarbonCitationJudged
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93NoncarbonCitationAuthorityObservation policy) : Prop :=
  observation.ValidFor policy source

def P93NoncarbonOnicApplicable
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93NoncarbonOnicAuthorityObservation policy,
    observation.ValidFor policy source

def P93NoncarbonOnicJudged
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93NoncarbonOnicAuthorityObservation policy) : Prop :=
  observation.ValidFor policy source

def P93NoncarbonOxideApplicable
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93NoncarbonOxideAuthorityObservation policy,
    observation.ValidFor policy source

def P93NoncarbonOxideJudged
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93NoncarbonOxideAuthorityObservation policy) : Prop :=
  observation.ValidFor policy source ∧
    oxideLigandCount observation.family observation.firstBonding =
      oxideLigandCount observation.family observation.secondBonding

def P93NoncarbonPhosphorusOxoApplicable
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93NoncarbonPhosphorusOxoAuthorityObservation policy,
    observation.ValidFor policy source

def P93NoncarbonPhosphorusOxoJudged
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93NoncarbonPhosphorusOxoAuthorityObservation policy) : Prop :=
  observation.ValidFor policy source ∧
    phosphorusOxoEffectiveBondOrder observation.family
        observation.firstWrittenAsDouble =
      phosphorusOxoEffectiveBondOrder observation.family
        observation.secondWrittenAsDouble ∧
    SameConfigurationIgnoringFormalCharges
      observation.firstCharges observation.secondCharges

def P93NoncarbonChalcogenOxoApplicable
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93NoncarbonChalcogenOxoAuthorityObservation policy,
    observation.ValidFor policy source

def P93NoncarbonChalcogenOxoJudged
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93NoncarbonChalcogenOxoAuthorityObservation policy) : Prop :=
  observation.ValidFor policy source ∧
    UsesPhosphateConfigurationTreatment observation.family ∧
    phosphorusOxoEffectiveBondOrder .related
        observation.firstWrittenAsDouble =
      phosphorusOxoEffectiveBondOrder .related
        observation.secondWrittenAsDouble ∧
    SameConfigurationIgnoringFormalCharges
      observation.firstCharges observation.secondCharges

def P93NoncarbonGroup14Applicable
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93NoncarbonGroup14AuthorityObservation policy,
    observation.ValidFor policy source

def P93NoncarbonGroup14Judged
    (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93NoncarbonGroup14AuthorityObservation policy) : Prop :=
  observation.ValidFor policy source ∧
    UsesCarbonTetrahedralMethod observation.family

def p93OtherElementTetrahedraReference
    (policy : P93NoncarbonTetrahedralAuthorityPolicy) : ProvisionReference where
  Observation := P93NoncarbonTetrahedralAssignment policy
  Applicable := P93NoncarbonTetrahedralApplicable policy
  Judges := P93NoncarbonTetrahedralJudged policy

def p93OtherElementGeneralMethodologyReference
    (policy : P93NoncarbonTetrahedralAuthorityPolicy) : ProvisionReference where
  Observation := P93NoncarbonCitationAuthorityObservation policy
  Applicable := P93NoncarbonTetrahedralApplicable policy
  Judges := P93NoncarbonCitationJudged policy

def p93AzaniumPhosphaniumReference
    (policy : P93NoncarbonTetrahedralAuthorityPolicy) : ProvisionReference where
  Observation := P93NoncarbonOnicAuthorityObservation policy
  Applicable := P93NoncarbonOnicApplicable policy
  Judges := P93NoncarbonOnicJudged policy

def p93AminePhosphaneOxidesReference
    (policy : P93NoncarbonTetrahedralAuthorityPolicy) : ProvisionReference where
  Observation := P93NoncarbonOxideAuthorityObservation policy
  Applicable := P93NoncarbonOxideApplicable policy
  Judges := P93NoncarbonOxideJudged policy

def p93PhosphatesPhosphonatesReference
    (policy : P93NoncarbonTetrahedralAuthorityPolicy) : ProvisionReference where
  Observation := P93NoncarbonPhosphorusOxoAuthorityObservation policy
  Applicable := P93NoncarbonPhosphorusOxoApplicable policy
  Judges := P93NoncarbonPhosphorusOxoJudged policy

def p93SulfatesSulfonatesReference
    (policy : P93NoncarbonTetrahedralAuthorityPolicy) : ProvisionReference where
  Observation := P93NoncarbonChalcogenOxoAuthorityObservation policy
  Applicable := P93NoncarbonChalcogenOxoApplicable policy
  Judges := P93NoncarbonChalcogenOxoJudged policy

def p93Group14NoncarbonReference
    (policy : P93NoncarbonTetrahedralAuthorityPolicy) : ProvisionReference where
  Observation := P93NoncarbonGroup14AuthorityObservation policy
  Applicable := P93NoncarbonGroup14Applicable policy
  Judges := P93NoncarbonGroup14Judged policy

inductive Remaining71P93NoncarbonAuthorityRow where
  | otherElementTetrahedra
  | otherElementGeneralMethodology
  | azaniumPhosphanium
  | aminePhosphaneOxides
  | phosphatesPhosphonates
  | sulfatesSulfonates
  | group14Noncarbon
  deriving DecidableEq, Repr

namespace Remaining71P93NoncarbonAuthorityRow

def all : List Remaining71P93NoncarbonAuthorityRow :=
  [ .otherElementTetrahedra
  , .otherElementGeneralMethodology
  , .azaniumPhosphanium
  , .aminePhosphaneOxides
  , .phosphatesPhosphonates
  , .sulfatesSulfonates
  , .group14Noncarbon
  ]

def provision : Remaining71P93NoncarbonAuthorityRow → IUPACNormativeProvision
  | .otherElementTetrahedra => .p93OtherElementTetrahedra
  | .otherElementGeneralMethodology => .p93OtherElementGeneralMethodology
  | .azaniumPhosphanium => .p93AzaniumPhosphanium
  | .aminePhosphaneOxides => .p93AminePhosphaneOxides
  | .phosphatesPhosphonates => .p93PhosphatesPhosphonates
  | .sulfatesSulfonates => .p93SulfatesSulfonates
  | .group14Noncarbon => .p93Group14Noncarbon

def kind (_row : Remaining71P93NoncarbonAuthorityRow) : ProvisionKind :=
  .spatialDescriptor

def reference (policy : P93NoncarbonTetrahedralAuthorityPolicy) :
    Remaining71P93NoncarbonAuthorityRow → ProvisionReference
  | .otherElementTetrahedra => p93OtherElementTetrahedraReference policy
  | .otherElementGeneralMethodology =>
      p93OtherElementGeneralMethodologyReference policy
  | .azaniumPhosphanium => p93AzaniumPhosphaniumReference policy
  | .aminePhosphaneOxides => p93AminePhosphaneOxidesReference policy
  | .phosphatesPhosphonates => p93PhosphatesPhosphonatesReference policy
  | .sulfatesSulfonates => p93SulfatesSulfonatesReference policy
  | .group14Noncarbon => p93Group14NoncarbonReference policy

def semantics (policy : P93NoncarbonTetrahedralAuthorityPolicy)
    (row : Remaining71P93NoncarbonAuthorityRow) : ReviewedProvisionSemantics where
  kind := row.kind
  sourceSuppliesRule := true
  reference := reference policy row

@[simp] theorem all_length : all.length = 7 := by
  rfl

theorem all_nodup : all.Nodup := by
  decide

@[simp] theorem all_provisions_exact :
    all.map provision = p93NoncarbonTetrahedraSemanticsSlice := by
  rfl

set_option maxRecDepth 16384 in
@[simp] theorem classifier_exact (row : Remaining71P93NoncarbonAuthorityRow) :
    globalProvisionKind row.provision = row.kind := by
  cases row <;> decide

end Remaining71P93NoncarbonAuthorityRow

theorem remaining71P93Noncarbon_sourceAuditComplete
    {provision : IUPACNormativeProvision}
    (member : provision ∈ p93NoncarbonTetrahedraSemanticsSlice) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  have sourceNotIncomplete :
      provision.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources := by
    have everySourceClosed : p93NoncarbonTetrahedraSemanticsSlice.Forall (fun row =>
        row.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources) := by
      decide
    exact (List.forall_iff_forall_mem.mp everySourceClosed) provision member
  apply Classical.byContradiction
  intro auditIncomplete
  exact sourceNotIncomplete
    ((IUPACNormativeSource.mem_currentIncompleteProvisionAuditSources_iff
      provision.source).2 auditIncomplete)

theorem exists_remaining71P93NoncarbonAuthorityRow
    {provision : IUPACNormativeProvision}
    (member : provision ∈ p93NoncarbonTetrahedraSemanticsSlice) :
    ∃ row, row ∈ Remaining71P93NoncarbonAuthorityRow.all ∧
      row.provision = provision := by
  rw [← Remaining71P93NoncarbonAuthorityRow.all_provisions_exact] at member
  simpa only [List.mem_map] using member

noncomputable def remaining71P93NoncarbonAuthorityRowOf
    (provision : IUPACNormativeProvision)
    (member : provision ∈ p93NoncarbonTetrahedraSemanticsSlice) :
    Remaining71P93NoncarbonAuthorityRow :=
  Classical.choose (exists_remaining71P93NoncarbonAuthorityRow member)

theorem remaining71P93NoncarbonAuthorityRowOf_provision
    (provision : IUPACNormativeProvision)
    (member : provision ∈ p93NoncarbonTetrahedraSemanticsSlice) :
    (remaining71P93NoncarbonAuthorityRowOf provision member).provision = provision :=
  (Classical.choose_spec (exists_remaining71P93NoncarbonAuthorityRow member)).2

structure Remaining71P93NoncarbonReviewedSemanticsTable where
  reviewed : ReviewedProvisionBatch p93NoncarbonTetrahedraSemanticsSlice.toFinset
  classifier_exact : ∀ {provision : IUPACNormativeProvision}
    (member : provision ∈ p93NoncarbonTetrahedraSemanticsSlice.toFinset),
      (reviewed.row provision member).kind = globalProvisionKind provision

noncomputable def remaining71P93NoncarbonReviewedSemantics
    (policy : P93NoncarbonTetrahedralAuthorityPolicy) :
    Remaining71P93NoncarbonReviewedSemanticsTable where
  reviewed :=
    { ChemicallyAdmitted := AuthoritativeChemicalInput.StructurallyWellFormed
      row := fun provision member =>
        Remaining71P93NoncarbonAuthorityRow.semantics policy
          (remaining71P93NoncarbonAuthorityRowOf provision (by simpa using member))
      sourceAudited := by
        intro provision member
        exact remaining71P93Noncarbon_sourceAuditComplete (by simpa using member) }
  classifier_exact := by
    intro provision member
    let row := remaining71P93NoncarbonAuthorityRowOf provision (by simpa using member)
    have rowProvision : row.provision = provision :=
      remaining71P93NoncarbonAuthorityRowOf_provision provision (by simpa using member)
    have classified := Remaining71P93NoncarbonAuthorityRow.classifier_exact row
    change row.kind = globalProvisionKind provision
    simpa [rowProvision] using classified.symm

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93NoncarbonAuthorityRow.all_length
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93NoncarbonAuthorityRow.all_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.remaining71P93Noncarbon_sourceAuditComplete
