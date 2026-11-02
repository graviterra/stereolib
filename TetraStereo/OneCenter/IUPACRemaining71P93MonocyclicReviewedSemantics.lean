import TetraStereo.OneCenter.IUPACRemaining71P93CyclicFamilyPartition
import TetraStereo.OneCenter.IUPACP93MonocyclicAuthorityCarrier

set_option autoImplicit false

/-!
# Reviewed nine-row monocyclic P-93 authority family

The P-93.5.1 provisions are exact projections of one source-bound monocycle carrier.  Closed-ring
constitution, physical stereogenic units, citation tokens, configuration knowledge, preferred
notation, mean-plane evidence, reference-ligand selection, unsaturation topology, and exocyclic
naming alternatives remain independent of the production descriptor pipeline.

The two exocyclic rows are separated by descriptor vocabulary, exactly as in P-93.5.1.4.2:
the first judges `E`/`Z`; the second requires a present descriptor other than `E` or `Z`.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

open BlueBookP93
open BlueBookP93.Cyclic

def P93MonocyclicGeneralApplicable
    (policy : P93MonocyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ assignment : P93MonocyclicGeneralAssignment policy,
    assignment.ValidFor policy source

def P93MonocyclicAbsoluteCenterJudged
    (policy : P93MonocyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93MonocyclicCenterAuthorityObservation policy) : Prop :=
  observation.ValidFor policy source ∧
    observation.knowledge = .absolute

def P93MonocyclicAbsoluteCenterApplicable
    (policy : P93MonocyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93MonocyclicCenterAuthorityObservation policy,
    P93MonocyclicAbsoluteCenterJudged policy source observation

/-- P-93.5.1.1.2 classifies the cyclic molecule as achiral; it does not say that every
descriptor-bearing center in the molecule is pseudoasymmetric. -/
def P93MonocyclicAchiralCenterJudged
    (policy : P93MonocyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93MonocyclicCenterAuthorityObservation policy) : Prop :=
  observation.ValidFor policy source ∧
    ∃ center,
      observation.physical.unit = .atomCenter center ∧
        policy.AchiralMonocyclicCenterObserved source center

def P93MonocyclicAchiralCenterApplicable
    (policy : P93MonocyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93MonocyclicCenterAuthorityObservation policy,
    P93MonocyclicAchiralCenterJudged policy source observation

def P93MonocyclicCisTransApplicable
    (policy : P93MonocyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93MonocyclicCisTransAuthorityObservation policy,
    observation.ValidFor policy source

def P93MonocyclicRCTApplicable
    (policy : P93MonocyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93MonocyclicRCTAuthorityObservation policy,
    observation.ValidFor policy source

def P93UnsaturatedMonocycleJudged
    (policy : P93MonocyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93MonocyclicUnsaturationAuthorityObservation policy) : Prop :=
  observation.ValidFor policy source ∧
    observation.topology = .ordinaryCyclicDoubleBondSystem

def P93UnsaturatedMonocycleApplicable
    (policy : P93MonocyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93MonocyclicUnsaturationAuthorityObservation policy,
    P93UnsaturatedMonocycleJudged policy source observation

def P93MonocyclicDoubleBondApplicable
    (policy : P93MonocyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93MonocyclicDoubleBondAuthorityObservation policy,
    observation.ValidFor policy source

def P93ExocyclicEZDescriptor :
    Option BlueBookP93.Acyclic.Descriptor → Prop
  | some .E | some .Z => True
  | _ => False

def P93ExocyclicOtherDescriptor :
    Option BlueBookP93.Acyclic.Descriptor → Prop
  | some descriptor => descriptor ≠ .E ∧ descriptor ≠ .Z
  | none => False

def P93ExocyclicDoubleBondEZJudged
    (policy : P93MonocyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93MonocyclicExocyclicAuthorityObservation policy) : Prop :=
  observation.ValidFor policy source ∧
    P93ExocyclicEZDescriptor observation.descriptor?

def P93ExocyclicDoubleBondEZApplicable
    (policy : P93MonocyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93MonocyclicExocyclicAuthorityObservation policy,
    P93ExocyclicDoubleBondEZJudged policy source observation

def P93ExocyclicDoubleBondOtherJudged
    (policy : P93MonocyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput)
    (observation : P93MonocyclicExocyclicAuthorityObservation policy) : Prop :=
  observation.ValidFor policy source ∧
    P93ExocyclicOtherDescriptor observation.descriptor?

def P93ExocyclicDoubleBondOtherApplicable
    (policy : P93MonocyclicAuthorityPolicy)
    (source : AuthoritativeChemicalInput) : Prop :=
  ∃ observation : P93MonocyclicExocyclicAuthorityObservation policy,
    P93ExocyclicDoubleBondOtherJudged policy source observation

theorem p93ExocyclicDescriptorFamilies_disjoint
    (descriptor? : Option BlueBookP93.Acyclic.Descriptor) :
    ¬(P93ExocyclicEZDescriptor descriptor? ∧
      P93ExocyclicOtherDescriptor descriptor?) := by
  cases descriptor? with
  | none => simp [P93ExocyclicEZDescriptor, P93ExocyclicOtherDescriptor]
  | some descriptor =>
      cases descriptor <;>
        simp [P93ExocyclicEZDescriptor, P93ExocyclicOtherDescriptor]

def p93CyclicConfigurationsReference
    (policy : P93MonocyclicAuthorityPolicy) : ProvisionReference where
  Observation := P93MonocyclicGeneralAssignment policy
  Applicable := P93MonocyclicGeneralApplicable policy
  Judges := fun source assignment => assignment.ValidFor policy source

def p93MonocyclicAbsoluteCentersReference
    (policy : P93MonocyclicAuthorityPolicy) : ProvisionReference where
  Observation := P93MonocyclicCenterAuthorityObservation policy
  Applicable := P93MonocyclicAbsoluteCenterApplicable policy
  Judges := P93MonocyclicAbsoluteCenterJudged policy

def p93MonocyclicAchiralCentersReference
    (policy : P93MonocyclicAuthorityPolicy) : ProvisionReference where
  Observation := P93MonocyclicCenterAuthorityObservation policy
  Applicable := P93MonocyclicAchiralCenterApplicable policy
  Judges := P93MonocyclicAchiralCenterJudged policy

def p93MonocyclicCisTransReference
    (policy : P93MonocyclicAuthorityPolicy) : ProvisionReference where
  Observation := P93MonocyclicCisTransAuthorityObservation policy
  Applicable := P93MonocyclicCisTransApplicable policy
  Judges := fun source observation => observation.ValidFor policy source

def p93MonocyclicRCTReference
    (policy : P93MonocyclicAuthorityPolicy) : ProvisionReference where
  Observation := P93MonocyclicRCTAuthorityObservation policy
  Applicable := P93MonocyclicRCTApplicable policy
  Judges := fun source observation => observation.ValidFor policy source

def p93UnsaturatedMonocyclesReference
    (policy : P93MonocyclicAuthorityPolicy) : ProvisionReference where
  Observation := P93MonocyclicUnsaturationAuthorityObservation policy
  Applicable := P93UnsaturatedMonocycleApplicable policy
  Judges := P93UnsaturatedMonocycleJudged policy

def p93CyclicDoubleBondsReference
    (policy : P93MonocyclicAuthorityPolicy) : ProvisionReference where
  Observation := P93MonocyclicDoubleBondAuthorityObservation policy
  Applicable := P93MonocyclicDoubleBondApplicable policy
  Judges := fun source observation => observation.ValidFor policy source

def p93ExocyclicDoubleBondEZReference
    (policy : P93MonocyclicAuthorityPolicy) : ProvisionReference where
  Observation := P93MonocyclicExocyclicAuthorityObservation policy
  Applicable := P93ExocyclicDoubleBondEZApplicable policy
  Judges := P93ExocyclicDoubleBondEZJudged policy

def p93ExocyclicDoubleBondOtherReference
    (policy : P93MonocyclicAuthorityPolicy) : ProvisionReference where
  Observation := P93MonocyclicExocyclicAuthorityObservation policy
  Applicable := P93ExocyclicDoubleBondOtherApplicable policy
  Judges := P93ExocyclicDoubleBondOtherJudged policy

inductive Remaining71P93MonocyclicAuthorityRow where
  | cyclicConfigurations
  | monocyclicAbsoluteCenters
  | monocyclicAchiralCenters
  | monocyclicCisTrans
  | monocyclicRCT
  | unsaturatedMonocycles
  | cyclicDoubleBonds
  | exocyclicDoubleBondEZ
  | exocyclicDoubleBondOther
  deriving DecidableEq, Repr

namespace Remaining71P93MonocyclicAuthorityRow

def all : List Remaining71P93MonocyclicAuthorityRow :=
  [ .cyclicConfigurations
  , .monocyclicAbsoluteCenters
  , .monocyclicAchiralCenters
  , .monocyclicCisTrans
  , .monocyclicRCT
  , .unsaturatedMonocycles
  , .cyclicDoubleBonds
  , .exocyclicDoubleBondEZ
  , .exocyclicDoubleBondOther
  ]

def provision : Remaining71P93MonocyclicAuthorityRow → IUPACNormativeProvision
  | .cyclicConfigurations => .p93CyclicConfigurations
  | .monocyclicAbsoluteCenters => .p93MonocyclicAbsoluteCenters
  | .monocyclicAchiralCenters => .p93MonocyclicAchiralCenters
  | .monocyclicCisTrans => .p93MonocyclicCisTrans
  | .monocyclicRCT => .p93MonocyclicRCT
  | .unsaturatedMonocycles => .p93UnsaturatedMonocycles
  | .cyclicDoubleBonds => .p93CyclicDoubleBonds
  | .exocyclicDoubleBondEZ => .p93ExocyclicDoubleBondEZ
  | .exocyclicDoubleBondOther => .p93ExocyclicDoubleBondOther

def kind (_row : Remaining71P93MonocyclicAuthorityRow) : ProvisionKind :=
  .spatialDescriptor

def reference (policy : P93MonocyclicAuthorityPolicy) :
    Remaining71P93MonocyclicAuthorityRow → ProvisionReference
  | .cyclicConfigurations => p93CyclicConfigurationsReference policy
  | .monocyclicAbsoluteCenters => p93MonocyclicAbsoluteCentersReference policy
  | .monocyclicAchiralCenters => p93MonocyclicAchiralCentersReference policy
  | .monocyclicCisTrans => p93MonocyclicCisTransReference policy
  | .monocyclicRCT => p93MonocyclicRCTReference policy
  | .unsaturatedMonocycles => p93UnsaturatedMonocyclesReference policy
  | .cyclicDoubleBonds => p93CyclicDoubleBondsReference policy
  | .exocyclicDoubleBondEZ => p93ExocyclicDoubleBondEZReference policy
  | .exocyclicDoubleBondOther => p93ExocyclicDoubleBondOtherReference policy

def semantics (policy : P93MonocyclicAuthorityPolicy)
    (row : Remaining71P93MonocyclicAuthorityRow) : ReviewedProvisionSemantics where
  kind := row.kind
  sourceSuppliesRule := true
  reference := reference policy row

@[simp] theorem all_length : all.length = 9 := by
  rfl

theorem all_nodup : all.Nodup := by
  decide

@[simp] theorem all_provisions_exact :
    all.map provision =
      Remaining71P93CyclicAuthorityRow.monocyclicRows.map
        Remaining71P93CyclicAuthorityRow.provision := by
  rfl

set_option maxRecDepth 16384 in
@[simp] theorem classifier_exact (row : Remaining71P93MonocyclicAuthorityRow) :
    globalProvisionKind row.provision = row.kind := by
  cases row <;> decide

end Remaining71P93MonocyclicAuthorityRow

def p93MonocyclicSemanticsSlice : List IUPACNormativeProvision :=
  Remaining71P93MonocyclicAuthorityRow.all.map
    Remaining71P93MonocyclicAuthorityRow.provision

@[simp] theorem p93MonocyclicSemanticsSlice_length :
    p93MonocyclicSemanticsSlice.length = 9 := by
  rfl

@[simp] theorem p93MonocyclicSemanticsSlice_exact :
    p93MonocyclicSemanticsSlice =
      Remaining71P93CyclicAuthorityRow.monocyclicRows.map
        Remaining71P93CyclicAuthorityRow.provision := by
  rfl

theorem remaining71P93Monocyclic_sourceAuditComplete
    {provision : IUPACNormativeProvision}
    (member : provision ∈ p93MonocyclicSemanticsSlice) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  have sourceNotIncomplete :
      provision.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources := by
    have everySourceClosed : p93MonocyclicSemanticsSlice.Forall (fun row =>
        row.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources) := by
      decide
    exact (List.forall_iff_forall_mem.mp everySourceClosed) provision member
  apply Classical.byContradiction
  intro auditIncomplete
  exact sourceNotIncomplete
    ((IUPACNormativeSource.mem_currentIncompleteProvisionAuditSources_iff
      provision.source).2 auditIncomplete)

theorem exists_remaining71P93MonocyclicAuthorityRow
    {provision : IUPACNormativeProvision}
    (member : provision ∈ p93MonocyclicSemanticsSlice) :
    ∃ row, row ∈ Remaining71P93MonocyclicAuthorityRow.all ∧
      row.provision = provision := by
  change provision ∈
    Remaining71P93MonocyclicAuthorityRow.all.map
      Remaining71P93MonocyclicAuthorityRow.provision at member
  simpa only [List.mem_map] using member

noncomputable def remaining71P93MonocyclicAuthorityRowOf
    (provision : IUPACNormativeProvision)
    (member : provision ∈ p93MonocyclicSemanticsSlice) :
    Remaining71P93MonocyclicAuthorityRow :=
  Classical.choose (exists_remaining71P93MonocyclicAuthorityRow member)

theorem remaining71P93MonocyclicAuthorityRowOf_provision
    (provision : IUPACNormativeProvision)
    (member : provision ∈ p93MonocyclicSemanticsSlice) :
    (remaining71P93MonocyclicAuthorityRowOf provision member).provision = provision :=
  (Classical.choose_spec (exists_remaining71P93MonocyclicAuthorityRow member)).2

structure Remaining71P93MonocyclicReviewedSemanticsTable where
  reviewed : ReviewedProvisionBatch p93MonocyclicSemanticsSlice.toFinset
  classifier_exact : ∀ {provision : IUPACNormativeProvision}
    (member : provision ∈ p93MonocyclicSemanticsSlice.toFinset),
      (reviewed.row provision member).kind = globalProvisionKind provision

noncomputable def remaining71P93MonocyclicReviewedSemantics
    (policy : P93MonocyclicAuthorityPolicy) :
    Remaining71P93MonocyclicReviewedSemanticsTable where
  reviewed :=
    { ChemicallyAdmitted := AuthoritativeChemicalInput.StructurallyWellFormed
      row := fun provision member =>
        Remaining71P93MonocyclicAuthorityRow.semantics policy
          (remaining71P93MonocyclicAuthorityRowOf provision (by simpa using member))
      sourceAudited := by
        intro provision member
        exact remaining71P93Monocyclic_sourceAuditComplete (by simpa using member) }
  classifier_exact := by
    intro provision member
    let row := remaining71P93MonocyclicAuthorityRowOf provision (by simpa using member)
    have rowProvision : row.provision = provision :=
      remaining71P93MonocyclicAuthorityRowOf_provision provision (by simpa using member)
    have classified := Remaining71P93MonocyclicAuthorityRow.classifier_exact row
    change row.kind = globalProvisionKind provision
    simpa [rowProvision] using classified.symm

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p93ExocyclicDescriptorFamilies_disjoint
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93MonocyclicAuthorityRow.all_length
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93MonocyclicAuthorityRow.all_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.remaining71P93Monocyclic_sourceAuditComplete
