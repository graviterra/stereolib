import TetraStereo.OneCenter.IUPACRemaining71P93MonocyclicReviewedSemantics
import TetraStereo.OneCenter.IUPACRemaining71P93VonBaeyerReviewedSemantics
import TetraStereo.OneCenter.IUPACRemaining71P93SpiroReviewedSemantics
import TetraStereo.OneCenter.IUPACRemaining71P93FusedCyclophaneReviewedSemantics
import TetraStereo.OneCenter.IUPACRemaining71P93FullereneReviewedSemantics
import TetraStereo.OneCenter.IUPACRemaining71P93RingAssemblyReviewedSemantics
import TetraStereo.OneCenter.IUPACRemaining71P93CoupledRingChainReviewedSemantics

set_option autoImplicit false

/-!
# Exhaustive reviewed 33-row cyclic P-93 semantics

This module compiles all seven checked cyclic authority families into one dependent reviewed
batch.  The compiler is exhaustive on `Remaining71P93CyclicAuthorityRow`: there is no fallback
reference and no generic authority oracle.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

structure P93CyclicReviewedPolicies where
  monocyclic : P93MonocyclicAuthorityPolicy
  vonBaeyer : P93VonBaeyerAuthorityPolicy
  spiro : P93SpiroAuthorityPolicy
  fused : P93FusedAuthorityPolicy
  cyclophane : P93CyclophaneAuthorityPolicy
  fullerene : P93FullereneAuthorityPolicy
  relationalFullerene : P93RelationalFullereneAuthorityPolicy
  ringAssembly : P93RingAssemblyAuthorityPolicy
  coupledRingChain : P93CoupledRingChainAuthorityPolicy

namespace Remaining71P93CyclicAuthorityRow

def reference
    (policies : P93CyclicReviewedPolicies) :
    Remaining71P93CyclicAuthorityRow → ProvisionReference
  | .cyclicConfigurations =>
      Remaining71P93MonocyclicAuthorityRow.reference policies.monocyclic
        .cyclicConfigurations
  | .monocyclicAbsoluteCenters =>
      Remaining71P93MonocyclicAuthorityRow.reference policies.monocyclic
        .monocyclicAbsoluteCenters
  | .monocyclicAchiralCenters =>
      Remaining71P93MonocyclicAuthorityRow.reference policies.monocyclic
        .monocyclicAchiralCenters
  | .monocyclicCisTrans =>
      Remaining71P93MonocyclicAuthorityRow.reference policies.monocyclic
        .monocyclicCisTrans
  | .monocyclicRCT =>
      Remaining71P93MonocyclicAuthorityRow.reference policies.monocyclic
        .monocyclicRCT
  | .unsaturatedMonocycles =>
      Remaining71P93MonocyclicAuthorityRow.reference policies.monocyclic
        .unsaturatedMonocycles
  | .cyclicDoubleBonds =>
      Remaining71P93MonocyclicAuthorityRow.reference policies.monocyclic
        .cyclicDoubleBonds
  | .exocyclicDoubleBondEZ =>
      Remaining71P93MonocyclicAuthorityRow.reference policies.monocyclic
        .exocyclicDoubleBondEZ
  | .exocyclicDoubleBondOther =>
      Remaining71P93MonocyclicAuthorityRow.reference policies.monocyclic
        .exocyclicDoubleBondOther
  | .vonBaeyerCIPCenters =>
      Remaining71P93VonBaeyerAuthorityRow.reference policies.vonBaeyer
        .vonBaeyerCIPCenters
  | .vonBaeyerEndoExoSynAnti =>
      Remaining71P93VonBaeyerAuthorityRow.reference policies.vonBaeyer
        .vonBaeyerEndoExoSynAnti
  | .vonBaeyerCisTrans =>
      Remaining71P93VonBaeyerAuthorityRow.reference policies.vonBaeyer
        .vonBaeyerCisTrans
  | .vonBaeyerDoubleBonds =>
      Remaining71P93VonBaeyerAuthorityRow.reference policies.vonBaeyer
        .vonBaeyerDoubleBonds
  | .spiroXabcd =>
      Remaining71P93SpiroAuthorityRow.reference policies.spiro .spiroXabcd
  | .spiroXabab =>
      Remaining71P93SpiroAuthorityRow.reference policies.spiro .spiroXabab
  | .spiroDoubleBonds =>
      Remaining71P93SpiroAuthorityRow.reference policies.spiro .spiroDoubleBonds
  | .spiroNontetrahedralCenters =>
      Remaining71P93SpiroAuthorityRow.reference policies.spiro
        .spiroNontetrahedralCenters
  | .spiroAxialChirality =>
      Remaining71P93SpiroAuthorityRow.reference policies.spiro .spiroAxialChirality
  | .fusedBridgedCIP =>
      Remaining71P93FusedCyclophaneAuthorityRow.reference policies.fused
        policies.cyclophane .fusedBridgedCIP
  | .cisoidTransoid =>
      Remaining71P93FusedCyclophaneAuthorityRow.reference policies.fused
        policies.cyclophane .cisoidTransoid
  | .cyclophanePlanes =>
      Remaining71P93FusedCyclophaneAuthorityRow.reference policies.fused
        policies.cyclophane .cyclophanePlanes
  | .cyclophaneCenters =>
      Remaining71P93FusedCyclophaneAuthorityRow.reference policies.fused
        policies.cyclophane .cyclophaneCenters
  | .cyclophaneDoubleBonds =>
      Remaining71P93FusedCyclophaneAuthorityRow.reference policies.fused
        policies.cyclophane .cyclophaneDoubleBonds
  | .fullereneGeneralMethodology =>
      Remaining71P93FullereneAuthorityRow.reference policies.fullerene
        policies.relationalFullerene
        .generalMethodology
  | .fullereneInherentParentChirality =>
      Remaining71P93FullereneAuthorityRow.reference policies.fullerene
        policies.relationalFullerene
        .inherentParentChirality
  | .fullereneInherentSubstitutionChirality =>
      Remaining71P93FullereneAuthorityRow.reference policies.fullerene
        policies.relationalFullerene
        .inherentSubstitutionChirality
  | .fullereneNoninherentSubstitutionChirality =>
      Remaining71P93FullereneAuthorityRow.reference policies.fullerene
        policies.relationalFullerene
        .noninherentSubstitutionChirality
  | .fullereneChiralSubstituents =>
      Remaining71P93FullereneAuthorityRow.reference policies.fullerene
        policies.relationalFullerene
        .chiralSubstituents
  | .fullereneSuperimposedStereogenicElements =>
      Remaining71P93FullereneAuthorityRow.reference policies.fullerene
        policies.relationalFullerene
        .superimposedStereogenicElements
  | .ringAssemblyAxes =>
      Remaining71P93RingAssemblyAuthorityRow.reference policies.ringAssembly .axes
  | .ringAssemblyCenters =>
      Remaining71P93RingAssemblyAuthorityRow.reference policies.ringAssembly .centers
  | .ringAssemblyDoubleBonds =>
      Remaining71P93RingAssemblyAuthorityRow.reference policies.ringAssembly .doubleBonds
  | .coupledRingChainConfigurations =>
      Remaining71P93CoupledRingChainAuthorityRow.reference policies.coupledRingChain
        .configurations

def reviewedSemantics
    (policies : P93CyclicReviewedPolicies)
    (row : Remaining71P93CyclicAuthorityRow) : ReviewedProvisionSemantics where
  kind := row.kind
  sourceSuppliesRule := true
  reference := row.reference policies

end Remaining71P93CyclicAuthorityRow

def p93CyclicReviewedSemanticsSlice : List IUPACNormativeProvision :=
  Remaining71P93CyclicAuthorityRow.all.map
    Remaining71P93CyclicAuthorityRow.provision

@[simp] theorem p93CyclicReviewedSemanticsSlice_length :
    p93CyclicReviewedSemanticsSlice.length = 33 := by
  rfl

@[simp] theorem p93CyclicReviewedSemanticsSlice_exact :
    p93CyclicReviewedSemanticsSlice = p93CyclicSemanticsSlice := by
  exact Remaining71P93CyclicAuthorityRow.all_provisions_exact

set_option maxRecDepth 16384 in
theorem remaining71P93Cyclic_sourceAuditComplete
    {provision : IUPACNormativeProvision}
    (member : provision ∈ p93CyclicReviewedSemanticsSlice) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  have sourceNotIncomplete :
      provision.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources := by
    have everySourceClosed : p93CyclicReviewedSemanticsSlice.Forall (fun row =>
        row.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources) := by
      decide
    exact (List.forall_iff_forall_mem.mp everySourceClosed) provision member
  apply Classical.byContradiction
  intro auditIncomplete
  exact sourceNotIncomplete
    ((IUPACNormativeSource.mem_currentIncompleteProvisionAuditSources_iff
      provision.source).2 auditIncomplete)

theorem exists_remaining71P93CyclicAuthorityRow
    {provision : IUPACNormativeProvision}
    (member : provision ∈ p93CyclicReviewedSemanticsSlice) :
    ∃ row, row ∈ Remaining71P93CyclicAuthorityRow.all ∧
      row.provision = provision := by
  change provision ∈
    Remaining71P93CyclicAuthorityRow.all.map
      Remaining71P93CyclicAuthorityRow.provision at member
  simpa only [List.mem_map] using member

noncomputable def remaining71P93CyclicAuthorityRowOf
    (provision : IUPACNormativeProvision)
    (member : provision ∈ p93CyclicReviewedSemanticsSlice) :
    Remaining71P93CyclicAuthorityRow :=
  Classical.choose (exists_remaining71P93CyclicAuthorityRow member)

theorem remaining71P93CyclicAuthorityRowOf_provision
    (provision : IUPACNormativeProvision)
    (member : provision ∈ p93CyclicReviewedSemanticsSlice) :
    (remaining71P93CyclicAuthorityRowOf provision member).provision = provision :=
  (Classical.choose_spec
    (exists_remaining71P93CyclicAuthorityRow member)).2

structure Remaining71P93CyclicReviewedSemanticsTable where
  reviewed : ReviewedProvisionBatch p93CyclicReviewedSemanticsSlice.toFinset
  classifier_exact : ∀ {provision : IUPACNormativeProvision}
    (member : provision ∈ p93CyclicReviewedSemanticsSlice.toFinset),
      (reviewed.row provision member).kind = globalProvisionKind provision

noncomputable def remaining71P93CyclicReviewedSemantics
    (policies : P93CyclicReviewedPolicies) :
    Remaining71P93CyclicReviewedSemanticsTable where
  reviewed :=
    { ChemicallyAdmitted := AuthoritativeChemicalInput.StructurallyWellFormed
      row := fun provision member =>
        Remaining71P93CyclicAuthorityRow.reviewedSemantics policies
          (remaining71P93CyclicAuthorityRowOf provision (by simpa using member))
      sourceAudited := by
        intro provision member
        exact remaining71P93Cyclic_sourceAuditComplete (by simpa using member) }
  classifier_exact := by
    intro provision member
    let row := remaining71P93CyclicAuthorityRowOf provision (by simpa using member)
    have rowProvision : row.provision = provision :=
      remaining71P93CyclicAuthorityRowOf_provision provision (by simpa using member)
    have classified := Remaining71P93CyclicAuthorityRow.classifier_exact row
    change row.kind = globalProvisionKind provision
    simpa [rowProvision] using classified.symm

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p93CyclicReviewedSemanticsSlice_length
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.p93CyclicReviewedSemanticsSlice_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.remaining71P93Cyclic_sourceAuditComplete
