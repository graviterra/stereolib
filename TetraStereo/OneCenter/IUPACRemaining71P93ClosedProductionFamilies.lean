import TetraStereo.OneCenter.IUPACP93FullereneProductionCompleteness
import TetraStereo.OneCenter.IUPACP93AcyclicProductionCompleteness
import TetraStereo.OneCenter.IUPACP93SpiroReadyProductionCompleteness
import TetraStereo.OneCenter.IUPACP93NoncarbonProductionCompleteness
import TetraStereo.OneCenter.IUPACP93GeneralProductionCompleteness
import TetraStereo.OneCenter.IUPACP93MonocyclicProductionCompleteness
import TetraStereo.OneCenter.IUPACP93VonBaeyerProductionCompleteness
import TetraStereo.OneCenter.IUPACP93RingAssemblyProductionCompleteness
import TetraStereo.OneCenter.IUPACP93FusedCyclophaneProductionCompleteness
import TetraStereo.OneCenter.IUPACP93CoupledRingChainProductionCompleteness
import TetraStereo.OneCenter.IUPACRemaining71ReviewedSemantics

set_option autoImplicit false

/-!
# Closed remaining-P-93 production families

This module joins all proved P-93 production/reference families into one dependent 56-row
program.  Several families are executable analyzers; others are exact finite or source/core
relations.  The sum theorem is the only family interface required by the global dispatcher, so
family closure is propagated without adding provision-specific proof branches.

All component theorems remain uniform in explicit reviewed policies.  This assembly removes
`ProvisionCorrect` caller duties for all 56 rows relative to the explicit reviewed policies, but
does not claim that the canonical audited policies or nonvacuity witnesses have been constructed.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

inductive Remaining71P93ClosedProductionRow where
  | fullerene (row : Remaining71P93FullereneAuthorityRow)
  | noncarbon (row : Remaining71P93NoncarbonAuthorityRow)
  | general (row : Remaining71P93GeneralAuthorityRow)
  | monocyclic (row : Remaining71P93MonocyclicAuthorityRow)
  | vonBaeyer (row : Remaining71P93VonBaeyerAuthorityRow)
  | ringAssembly (row : Remaining71P93RingAssemblyAuthorityRow)
  | acyclic (row : Remaining71P93AcyclicAuthorityRow)
  | spiro (row : Remaining71P93SpiroReadyAuthorityRow)
  | spiroNontetrahedral
  | fusedCyclophane (row : Remaining71P93FusedCyclophaneAuthorityRow)
  | coupledRingChain (row : Remaining71P93CoupledRingChainAuthorityRow)
  deriving DecidableEq, Repr

namespace Remaining71P93ClosedProductionRow

def fullereneRows : List Remaining71P93ClosedProductionRow :=
  Remaining71P93FullereneAuthorityRow.all.map .fullerene

def noncarbonRows : List Remaining71P93ClosedProductionRow :=
  Remaining71P93NoncarbonAuthorityRow.all.map .noncarbon

def generalRows : List Remaining71P93ClosedProductionRow :=
  Remaining71P93GeneralAuthorityRow.all.map .general

def monocyclicRows : List Remaining71P93ClosedProductionRow :=
  Remaining71P93MonocyclicAuthorityRow.all.map .monocyclic

def vonBaeyerRows : List Remaining71P93ClosedProductionRow :=
  Remaining71P93VonBaeyerAuthorityRow.all.map .vonBaeyer

def ringAssemblyRows : List Remaining71P93ClosedProductionRow :=
  Remaining71P93RingAssemblyAuthorityRow.all.map .ringAssembly

def acyclicRows : List Remaining71P93ClosedProductionRow :=
  Remaining71P93AcyclicAuthorityRow.all.map .acyclic

def spiroRows : List Remaining71P93ClosedProductionRow :=
  Remaining71P93SpiroReadyAuthorityRow.all.map .spiro

def fusedCyclophaneRows : List Remaining71P93ClosedProductionRow :=
  Remaining71P93FusedCyclophaneAuthorityRow.all.map .fusedCyclophane

def coupledRingChainRows : List Remaining71P93ClosedProductionRow :=
  Remaining71P93CoupledRingChainAuthorityRow.all.map .coupledRingChain

def all : List Remaining71P93ClosedProductionRow :=
  fullereneRows ++ noncarbonRows ++ generalRows ++ monocyclicRows ++ vonBaeyerRows ++
    ringAssemblyRows ++ acyclicRows ++ spiroRows ++ [.spiroNontetrahedral] ++
      fusedCyclophaneRows ++ coupledRingChainRows

def provision : Remaining71P93ClosedProductionRow → IUPACNormativeProvision
  | .fullerene row => row.provision
  | .noncarbon row => row.provision
  | .general row => row.provision
  | .monocyclic row => row.provision
  | .vonBaeyer row => row.provision
  | .ringAssembly row => row.provision
  | .acyclic row => row.provision
  | .spiro row => row.provision
  | .spiroNontetrahedral => .p93SpiroNontetrahedralCenters
  | .fusedCyclophane row => row.provision
  | .coupledRingChain row => row.provision

def reference
    (policies : Remaining71ReviewedPolicies) :
    Remaining71P93ClosedProductionRow → ProvisionReference
  | .fullerene row => row.reference policies.p93Cyclic.fullerene
      policies.p93Cyclic.relationalFullerene
  | .noncarbon row => row.reference policies.p93Noncarbon
  | .general row => row.reference policies.p93General
  | .monocyclic row => row.reference policies.p93Cyclic.monocyclic
  | .vonBaeyer row => row.reference policies.p93Cyclic.vonBaeyer
  | .ringAssembly row => row.reference policies.p93Cyclic.ringAssembly
  | .acyclic row => row.reference policies.p93Acyclic
  | .spiro row => row.reference policies.p93Cyclic.spiro
  | .spiroNontetrahedral =>
      Remaining71P93SpiroAuthorityRow.reference policies.p93Cyclic.spiro
        .spiroNontetrahedralCenters
  | .fusedCyclophane row =>
      row.reference policies.p93Cyclic.fused policies.p93Cyclic.cyclophane
  | .coupledRingChain row => row.reference policies.p93Cyclic.coupledRingChain

def ProductionJudges
    (policies : Remaining71ReviewedPolicies) :
    (row : Remaining71P93ClosedProductionRow) →
      AuthoritativeChemicalInput → (row.reference policies).Observation → Prop
  | .fullerene row => row.ProductionJudges policies.p93Cyclic.fullerene
      policies.p93Cyclic.relationalFullerene
  | .noncarbon row => row.ProductionJudges policies.p93Noncarbon
  | .general row => row.ProductionJudges policies.p93General
  | .monocyclic row => row.ProductionJudges policies.p93Cyclic.monocyclic
  | .vonBaeyer row => row.ProductionJudges policies.p93Cyclic.vonBaeyer
  | .ringAssembly row => row.ProductionJudges policies.p93Cyclic.ringAssembly
  | .acyclic row => row.ProductionJudges policies.p93Acyclic
  | .spiro row => row.ProductionJudges policies.p93Cyclic.spiro
  | .spiroNontetrahedral => P93SpiroNontetrahedralSourceCore policies.p93Cyclic.spiro
  | .fusedCyclophane row =>
      row.ProductionJudges policies.p93Cyclic.fused policies.p93Cyclic.cyclophane
  | .coupledRingChain row =>
      row.ProductionJudges policies.p93Cyclic.coupledRingChain

def provisions : List IUPACNormativeProvision :=
  all.map provision

@[simp] theorem all_length : all.length = 56 := by
  simp [all, fullereneRows, noncarbonRows, generalRows, monocyclicRows, vonBaeyerRows,
    ringAssemblyRows, acyclicRows, spiroRows, fusedCyclophaneRows, coupledRingChainRows]

@[simp] theorem provisions_length : provisions.length = 56 := by
  simp [provisions]

@[simp] theorem provisions_exact :
    provisions =
      [ .p93FullereneGeneralMethodology
      , .p93FullereneInherentParentChirality
      , .p93FullereneInherentSubstitutionChirality
      , .p93FullereneNoninherentSubstitutionChirality
      , .p93FullereneChiralSubstituents
      , .p93FullereneSuperimposedStereogenicElements
      , .p93OtherElementTetrahedra
      , .p93OtherElementGeneralMethodology
      , .p93AzaniumPhosphanium
      , .p93AminePhosphaneOxides
      , .p93PhosphatesPhosphonates
      , .p93SulfatesSulfonates
      , .p93Group14Noncarbon
      , .p93AbsoluteConfiguration
      , .p93RelativeConfiguration
      , .p93MixedAbsoluteRelativeConfiguration
      , .p93Racemates
      , .p93Ambo
      , .p93CyclicConfigurations
      , .p93MonocyclicAbsoluteCenters
      , .p93MonocyclicAchiralCenters
      , .p93MonocyclicCisTrans
      , .p93MonocyclicRCT
      , .p93UnsaturatedMonocycles
      , .p93CyclicDoubleBonds
      , .p93ExocyclicDoubleBondEZ
      , .p93ExocyclicDoubleBondOther
      , .p93VonBaeyerCIPCenters
      , .p93VonBaeyerEndoExoSynAnti
      , .p93VonBaeyerCisTrans
      , .p93VonBaeyerDoubleBonds
      , .p93RingAssemblyAxes
      , .p93RingAssemblyCenters
      , .p93RingAssemblyDoubleBonds
      , .p93AcyclicCenters
      , .p93SingleAcyclicCenter
      , .p93MultipleDescriptorsOneCenter
      , .p93PrefixComponentCenters
      , .p93OrdinaryDoubleBonds
      , .p93DoubleBondEZCisTrans
      , .p93MultipleDoubleBonds
      , .p93HeteroatomDoubleBonds
      , .p93EvenCumulenes
      , .p93OddCumulenes
      , .p93MultipleAcyclicStereogenicUnits
      , .p93SpiroXabcd
      , .p93SpiroXabab
      , .p93SpiroDoubleBonds
      , .p93SpiroAxialChirality
      , .p93SpiroNontetrahedralCenters
      , .p93FusedBridgedCIP
      , .p93CisoidTransoid
      , .p93CyclophanePlanes
      , .p93CyclophaneCenters
      , .p93CyclophaneDoubleBonds
      , .p93CoupledRingChainConfigurations
      ] := by
  rfl

theorem all_nodup : all.Nodup := by
  decide

theorem provisions_nodup : provisions.Nodup := by
  decide

theorem production_eq_reference
    (policies : Remaining71ReviewedPolicies)
    (row : Remaining71P93ClosedProductionRow)
    (source : AuthoritativeChemicalInput)
    (observation : (row.reference policies).Observation) :
    row.ProductionJudges policies source observation ↔
      (row.reference policies).Judges source observation := by
  cases row with
  | fullerene child =>
      exact child.production_eq_reference policies.p93Cyclic.fullerene
        policies.p93Cyclic.relationalFullerene source observation
  | noncarbon child =>
      exact child.production_eq_reference policies.p93Noncarbon source observation
  | general child =>
      exact child.production_eq_reference policies.p93General source observation
  | monocyclic child =>
      exact child.production_eq_reference policies.p93Cyclic.monocyclic source observation
  | vonBaeyer child =>
      exact child.production_eq_reference policies.p93Cyclic.vonBaeyer source observation
  | ringAssembly child =>
      exact child.production_eq_reference policies.p93Cyclic.ringAssembly source observation
  | acyclic child =>
      exact child.production_eq_reference policies.p93Acyclic source observation
  | spiro child =>
      exact child.production_eq_reference policies.p93Cyclic.spiro source observation
  | spiroNontetrahedral =>
      exact p93SpiroNontetrahedral_sourceCore_iff_validFor
        policies.p93Cyclic.spiro source observation
  | fusedCyclophane child =>
      exact child.production_eq_reference policies.p93Cyclic.fused
        policies.p93Cyclic.cyclophane source observation
  | coupledRingChain child =>
      exact child.production_eq_reference policies.p93Cyclic.coupledRingChain
        source observation

theorem reference_applicable_of_judged
    (policies : Remaining71ReviewedPolicies)
    (row : Remaining71P93ClosedProductionRow)
    (source : AuthoritativeChemicalInput)
    (observation : (row.reference policies).Observation)
    (judged : (row.reference policies).Judges source observation) :
    (row.reference policies).Applicable source := by
  cases row with
  | fullerene child =>
      exact child.reference_applicable_of_judged
        policies.p93Cyclic.fullerene policies.p93Cyclic.relationalFullerene
        source observation judged
  | noncarbon child =>
      exact child.reference_applicable_of_judged
        policies.p93Noncarbon source observation judged
  | general child =>
      exact child.reference_applicable_of_judged
        policies.p93General source observation judged
  | monocyclic child =>
      exact child.reference_applicable_of_judged
        policies.p93Cyclic.monocyclic source observation judged
  | vonBaeyer child =>
      exact child.reference_applicable_of_judged
        policies.p93Cyclic.vonBaeyer source observation judged
  | ringAssembly child =>
      exact child.reference_applicable_of_judged
        policies.p93Cyclic.ringAssembly source observation judged
  | acyclic child =>
      exact child.reference_applicable_of_judged
        policies.p93Acyclic source observation judged
  | spiro child =>
      exact child.reference_applicable_of_judged
        policies.p93Cyclic.spiro source observation judged
  | spiroNontetrahedral => exact ⟨observation, judged⟩
  | fusedCyclophane child =>
      exact child.reference_applicable_of_judged policies.p93Cyclic.fused
        policies.p93Cyclic.cyclophane source observation judged
  | coupledRingChain child =>
      exact child.reference_applicable_of_judged policies.p93Cyclic.coupledRingChain
        source observation judged

theorem exists_row
    {provision : IUPACNormativeProvision}
    (member : provision ∈ provisions) :
    ∃ row, row ∈ all ∧ row.provision = provision := by
  simpa only [provisions, List.mem_map] using member

noncomputable def rowOf
    (provision : IUPACNormativeProvision)
    (member : provision ∈ provisions) : Remaining71P93ClosedProductionRow :=
  Classical.choose (exists_row member)

theorem rowOf_provision
    (provision : IUPACNormativeProvision)
    (member : provision ∈ provisions) :
    (rowOf provision member).provision = provision :=
  (Classical.choose_spec (exists_row member)).2

end Remaining71P93ClosedProductionRow
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93ClosedProductionRow.provisions_length
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93ClosedProductionRow.provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93ClosedProductionRow.provisions_nodup
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93ClosedProductionRow.production_eq_reference
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93ClosedProductionRow.reference_applicable_of_judged
