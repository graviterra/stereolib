import TetraStereo.OneCenter.IUPACGlobalCompilerAssembly
import TetraStereo.OneCenter.IUPACPrimitive35Interpreter
import TetraStereo.OneCenter.IUPACRemaining71P93ClosedProductionFamilies

set_option autoImplicit false















namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

inductive Remaining71P93DescriptorKernelRow where
  | general (row : Remaining71P93GeneralAuthorityRow)
  | noncarbon (row : Remaining71P93NoncarbonAuthorityRow)
  | acyclic (row : Remaining71P93AcyclicAuthorityRow)
  | cyclic (row : Remaining71P93CyclicAuthorityRow)
  deriving DecidableEq, Repr

namespace Remaining71P93DescriptorKernelRow

def generalRows : List Remaining71P93DescriptorKernelRow :=
  Remaining71P93GeneralAuthorityRow.all.map .general

def noncarbonRows : List Remaining71P93DescriptorKernelRow :=
  Remaining71P93NoncarbonAuthorityRow.all.map .noncarbon

def acyclicRows : List Remaining71P93DescriptorKernelRow :=
  Remaining71P93AcyclicAuthorityRow.all.map .acyclic

def cyclicRows : List Remaining71P93DescriptorKernelRow :=
  Remaining71P93CyclicAuthorityRow.all.map .cyclic

def all : List Remaining71P93DescriptorKernelRow :=
  generalRows ++ noncarbonRows ++ acyclicRows ++ cyclicRows

@[simp] theorem all_length : all.length = 56 := by
  simp [all, generalRows, noncarbonRows, acyclicRows, cyclicRows]

def toReviewedRow : Remaining71P93DescriptorKernelRow → Remaining71ReviewedRow
  | .general row => .p93General row
  | .noncarbon row => .p93Noncarbon row
  | .acyclic row => .p93Acyclic row
  | .cyclic row => .p93Cyclic row

def provision (row : Remaining71P93DescriptorKernelRow) : IUPACNormativeProvision :=
  row.toReviewedRow.provision

def reference
    (policies : Remaining71ReviewedPolicies)
    (row : Remaining71P93DescriptorKernelRow) : ProvisionReference :=
  row.toReviewedRow.reference policies

/-- Embed the six-row fullerene family into the exhaustive remaining-P-93 dispatch type. -/
def ofFullerene : Remaining71P93FullereneAuthorityRow →
    Remaining71P93DescriptorKernelRow
  | .generalMethodology => .cyclic .fullereneGeneralMethodology
  | .inherentParentChirality => .cyclic .fullereneInherentParentChirality
  | .inherentSubstitutionChirality =>
      .cyclic .fullereneInherentSubstitutionChirality
  | .noninherentSubstitutionChirality =>
      .cyclic .fullereneNoninherentSubstitutionChirality
  | .chiralSubstituents => .cyclic .fullereneChiralSubstituents
  | .superimposedStereogenicElements =>
      .cyclic .fullereneSuperimposedStereogenicElements

@[simp] theorem ofFullerene_provision
    (row : Remaining71P93FullereneAuthorityRow) :
    (ofFullerene row).provision = row.provision := by
  cases row <;> rfl

@[simp] theorem ofFullerene_reference
    (policies : Remaining71ReviewedPolicies)
    (row : Remaining71P93FullereneAuthorityRow) :
    (ofFullerene row).reference policies =
      row.reference policies.p93Cyclic.fullerene
        policies.p93Cyclic.relationalFullerene := by
  cases row <;> rfl

theorem ofFullerene_mem_all
    (row : Remaining71P93FullereneAuthorityRow) :
    ofFullerene row ∈ all := by
  cases row <;>
    simp [ofFullerene, all, cyclicRows,
      Remaining71P93CyclicAuthorityRow.all,
      Remaining71P93CyclicAuthorityRow.fullereneRows]

/-- Embed the complete nine-row monocyclic family into the cyclic dispatcher. -/
def ofMonocyclic : Remaining71P93MonocyclicAuthorityRow →
    Remaining71P93DescriptorKernelRow
  | .cyclicConfigurations => .cyclic .cyclicConfigurations
  | .monocyclicAbsoluteCenters => .cyclic .monocyclicAbsoluteCenters
  | .monocyclicAchiralCenters => .cyclic .monocyclicAchiralCenters
  | .monocyclicCisTrans => .cyclic .monocyclicCisTrans
  | .monocyclicRCT => .cyclic .monocyclicRCT
  | .unsaturatedMonocycles => .cyclic .unsaturatedMonocycles
  | .cyclicDoubleBonds => .cyclic .cyclicDoubleBonds
  | .exocyclicDoubleBondEZ => .cyclic .exocyclicDoubleBondEZ
  | .exocyclicDoubleBondOther => .cyclic .exocyclicDoubleBondOther

@[simp] theorem ofMonocyclic_provision
    (row : Remaining71P93MonocyclicAuthorityRow) :
    (ofMonocyclic row).provision = row.provision := by
  cases row <;> rfl

@[simp] theorem ofMonocyclic_reference
    (policies : Remaining71ReviewedPolicies)
    (row : Remaining71P93MonocyclicAuthorityRow) :
    (ofMonocyclic row).reference policies =
      row.reference policies.p93Cyclic.monocyclic := by
  cases row <;> rfl

theorem ofMonocyclic_mem_all
    (row : Remaining71P93MonocyclicAuthorityRow) :
    ofMonocyclic row ∈ all := by
  cases row <;>
    simp [ofMonocyclic, all, cyclicRows,
      Remaining71P93CyclicAuthorityRow.all,
      Remaining71P93CyclicAuthorityRow.monocyclicRows]

def ofVonBaeyer : Remaining71P93VonBaeyerAuthorityRow →
    Remaining71P93DescriptorKernelRow
  | .vonBaeyerCIPCenters => .cyclic .vonBaeyerCIPCenters
  | .vonBaeyerEndoExoSynAnti => .cyclic .vonBaeyerEndoExoSynAnti
  | .vonBaeyerCisTrans => .cyclic .vonBaeyerCisTrans
  | .vonBaeyerDoubleBonds => .cyclic .vonBaeyerDoubleBonds

@[simp] theorem ofVonBaeyer_provision
    (row : Remaining71P93VonBaeyerAuthorityRow) :
    (ofVonBaeyer row).provision = row.provision := by
  cases row <;> rfl

@[simp] theorem ofVonBaeyer_reference
    (policies : Remaining71ReviewedPolicies)
    (row : Remaining71P93VonBaeyerAuthorityRow) :
    (ofVonBaeyer row).reference policies = row.reference policies.p93Cyclic.vonBaeyer := by
  cases row <;> rfl

theorem ofVonBaeyer_mem_all
    (row : Remaining71P93VonBaeyerAuthorityRow) :
    ofVonBaeyer row ∈ all := by
  cases row <;>
    simp [ofVonBaeyer, all, cyclicRows,
      Remaining71P93CyclicAuthorityRow.all,
      Remaining71P93CyclicAuthorityRow.vonBaeyerRows]

def ofRingAssembly : Remaining71P93RingAssemblyAuthorityRow →
    Remaining71P93DescriptorKernelRow
  | .axes => .cyclic .ringAssemblyAxes
  | .centers => .cyclic .ringAssemblyCenters
  | .doubleBonds => .cyclic .ringAssemblyDoubleBonds

@[simp] theorem ofRingAssembly_provision
    (row : Remaining71P93RingAssemblyAuthorityRow) :
    (ofRingAssembly row).provision = row.provision := by
  cases row <;> rfl

@[simp] theorem ofRingAssembly_reference
    (policies : Remaining71ReviewedPolicies)
    (row : Remaining71P93RingAssemblyAuthorityRow) :
    (ofRingAssembly row).reference policies =
      row.reference policies.p93Cyclic.ringAssembly := by
  cases row <;> rfl

theorem ofRingAssembly_mem_all
    (row : Remaining71P93RingAssemblyAuthorityRow) :
    ofRingAssembly row ∈ all := by
  cases row <;>
    simp [ofRingAssembly, all, cyclicRows,
      Remaining71P93CyclicAuthorityRow.all,
      Remaining71P93CyclicAuthorityRow.ringAssemblyRows]

/-- Embed the four source/core-complete spiro rows into the cyclic dispatcher family. -/
def ofSpiro : Remaining71P93SpiroReadyAuthorityRow →
    Remaining71P93DescriptorKernelRow
  | .spiroXabcd => .cyclic .spiroXabcd
  | .spiroXabab => .cyclic .spiroXabab
  | .spiroDoubleBonds => .cyclic .spiroDoubleBonds
  | .spiroAxialChirality => .cyclic .spiroAxialChirality

@[simp] theorem ofSpiro_provision
    (row : Remaining71P93SpiroReadyAuthorityRow) :
    (ofSpiro row).provision = row.provision := by
  cases row <;> rfl

@[simp] theorem ofSpiro_reference
    (policies : Remaining71ReviewedPolicies)
    (row : Remaining71P93SpiroReadyAuthorityRow) :
    (ofSpiro row).reference policies = row.reference policies.p93Cyclic.spiro := by
  cases row <;> rfl

theorem ofSpiro_mem_all
    (row : Remaining71P93SpiroReadyAuthorityRow) :
    ofSpiro row ∈ all := by
  cases row <;>
    simp [ofSpiro, all, cyclicRows,
      Remaining71P93CyclicAuthorityRow.all,
      Remaining71P93CyclicAuthorityRow.spiroRows]

def ofFusedCyclophane : Remaining71P93FusedCyclophaneAuthorityRow →
    Remaining71P93DescriptorKernelRow
  | .fusedBridgedCIP => .cyclic .fusedBridgedCIP
  | .cisoidTransoid => .cyclic .cisoidTransoid
  | .cyclophanePlanes => .cyclic .cyclophanePlanes
  | .cyclophaneCenters => .cyclic .cyclophaneCenters
  | .cyclophaneDoubleBonds => .cyclic .cyclophaneDoubleBonds

@[simp] theorem ofFusedCyclophane_provision
    (row : Remaining71P93FusedCyclophaneAuthorityRow) :
    (ofFusedCyclophane row).provision = row.provision := by
  cases row <;> rfl

@[simp] theorem ofFusedCyclophane_reference
    (policies : Remaining71ReviewedPolicies)
    (row : Remaining71P93FusedCyclophaneAuthorityRow) :
    (ofFusedCyclophane row).reference policies =
      row.reference policies.p93Cyclic.fused policies.p93Cyclic.cyclophane := by
  cases row <;> rfl

theorem ofFusedCyclophane_mem_all
    (row : Remaining71P93FusedCyclophaneAuthorityRow) :
    ofFusedCyclophane row ∈ all := by
  cases row <;>
    simp [ofFusedCyclophane, all, cyclicRows,
      Remaining71P93CyclicAuthorityRow.all,
      Remaining71P93CyclicAuthorityRow.fusedAndCyclophaneRows]

def ofCoupledRingChain : Remaining71P93CoupledRingChainAuthorityRow →
    Remaining71P93DescriptorKernelRow
  | .configurations => .cyclic .coupledRingChainConfigurations

@[simp] theorem ofCoupledRingChain_provision
    (row : Remaining71P93CoupledRingChainAuthorityRow) :
    (ofCoupledRingChain row).provision = row.provision := by
  cases row
  rfl

@[simp] theorem ofCoupledRingChain_reference
    (policies : Remaining71ReviewedPolicies)
    (row : Remaining71P93CoupledRingChainAuthorityRow) :
    (ofCoupledRingChain row).reference policies =
      row.reference policies.p93Cyclic.coupledRingChain := by
  cases row
  rfl

theorem ofCoupledRingChain_mem_all
    (row : Remaining71P93CoupledRingChainAuthorityRow) :
    ofCoupledRingChain row ∈ all := by
  cases row
  simp [ofCoupledRingChain, all, cyclicRows,
    Remaining71P93CyclicAuthorityRow.all,
    Remaining71P93CyclicAuthorityRow.coupledRingChainRows]

/-- Embed every proved P-93 production family into the exhaustive 56-row dispatcher. -/
def ofClosedProduction : Remaining71P93ClosedProductionRow →
    Remaining71P93DescriptorKernelRow
  | .fullerene row => ofFullerene row
  | .noncarbon row => .noncarbon row
  | .general row => .general row
  | .monocyclic row => ofMonocyclic row
  | .vonBaeyer row => ofVonBaeyer row
  | .ringAssembly row => ofRingAssembly row
  | .acyclic row => .acyclic row
  | .spiro row => ofSpiro row
  | .spiroNontetrahedral => .cyclic .spiroNontetrahedralCenters
  | .fusedCyclophane row => ofFusedCyclophane row
  | .coupledRingChain row => ofCoupledRingChain row

@[simp] theorem ofClosedProduction_provision
    (row : Remaining71P93ClosedProductionRow) :
    (ofClosedProduction row).provision = row.provision := by
  cases row with
  | fullerene child => exact ofFullerene_provision child
  | noncarbon child => rfl
  | general child => rfl
  | monocyclic child => exact ofMonocyclic_provision child
  | vonBaeyer child => exact ofVonBaeyer_provision child
  | ringAssembly child => exact ofRingAssembly_provision child
  | acyclic child => rfl
  | spiro child => exact ofSpiro_provision child
  | spiroNontetrahedral => rfl
  | fusedCyclophane child => exact ofFusedCyclophane_provision child
  | coupledRingChain child => exact ofCoupledRingChain_provision child

@[simp] theorem ofClosedProduction_reference
    (policies : Remaining71ReviewedPolicies)
    (row : Remaining71P93ClosedProductionRow) :
    (ofClosedProduction row).reference policies = row.reference policies := by
  cases row with
  | fullerene child => exact ofFullerene_reference policies child
  | noncarbon child => rfl
  | general child => rfl
  | monocyclic child => exact ofMonocyclic_reference policies child
  | vonBaeyer child => exact ofVonBaeyer_reference policies child
  | ringAssembly child => exact ofRingAssembly_reference policies child
  | acyclic child => rfl
  | spiro child => exact ofSpiro_reference policies child
  | spiroNontetrahedral => rfl
  | fusedCyclophane child => exact ofFusedCyclophane_reference policies child
  | coupledRingChain child => exact ofCoupledRingChain_reference policies child

theorem ofClosedProduction_mem_all
    (row : Remaining71P93ClosedProductionRow) :
    ofClosedProduction row ∈ all := by
  cases row with
  | fullerene child => exact ofFullerene_mem_all child
  | noncarbon child =>
      cases child <;>
        simp [ofClosedProduction, all, noncarbonRows,
          Remaining71P93NoncarbonAuthorityRow.all]
  | general child =>
      cases child <;>
        simp [ofClosedProduction, all, generalRows,
          Remaining71P93GeneralAuthorityRow.all]
  | monocyclic child => exact ofMonocyclic_mem_all child
  | vonBaeyer child => exact ofVonBaeyer_mem_all child
  | ringAssembly child => exact ofRingAssembly_mem_all child
  | acyclic child =>
      cases child <;>
        simp [ofClosedProduction, all, acyclicRows,
          Remaining71P93AcyclicAuthorityRow.all]
  | spiro child => exact ofSpiro_mem_all child
  | spiroNontetrahedral =>
      simp [ofClosedProduction, all, cyclicRows,
        Remaining71P93CyclicAuthorityRow.all,
        Remaining71P93CyclicAuthorityRow.spiroRows]
  | fusedCyclophane child => exact ofFusedCyclophane_mem_all child
  | coupledRingChain child => exact ofCoupledRingChain_mem_all child

/-! Only explicit family production relations occur below.  Their assembled equivalence theorem
closes the provision-relative duty inventory; canonical-policy construction and computational
executability remain separate release obligations. -/
def DescriptorKernelJudges
    (policies : Remaining71ReviewedPolicies) :
    (row : Remaining71P93DescriptorKernelRow) →
      AuthoritativeChemicalInput → (row.reference policies).Observation → Prop
  | .noncarbon row, source, observation =>
      row.ProductionJudges policies.p93Noncarbon source observation

  | .acyclic row, source, observation =>
      row.ProductionJudges policies.p93Acyclic source observation

  | .cyclic .monocyclicRCT, _source, observation =>
      Remaining71P93MonocyclicAuthorityRow.ProductionJudges
        policies.p93Cyclic.monocyclic .monocyclicRCT _source observation
  | .cyclic .cyclicConfigurations, source, observation =>
      Remaining71P93MonocyclicAuthorityRow.ProductionJudges
        policies.p93Cyclic.monocyclic .cyclicConfigurations source observation
  | .cyclic .monocyclicAbsoluteCenters, source, observation =>
      Remaining71P93MonocyclicAuthorityRow.ProductionJudges
        policies.p93Cyclic.monocyclic .monocyclicAbsoluteCenters source observation
  | .cyclic .monocyclicAchiralCenters, source, observation =>
      Remaining71P93MonocyclicAuthorityRow.ProductionJudges
        policies.p93Cyclic.monocyclic .monocyclicAchiralCenters source observation
  | .cyclic .monocyclicCisTrans, source, observation =>
      Remaining71P93MonocyclicAuthorityRow.ProductionJudges
        policies.p93Cyclic.monocyclic .monocyclicCisTrans source observation
  | .cyclic .unsaturatedMonocycles, source, observation =>
      Remaining71P93MonocyclicAuthorityRow.ProductionJudges
        policies.p93Cyclic.monocyclic .unsaturatedMonocycles source observation
  | .cyclic .cyclicDoubleBonds, source, observation =>
      Remaining71P93MonocyclicAuthorityRow.ProductionJudges
        policies.p93Cyclic.monocyclic .cyclicDoubleBonds source observation
  | .cyclic .exocyclicDoubleBondEZ, source, observation =>
      Remaining71P93MonocyclicAuthorityRow.ProductionJudges
        policies.p93Cyclic.monocyclic .exocyclicDoubleBondEZ source observation
  | .cyclic .exocyclicDoubleBondOther, source, observation =>
      Remaining71P93MonocyclicAuthorityRow.ProductionJudges
        policies.p93Cyclic.monocyclic .exocyclicDoubleBondOther source observation
  | .cyclic .vonBaeyerCIPCenters, source, observation =>
      Remaining71P93VonBaeyerAuthorityRow.ProductionJudges
        policies.p93Cyclic.vonBaeyer .vonBaeyerCIPCenters source observation
  | .cyclic .vonBaeyerEndoExoSynAnti, source, observation =>
      Remaining71P93VonBaeyerAuthorityRow.ProductionJudges
        policies.p93Cyclic.vonBaeyer .vonBaeyerEndoExoSynAnti source observation
  | .cyclic .vonBaeyerCisTrans, source, observation =>
      Remaining71P93VonBaeyerAuthorityRow.ProductionJudges
        policies.p93Cyclic.vonBaeyer .vonBaeyerCisTrans source observation
  | .cyclic .vonBaeyerDoubleBonds, source, observation =>
      Remaining71P93VonBaeyerAuthorityRow.ProductionJudges
        policies.p93Cyclic.vonBaeyer .vonBaeyerDoubleBonds source observation
  | .cyclic .ringAssemblyAxes, source, observation =>
      Remaining71P93RingAssemblyAuthorityRow.ProductionJudges
        policies.p93Cyclic.ringAssembly .axes source observation
  | .cyclic .ringAssemblyCenters, source, observation =>
      Remaining71P93RingAssemblyAuthorityRow.ProductionJudges
        policies.p93Cyclic.ringAssembly .centers source observation
  | .cyclic .ringAssemblyDoubleBonds, source, observation =>
      Remaining71P93RingAssemblyAuthorityRow.ProductionJudges
        policies.p93Cyclic.ringAssembly .doubleBonds source observation
  | .cyclic .spiroXabcd, source, observation =>
      Remaining71P93SpiroReadyAuthorityRow.ProductionJudges
        policies.p93Cyclic.spiro .spiroXabcd source observation
  | .cyclic .spiroXabab, source, observation =>
      Remaining71P93SpiroReadyAuthorityRow.ProductionJudges
        policies.p93Cyclic.spiro .spiroXabab source observation
  | .cyclic .spiroDoubleBonds, source, observation =>
      Remaining71P93SpiroReadyAuthorityRow.ProductionJudges
        policies.p93Cyclic.spiro .spiroDoubleBonds source observation
  | .cyclic .spiroAxialChirality, source, observation =>
      Remaining71P93SpiroReadyAuthorityRow.ProductionJudges
        policies.p93Cyclic.spiro .spiroAxialChirality source observation
  | .cyclic .spiroNontetrahedralCenters, source, observation =>
      P93SpiroNontetrahedralSourceCore policies.p93Cyclic.spiro source observation
  | .cyclic .fusedBridgedCIP, source, observation =>
      Remaining71P93FusedCyclophaneAuthorityRow.ProductionJudges
        policies.p93Cyclic.fused policies.p93Cyclic.cyclophane
        .fusedBridgedCIP source observation
  | .cyclic .cisoidTransoid, source, observation =>
      Remaining71P93FusedCyclophaneAuthorityRow.ProductionJudges
        policies.p93Cyclic.fused policies.p93Cyclic.cyclophane
        .cisoidTransoid source observation
  | .cyclic .cyclophanePlanes, source, observation =>
      Remaining71P93FusedCyclophaneAuthorityRow.ProductionJudges
        policies.p93Cyclic.fused policies.p93Cyclic.cyclophane
        .cyclophanePlanes source observation
  | .cyclic .cyclophaneCenters, source, observation =>
      Remaining71P93FusedCyclophaneAuthorityRow.ProductionJudges
        policies.p93Cyclic.fused policies.p93Cyclic.cyclophane
        .cyclophaneCenters source observation
  | .cyclic .cyclophaneDoubleBonds, source, observation =>
      Remaining71P93FusedCyclophaneAuthorityRow.ProductionJudges
        policies.p93Cyclic.fused policies.p93Cyclic.cyclophane
        .cyclophaneDoubleBonds source observation
  | .cyclic .coupledRingChainConfigurations, source, observation =>
      Remaining71P93CoupledRingChainAuthorityRow.ProductionJudges
        policies.p93Cyclic.coupledRingChain .configurations source observation
  | .cyclic .fullereneGeneralMethodology, source, observation =>
      Remaining71P93FullereneAuthorityRow.ProductionJudges
        policies.p93Cyclic.fullerene policies.p93Cyclic.relationalFullerene
        .generalMethodology source observation
  | .cyclic .fullereneInherentParentChirality, source, observation =>
      Remaining71P93FullereneAuthorityRow.ProductionJudges
        policies.p93Cyclic.fullerene policies.p93Cyclic.relationalFullerene
        .inherentParentChirality source observation
  | .cyclic .fullereneInherentSubstitutionChirality, source, observation =>
      Remaining71P93FullereneAuthorityRow.ProductionJudges
        policies.p93Cyclic.fullerene policies.p93Cyclic.relationalFullerene
        .inherentSubstitutionChirality source observation
  | .cyclic .fullereneNoninherentSubstitutionChirality, source, observation =>
      Remaining71P93FullereneAuthorityRow.ProductionJudges
        policies.p93Cyclic.fullerene policies.p93Cyclic.relationalFullerene
        .noninherentSubstitutionChirality source observation
  | .cyclic .fullereneChiralSubstituents, source, observation =>
      Remaining71P93FullereneAuthorityRow.ProductionJudges
        policies.p93Cyclic.fullerene policies.p93Cyclic.relationalFullerene
        .chiralSubstituents source observation
  | .cyclic .fullereneSuperimposedStereogenicElements, source, observation =>
      Remaining71P93FullereneAuthorityRow.ProductionJudges
        policies.p93Cyclic.fullerene policies.p93Cyclic.relationalFullerene
        .superimposedStereogenicElements source observation
  | .general row, source, observation =>
      row.ProductionJudges policies.p93General source observation

/-- The exact rows backed by local descriptor relations in this module.  This is a kernel-coverage
inventory, not the provision-correctness frontier. -/
def descriptorKernelReadyRows : List Remaining71P93DescriptorKernelRow :=
  [ .acyclic .acyclicCenters
  , .acyclic .singleAcyclicCenter
  , .acyclic .multipleDescriptorsOneCenter
  , .acyclic .prefixComponentCenters
  , .acyclic .ordinaryDoubleBonds
  , .acyclic .doubleBondEZCisTrans
  , .acyclic .multipleDoubleBonds
  , .acyclic .heteroatomDoubleBonds
  , .acyclic .evenCumulenes
  , .acyclic .oddCumulenes
  , .acyclic .multipleAcyclicStereogenicUnits
  , .cyclic .spiroXabcd
  , .cyclic .spiroXabab
  , .cyclic .spiroDoubleBonds
  , .cyclic .spiroAxialChirality
  , .cyclic .fullereneGeneralMethodology
  , .cyclic .fullereneInherentParentChirality
  , .cyclic .fullereneInherentSubstitutionChirality
  , .cyclic .fullereneNoninherentSubstitutionChirality
  , .cyclic .fullereneChiralSubstituents
  , .cyclic .fullereneSuperimposedStereogenicElements
  , .noncarbon .otherElementTetrahedra
  , .noncarbon .otherElementGeneralMethodology
  , .noncarbon .azaniumPhosphanium
  , .noncarbon .aminePhosphaneOxides
  , .noncarbon .phosphatesPhosphonates
  , .noncarbon .sulfatesSulfonates
  , .noncarbon .group14Noncarbon
  , .general .absoluteConfiguration
  , .general .relativeConfiguration
  , .general .mixedAbsoluteRelativeConfiguration
  , .general .racemates
  , .general .ambo
  , .cyclic .cyclicConfigurations
  , .cyclic .monocyclicAbsoluteCenters
  , .cyclic .monocyclicAchiralCenters
  , .cyclic .monocyclicCisTrans
  , .cyclic .monocyclicRCT
  , .cyclic .unsaturatedMonocycles
  , .cyclic .cyclicDoubleBonds
  , .cyclic .exocyclicDoubleBondEZ
  , .cyclic .exocyclicDoubleBondOther
  , .cyclic .spiroNontetrahedralCenters
  , .cyclic .fusedBridgedCIP
  , .cyclic .cisoidTransoid
  , .cyclic .cyclophanePlanes
  , .cyclic .cyclophaneCenters
  , .cyclic .cyclophaneDoubleBonds
  , .cyclic .coupledRingChainConfigurations
  , .cyclic .vonBaeyerCIPCenters
  , .cyclic .vonBaeyerEndoExoSynAnti
  , .cyclic .vonBaeyerCisTrans
  , .cyclic .vonBaeyerDoubleBonds
  , .cyclic .ringAssemblyAxes
  , .cyclic .ringAssemblyCenters
  , .cyclic .ringAssemblyDoubleBonds
  ]

@[simp] theorem descriptorKernelReadyRows_length : descriptorKernelReadyRows.length = 56 := by
  rfl

/-- The rows for which this module does not yet contain even a descriptor kernel. -/
def NoDescriptorKernel (row : Remaining71P93DescriptorKernelRow) : Prop :=
  row ∉ descriptorKernelReadyRows

instance (row : Remaining71P93DescriptorKernelRow) : Decidable row.NoDescriptorKernel := by
  unfold NoDescriptorKernel
  infer_instance

def noDescriptorKernelRows : List Remaining71P93DescriptorKernelRow :=
  all.filter fun row => decide row.NoDescriptorKernel

set_option maxRecDepth 16384 in
@[simp] theorem noDescriptorKernelRows_length : noDescriptorKernelRows.length = 0 := by
  decide

/-- An unresolved row is definitionally nonproducing.  Its status cannot be converted into a
vacuous global correctness theorem. -/
theorem descriptorKernel_false_of_noDescriptorKernel
    (policies : Remaining71ReviewedPolicies)
    (row : Remaining71P93DescriptorKernelRow)
    (noKernel : row.NoDescriptorKernel)
    (source : AuthoritativeChemicalInput)
    (observation : (row.reference policies).Observation) :
    ¬row.DescriptorKernelJudges policies source observation := by
  cases row with
  | general child => cases child <;>
      simp_all [NoDescriptorKernel, descriptorKernelReadyRows]
  | noncarbon child => cases child <;>
      simp_all [NoDescriptorKernel, descriptorKernelReadyRows]
  | acyclic child => cases child <;>
      simp_all [NoDescriptorKernel, descriptorKernelReadyRows]
  | cyclic child => cases child <;>
      simp_all [NoDescriptorKernel, descriptorKernelReadyRows]

theorem closedProductionDescriptorKernel_eq_reference
    (policies : Remaining71ReviewedPolicies)
    (row : Remaining71P93ClosedProductionRow)
    (source : AuthoritativeChemicalInput)
    (observation : ((ofClosedProduction row).reference policies).Observation) :
    DescriptorKernelJudges policies (ofClosedProduction row) source observation ↔
      ((ofClosedProduction row).reference policies).Judges source observation := by
  cases row with
  | fullerene child =>
      cases child <;>
        exact Remaining71P93FullereneAuthorityRow.production_eq_reference
          policies.p93Cyclic.fullerene policies.p93Cyclic.relationalFullerene
          _ source observation
  | noncarbon child =>
      exact child.production_eq_reference policies.p93Noncarbon source observation
  | general child =>
      exact child.production_eq_reference policies.p93General source observation
  | monocyclic child =>
      cases child <;> rfl
  | vonBaeyer child =>
      cases child <;> rfl
  | ringAssembly child =>
      cases child <;> rfl
  | acyclic child =>
      exact child.production_eq_reference policies.p93Acyclic source observation
  | spiro child =>
      cases child with
      | spiroXabcd =>
          exact Remaining71P93SpiroReadyAuthorityRow.production_eq_reference
            policies.p93Cyclic.spiro .spiroXabcd source observation
      | spiroXabab =>
          exact Remaining71P93SpiroReadyAuthorityRow.production_eq_reference
            policies.p93Cyclic.spiro .spiroXabab source observation
      | spiroDoubleBonds =>
          exact Remaining71P93SpiroReadyAuthorityRow.production_eq_reference
            policies.p93Cyclic.spiro .spiroDoubleBonds source observation
      | spiroAxialChirality =>
          exact Remaining71P93SpiroReadyAuthorityRow.production_eq_reference
            policies.p93Cyclic.spiro .spiroAxialChirality source observation
  | spiroNontetrahedral =>
      exact p93SpiroNontetrahedral_sourceCore_iff_validFor
        policies.p93Cyclic.spiro source observation
  | fusedCyclophane child =>
      cases child <;>
        exact Remaining71P93FusedCyclophaneAuthorityRow.production_eq_reference
          policies.p93Cyclic.fused policies.p93Cyclic.cyclophane _ source observation
  | coupledRingChain child =>
      cases child
      exact Remaining71P93CoupledRingChainAuthorityRow.production_eq_reference
        policies.p93Cyclic.coupledRingChain .configurations source observation

theorem toReviewedRow_mem_all (row : Remaining71P93DescriptorKernelRow) :
    row.toReviewedRow ∈ Remaining71ReviewedRow.all := by
  cases row with
  | general child =>
      cases child <;>
        simp [toReviewedRow, Remaining71ReviewedRow.all,
          Remaining71ReviewedRow.generalRows,
          Remaining71P93GeneralAuthorityRow.all]
  | noncarbon child =>
      cases child <;>
        simp [toReviewedRow, Remaining71ReviewedRow.all,
          Remaining71ReviewedRow.noncarbonRows,
          Remaining71P93NoncarbonAuthorityRow.all]
  | acyclic child =>
      cases child <;>
        simp [toReviewedRow, Remaining71ReviewedRow.all,
          Remaining71ReviewedRow.acyclicRows,
          Remaining71P93AcyclicAuthorityRow.all]
  | cyclic child =>
      cases child <;>
        simp [toReviewedRow, Remaining71ReviewedRow.all,
          Remaining71ReviewedRow.cyclicRows,
          Remaining71P93CyclicAuthorityRow.all,
          Remaining71P93CyclicAuthorityRow.monocyclicRows,
          Remaining71P93CyclicAuthorityRow.vonBaeyerRows,
          Remaining71P93CyclicAuthorityRow.spiroRows,
          Remaining71P93CyclicAuthorityRow.fusedAndCyclophaneRows,
          Remaining71P93CyclicAuthorityRow.fullereneRows,
          Remaining71P93CyclicAuthorityRow.ringAssemblyRows,
          Remaining71P93CyclicAuthorityRow.coupledRingChainRows]

def toDescriptorBearingReviewedRow
    (row : Remaining71P93DescriptorKernelRow) : DescriptorBearingReviewedRow :=
  .remaining71 row.toReviewedRow

theorem toDescriptorBearingReviewedRow_mem_all
    (row : Remaining71P93DescriptorKernelRow) :
    row.toDescriptorBearingReviewedRow ∈ DescriptorBearingReviewedRow.all := by
  simp [toDescriptorBearingReviewedRow, DescriptorBearingReviewedRow.all,
    DescriptorBearingReviewedRow.remaining71Rows, row.toReviewedRow_mem_all]

theorem descriptorAssignmentBearing (row : Remaining71P93DescriptorKernelRow) :
    DescriptorAssignmentBearing row.provision := by
  apply descriptorBearingOfReviewedMember row.provision
  rw [List.mem_toFinset]
  change row.provision ∈
    DescriptorBearingReviewedRow.all.map DescriptorBearingReviewedRow.provision
  exact List.mem_map.mpr
    ⟨row.toDescriptorBearingReviewedRow,
      row.toDescriptorBearingReviewedRow_mem_all, rfl⟩

def provisions : List IUPACNormativeProvision :=
  all.map provision

@[simp] theorem provisions_length : provisions.length = 56 := by
  simp [provisions]

@[simp] theorem provisions_exact :
    provisions = remainingP93DescriptorProvisions := by
  have generalExact : generalRows.map provision = p93GeneralSemanticsSlice := by
    simpa only [generalRows, List.map_map, Function.comp_def, provision,
      toReviewedRow, Remaining71ReviewedRow.provision] using
      Remaining71P93GeneralAuthorityRow.all_provisions_exact
  have noncarbonExact :
      noncarbonRows.map provision = p93NoncarbonTetrahedraSemanticsSlice := by
    simpa only [noncarbonRows, List.map_map, Function.comp_def, provision,
      toReviewedRow, Remaining71ReviewedRow.provision] using
      Remaining71P93NoncarbonAuthorityRow.all_provisions_exact
  have acyclicExact : acyclicRows.map provision = p93AcyclicSemanticsSlice := by
    simpa only [acyclicRows, List.map_map, Function.comp_def, provision,
      toReviewedRow, Remaining71ReviewedRow.provision] using
      Remaining71P93AcyclicAuthorityRow.all_provisions_exact
  have cyclicExact : cyclicRows.map provision = p93CyclicSemanticsSlice := by
    simpa only [cyclicRows, List.map_map, Function.comp_def, provision,
      toReviewedRow, Remaining71ReviewedRow.provision] using
      Remaining71P93CyclicAuthorityRow.all_provisions_exact
  simp only [provisions, all, List.map_append, generalExact, noncarbonExact,
    acyclicExact, cyclicExact, remainingP93DescriptorProvisions]

theorem provisions_nodup : provisions.Nodup := by
  rw [provisions_exact]
  have remainingNodup := remaining71DescriptorBearingProvisions_nodup
  change (remainingP93DescriptorProvisions ++ p94SemanticsSlice ++
    descriptorAssignmentAuthorityDataProvisions).Nodup at remainingNodup
  exact (List.nodup_append.mp (List.nodup_append.mp remainingNodup).1).1

/-- The exact P-93 provision-correctness frontier after all closed-family rows are discharged by
one sum theorem.  This is a caller-duty list, not the canonical-policy readiness frontier. -/
def openProductionDuties : List IUPACNormativeProvision :=
  provisions.filter fun provision =>
    decide (provision ∉ Remaining71P93ClosedProductionRow.provisions)

@[simp] theorem mem_openProductionDuties_iff
    (provision : IUPACNormativeProvision) :
    provision ∈ openProductionDuties ↔
      provision ∈ provisions ∧
        provision ∉ Remaining71P93ClosedProductionRow.provisions := by
  simp [openProductionDuties]

set_option maxRecDepth 16384 in
@[simp] theorem openProductionDuties_length : openProductionDuties.length = 0 := by
  decide

theorem exists_row
    {provision : IUPACNormativeProvision}
    (member : provision ∈ provisions) :
    ∃ row, row ∈ all ∧ row.provision = provision := by
  simpa only [provisions, List.mem_map] using member

noncomputable def rowOf
    (provision : IUPACNormativeProvision)
    (member : provision ∈ provisions) : Remaining71P93DescriptorKernelRow :=
  Classical.choose (exists_row member)

theorem rowOf_provision
    (provision : IUPACNormativeProvision)
    (member : provision ∈ provisions) :
    (rowOf provision member).provision = provision :=
  (Classical.choose_spec (exists_row member)).2

theorem rowOf_eq_ofClosedProduction
    (row : Remaining71P93ClosedProductionRow)
    (member : row.provision ∈ provisions) :
    rowOf row.provision member = ofClosedProduction row := by
  apply List.inj_on_of_nodup_map
    (show (all.map provision).Nodup by simpa [provisions] using provisions_nodup)
  · exact (Classical.choose_spec (exists_row member)).1
  · exact ofClosedProduction_mem_all row
  · exact (rowOf_provision row.provision member).trans
      (ofClosedProduction_provision row).symm

end Remaining71P93DescriptorKernelRow

open Remaining71P93DescriptorKernelRow

theorem descriptorBearingReviewedSemantics_remaining71P93_exact
    (policies : DescriptorBearingReviewedPolicies)
    (row : Remaining71P93DescriptorKernelRow) :
    (descriptorBearingReviewedSemantics policies).reviewed.row row.provision
        (descriptorBearingReviewedMember row.provision row.descriptorAssignmentBearing) =
      row.toReviewedRow.semantics policies.remaining71 := by
  change DescriptorBearingReviewedRow.semantics policies
      (descriptorBearingReviewedRowOf
        row.toDescriptorBearingReviewedRow.provision _) =
    row.toReviewedRow.semantics policies.remaining71
  rw [descriptorBearingReviewedRowOf_eq row.toDescriptorBearingReviewedRow
    row.toDescriptorBearingReviewedRow_mem_all]
  rfl

theorem globalReviewedSemantics_remaining71P93_exact
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (row : Remaining71P93DescriptorKernelRow) :
    global.reviewed.row row.provision =
      row.toReviewedRow.semantics policies.remaining71 := by
  rw [global.descriptorBearing_exact row.descriptorAssignmentBearing]
  exact descriptorBearingReviewedSemantics_remaining71P93_exact policies row

theorem remaining71P93GlobalReference_eq
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (row : Remaining71P93DescriptorKernelRow) :
    (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference
      row.provision = row.reference policies.remaining71 := by
  change ((globalDescriptorAssignmentProjection global.toFrozenCorpus).reference
    row.provision).toReference = row.reference policies.remaining71
  rw [DescriptorAssignmentProjection.descriptorBearing_exact
    (globalDescriptorAssignmentProjection global.toFrozenCorpus)
      row.provision row.descriptorAssignmentBearing]
  change (global.reviewed.row row.provision).reference =
    row.reference policies.remaining71
  rw [globalReviewedSemantics_remaining71P93_exact global row]
  rfl

theorem remaining71P93GlobalReference_eq_of_member
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ provisions) :
    (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference provision =
      (rowOf provision member).reference policies.remaining71 := by
  let row := rowOf provision member
  have rowProvision : row.provision = provision := rowOf_provision provision member
  calc
    (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference provision =
        (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference
          row.provision := congrArg
            ((globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference)
            rowProvision.symm
    _ = row.reference policies.remaining71 := remaining71P93GlobalReference_eq global row
    _ = (rowOf provision member).reference policies.remaining71 := rfl

/-- A mixed production dispatcher over the 56-row P-93 scope.  Its out-of-scope branch is the
required totalization only.  All in-scope rows carry provision-relative production relations;
canonical frozen-policy construction remains a separate boundary. -/
noncomputable def remaining71P93DescriptorKernelInterpreter
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative) :
    ProvisionInterpreter
      (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus where
  Produces := fun provision source observation =>
    if member : provision ∈ provisions then
      let row := rowOf provision member
      let referenceEq := remaining71P93GlobalReference_eq_of_member
        global provision member
      row.DescriptorKernelJudges policies.remaining71 source
        (cast (congrArg ProvisionReference.Observation referenceEq) observation)
    else False

@[simp] theorem remaining71P93DescriptorKernelInterpreter_exact
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ provisions)
    (source : AuthoritativeChemicalInput)
    (observation : ((globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference
      provision).Observation) :
    (remaining71P93DescriptorKernelInterpreter global).Produces provision source observation ↔
      (rowOf provision member).DescriptorKernelJudges policies.remaining71 source
        (cast (congrArg ProvisionReference.Observation
          (remaining71P93GlobalReference_eq_of_member global provision member)) observation) := by
  simp only [remaining71P93DescriptorKernelInterpreter, dif_pos member]

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93DescriptorKernelRow.all_length
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93DescriptorKernelRow.descriptorKernelReadyRows_length
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93DescriptorKernelRow.noDescriptorKernelRows_length
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93DescriptorKernelRow.provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93DescriptorKernelRow.openProductionDuties_length
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93DescriptorKernelRow.rowOf_eq_ofClosedProduction
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93DescriptorKernelRow.closedProductionDescriptorKernel_eq_reference
