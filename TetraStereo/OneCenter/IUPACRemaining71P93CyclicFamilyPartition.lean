import TetraStereo.OneCenter.IUPACRemaining71ProvisionInventory

set_option autoImplicit false

/-!
# Exact 33-row cyclic P-93 family partition

The cyclic P-93 queue is not one semantic shape.  This module freezes seven source-defined
compiler families while retaining an exhaustive row enumeration and exact projection onto the
manifest slice.  Later reviewed tables must supply a reference for every constructor; no fallback
row or family default exists.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

inductive P93CyclicAuthorityFamily where
  | monocyclic
  | vonBaeyer
  | spiro
  | fusedAndCyclophane
  | fullerene
  | ringAssembly
  | coupledRingChain
  deriving DecidableEq, Repr

inductive Remaining71P93CyclicAuthorityRow where
  | cyclicConfigurations
  | monocyclicAbsoluteCenters
  | monocyclicAchiralCenters
  | monocyclicCisTrans
  | monocyclicRCT
  | unsaturatedMonocycles
  | cyclicDoubleBonds
  | exocyclicDoubleBondEZ
  | exocyclicDoubleBondOther
  | vonBaeyerCIPCenters
  | vonBaeyerEndoExoSynAnti
  | vonBaeyerCisTrans
  | vonBaeyerDoubleBonds
  | spiroXabcd
  | spiroXabab
  | spiroDoubleBonds
  | spiroNontetrahedralCenters
  | spiroAxialChirality
  | fusedBridgedCIP
  | cisoidTransoid
  | cyclophanePlanes
  | cyclophaneCenters
  | cyclophaneDoubleBonds
  | fullereneGeneralMethodology
  | fullereneInherentParentChirality
  | fullereneInherentSubstitutionChirality
  | fullereneNoninherentSubstitutionChirality
  | fullereneChiralSubstituents
  | fullereneSuperimposedStereogenicElements
  | ringAssemblyAxes
  | ringAssemblyCenters
  | ringAssemblyDoubleBonds
  | coupledRingChainConfigurations
  deriving DecidableEq, Repr

namespace Remaining71P93CyclicAuthorityRow

def monocyclicRows : List Remaining71P93CyclicAuthorityRow :=
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

def vonBaeyerRows : List Remaining71P93CyclicAuthorityRow :=
  [ .vonBaeyerCIPCenters
  , .vonBaeyerEndoExoSynAnti
  , .vonBaeyerCisTrans
  , .vonBaeyerDoubleBonds
  ]

def spiroRows : List Remaining71P93CyclicAuthorityRow :=
  [ .spiroXabcd
  , .spiroXabab
  , .spiroDoubleBonds
  , .spiroNontetrahedralCenters
  , .spiroAxialChirality
  ]

def fusedAndCyclophaneRows : List Remaining71P93CyclicAuthorityRow :=
  [ .fusedBridgedCIP
  , .cisoidTransoid
  , .cyclophanePlanes
  , .cyclophaneCenters
  , .cyclophaneDoubleBonds
  ]

def fullereneRows : List Remaining71P93CyclicAuthorityRow :=
  [ .fullereneGeneralMethodology
  , .fullereneInherentParentChirality
  , .fullereneInherentSubstitutionChirality
  , .fullereneNoninherentSubstitutionChirality
  , .fullereneChiralSubstituents
  , .fullereneSuperimposedStereogenicElements
  ]

def ringAssemblyRows : List Remaining71P93CyclicAuthorityRow :=
  [ .ringAssemblyAxes
  , .ringAssemblyCenters
  , .ringAssemblyDoubleBonds
  ]

def coupledRingChainRows : List Remaining71P93CyclicAuthorityRow :=
  [ .coupledRingChainConfigurations ]

def all : List Remaining71P93CyclicAuthorityRow :=
  monocyclicRows ++ vonBaeyerRows ++ spiroRows ++ fusedAndCyclophaneRows ++
    fullereneRows ++ ringAssemblyRows ++ coupledRingChainRows

def family : Remaining71P93CyclicAuthorityRow → P93CyclicAuthorityFamily
  | .cyclicConfigurations
  | .monocyclicAbsoluteCenters
  | .monocyclicAchiralCenters
  | .monocyclicCisTrans
  | .monocyclicRCT
  | .unsaturatedMonocycles
  | .cyclicDoubleBonds
  | .exocyclicDoubleBondEZ
  | .exocyclicDoubleBondOther => .monocyclic
  | .vonBaeyerCIPCenters
  | .vonBaeyerEndoExoSynAnti
  | .vonBaeyerCisTrans
  | .vonBaeyerDoubleBonds => .vonBaeyer
  | .spiroXabcd
  | .spiroXabab
  | .spiroDoubleBonds
  | .spiroNontetrahedralCenters
  | .spiroAxialChirality => .spiro
  | .fusedBridgedCIP
  | .cisoidTransoid
  | .cyclophanePlanes
  | .cyclophaneCenters
  | .cyclophaneDoubleBonds => .fusedAndCyclophane
  | .fullereneGeneralMethodology
  | .fullereneInherentParentChirality
  | .fullereneInherentSubstitutionChirality
  | .fullereneNoninherentSubstitutionChirality
  | .fullereneChiralSubstituents
  | .fullereneSuperimposedStereogenicElements => .fullerene
  | .ringAssemblyAxes
  | .ringAssemblyCenters
  | .ringAssemblyDoubleBonds => .ringAssembly
  | .coupledRingChainConfigurations => .coupledRingChain

def provision : Remaining71P93CyclicAuthorityRow → IUPACNormativeProvision
  | .cyclicConfigurations => .p93CyclicConfigurations
  | .monocyclicAbsoluteCenters => .p93MonocyclicAbsoluteCenters
  | .monocyclicAchiralCenters => .p93MonocyclicAchiralCenters
  | .monocyclicCisTrans => .p93MonocyclicCisTrans
  | .monocyclicRCT => .p93MonocyclicRCT
  | .unsaturatedMonocycles => .p93UnsaturatedMonocycles
  | .cyclicDoubleBonds => .p93CyclicDoubleBonds
  | .exocyclicDoubleBondEZ => .p93ExocyclicDoubleBondEZ
  | .exocyclicDoubleBondOther => .p93ExocyclicDoubleBondOther
  | .vonBaeyerCIPCenters => .p93VonBaeyerCIPCenters
  | .vonBaeyerEndoExoSynAnti => .p93VonBaeyerEndoExoSynAnti
  | .vonBaeyerCisTrans => .p93VonBaeyerCisTrans
  | .vonBaeyerDoubleBonds => .p93VonBaeyerDoubleBonds
  | .spiroXabcd => .p93SpiroXabcd
  | .spiroXabab => .p93SpiroXabab
  | .spiroDoubleBonds => .p93SpiroDoubleBonds
  | .spiroNontetrahedralCenters => .p93SpiroNontetrahedralCenters
  | .spiroAxialChirality => .p93SpiroAxialChirality
  | .fusedBridgedCIP => .p93FusedBridgedCIP
  | .cisoidTransoid => .p93CisoidTransoid
  | .cyclophanePlanes => .p93CyclophanePlanes
  | .cyclophaneCenters => .p93CyclophaneCenters
  | .cyclophaneDoubleBonds => .p93CyclophaneDoubleBonds
  | .fullereneGeneralMethodology => .p93FullereneGeneralMethodology
  | .fullereneInherentParentChirality => .p93FullereneInherentParentChirality
  | .fullereneInherentSubstitutionChirality =>
      .p93FullereneInherentSubstitutionChirality
  | .fullereneNoninherentSubstitutionChirality =>
      .p93FullereneNoninherentSubstitutionChirality
  | .fullereneChiralSubstituents => .p93FullereneChiralSubstituents
  | .fullereneSuperimposedStereogenicElements =>
      .p93FullereneSuperimposedStereogenicElements
  | .ringAssemblyAxes => .p93RingAssemblyAxes
  | .ringAssemblyCenters => .p93RingAssemblyCenters
  | .ringAssemblyDoubleBonds => .p93RingAssemblyDoubleBonds
  | .coupledRingChainConfigurations => .p93CoupledRingChainConfigurations

def kind (_row : Remaining71P93CyclicAuthorityRow) : ProvisionKind :=
  .spatialDescriptor

@[simp] theorem monocyclicRows_length : monocyclicRows.length = 9 := by rfl
@[simp] theorem vonBaeyerRows_length : vonBaeyerRows.length = 4 := by rfl
@[simp] theorem spiroRows_length : spiroRows.length = 5 := by rfl
@[simp] theorem fusedAndCyclophaneRows_length :
    fusedAndCyclophaneRows.length = 5 := by rfl
@[simp] theorem fullereneRows_length : fullereneRows.length = 6 := by rfl
@[simp] theorem ringAssemblyRows_length : ringAssemblyRows.length = 3 := by rfl
@[simp] theorem coupledRingChainRows_length : coupledRingChainRows.length = 1 := by rfl

@[simp] theorem all_length : all.length = 33 := by
  rfl

theorem all_nodup : all.Nodup := by
  decide

@[simp] theorem all_provisions_exact :
    all.map provision = p93CyclicSemanticsSlice := by
  rfl

set_option maxRecDepth 16384 in
@[simp] theorem classifier_exact (row : Remaining71P93CyclicAuthorityRow) :
    globalProvisionKind row.provision = row.kind := by
  cases row <;> decide

end Remaining71P93CyclicAuthorityRow
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93CyclicAuthorityRow.all_length
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Remaining71P93CyclicAuthorityRow.all_provisions_exact
