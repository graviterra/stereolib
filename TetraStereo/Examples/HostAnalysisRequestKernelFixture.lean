import TetraStereo.Engine.HostAnalysisRequestBuilder
import TetraStereo.Examples.HostModuleCompiler

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo
namespace Examples
namespace HostAnalysisRequestBuilder

open Engine
open OneCenter

noncomputable section

/-! ### Broad multi-output analysis fixture -/

/-- Raw molecule with one tetrahedral center, one assigned alkene, and one cumulene candidate. -/
def broadSurfaceRaw : RawMolecule where
  atoms := List.replicate 12 (AtomSpec.aliphatic Element.C)
  bonds :=
    [ { source := 0, target := 1, kind := ParsedBondKind.single }
    , { source := 0, target := 2, kind := ParsedBondKind.single }
    , { source := 0, target := 3, kind := ParsedBondKind.single }
    , { source := 0, target := 4, kind := ParsedBondKind.single }
    , { source := 5, target := 6, kind := ParsedBondKind.double }
    , { source := 6, target := 7, kind := ParsedBondKind.double }
    , { source := 8, target := 9, kind := ParsedBondKind.double }
    , { source := 1, target := 8, kind := ParsedBondKind.up }
    , { source := 9, target := 4, kind := ParsedBondKind.down }
    ]

/-- Indexed annotations covering assigned axes, planes, helices, conformers, ensembles, and
virtual official-CIP nodes. -/
def broadSurfaceAnnotations : IndexedNoncenterStereoAnnotations where
  axes :=
    [ { axisStart := 5
        axisEnd := 7
        startHigh := 1
        startLow := 2
        endHigh := 3
        endLow := 4
        descriptor := AxialDescriptor.Ra } ]
  planes :=
    [ { planeAtoms := [1, 2, 3]
        pilotAtom := 1
        highReference := 2
        lowReference := 3
        descriptor := PlanarDescriptor.Rp } ]
  helices :=
    [ { helixPath := [1, 0, 2]
        frontReference := 1
        backReference := 2
        descriptor := HelicalDescriptor.M } ]
  conformations :=
    [ { support := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
        kind? := some OfficialStereogenicUnitKind.chiral } ]
  ensembles :=
    [ { support := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]
        kind? := some OfficialStereogenicUnitKind.chiral } ]
  auxiliaryRule5Nodes :=
    [ { anchor := 1
        support := [0]
        descriptor := OfficialRule5Descriptor.descriptorR } ]
  phantomNodes :=
    [ { anchor := 2
        support := [0] } ]
  lonePairNodes :=
    [ { anchor := 3
        support := [0] } ]


def broadSurfaceOfficialCenterTarget : HostOfficialStereoAnalysisTarget where
  keySuffix := "official-center-comparison"
  description := "official center branch comparison"
  definitionPrefix := "broadSurfaceOfficialCenter"
  centerAtom := 0
  left := 0
  right := 1
  target := HostOfficialStereoCertificateTarget.computedComparison



def broadSurfaceAnalysisPlan : HostStereochemicalAnalysisPlan where
  outputs :=
    [ HostStereochemicalOutputTarget.officialCenterComparison broadSurfaceOfficialCenterTarget
    , HostStereochemicalOutputTarget.noncenterDescriptor
        { keySuffix := "axial-unit"
          description := "assigned axial stereochemical unit"
          family := HostNoncenterDescriptorFamily.axial
          expectedResult? := some (HostMoleculeDescriptorResult.axial AxialDescriptor.Ra)
          expectedSourceKey? :=
            some (HostMoleculeDescriptorSourceKey.axial 5 7 1 2 3 4) }
    , HostStereochemicalOutputTarget.noncenterDescriptor
        { keySuffix := "planar-unit"
          description := "assigned planar stereochemical unit"
          family := HostNoncenterDescriptorFamily.planar
          expectedResult? := some (HostMoleculeDescriptorResult.planar PlanarDescriptor.Rp)
          expectedSourceKey? :=
            some (HostMoleculeDescriptorSourceKey.planar [1, 2, 3] 1 2 3) }
    , HostStereochemicalOutputTarget.noncenterDescriptor
        { keySuffix := "helical-unit"
          description := "assigned helical stereochemical unit"
          family := HostNoncenterDescriptorFamily.helical
          expectedResult? := some (HostMoleculeDescriptorResult.helical HelicalDescriptor.M)
          expectedSourceKey? :=
            some (HostMoleculeDescriptorSourceKey.helical [1, 0, 2] 1 2) }
    , HostStereochemicalOutputTarget.noncenterDescriptor
        { keySuffix := "alkene-unit"
          description := "assigned alkene E/Z unit"
          -- `broadSurfaceRaw` writes the marked substituents as `1 -up-> 8` and `9 -down-> 4`.
          -- Reoriented to their own alkene carbons both sides read `down`, so atoms 1 and 4 lie on
          -- the same side and the double bond is cis.
          family := HostNoncenterDescriptorFamily.alkene
          expectedResult? := some (HostMoleculeDescriptorResult.alkene DoubleBondStereo.Z)
          expectedSourceKey? := some (HostMoleculeDescriptorSourceKey.alkene 8 9) }
    , HostStereochemicalOutputTarget.noncenterDescriptor
        { keySuffix := "cumulene-unit"
          description := "parser-visible cumulene candidate"
          family := HostNoncenterDescriptorFamily.cumulene }
    , HostStereochemicalOutputTarget.noncenterDescriptor
        { keySuffix := "auxiliary-rule5-node"
          description := "auxiliary Rule-5 descriptor node"
          family := HostNoncenterDescriptorFamily.auxiliaryRule5
          expectedResult? :=
            some (HostMoleculeDescriptorResult.auxiliaryRule5
              OfficialRule5Descriptor.descriptorR.asAuxiliary)
          expectedSourceKey? :=
            some (HostMoleculeDescriptorSourceKey.auxiliaryRule5 1 [0] (some 0)) }
    , HostStereochemicalOutputTarget.noncenterDescriptor
        { keySuffix := "phantom-node"
          description := "phantom official-CIP node"
          family := HostNoncenterDescriptorFamily.phantom }
    , HostStereochemicalOutputTarget.noncenterDescriptor
        { keySuffix := "lone-pair-node"
          description := "lone-pair official-CIP node"
          family := HostNoncenterDescriptorFamily.lonePair }
    , HostStereochemicalOutputTarget.graphRelation
        { keySuffix := "multicenter-relation"
          description := "multi-center relation exactly-one theorem family"
          kind := HostGraphRelationTargetKind.multiCenterCipRSExactlyOne }
    , HostStereochemicalOutputTarget.graphRelation
        { keySuffix := "graph-classifier-sound"
          description := "graph descriptor classifier soundness theorem family"
          kind := HostGraphRelationTargetKind.descriptorClassifierSound }
    , HostStereochemicalOutputTarget.graphRelation
        { keySuffix := "graph-classifier-self-same"
          description := "graph descriptor classifier proves a concrete self/same outcome"
          kind := HostGraphRelationTargetKind.descriptorClassifierSound
          configurationPolicy := HostMoleculeGraphConfigurationPolicy.identitySelf
          expectedOutcome? := some CipRSClassRelation.same }
    , HostStereochemicalOutputTarget.graphRelation
        { keySuffix := "graph-classifier-mirror-meso-same"
          description := "graph descriptor classifier proves mirror/same under meso evidence"
          kind := HostGraphRelationTargetKind.descriptorClassifierSound
          expectedOutcome? := some CipRSClassRelation.same
          outcomePrecondition := HostMoleculeGraphOutcomePrecondition.descriptorMesoLeft }
    , HostStereochemicalOutputTarget.graphRelation
        { keySuffix := "graph-classifier-mirror-chiral-enantiomeric"
          description := "graph descriptor classifier proves mirror/enantiomeric under chirality evidence"
          kind := HostGraphRelationTargetKind.descriptorClassifierSound
          expectedOutcome? := some CipRSClassRelation.enantiomeric
          outcomePrecondition := HostMoleculeGraphOutcomePrecondition.descriptorChiralLeft }
    , HostStereochemicalOutputTarget.graphRelation
        { keySuffix := "graph-classifier-refusal"
          description := "graph descriptor classifier refusal theorem family"
          kind := HostGraphRelationTargetKind.descriptorClassifierRefusal }
    , HostStereochemicalOutputTarget.conformerClaim
        { keySuffix := "conformer-profile-chiral"
          description := "conformational profile chirality theorem family"
          kind := HostConformerClaimTargetKind.profileChiralRefutesAchiral
          expectedKind? := some OfficialStereogenicUnitKind.chiral
          expectedSourceKey? :=
            some (HostMoleculeDescriptorSourceKey.conformer ""
              [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]) }
    , HostStereochemicalOutputTarget.ensembleClaim
        { keySuffix := "ensemble-descriptor-chiral"
          description := "ensemble descriptor chirality theorem family"
          kind := HostEnsembleClaimTargetKind.descriptorChiralRefutesAchiral
          expectedKind? := some OfficialStereogenicUnitKind.chiral
          expectedSourceKey? :=
            some (HostMoleculeDescriptorSourceKey.ensemble ""
              [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11]) }
    ]


def broadSurfaceMoleculeAnalysisRequest : HostMoleculeAnalysisRequest where
  key := "host-analysis-broad-stereochemical-surface"
  description := "molecule-derived broad stereochemical surface analysis"
  packet := rawMoleculePacket broadSurfaceRaw ChemistryImportTrust.proofCertifiedAdapter
  annotations := broadSurfaceAnnotations
  analysisPlan := broadSurfaceAnalysisPlan
  broadClaimPolicy := HostBroadClaimPolicy.none
  moduleNamespaceBase := ["TetraStereoGenerated", "Examples", "BroadSurface", "Modules"]
  certificateNamespaceBase := ["TetraStereoGenerated", "Examples", "BroadSurface", "Certificates"]
  claimNamespacePath := ["TetraStereoGenerated", "Examples", "BroadSurface", "Claims"]
  witnessNamespacePath := ["TetraStereoGenerated", "Examples", "BroadSurface", "Witnesses"]
  suiteNamespacePath := ["TetraStereoGenerated", "Examples", "BroadSurface", "Suites"]
  suiteFileName := "BroadSurfaceMoleculeAnalysisSuite.lean"
  suiteTheoremName := "broad_surface_molecule_analysis_suite_checked"

end
end HostAnalysisRequestBuilder
end Examples
end TetraStereo
