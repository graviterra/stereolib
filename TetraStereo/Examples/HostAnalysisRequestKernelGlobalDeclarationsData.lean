import TetraStereo.Examples.HostAnalysisRequestKernelWitness0Declarations
import TetraStereo.Examples.HostAnalysisRequestKernelWitness1Declarations
import TetraStereo.Examples.HostAnalysisRequestKernelWitness2Declarations
import TetraStereo.Examples.HostAnalysisRequestKernelWitness3Declarations
import TetraStereo.Examples.HostAnalysisRequestKernelWitness4Declarations
import TetraStereo.Examples.HostAnalysisRequestKernelWitness5Declarations
import TetraStereo.Examples.HostAnalysisRequestKernelWitness6Declarations
import TetraStereo.Examples.HostAnalysisRequestKernelWitness7Declarations
import TetraStereo.Examples.HostAnalysisRequestKernelWitness8Declarations
import TetraStereo.Examples.HostAnalysisRequestKernelWitness9Declarations
import TetraStereo.Examples.HostAnalysisRequestKernelWitness10Declarations
import TetraStereo.Examples.HostAnalysisRequestKernelWitness11Declarations
import TetraStereo.Examples.HostAnalysisRequestKernelWitness12Declarations
import TetraStereo.Examples.HostAnalysisRequestKernelWitness13Declarations
import TetraStereo.Examples.HostAnalysisRequestKernelWitness14Declarations
import TetraStereo.Examples.HostAnalysisRequestKernelWitness15Declarations
import TetraStereo.Examples.HostAnalysisRequestKernelWitnesses
import TetraStereo.Examples.HostAnalysisRequestKernelGlobalDeclarationsHead

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo.Examples.HostAnalysisRequestKernelProof

open TetraStereo.Engine
open TetraStereo.Examples.HostAnalysisRequestBuilder

noncomputable section

def broadSurfaceDeclarationHeadLegacy : List String :=
  [ "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter.hostOfficialStereoOwnerRequestKey"
  , "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter.hostOfficialStereoPackageKeySuffix"
  , "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter.broadSurfaceOfficialCenterRaw"
  , "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter.broadSurfaceOfficialCenterPacket"
  , "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter.broadSurfaceOfficialCenterImportRequest"
  , "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter.broadSurfaceOfficialCenterImportResult"
  , "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter.broadSurfaceOfficialCenterSafeImport_eq_ok"
  , "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter.broadSurfaceOfficialCenterIntakeTheoremPlan"
  , "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter.broadSurfaceOfficialCenterIntakeSuccess"
  , "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter.broadSurfaceOfficialCenterIntakeSuccess_checked"
  , "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter.broadSurfaceOfficialCenterExportSpec"
  , "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter.broadSurfaceOfficialCenterQuery"
  , "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter.broadSurfaceOfficialCenterBlueprint"
  , "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter.broadSurfaceOfficialCenterPreparedResult"
  , "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter.broadSurfaceOfficialCenterPreparedResult_builds"
  , "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter.broadSurfaceOfficialCenterCenter_mem"
  , "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter.broadSurfaceOfficialCenterRequestFallback"
  , "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter.broadSurfaceOfficialCenterRequest"
  , "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter.broadSurfaceOfficialCenterRequest_target_claim"
  , "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter.broadSurfaceOfficialCenterHostQueryBuilds"
  , "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter.broadSurfaceOfficialCenterHostQuerySourceSpec"
  , "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter.broadSurfaceOfficialCenterCertificateSourceEntry"
  , "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter.broadSurfaceOfficialCenterCertificateSourceEntry_key"
  , "TetraStereoGenerated.Examples.BroadSurface.Modules.broadSurfaceOfficialCenter.broadSurfaceOfficialCenterHostQueryClaim_checked"
  , "TetraStereoGenerated.Examples.BroadSurface.Certificates.broadSurfaceOfficialCenter_official_stereo_query_checked"
  , "TetraStereoGenerated.Examples.BroadSurface.Claims.khost_x45_analysis_x45_broad_x45_stereochemical_x45_surface.host_official_cip_assignment_success_resolved"
  , "TetraStereoGenerated.Examples.BroadSurface.Claims.khost_x45_analysis_x45_broad_x45_stereochemical_x45_surface.host_stereo_element_mirror_involutive"
  , "TetraStereoGenerated.Examples.BroadSurface.Claims.khost_x45_analysis_x45_broad_x45_stereochemical_x45_surface.host_multi_center_cip_rs_exactly_one"
  , "TetraStereoGenerated.Examples.BroadSurface.Claims.khost_x45_analysis_x45_broad_x45_stereochemical_x45_surface.host_graph_descriptor_classifier_sound"
  , "TetraStereoGenerated.Examples.BroadSurface.Claims.khost_x45_analysis_x45_broad_x45_stereochemical_x45_surface.host_graph_descriptor_classifier_refuses"
  , "TetraStereoGenerated.Examples.BroadSurface.Claims.khost_x45_analysis_x45_broad_x45_stereochemical_x45_surface.host_conformational_profile_chiral_refutes_achiral"
  , "TetraStereoGenerated.Examples.BroadSurface.Claims.khost_x45_analysis_x45_broad_x45_stereochemical_x45_surface.host_descriptor_chiral_ensemble_refutes_achiral" ]

def broadSurfaceDeclarationHead : List String :=
  broadSurfaceDeclarationHeadValue

def broadSurfaceDeclarationTail : List String :=
  [ "TetraStereoGenerated.Examples.BroadSurface.Suites.broad_surface_molecule_analysis_suite_checked" ]

def broadSurfaceDeclarationChunk0 : List String :=
  broadSurfaceDeclarationHead

def broadSurfaceDeclarationChunk1 : List String :=
  witness0DeclarationNames ++ witness1DeclarationNames ++ witness2DeclarationNames ++ witness3DeclarationNames

def broadSurfaceDeclarationChunk2 : List String :=
  witness4DeclarationNames ++ witness5DeclarationNames ++ witness6DeclarationNames ++ witness7DeclarationNames

def broadSurfaceDeclarationChunk3 : List String :=
  witness8DeclarationNames ++ witness9DeclarationNames ++ witness10DeclarationNames ++ witness11DeclarationNames

def broadSurfaceDeclarationChunk4 : List String :=
  witness12DeclarationNames ++ witness13DeclarationNames ++ witness14DeclarationNames ++ witness15DeclarationNames ++ broadSurfaceDeclarationTail

def broadSurfaceSuiteDeclarationNames : List String :=
  broadSurfaceDeclarationHead ++ witness0DeclarationNames ++ witness1DeclarationNames ++
    witness2DeclarationNames ++ witness3DeclarationNames ++ witness4DeclarationNames ++
      witness5DeclarationNames ++ witness6DeclarationNames ++ witness7DeclarationNames ++
        witness8DeclarationNames ++ witness9DeclarationNames ++ witness10DeclarationNames ++
          witness11DeclarationNames ++ witness12DeclarationNames ++ witness13DeclarationNames ++
            witness14DeclarationNames ++ witness15DeclarationNames ++ broadSurfaceDeclarationTail

theorem hasDuplicateStrings_append (left right : List String) :
    hasDuplicateStrings (left ++ right) =
      (hasDuplicateStrings left || stringListsIntersect left right || hasDuplicateStrings right) := by
  induction left with
  | nil => rfl
  | cons value rest ih =>
      simp only [List.cons_append, hasDuplicateStrings, List.contains_append,
        stringListsIntersect, List.any_cons, ih]
      simp only [Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]

theorem stringListsIntersect_append_left (left middle right : List String) :
    stringListsIntersect (left ++ middle) right =
      (stringListsIntersect left right || stringListsIntersect middle right) := by
  simp [stringListsIntersect, List.any_append]

theorem stringListsIntersect_append_right (left middle right : List String) :
    stringListsIntersect left (middle ++ right) =
      (stringListsIntersect left middle || stringListsIntersect left right) := by
  unfold stringListsIntersect
  induction left with
  | nil => rfl
  | cons value rest ih =>
      simp only [List.any_cons]
      rw [ih]
      simp only [List.contains_append]
      simp only [Bool.or_assoc, Bool.or_left_comm]

theorem broadSurface_suiteDeclarationNames_chunks :
    broadSurfaceSuiteDeclarationNames =
      broadSurfaceDeclarationChunk0 ++ broadSurfaceDeclarationChunk1 ++
        broadSurfaceDeclarationChunk2 ++ broadSurfaceDeclarationChunk3 ++
          broadSurfaceDeclarationChunk4 := by
  unfold broadSurfaceSuiteDeclarationNames broadSurfaceDeclarationChunk0
    broadSurfaceDeclarationChunk1 broadSurfaceDeclarationChunk2 broadSurfaceDeclarationChunk3
    broadSurfaceDeclarationChunk4
  simp only [List.append_assoc]

set_option maxHeartbeats 1000000 in
theorem broadSurface_suiteDeclarationNames_eq :
    broadSurfaceMoleculeAnalysisRequest.suiteRequest.suiteDeclarationNames =
      broadSurfaceSuiteDeclarationNames := by
  unfold HostAnalysisSuiteRequest.suiteDeclarationNames
  unfold HostAnalysisSuiteRequest.witnessDeclarationNames
  rw [show broadSurfaceMoleculeAnalysisRequest.suiteRequest.witnessRequests =
      [witness0, witness1, witness2, witness3, witness4, witness5, witness6, witness7,
        witness8, witness9, witness10, witness11, witness12, witness13, witness14, witness15] by
    exact broadSurface_witness_list]
  simp only [List.flatMap_cons, List.flatMap_nil, witness0_declarationNames,
    witness1_declarationNames, witness2_declarationNames, witness3_declarationNames,
    witness4_declarationNames, witness5_declarationNames, witness6_declarationNames,
    witness7_declarationNames, witness8_declarationNames, witness9_declarationNames,
    witness10_declarationNames, witness11_declarationNames, witness12_declarationNames,
    witness13_declarationNames, witness14_declarationNames, witness15_declarationNames]
  rw [broadSurface_declarationHead_eq]
  rfl

end
end TetraStereo.Examples.HostAnalysisRequestKernelProof
