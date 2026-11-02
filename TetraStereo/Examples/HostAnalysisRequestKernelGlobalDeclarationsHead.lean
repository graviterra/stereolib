import TetraStereo.Examples.HostAnalysisRequestKernelFixture

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo.Examples.HostAnalysisRequestKernelProof

open TetraStereo.Engine
open TetraStereo.Examples.HostAnalysisRequestBuilder

noncomputable section

def broadSurfaceDeclarationHeadValue : List String :=
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

set_option maxHeartbeats 1000000 in
theorem broadSurface_declarationHead_eq :
    broadSurfaceMoleculeAnalysisRequest.suiteRequest.officialHostDeclarationNames ++
        (broadSurfaceMoleculeAnalysisRequest.suiteRequest.officialStereoRequests.map
          HostAnalysisSuiteRequest.officialCertificateTheoremName) ++
      (broadSurfaceMoleculeAnalysisRequest.suiteRequest.claimRequests.map
        HostAnalysisSuiteRequest.claimTheoremName) =
      broadSurfaceDeclarationHeadValue := by
  rfl

end
end TetraStereo.Examples.HostAnalysisRequestKernelProof
