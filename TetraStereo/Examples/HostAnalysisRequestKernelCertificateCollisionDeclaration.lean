import TetraStereo.Examples.HostAnalysisRequestKernelCertificateCollisionPackage

set_option autoImplicit false

namespace TetraStereo.Examples.HostAnalysisRequestKernelProof

open TetraStereo.Engine

theorem certificateKeyCollisionSuiteRequest_global_declaration_rejected :
    validationRejected certificateKeyCollisionSuiteRequest.validateGlobalDeclarationNameShape =
      true := by
  unfold HostAnalysisSuiteRequest.validateGlobalDeclarationNameShape
  exact validation_rejected_around _ _ _
    certificateKeyCollisionSuiteRequest_unique_package_keys_rejected

end TetraStereo.Examples.HostAnalysisRequestKernelProof
