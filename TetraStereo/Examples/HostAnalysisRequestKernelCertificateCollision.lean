import TetraStereo.Examples.HostAnalysisRequestKernelCertificateCollisionResult
import TetraStereo.Examples.HostAnalysisRequestKernelCertificateCollisionGenerated

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo.Examples.HostAnalysisRequestKernelProof

open TetraStereo.Engine

set_option maxHeartbeats 1000000 in
theorem certificateKeyCollisionSuiteRequest_rejected :
    (match certificateKeyCollisionSuiteRequest.validateGeneratedShape with
      | Except.ok () => false
      | Except.error _ => true) = true := by
  exact Eq.mp
    (congrArg (fun value => value = true)
      certificateKeyCollisionSuiteRequest_validationRejected_eq_match)
    certificateKeyCollisionSuiteRequest_validation_rejected

end TetraStereo.Examples.HostAnalysisRequestKernelProof
