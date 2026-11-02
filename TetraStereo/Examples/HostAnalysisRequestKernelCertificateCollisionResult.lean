import TetraStereo.Examples.HostAnalysisRequestKernelCertificateCollisionGlobal

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo.Examples.HostAnalysisRequestKernelProof

open TetraStereo.Engine

set_option maxHeartbeats 1000000 in
theorem certificateKeyCollisionSuiteRequest_validationRejected_eq_match :
    validationRejected certificateKeyCollisionSuiteRequest.validateGeneratedShape =
      (match certificateKeyCollisionSuiteRequest.validateGeneratedShape with
        | Except.ok () => false
        | Except.error _ => true) :=
  validationRejected_eq_match certificateKeyCollisionSuiteRequest.validateGeneratedShape

end TetraStereo.Examples.HostAnalysisRequestKernelProof
