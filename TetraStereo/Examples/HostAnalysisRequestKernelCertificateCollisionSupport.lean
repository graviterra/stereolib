import TetraStereo.Examples.HostAnalysisRequestKernelCertificateCollisionData

set_option autoImplicit false

namespace TetraStereo.Examples.HostAnalysisRequestKernelProof

def validationRejected (result : Except String Unit) : Bool :=
  match result with
  | Except.ok () => false
  | Except.error _ => true

theorem validation_rejected_before
    (pre result : Except String Unit) (h : validationRejected result = true) :
    validationRejected (do pre; result) = true := by
  cases pre with
  | error _ => rfl
  | ok _ => exact h

theorem validation_rejected_after
    (result post : Except String Unit) (h : validationRejected result = true) :
    validationRejected (do result; post) = true := by
  cases result with
  | error _ => rfl
  | ok _ => contradiction

theorem validation_rejected_around
    (pre result post : Except String Unit) (h : validationRejected result = true) :
    validationRejected (do pre; result; post) = true :=
  validation_rejected_before pre (do result; post) (validation_rejected_after result post h)

theorem validationRejected_eq_match (result : Except String Unit) :
    validationRejected result =
    (match result with
      | Except.ok () => false
      | Except.error _ => true) := by
  rfl

end TetraStereo.Examples.HostAnalysisRequestKernelProof
