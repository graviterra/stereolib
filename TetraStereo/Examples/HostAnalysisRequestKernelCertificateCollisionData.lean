import TetraStereo.Examples.HostAnalysisRequestKernelValidation

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo.Examples.HostAnalysisRequestKernelProof

open TetraStereo.Engine
open TetraStereo.Examples.HostAnalysisRequestBuilder

noncomputable section

def certificateKeyCollisionClaimRequest : HostStereoClaimRequest where
  target := HostStereoClaimTarget.officialCIPAssignmentSuccessResolved
  key :=
    "host-analysis-broad-stereochemical-surface::target-witness::axial::axial-unit::descriptor-result::axial-Ra::source::source-axial-a5-a7-a1-a2-a3-a4::descriptor-result-certificate"
  description := "broad claim deliberately colliding with an axial target certificate"
  namespacePath := ["TetraStereoGenerated", "Examples", "CertificateKeyCollisionClaim"]

def certificateKeyCollisionSuiteRequest : HostAnalysisSuiteRequest :=
  { broadSurfaceMoleculeAnalysisRequest.suiteRequest with
    claimRequests :=
      broadSurfaceMoleculeAnalysisRequest.claimRequests ++ [certificateKeyCollisionClaimRequest] }

private theorem duplicate_strings_of_mem_suffix {x : String} {xs suffix : List String}
    (h : x ∈ suffix) : hasDuplicateStrings (xs ++ x :: suffix) = true := by
  induction xs with
  | nil => simp [hasDuplicateStrings, h]
  | cons _ rest ih => simp [hasDuplicateStrings, ih]

set_option maxHeartbeats 1000000 in
theorem certificateKeyCollisionSuiteRequest_duplicate_package_keys :
    hasDuplicateStrings certificateKeyCollisionSuiteRequest.packageKeys = true := by
  have hcertificate :
      certificateKeyCollisionClaimRequest.key ∈
        certificateKeyCollisionSuiteRequest.witnessCertificateKeys := by
    have hhead :
        certificateKeyCollisionSuiteRequest.witnessCertificateKeys.head? =
          some certificateKeyCollisionClaimRequest.key := by
      rfl
    cases hkeys : certificateKeyCollisionSuiteRequest.witnessCertificateKeys with
    | nil => simp [hkeys] at hhead
    | cons first rest =>
        have hfirst : certificateKeyCollisionClaimRequest.key = first := by
          simpa [hkeys] using hhead.symm
        rw [hfirst]
        simp
  have hsuffix :
      certificateKeyCollisionClaimRequest.key ∈
        certificateKeyCollisionSuiteRequest.witnessPackageKeys ++
          certificateKeyCollisionSuiteRequest.witnessCertificateKeys :=
    List.mem_append_right certificateKeyCollisionSuiteRequest.witnessPackageKeys hcertificate
  unfold certificateKeyCollisionSuiteRequest at hsuffix
  unfold certificateKeyCollisionSuiteRequest HostAnalysisSuiteRequest.packageKeys
    HostAnalysisSuiteRequest.claimPackageKeys
  simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc]
  apply duplicate_strings_of_mem_suffix (x := certificateKeyCollisionClaimRequest.key)
  exact hsuffix

end
end TetraStereo.Examples.HostAnalysisRequestKernelProof
