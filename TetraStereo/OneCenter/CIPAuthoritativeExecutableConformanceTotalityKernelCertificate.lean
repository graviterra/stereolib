import TetraStereo.OneCenter.CIPAuthoritativeExecutableConformanceTotality
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Kernel-only certificate for executable authoritative conformance totality

This certificate checks that molecule-wide discovery totality reaches the actual executable
conformance wrappers and the public certified analyzer-member boundary.  The final endpoint
constructs the execution witness rather than accepting a caller-supplied discovery.
-/

assert_kernel_only TetraStereo.OneCenter.executableAuthoritativeSupportedMoleculeCIPConformance?_exists_of_chemical_applicability
assert_kernel_only TetraStereo.OneCenter.executableCertifiedAuthoritativeSupportedMoleculeCIPConformance?_exists_of_chemical_applicability
assert_kernel_only TetraStereo.OneCenter.analyzeCertifiedNormalized_member_exists_totalAuthoritativeConformance_and_judged_of_chemical_applicability

namespace TetraStereo.OneCenter

open AuthoritativeCIPMancudeTotality



example
    (certified : CertifiedChemistryNormalizationResult) (assignment : StereoAssignment)
    (member : assignment ∈ analyzeCertifiedNormalized certified)
    (kekule : LocalizedMancudeKekuleAdmissible certified.result.parsed) :
    ∃ execution,
      executableCertifiedAuthoritativeSupportedMoleculeCIPConformanceOfCertified? certified =
          some execution ∧
        IndependentlyJudgedAuthorityFacingStereoAssignment certified.result assignment := by
  exact
    analyzeCertifiedNormalized_member_exists_totalAuthoritativeConformance_and_judged_of_chemical_applicability
      certified assignment member kekule

end TetraStereo.OneCenter
