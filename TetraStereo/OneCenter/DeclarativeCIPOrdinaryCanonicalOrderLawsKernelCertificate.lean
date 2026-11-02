import TetraStereo.OneCenter.DeclarativeCIPOrdinaryCanonicalOrderLaws
import TetraStereo.KernelOnly

set_option autoImplicit false

assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.stereochemicalHierarchyOutcome_iff_lexOutcome
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.StereochemicalProblemData.ordinary_constitutional_ruleOutcome_iff
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.StereochemicalProblemData.ordinary_stereochemical_ruleOutcome_iff
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.StereochemicalProblemData.ordinary_ruleOutcome_lex
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.StereochemicalProblemData.withOrdinaryCanonicalAddressing_ordinaryOrderLaws
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.StereochemicalProblemData.withOrdinaryCanonicalAddressing_ordinaryPriority

namespace TetraStereo.OneCenter.DeclarativeCIP.OrdinaryCanonicalOrderLawsKernelCertificate

/-- The reversed-address code reverses lexicographic order: `[]` precedes `[0]` lexicographically,
so its code is the larger one. -/
theorem dualAddress_reverses : dualAddressAux [0] < dualAddressAux [] := by decide

/-- The integer code is monotone across zero. -/
theorem intCode_monotone_example : intCode.code (-2) < intCode.code (-1) ∧
    intCode.code (-1) < intCode.code 0 ∧ intCode.code 0 < intCode.code 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end TetraStereo.OneCenter.DeclarativeCIP.OrdinaryCanonicalOrderLawsKernelCertificate

assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.listCode
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.pairCode
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.dualAddressCode
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.intCode
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.stereoValueCode
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.mem_windowPaths
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.windowPaths_pairwise
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.lexOutcome_iff_samples
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.LexCode.map_orderedKeyOutcome_iff
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.StereochemicalProblemData.constitutionalSampleKey_characterizes
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.StereochemicalProblemData.stereochemicalSampleKey_characterizes
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.StereochemicalProblemData.withOrdinaryCanonicalAddressing_ordinaryRuleKeyModel
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.StereochemicalProblemData.withOrdinaryCanonicalAddressing_ordinaryPriority_of_keyModel
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.OrdinaryCanonicalOrderLawsKernelCertificate.dualAddress_reverses
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.OrdinaryCanonicalOrderLawsKernelCertificate.intCode_monotone_example
