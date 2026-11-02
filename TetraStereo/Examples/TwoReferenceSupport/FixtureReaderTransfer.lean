import TetraStereo.Examples.TwoReferenceSupport.FixtureOccurrences
import TetraStereo.OneCenter.LocalizedActualMolecularEvidenceRefinement
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace FixtureReaderTransfer

open TetraStereo.OneCenter
open TetraStereo.OneCenter.LocalizedTwoReferencePseudoasymmetryFixture
open FixtureOccurrences

/-- The actual molecular-frame path for the root-tree occurrence at atom 4. -/
theorem molecularFrameUnit4 :
    input.certified.molecularFrameUnit occurrence4.1 = ⟨atom0, [atom3, atom4]⟩ := by
  rfl

/-- The actual molecular-frame path for the root-tree occurrence at atom 11. -/
theorem molecularFrameUnit11 :
    input.certified.molecularFrameUnit occurrence11.1 = ⟨atom0, [atom3, atom11]⟩ := by
  rfl

/-- The actual molecular-frame path for the root-tree occurrence at atom 19. -/
theorem molecularFrameUnit19 :
    input.certified.molecularFrameUnit occurrence19.1 = ⟨atom0, [atom18, atom19]⟩ := by
  rfl

/-- The actual molecular-frame path for the root-tree occurrence at atom 26. -/
theorem molecularFrameUnit26 :
    input.certified.molecularFrameUnit occurrence26.1 = ⟨atom0, [atom18, atom26]⟩ := by
  rfl

/-- The actual molecular-frame path for the root-tree occurrence at atom 7. -/
theorem molecularFrameUnit7 :
    input.certified.molecularFrameUnit occurrence7.1 = ⟨atom0, [atom3, atom4, atom7]⟩ := by
  rfl

/-- The actual molecular-frame path for the root-tree occurrence at atom 14. -/
theorem molecularFrameUnit14 :
    input.certified.molecularFrameUnit occurrence14.1 = ⟨atom0, [atom3, atom11, atom14]⟩ := by
  rfl

/-- The actual molecular-frame path for the root-tree occurrence at atom 22. -/
theorem molecularFrameUnit22 :
    input.certified.molecularFrameUnit occurrence22.1 = ⟨atom0, [atom18, atom19, atom22]⟩ := by
  rfl

/-- The actual molecular-frame path for the root-tree occurrence at atom 29. -/
theorem molecularFrameUnit29 :
    input.certified.molecularFrameUnit occurrence29.1 = ⟨atom0, [atom18, atom26, atom29]⟩ := by
  rfl

assert_kernel_only molecularFrameUnit4
assert_kernel_only molecularFrameUnit11
assert_kernel_only molecularFrameUnit19
assert_kernel_only molecularFrameUnit26
assert_kernel_only molecularFrameUnit7
assert_kernel_only molecularFrameUnit14
assert_kernel_only molecularFrameUnit22
assert_kernel_only molecularFrameUnit29

end FixtureReaderTransfer
