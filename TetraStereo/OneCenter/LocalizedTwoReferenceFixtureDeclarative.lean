import TetraStereo.OneCenter.LocalizedTwoReferenceFixtureRootLetter
import TetraStereo.OneCenter.LocalizedActualOrderedRootDeclarativeDescriptor
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# The 33-atom fixture through the declarative eight-rule problem

Integration check of the general root theorem (`orderedReferenceState_top_descriptorJudgment`) at
the two-reference pseudoasymmetry fixture: with the accepted physical transport, the root's unique
declarative descriptor judgment is `R`, exactly one pair of root ligands reaches Rule 5 with every
earlier rule tied, and the evaluator's `r` (`LocalizedTwoReferenceFixtureRootLetter.root_letter`)
is its pseudoasymmetric classification.
-/

namespace TetraStereo.OneCenter
namespace LocalizedTwoReferenceFixtureDeclarative

open DeclarativeCIP
open CertifiedLocalizedCIPInput
open LocalizedTwoReferencePseudoasymmetryFixture
open LocalizedTwoReferenceFixturePhysicalInstance
open Rule4aTableBridge.ActualCentrePhysicalSetup

/-- **The fixture's declarative judgment.**  The unique descriptor licensed by the declarative
eight-rule problem at the root is `R`, the declarative Rule-5 pair count is one, and the
evaluator's fixed point `r` is the pseudoasymmetric classification of that judgment. -/
theorem fixture_descriptorJudgment :
    (geoProblem (input := input)).DescriptorJudgment (actualReferenceDescriptorMap input)
        setup.declUnit Descriptor.R ∧
      (∀ descriptor, (geoProblem (input := input)).DescriptorJudgment
        (actualReferenceDescriptorMap input) setup.declUnit descriptor → descriptor = .R) ∧
      setup.declarativeRule5PairCount = 1 ∧
      input.certified.orderedReferenceState (LocalizedUniversalReference.carrierFuel input)
          (ActualReaderPhysicalBranchInverse.topTarget input rootP) =
        some (classifyTetrahedralRSPseudo RS.R setup.declarativeRule5PairCount) := by
  obtain ⟨rs, hstate, hjudg, huniq⟩ :=
    setup.orderedReferenceState_top_descriptorJudgment
      FixturePhysicalTransport.pairwiseProperDistinguishable_actual_root
      FixtureRootGeometry.actualCanonicalRootCoordinates
  have hcount : setup.declarativeRule5PairCount = 1 :=
    (setup.declarativeRule5PairCount_eq_physical
      FixturePhysicalTransport.pairwiseProperDistinguishable_actual_root).trans
      FixturePhysicalTransport.physicalEnantiomorphicPairCount_actual_root_eq_one
  have hletter := LocalizedTwoReferenceFixtureRootLetter.root_letter
  have hstate' : input.certified.orderedReferenceState
      (LocalizedUniversalReference.carrierFuel input)
      (ActualReaderPhysicalBranchInverse.topTarget input rootP) =
        some (classifyTetrahedralRSPseudo rs setup.declarativeRule5PairCount) := hstate
  rw [hletter, hcount] at hstate'
  have hrs : rs = RS.R := by
    cases rs
    · rfl
    · cases Option.some.inj hstate'
  subst hrs
  exact ⟨hjudg, huniq, hcount, by rw [hletter, hcount]; rfl⟩

end LocalizedTwoReferenceFixtureDeclarative
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixtureDeclarative.fixture_descriptorJudgment
