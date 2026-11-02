import TetraStereo.OneCenter.LocalizedContextGeneratedDescriptor
import TetraStereo.OneCenter.LocalizedTwoReferenceFixturePhysicalInstance
import TetraStereo.Examples.TwoReferenceSupport.FixtureReaderTransfer
import TetraStereo.Examples.TwoReferenceSupport.FixtureGraphDomain
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Apply the arbitrary detected-carrier occurrence contextual outcome to the accepted 33-atom
fixture, including an explicit non-root occurrence. This uses the revised generated reference
state; no old ordered-map label is transferred. -/

namespace TetraStereo.OneCenter.LocalizedTwoReferenceFixtureContextualCorrectness

open DeclarativeCIP
open LocalizedTwoReferencePseudoasymmetryFixture
open LocalizedTwoReferenceFixturePhysicalInstance
open FixtureOccurrences

abbrev fixtureInput := LocalizedTwoReferencePseudoasymmetryFixture.input

/-- Every detected carrier occurrence in the accepted fixture satisfies the generated
contextual outcome theorem, instantiated with the fixture's actual finite simple acyclic graph. -/
theorem every_detected_occurrence_contextual_outcome
    (target : LocalizedRuleMajorReference.Occurrence fixtureInput)
    (unit : DetectedOccurrence fixtureInput.certified.moleculeGraph)
    (targetUnit : fixtureInput.certified.molecularFrameUnit target.1 = unit.1) :
    let frames := LocalizedRuleMajorReference.generatedContextFrameCompilation fixtureInput
      FixtureGraphDomain.simpleBonded FixtureGraphDomain.acyclic target unit targetUnit
    ContextualOutcomeAt fixtureInput.certified.moleculeGraph
      (LocalizedRuleMajorReference.descriptorMap fixtureInput) unit
      frames.graphs frames.W frames.D frames.coordinates
      (LocalizedRuleMajorReference.referenceState fixtureInput target) := by
  exact LocalizedRuleMajorReference.every_detected_auxiliary_occurrence_contextual_outcome
    fixtureInput FixtureGraphDomain.simpleBonded FixtureGraphDomain.acyclic
    target unit targetUnit

/-- Occurrence 4 is a concrete non-root application of the all-target result. Its detected unit
has the nonempty molecular path `[atom3, atom4]`; the outcome concerns the revised rule-major
reference state, not the fixture's prior ordered-reference labels. -/
theorem occurrence4_nonroot_contextual_outcome :
    (fixtureInput.certified.molecularFrameUnit occurrence4.1).path ≠ [] ∧
      let frames := LocalizedRuleMajorReference.generatedContextFrameCompilation fixtureInput
        FixtureGraphDomain.simpleBonded FixtureGraphDomain.acyclic occurrence4 unit4
        FixtureReaderTransfer.molecularFrameUnit4
      ContextualOutcomeAt fixtureInput.certified.moleculeGraph
        (LocalizedRuleMajorReference.descriptorMap fixtureInput) unit4
        frames.graphs frames.W frames.D frames.coordinates
        (LocalizedRuleMajorReference.referenceState fixtureInput occurrence4) := by
  refine ⟨?_, every_detected_occurrence_contextual_outcome occurrence4 unit4
    FixtureReaderTransfer.molecularFrameUnit4⟩
  rw [FixtureReaderTransfer.molecularFrameUnit4]
  simp

end TetraStereo.OneCenter.LocalizedTwoReferenceFixtureContextualCorrectness

assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixtureContextualCorrectness.every_detected_occurrence_contextual_outcome
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixtureContextualCorrectness.occurrence4_nonroot_contextual_outcome
