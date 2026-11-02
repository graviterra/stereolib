import TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureWholeReport
import TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness
import TetraStereo.OneCenter.LocalizedRuleMajorReportCorrectness
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 8192

/-!
# Physical meaning of the cyclic fixture report

At every actual detected center, the shared descriptor in the production report has the exact
physical case criterion and the raw letter of an independently sorted retained-key order agrees
with the absolute geometric orientation.
-/

namespace TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixturePhysicalReport

noncomputable section

open TetraStereo.OneCenter
open TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixture
open TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels
open TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureDomain
open TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureRootSymmetry
open TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureEvaluation
open TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureWholeReport
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCorrectness
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalDomain
open TetraStereo.OneCenter.AcyclicCutBranchAutomorphism
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport
open TetraStereo.OneCenter.LocalizedCyclicRootIndependentJudgment
open TetraStereo.OneCenter.LocalizedCyclicRootPhysicalSetup
open TetraStereo.OneCenter.LocalizedRuleMajorReference

private theorem fixtureSimpleBonded : symmetricCertified.moleculeGraph.SimpleBonded := by
  change graph.SimpleBonded
  exact simple_bonded

private theorem fixtureConstantCharge :
    ConstantFormalCharge symmetricCertified.moleculeGraph := by
  refine ⟨0, ?_⟩
  intro atom
  fin_cases atom <;> decide

private theorem report_member_returns_at_center
    (center : symmetricCertified.TetrahedralCenter)
    (descriptor : LocalizedAuxiliaryLabel)
    (member : (center.1.val, some descriptor) ∈ analyze fixtureReference) :
    referenceState fixtureReference (finalTarget fixtureReference center) = some descriptor := by
  have extracted := (mem_analyze_iff fixtureReference center.1.val (some descriptor)).mp member
  obtain ⟨reportedCenter, atomEq, returned⟩ := extracted
  have centersEq : reportedCenter = center := by
    apply Subtype.ext
    apply Fin.ext
    exact atomEq
  simpa [finalTarget, centersEq] using returned

/-- Every actual detected-center entry in the production report has the physical case and
orientation specified by its independent retained-key reading. The descriptor is the common actual
report witness from `every_detected_root_reported_lowercase_shared`. -/
theorem every_detected_report_entry_has_physical_reading :
    ∀ center : symmetricCertified.TetrahedralCenter,
      ∃ descriptor : LocalizedAuxiliaryLabel,
        (center.1.val, some descriptor) ∈ analyze fixtureReference ∧
        (descriptor.IsLowercase ↔
          physicalEnantiomorphicPairCount symmetricCertified.detectedMultiCenterMolecule
            detectedCfg center = 1) ∧
        ∃ (τ : Equiv.Perm (Fin 4)) (raw : RS),
          [τ 0, τ 1, τ 2, τ 3].Pairwise (fun left right =>
            canonicalCutKeys fixtureReference fixtureSimpleBonded center right <
              canonicalCutKeys fixtureReference fixtureSimpleBonded center left) ∧
          (raw = RS.R ↔
            permHandedness
                ((finalRootFrames fixtureReference fixtureSimpleBonded center).detectedLigandPermutation * τ) *
              symmetricCertified.detectedMultiCenterMolecule.configurationSign detectedCfg center = -1) ∧
          descriptor = classifyTetrahedralRSPseudo raw
            (physicalEnantiomorphicPairCount symmetricCertified.detectedMultiCenterMolecule
              detectedCfg center) := by
  obtain ⟨descriptor, _lowercase, allCenters⟩ := every_detected_root_reported_lowercase_shared
  intro center
  have member := allCenters center
  have returned := report_member_returns_at_center center descriptor member
  have physical := finalRoot_physical_letter_of_pairs
    (input := fixtureReference) (singleBonded := fixtureSimpleBonded) (center := center)
    fixtureConstantCharge detectedCfg (detectedDomainAtEveryRoot center)
    (detectedConstitutionalPairsEnantiomorphic center) (detectedCoordinates_at center) returned
  exact ⟨descriptor, physical.1, physical.2.1, physical.2.2⟩

end
end TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixturePhysicalReport

assert_kernel_only
  TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixturePhysicalReport.every_detected_report_entry_has_physical_reading
