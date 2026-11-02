import TetraStereo.OneCenter.LocalizedOrderedPhysicalMoleculeDomain
import TetraStereo.OneCenter.LocalizedOrderedPhysicalMoleculeCorrectness
import TetraStereo.OneCenter.LocalizedTwoReferenceFixtureWholeMolecule
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The general physical domain is inhabited by the accepted 33-atom molecule, whose
distinguished root has a genuine two-reference arm and whose actual report has a lowercase root.
No domain clause is discharged by assuming an evaluator result. -/

namespace TetraStereo.OneCenter.LocalizedTwoReferenceGeneralDomain
open CertifiedLocalizedCIPInput
open LocalizedTwoReferencePseudoasymmetryFixture
open LocalizedTwoReferenceFixturePhysicalInstance

theorem fixture_domain : OrderedTreePhysicalDomain input cfg rootP where
  singleBonded := FixtureGraphDomain.simpleBonded
  acyclic := FixtureGraphDomain.acyclic
  constantCharge := FixtureGraphDomain.constantFormalCharge
  noDouble := FixtureGraphDomain.noLocalizedDoubleBondRecords
  centers := physicalDomain
  rootDistinct := FixturePhysicalTransport.pairwiseProperDistinguishable_actual_root
  rootCoordinates := FixtureRootGeometry.actualCanonicalRootCoordinates

theorem fixture_two_references :
    (setup.slotKey 2).prior.references = [RS.R, RS.S] :=
  LocalizedTwoReferenceFixtureRootLetter.references_N3

theorem fixture_complete_report :
    LocalizedOrderedReference.analyze input =
      LocalizedTwoReferenceFixtureWholeMolecule.expectedReport :=
  LocalizedTwoReferenceFixtureWholeMolecule.exact_report

/-- The nine-label concrete report instantiates the general own-map theorem at every detected
centre, including the two-reference pseudoasymmetric root. -/
theorem fixture_independent_report (atom : Nat)
    (outcome : Option LocalizedAuxiliaryLabel) :
    (atom, outcome) ∈ LocalizedTwoReferenceFixtureWholeMolecule.expectedReport ↔
      ∃ center : input.certified.TetrahedralCenter, center.1.1 = atom ∧
        DeclarativeCIP.FinalTetrahedralOutcome
          (Rule4aTableBridge.ActualCentrePhysicalSetup.geoProblem (input := input))
          (actualOrderedReferenceDescriptorMap input) (input.certified.topUnit center) outcome := by
  rw [← fixture_complete_report]
  exact fixture_domain.mem_report_iff atom outcome

end TetraStereo.OneCenter.LocalizedTwoReferenceGeneralDomain

assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceGeneralDomain.fixture_domain
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceGeneralDomain.fixture_two_references
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceGeneralDomain.fixture_complete_report
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceGeneralDomain.fixture_independent_report
