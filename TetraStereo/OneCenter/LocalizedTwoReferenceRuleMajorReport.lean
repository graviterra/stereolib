import TetraStereo.OneCenter.LocalizedRuleMajorReportCorrectness
import TetraStereo.OneCenter.LocalizedTwoReferenceFixtureWholeInventory
import TetraStereo.Examples.TwoReferenceSupport.FixtureInventory
import TetraStereo.Examples.TwoReferenceSupport.FixtureCalibration
import TetraStereo.Examples.TwoReferenceSupport.FixtureRootGeometry
import TetraStereo.Examples.TwoReferenceSupport.FixtureGraphDomain
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-!
# Independent rule-major report on the actual two-reference fixture

This instantiates the report correctness theorem using source-coordinate readbacks for the
fixture's nine detected centers.  The center inventory and the eight canonical coordinate
calibrations are the frozen finite facts; no whole-carrier state is evaluated here.
-/

namespace TetraStereo.OneCenter
namespace LocalizedTwoReferenceRuleMajorReport

open CertifiedLocalizedCIPInput
open DeclarativeCIP
open LocalizedTwoReferencePseudoasymmetryFixture
open LocalizedTwoReferenceFixtureWholeInventory
open FixtureInventory
open FixtureCalibration
open FixtureRootGeometry

noncomputable section
open scoped Classical

private abbrev fixtureInput := input

private theorem canonicalCoordinateData
    (center : fixtureInput.certified.TetrahedralCenter) :
    ∃ pointAt : Fin 4 → CartesianPoint3,
      (∀ i, fixtureInput.certified.spatialPointAt?
        (fixtureInput.certified.canonicalLigandAtom center i) = some (pointAt i)) ∧
      CartesianPoint3.orientedVolume (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3) ≠ 0 := by
  have hmem : center.1 ∈ fixtureInput.certified.tetrahedralCenterSet := center.2
  change center.1 ∈ FixtureInventory.Input.tetrahedralCenterSet at hmem
  rw [FixtureInventory.detectedCenterSet] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h0 | h4 | h7 | h11 | h14 | h19 | h22 | h26 | h29
  · have heq : center = FixtureRootGeometry.rootCenter := Subtype.ext h0
    subst center
    exact FixtureRootGeometry.actualCanonicalRootCoordinates
  · have heq : center = FixtureInventory.center4 := Subtype.ext h4
    subst center
    exact ⟨FixtureCalibration.canonicalPoint4,
      FixtureCalibration.canonicalObserved4, by
        rw [FixtureCalibration.canonicalVolume4]
        norm_num⟩
  · have heq : center = FixtureInventory.center7 := Subtype.ext h7
    subst center
    exact ⟨FixtureCalibration.canonicalPoint7,
      FixtureCalibration.canonicalObserved7, by
        rw [FixtureCalibration.canonicalVolume7]
        norm_num⟩
  · have heq : center = FixtureInventory.center11 := Subtype.ext h11
    subst center
    exact ⟨FixtureCalibration.canonicalPoint11,
      FixtureCalibration.canonicalObserved11, by
        rw [FixtureCalibration.canonicalVolume11]
        norm_num⟩
  · have heq : center = FixtureInventory.center14 := Subtype.ext h14
    subst center
    exact ⟨FixtureCalibration.canonicalPoint14,
      FixtureCalibration.canonicalObserved14, by
        rw [FixtureCalibration.canonicalVolume14]
        norm_num⟩
  · have heq : center = FixtureInventory.center19 := Subtype.ext h19
    subst center
    exact ⟨FixtureCalibration.canonicalPoint19,
      FixtureCalibration.canonicalObserved19, by
        rw [FixtureCalibration.canonicalVolume19]
        norm_num⟩
  · have heq : center = FixtureInventory.center22 := Subtype.ext h22
    subst center
    exact ⟨FixtureCalibration.canonicalPoint22,
      FixtureCalibration.canonicalObserved22, by
        rw [FixtureCalibration.canonicalVolume22]
        norm_num⟩
  · have heq : center = FixtureInventory.center26 := Subtype.ext h26
    subst center
    exact ⟨FixtureCalibration.canonicalPoint26,
      FixtureCalibration.canonicalObserved26, by
        rw [FixtureCalibration.canonicalVolume26]
        norm_num⟩
  · have heq : center = FixtureInventory.center29 := Subtype.ext h29
    subst center
    exact ⟨FixtureCalibration.canonicalPoint29,
      FixtureCalibration.canonicalObserved29, by
        rw [FixtureCalibration.canonicalVolume29]
        norm_num⟩

private def canonicalPoints
    (center : fixtureInput.certified.TetrahedralCenter) : Fin 4 → CartesianPoint3 :=
  Classical.choose (canonicalCoordinateData center)

private theorem canonicalPoints_available
    (center : fixtureInput.certified.TetrahedralCenter) (i : Fin 4) :
    fixtureInput.certified.spatialPointAt?
      (fixtureInput.certified.canonicalLigandAtom center i) = some (canonicalPoints center i) :=
  (Classical.choose_spec (canonicalCoordinateData center)).1 i

private theorem canonicalPoints_nonzero
    (center : fixtureInput.certified.TetrahedralCenter) :
    CartesianPoint3.orientedVolume (canonicalPoints center 0) (canonicalPoints center 1)
      (canonicalPoints center 2) (canonicalPoints center 3) ≠ 0 :=
  (Classical.choose_spec (canonicalCoordinateData center)).2

/-- The actual new rule-major report has the exact nine-center detector inventory, with no
duplicates, and every emitted optional result is equivalent to the independent complete-key
judgment computed from that center's own generated auxiliary map. -/
theorem actual_report_nine_centers_and_sound :
    (LocalizedRuleMajorReference.analyze fixtureInput).map Prod.fst =
        [0, 4, 7, 11, 14, 19, 22, 26, 29] ∧
      ((LocalizedRuleMajorReference.analyze fixtureInput).map Prod.fst).Nodup ∧
      (LocalizedRuleMajorReference.analyze fixtureInput).length = 9 ∧
      ∀ atom outcome,
        (atom, outcome) ∈ LocalizedRuleMajorReference.analyze fixtureInput ↔
          ∃ center : fixtureInput.certified.TetrahedralCenter,
            center.1.1 = atom ∧
            DeclarativeCIP.CompleteRootOutcome
              (LocalizedRuleMajorReference.generatedFrameComparison fixtureInput center
                FixtureGraphDomain.simpleBonded FixtureGraphDomain.acyclic).data.fullKey
              (canonicalPoints center) outcome := by
  obtain ⟨hcenters, hnodup, hlength, hsound⟩ :=
    LocalizedRuleMajorReference.analyze_complete_root_outcomes fixtureInput
      FixtureGraphDomain.simpleBonded FixtureGraphDomain.acyclic canonicalPoints
      canonicalPoints_available canonicalPoints_nonzero
  have hindices :
      fixtureInput.certified.canonicalTetrahedralCenters.map (fun center => center.1.1) =
        [0, 4, 7, 11, 14, 19, 22, 26, 29] := by
    rw [LocalizedTwoReferenceFixtureWholeInventory.canonicalCenters]
    rfl
  have hcard : fixtureInput.certified.tetrahedralCenterSet.card = 9 := by
    change FixtureInventory.Input.tetrahedralCenterSet.card = 9
    rw [FixtureInventory.detectedCenterSet]
    decide +kernel
  exact ⟨hcenters.trans hindices, hnodup, hlength.trans hcard, hsound⟩

end
end LocalizedTwoReferenceRuleMajorReport
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceRuleMajorReport.actual_report_nine_centers_and_sound
