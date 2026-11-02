import TetraStereo.OneCenter.LocalizedTwoReferenceFixturePhysicalInstance
import TetraStereo.OneCenter.LocalizedOrderedFirstSphereDescriptor
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Ordered labels at the actual final occurrences of the eight rigid centres

Each label is computed at that centre's own actual `topTarget`. The proof obtains an actual frame
from the accepted coordinate calibration and fixes every pair comparison by first-sphere atomic
number for the ordered evaluator's own state view. No physical domain rooted at each centre is
assumed.
-/

namespace TetraStereo.OneCenter
namespace LocalizedTwoReferenceFixtureFinalCenters

open CertifiedLocalizedCIPInput
open LocalizedUniversalReference
open LocalizedTwoReferencePseudoasymmetryFixture
open LocalizedTwoReferenceFixturePhysicalInstance
open FixtureOccurrences
open FixtureInventory
open FixtureCalibration

noncomputable section
open scoped Classical

private abbrev fixtureInput := LocalizedTwoReferencePseudoasymmetryFixture.input
private abbrev fixtureFuel := LocalizedUniversalReference.carrierFuel fixtureInput

private theorem canonicalPointReads (center : fixtureInput.certified.TetrahedralCenter)
    (pointsAt : Fin 4 → CartesianPoint3)
    (observed : ∀ i, fixtureInput.certified.spatialPointAt?
      (fixtureInput.certified.canonicalLigandAtom center i) = some (pointsAt i)) :
    ∀ order : List (Fin 4),
      order.mapM (fun i => fixtureInput.certified.spatialPointAt?
        (fixtureInput.certified.canonicalLigandAtom center i)) = some (order.map pointsAt) := by
  intro order
  induction order with
  | nil => rfl
  | cons i rest ih =>
      simp only [List.mapM_cons, observed i]
      rw [ih]
      rfl

/-- One actual final-centre assignment from canonical source geometry and a strictly descending
first-sphere priority list. -/
theorem orderedTop_eq_chiral_of_canonicalPriority
    (center : fixtureInput.certified.TetrahedralCenter)
    (calibrated : ActualPhysicalGeneralRigidCalibratedCenter fixtureInput.certified
      fixtureInput.certified.detectedMultiCenterMolecule FixtureCalibration.actualConfiguration
      ⟨center.1, center.2⟩)
    (pointsAt : Fin 4 → CartesianPoint3)
    (observed : ∀ i, fixtureInput.certified.spatialPointAt?
      (fixtureInput.certified.canonicalLigandAtom center i) = some (pointsAt i))
    (priority : Fin 4 → Nat)
    (atomZ : ∀ i, fixtureInput.certified.moleculeGraph.atomZ
      (fixtureInput.certified.canonicalLigandAtom center i) = priority i)
    (priorityInjective : Function.Injective priority)
    (order : List (Fin 4))
    (orderPerm : order.Perm (List.finRange 4))
    (orderSorted : order.Pairwise (fun a b => priority b < priority a))
    (raw : RS)
    (geometry : RationalTetrahedralDescriptor (order.map pointsAt) raw) :
    fixtureInput.certified.orderedReferenceState fixtureFuel
      (ActualReaderPhysicalBranchInverse.topTarget fixtureInput
        (⟨center.1, center.2⟩ : fixtureInput.certified.detectedMultiCenterMolecule.Center)) =
        some (.chiral raw) := by
  let detectedCenter : fixtureInput.certified.detectedMultiCenterMolecule.Center :=
    ⟨center.1, center.2⟩
  let target := ActualReaderPhysicalBranchInverse.topTarget fixtureInput detectedCenter
  have targetCurrent : target.1.node.current? = some center.1 := by
    exact ActualReaderPhysicalBranchInverse.topTarget_current fixtureInput detectedCenter
  have calibratedCanonical : ActualGeneralRigidCalibratedCenter fixtureInput.certified
      (fixtureInput.certified.canonicalReindexConfiguration
        FixtureCalibration.actualConfiguration) center := by
    simpa [detectedCenter] using
      actualGeneralRigidCalibratedCenter_of_physicalGeneralRigidCalibratedCenter
        fixtureInput.certified FixtureCalibration.actualConfiguration detectedCenter calibrated
  obtain ⟨frame, alpha, _framePoints, frameComputed, ligandLink, frameSpatial,
      _observedFramePoints, _frameCalibration⟩ :=
    exists_frameAndCalibration_of_generalRigidCenter fixtureInput
      FixtureGraphDomain.simpleBonded FixtureGraphDomain.acyclic
      (fixtureInput.certified.canonicalReindexConfiguration
        FixtureCalibration.actualConfiguration)
      center target targetCurrent calibratedCanonical
  have derived : fixtureInput.certified.DeclarativeLocalizedOccurrenceFourLigandFrame target frame :=
    fixtureInput.certified.localizedOccurrenceFourLigandFrame?_sound target frame frameComputed
  have centerReal : fixtureInput.certified.RealTetrahedralCenterNode target.1.node center :=
    ⟨fixtureInput.certified.carrierOccurrence_provenance_real
      FixtureGraphDomain.simpleBonded FixtureGraphDomain.acyclic target, targetCurrent⟩
  have framePointEq : ∀ i, _framePoints i = pointsAt i := by
    intro i
    exact Option.some.inj ((_observedFramePoints i).symm.trans (observed i))
  have spatialCorrespondence : ∀ i,
      fixtureInput.certified.localizedRerootCursorSpatialPoint? (frame.cursorAt i) =
        fixtureInput.certified.spatialPointAt?
          (fixtureInput.certified.canonicalLigandAtom center (alpha i)) := by
    intro i
    rw [frameSpatial i, framePointEq (alpha i)]
    exact (observed (alpha i)).symm
  let slotZ : Fin 4 → Nat := fun i => priority (alpha i)
  have slotZ_eq : ∀ i, fixtureInput.certified.moleculeGraph.atomZ
      (cursorAtom FixtureGraphDomain.simpleBonded FixtureGraphDomain.acyclic
        (frame.cursorAt i)) = slotZ i := by
    intro i
    rw [cursorAtom_eq_of_observed FixtureGraphDomain.simpleBonded
      FixtureGraphDomain.acyclic (ligandLink i), atomZ (alpha i)]
  have priorityOrder : ∀ ℓ m, ℓ ≠ m →
      fixtureInput.certified.compareLocalizedOccurrenceThroughRule5OrderedAt? target
        (fixtureInput.certified.localizedDependencyView
          (fixtureInput.certified.orderedReferenceState fixtureFuel) target)
        frame (alpha.symm ℓ) (alpha.symm m) =
          strictRankComparison slotZ (alpha.symm ℓ) (alpha.symm m) := by
    intro ℓ m hne
    have different : slotZ (alpha.symm ℓ) ≠ slotZ (alpha.symm m) := by
      dsimp [slotZ]
      intro h
      apply hne
      exact priorityInjective (by simpa using h)
    exact orderedComparison_eq_strictRank_of_slotZ fixtureInput target
      (fixtureInput.certified.localizedDependencyView
        (fixtureInput.certified.orderedReferenceState fixtureFuel) target)
      frame derived FixtureGraphDomain.simpleBonded FixtureGraphDomain.acyclic
      slotZ slotZ_eq different
  have geometryRaw : descriptorOfPriorityOrderedPoints? (order.map pointsAt) = some raw :=
    (descriptorOfPriorityOrderedPoints?_eq_some_iff (order.map pointsAt) raw).mpr geometry
  exact orderedReferenceState_eq_chiral_of_strictPriorityCallback fixtureInput target frame
    frameComputed center centerReal alpha priority priorityInjective priorityOrder
    order orderPerm orderSorted (order.map pointsAt) spatialCorrespondence
    (canonicalPointReads center pointsAt observed order)
    raw geometryRaw

private theorem zA_injective : Function.Injective zA := by
  intro i j hij
  revert i j
  decide +kernel

private theorem zB_injective : Function.Injective zB := by
  intro i j hij
  revert i j
  decide +kernel

private theorem orderA_perm :
    ([2, 0, 3, 1] : List (Fin 4)).Perm (List.finRange 4) := by decide

private theorem orderB_perm :
    ([3, 2, 0, 1] : List (Fin 4)).Perm (List.finRange 4) := by decide

private theorem orderA_sorted : ([2, 0, 3, 1] : List (Fin 4)).Pairwise
    (fun a b => zA b < zA a) := by decide

private theorem orderB_sorted : ([3, 2, 0, 1] : List (Fin 4)).Pairwise
    (fun a b => zB b < zB a) := by decide

theorem orderedTop4 :
    fixtureInput.certified.orderedReferenceState fixtureFuel
      (ActualReaderPhysicalBranchInverse.topTarget fixtureInput
        (⟨FixtureInventory.center4.1, FixtureInventory.center4.2⟩ : fixtureInput.certified.detectedMultiCenterMolecule.Center)) =
        some (.chiral RS.R) := by
  exact orderedTop_eq_chiral_of_canonicalPriority FixtureInventory.center4
    actualCalibration4 canonicalPoint4 canonicalObserved4 zA atomZ4 zA_injective
    [2, 0, 3, 1] orderA_perm orderA_sorted RS.R geometry4

theorem orderedTop7 :
    fixtureInput.certified.orderedReferenceState fixtureFuel
      (ActualReaderPhysicalBranchInverse.topTarget fixtureInput
        (⟨FixtureInventory.center7.1, FixtureInventory.center7.2⟩ : fixtureInput.certified.detectedMultiCenterMolecule.Center)) =
        some (.chiral RS.R) := by
  exact orderedTop_eq_chiral_of_canonicalPriority FixtureInventory.center7
    actualCalibration7 canonicalPoint7 canonicalObserved7 zB atomZ7 zB_injective
    [3, 2, 0, 1] orderB_perm orderB_sorted RS.R geometry7

theorem orderedTop11 :
    fixtureInput.certified.orderedReferenceState fixtureFuel
      (ActualReaderPhysicalBranchInverse.topTarget fixtureInput
        (⟨FixtureInventory.center11.1, FixtureInventory.center11.2⟩ : fixtureInput.certified.detectedMultiCenterMolecule.Center)) =
        some (.chiral RS.S) := by
  exact orderedTop_eq_chiral_of_canonicalPriority FixtureInventory.center11
    actualCalibration11 canonicalPoint11 canonicalObserved11 zA atomZ11 zA_injective
    [2, 0, 3, 1] orderA_perm orderA_sorted RS.S geometry11

theorem orderedTop14 :
    fixtureInput.certified.orderedReferenceState fixtureFuel
      (ActualReaderPhysicalBranchInverse.topTarget fixtureInput
        (⟨FixtureInventory.center14.1, FixtureInventory.center14.2⟩ : fixtureInput.certified.detectedMultiCenterMolecule.Center)) =
        some (.chiral RS.R) := by
  exact orderedTop_eq_chiral_of_canonicalPriority FixtureInventory.center14
    actualCalibration14 canonicalPoint14 canonicalObserved14 zB atomZ14 zB_injective
    [3, 2, 0, 1] orderB_perm orderB_sorted RS.R geometry14

theorem orderedTop19 :
    fixtureInput.certified.orderedReferenceState fixtureFuel
      (ActualReaderPhysicalBranchInverse.topTarget fixtureInput
        (⟨FixtureInventory.center19.1, FixtureInventory.center19.2⟩ : fixtureInput.certified.detectedMultiCenterMolecule.Center)) =
        some (.chiral RS.S) := by
  exact orderedTop_eq_chiral_of_canonicalPriority FixtureInventory.center19
    actualCalibration19 canonicalPoint19 canonicalObserved19 zA atomZ19 zA_injective
    [2, 0, 3, 1] orderA_perm orderA_sorted RS.S geometry19

theorem orderedTop22 :
    fixtureInput.certified.orderedReferenceState fixtureFuel
      (ActualReaderPhysicalBranchInverse.topTarget fixtureInput
        (⟨FixtureInventory.center22.1, FixtureInventory.center22.2⟩ : fixtureInput.certified.detectedMultiCenterMolecule.Center)) =
        some (.chiral RS.S) := by
  exact orderedTop_eq_chiral_of_canonicalPriority FixtureInventory.center22
    actualCalibration22 canonicalPoint22 canonicalObserved22 zB atomZ22 zB_injective
    [3, 2, 0, 1] orderB_perm orderB_sorted RS.S geometry22

theorem orderedTop26 :
    fixtureInput.certified.orderedReferenceState fixtureFuel
      (ActualReaderPhysicalBranchInverse.topTarget fixtureInput
        (⟨FixtureInventory.center26.1, FixtureInventory.center26.2⟩ : fixtureInput.certified.detectedMultiCenterMolecule.Center)) =
        some (.chiral RS.R) := by
  exact orderedTop_eq_chiral_of_canonicalPriority FixtureInventory.center26
    actualCalibration26 canonicalPoint26 canonicalObserved26 zA atomZ26 zA_injective
    [2, 0, 3, 1] orderA_perm orderA_sorted RS.R geometry26

theorem orderedTop29 :
    fixtureInput.certified.orderedReferenceState fixtureFuel
      (ActualReaderPhysicalBranchInverse.topTarget fixtureInput
        (⟨FixtureInventory.center29.1, FixtureInventory.center29.2⟩ : fixtureInput.certified.detectedMultiCenterMolecule.Center)) =
        some (.chiral RS.S) := by
  exact orderedTop_eq_chiral_of_canonicalPriority FixtureInventory.center29
    actualCalibration29 canonicalPoint29 canonicalObserved29 zB atomZ29 zB_injective
    [3, 2, 0, 1] orderB_perm orderB_sorted RS.S geometry29

end
end LocalizedTwoReferenceFixtureFinalCenters
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixtureFinalCenters.orderedTop_eq_chiral_of_canonicalPriority
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixtureFinalCenters.orderedTop4
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixtureFinalCenters.orderedTop7
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixtureFinalCenters.orderedTop11
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixtureFinalCenters.orderedTop14
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixtureFinalCenters.orderedTop19
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixtureFinalCenters.orderedTop22
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixtureFinalCenters.orderedTop26
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixtureFinalCenters.orderedTop29
