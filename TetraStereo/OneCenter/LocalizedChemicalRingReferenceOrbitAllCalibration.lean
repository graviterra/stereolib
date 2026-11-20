import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCalibration
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-! All five detected centers of the cyclic input have nondegenerate actual coordinates.
The calibrations use the same coordinate-derived, frame-reindexed configuration as the
accepted orientation decoder. No descriptor or ranking is prescribed.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitAllCalibration

open LocalizedChemicalRingReferenceOrbitInput LocalizedChemicalRingReferenceOrbitCalibration
open LocalizedActualPhysicalBranchDecision LocalizedRecursiveAuxiliaryPhysicalDomain
open CertifiedLocalizedCIPInput CartesianPoint3

def neighborsAt (a : Fin 46) : Fin 4 → Fin 46 :=
  if a = 0 then ![28, 29, 30, 31]
  else if a = 2 then ![1, 5, 6, 7]
  else if a = 3 then ![14, 17, 18, 40]
  else if a = 4 then ![15, 16, 19, 41]
  else ![1, 27, 34, 35]

def pointsAt (a : Fin 46) : Fin 4 → CartesianPoint3 :=
  if a = 0 then ![point 30 30 30, point 31 30 30, point 30 30 31, point 30 31 30]
  else if a = 2 then ![point 0 0 0, point 1 0 0, point 0 0 1, point 0 1 0]
  else if a = 3 then ![point 10 10 10, point 11 10 10, point 10 10 11, point 10 11 10]
  else if a = 4 then ![point 20 20 20, point 21 20 20, point 20 21 20, point 20 20 21]
  else ![point 0 0 0, point 2 0 0, point 0 0 2, point 0 2 0]

theorem center_cases (c : canon.Center) :
    c.1 = (0 : Fin 46) ∨ c.1 = (2 : Fin 46) ∨ c.1 = (3 : Fin 46) ∨
      c.1 = (4 : Fin 46) ∨ c.1 = (26 : Fin 46) := by
  have member : c.1 ∈ graph.tetrahedralCenterSet := c.2
  rw [detected_inventory] at member
  simpa only [Finset.mem_insert, Finset.mem_singleton] using member

private theorem neighbor_sorted (c : canon.Center) :
    (certified.moleculeGraph.neighborFinset c.1).sort (· ≤ ·) = List.ofFn (neighborsAt c.1) := by
  have finite (a : Fin 46) (known : a = 0 ∨ a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 26) :
      graph.neighborFinset a = (List.ofFn (neighborsAt a)).toFinset := by
    ext b
    rw [graph.mem_neighborFinset]
    rcases known with rfl | rfl | rfl | rfl | rfl <;> fin_cases b <;> decide +kernel
  have ordered : (List.ofFn (neighborsAt c.1)).Pairwise (· ≤ ·) := by
    rcases center_cases c with h | h | h | h | h <;> rw [h] <;> decide +kernel
  have nodup : (List.ofFn (neighborsAt c.1)).Nodup := by
    rcases center_cases c with h | h | h | h | h <;> rw [h] <;> decide +kernel
  change (graph.neighborFinset c.1).sort (· ≤ ·) = _
  rw [finite c.1 (center_cases c)]
  exact (List.toFinset_sort (· ≤ ·) nodup).mpr ordered

theorem canonical_neighbors (c : canon.Center) (i : Fin 4) :
    canon.ligandAtomAt c i = neighborsAt c.1 i := by
  have sorted := neighbor_sorted c
  unfold canon actualCanonicalMolecule MultiCenterMolecule.ligandAtomAt
    canonicalLigandAtom canonicalNeighborList
  simp [sorted]
  fin_cases i <;> rfl

theorem all_observed (c : canon.Center) (i : Fin 4) :
    certified.spatialPointAt? (canon.ligandAtomAt c i) = some (pointsAt c.1 i) := by
  rw [canonical_neighbors]
  rcases center_cases c with h | h | h | h | h <;> rw [h] <;> fin_cases i <;> rfl

theorem all_nonzero (c : canon.Center) :
    orientedVolume (pointsAt c.1 0) (pointsAt c.1 1) (pointsAt c.1 2) (pointsAt c.1 3) ≠ 0 := by
  rcases center_cases c with h | h | h | h | h <;> rw [h] <;> decide +kernel

theorem canonical_all_calibrated (c : canon.Center) :
    ActualPhysicalCalibratedCoordinates certified canon (coordinateCfg certified) c :=
  coordinateCfg_calibrated certified c (pointsAt c.1) (all_observed c) (all_nonzero c)

noncomputable section

private theorem calibration_reindexed (c : canon.Center) :
    ActualPhysicalCalibratedCoordinates certified (canon.reindexFrames frameChange)
      (canon.reindexConfiguration frameChange (coordinateCfg certified)) c := by
  obtain ⟨P, seen, nonzero, sign⟩ := canonical_all_calibrated c
  refine ⟨fun i => P (frameChange c i), ?_, ?_, ?_⟩
  · intro i
    rw [MultiCenterMolecule.reindexFrames_ligandAtomAt]
    exact seen _
  · exact cartesianOrientedVolume_perm_ne_zero P (frameChange c) nonzero
  · have vec : ∀ k : Fin 4,
        RationalTetrahedralPermutation.pointVector (P 0) (P 1) (P 2) (P 3) k = P k := by
      intro k
      fin_cases k <;> rfl
    have volume : RationalTetrahedralPermutation.permutedOrientedVolume
        (P 0) (P 1) (P 2) (P 3) (frameChange c) =
        orientedVolume (P (frameChange c 0)) (P (frameChange c 1))
          (P (frameChange c 2)) (P (frameChange c 3)) := by
      simp only [RationalTetrahedralPermutation.permutedOrientedVolume, vec]
    rw [← volume, rationalVolumeSign_permutedOrientedVolume, sign,
      MultiCenterMolecule.configurationSign_reindexConfiguration]

/-- Every actual detected center is calibrated, with the accepted single configuration. -/
theorem all_calibrated (c : physical.Center) :
    ActualPhysicalCalibratedCoordinates certified physical cfg c := by
  let c' : canon.Center := ⟨c.1, c.2⟩
  have transferred : Eq.mp (congrArg MultiCenterMolecule.Center frameChange_spec) c' = c := by
    have center_val {m n : MultiCenterMolecule (Fin 46)} (h : m = n) (d : m.Center) :
        (Eq.mp (congrArg MultiCenterMolecule.Center h) d).1 = d.1 := by cases h; rfl
    exact Subtype.ext (center_val frameChange_spec c')
  have transport {m n : MultiCenterMolecule (Fin 46)} (h : m = n)
      (configuration : m.Configuration) (d : m.Center)
      (hcal : ActualPhysicalCalibratedCoordinates certified m configuration d) :
      ActualPhysicalCalibratedCoordinates certified n
        (Eq.mp (congrArg MultiCenterMolecule.Configuration h) configuration)
        (Eq.mp (congrArg MultiCenterMolecule.Center h) d) := by
    cases h
    exact hcal
  simpa only [cfg, transferred] using transport frameChange_spec
    (canon.reindexConfiguration frameChange (coordinateCfg certified)) c'
    (calibration_reindexed c')

def otherCurrent : physical.Center := ⟨(26 : Fin 46), by
  change (26 : Fin 46) ∈ graph.tetrahedralCenterSet
  rw [detected_inventory]
  decide⟩

theorem other_calibrated : ActualPhysicalCalibratedCoordinates certified physical cfg otherCurrent :=
  all_calibrated otherCurrent

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitAllCalibration

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitAllCalibration.center_cases
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitAllCalibration.canonical_neighbors
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitAllCalibration.all_observed
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitAllCalibration.all_nonzero
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitAllCalibration.canonical_all_calibrated
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitAllCalibration.all_calibrated
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitAllCalibration.other_calibrated
