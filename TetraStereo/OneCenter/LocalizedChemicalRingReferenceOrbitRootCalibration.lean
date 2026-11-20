import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitKeySeparation
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The root geometry of the 46-atom cyclic input calibrates the same physical
configuration used to decode its generated observations. No descriptor is prescribed.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitRootCalibration

open LocalizedChemicalRingReferenceOrbitInput LocalizedChemicalRingReferenceOrbitCalibration
open LocalizedChemicalRingReferenceOrbitKeySeparation LocalizedActualPhysicalBranchDecision
open LocalizedRecursiveAuxiliaryPhysicalDomain CertifiedLocalizedCIPInput CartesianPoint3

def canonicalRoot : canon.Center := ⟨(0 : Fin 46), by
  change (0 : Fin 46) ∈ graph.tetrahedralCenterSet
  rw [detected_inventory]
  decide⟩

def rootPoints : Fin 4 → CartesianPoint3 :=
  ![point 30 30 30, point 31 30 30, point 30 30 31, point 30 31 30]

theorem canonical_root_ligands (i : Fin 4) :
    canon.ligandAtomAt canonicalRoot i = (![28, 29, 30, 31] : Fin 4 → Fin 46) i := by
  have neighbors : graph.neighborFinset 0 = ([28, 29, 30, 31] : List (Fin 46)).toFinset := by
    ext a
    rw [graph.mem_neighborFinset]
    fin_cases a <;> decide +kernel
  have sorted : (graph.neighborFinset 0).sort (· ≤ ·) = [28, 29, 30, 31] := by
    rw [neighbors]
    exact (List.toFinset_sort (· ≤ ·) (by decide)).mpr (by decide)
  have ordered : canon.ligandAtomAt canonicalRoot i =
      ([28, 29, 30, 31] : List (Fin 46)).get i := by
    have sortedRoot : (certified.moleculeGraph.neighborFinset canonicalRoot.1).sort (· ≤ ·) =
        ([28, 29, 30, 31] : List (Fin 46)) := sorted
    unfold canon actualCanonicalMolecule MultiCenterMolecule.ligandAtomAt
      canonicalLigandAtom canonicalNeighborList
    simp [sortedRoot]
    rfl
  fin_cases i <;> simpa using ordered

theorem root_observed (i : Fin 4) :
    certified.spatialPointAt? (canon.ligandAtomAt canonicalRoot i) = some (rootPoints i) := by
  rw [canonical_root_ligands]
  fin_cases i <;> rfl

theorem canonical_root_calibrated :
    ActualPhysicalCalibratedCoordinates certified canon (coordinateCfg certified) canonicalRoot :=
  coordinateCfg_calibrated certified canonicalRoot rootPoints root_observed (by decide +kernel)

noncomputable section

private theorem root_transfer :
    Eq.mp (congrArg MultiCenterMolecule.Center frameChange_spec) canonicalRoot = rootCenter := by
  have center_val {m n : MultiCenterMolecule (Fin 46)} (h : m = n) (c : m.Center) :
      (Eq.mp (congrArg MultiCenterMolecule.Center h) c).1 = c.1 := by cases h; rfl
  exact Subtype.ext (center_val frameChange_spec canonicalRoot)

private theorem calibration_reindexed :
    ActualPhysicalCalibratedCoordinates certified (canon.reindexFrames frameChange)
      (canon.reindexConfiguration frameChange (coordinateCfg certified)) canonicalRoot := by
  obtain ⟨P, seen, nonzero, sign⟩ := canonical_root_calibrated
  refine ⟨fun i => P (frameChange canonicalRoot i), ?_, ?_, ?_⟩
  · intro i
    rw [MultiCenterMolecule.reindexFrames_ligandAtomAt]
    exact seen _
  · exact cartesianOrientedVolume_perm_ne_zero P (frameChange canonicalRoot) nonzero
  · have vec : ∀ k : Fin 4,
        RationalTetrahedralPermutation.pointVector (P 0) (P 1) (P 2) (P 3) k = P k := by
      intro k
      fin_cases k <;> rfl
    have volume : RationalTetrahedralPermutation.permutedOrientedVolume
        (P 0) (P 1) (P 2) (P 3) (frameChange canonicalRoot) =
        orientedVolume (P (frameChange canonicalRoot 0)) (P (frameChange canonicalRoot 1))
          (P (frameChange canonicalRoot 2)) (P (frameChange canonicalRoot 3)) := by
      simp only [RationalTetrahedralPermutation.permutedOrientedVolume, vec]
    rw [← volume, rationalVolumeSign_permutedOrientedVolume, sign,
      MultiCenterMolecule.configurationSign_reindexConfiguration]

theorem root_calibrated :
    ActualPhysicalCalibratedCoordinates certified physical cfg rootCenter := by
  have transport {m n : MultiCenterMolecule (Fin 46)} (h : m = n)
      (configuration : m.Configuration) (c : m.Center)
      (hcal : ActualPhysicalCalibratedCoordinates certified m configuration c) :
      ActualPhysicalCalibratedCoordinates certified n
        (Eq.mp (congrArg MultiCenterMolecule.Configuration h) configuration)
        (Eq.mp (congrArg MultiCenterMolecule.Center h) c) := by
    cases h
    exact hcal
  simpa only [cfg, root_transfer] using transport frameChange_spec
    (canon.reindexConfiguration frameChange (coordinateCfg certified)) canonicalRoot
    calibration_reindexed

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitRootCalibration

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitRootCalibration.canonical_root_ligands
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitRootCalibration.root_observed
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitRootCalibration.canonical_root_calibrated
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitRootCalibration.root_calibrated
