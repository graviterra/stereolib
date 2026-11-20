import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitInput
import TetraStereo.OneCenter.LocalizedChemicalRingInheritedRefusalCases
import TetraStereo.OneCenter.LocalizedPhysicalDomainReindexing
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
The shortcut endpoint's actual coordinate frame is nondegenerate. Its physical
configuration is read from the spatial table and transferred to the detected frames by
the existing frame-reindexing theorem. Its actual occurrence frame is then constructed
from the certified reached raw query. No auxiliary labels or comparison outcomes are supplied.
Only the current center's calibration is asserted here.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCalibration

open LocalizedChemicalRingReferenceOrbitInput LocalizedActualPhysicalBranchDecision
open LocalizedRecursiveAuxiliaryPhysicalDomain LocalizedChemicalRingInheritedRefusalCases
open CertifiedLocalizedCIPInput CartesianPoint3

abbrev canon := actualCanonicalMolecule certified
def canonicalCurrent : canon.Center := ⟨(2 : Fin 46), by
  change (2 : Fin 46) ∈ graph.tetrahedralCenterSet
  rw [detected_inventory]
  decide⟩

def points : Fin 4 → CartesianPoint3 :=
  ![point 0 0 0, point 1 0 0, point 0 0 1, point 0 1 0]

private theorem ligand_of_sorted (c : canon.Center) (sorted : List certified.Atom)
    (ordered : (certified.moleculeGraph.neighborFinset c.1).sort (· ≤ ·) = sorted)
    (length : sorted.length = 4) (i : Fin 4) :
    canon.ligandAtomAt c i = sorted.get (Fin.cast length.symm i) := by
  unfold canon actualCanonicalMolecule MultiCenterMolecule.ligandAtomAt
    CertifiedLocalizedCIPInput.canonicalLigandAtom CertifiedLocalizedCIPInput.canonicalNeighborList
  simp [ordered]

theorem canonical_ligands (i : Fin 4) :
    canon.ligandAtomAt canonicalCurrent i = (![1, 5, 6, 7] : Fin 4 → Fin 46) i := by
  have neighbors : graph.neighborFinset 2 = ([1, 5, 6, 7] : List (Fin 46)).toFinset := by
    ext a
    rw [graph.mem_neighborFinset]
    fin_cases a <;> decide +kernel
  have sorted : (graph.neighborFinset 2).sort (· ≤ ·) = [1, 5, 6, 7] := by
    rw [neighbors]
    exact (List.toFinset_sort (· ≤ ·) (by decide)).mpr (by decide)
  have h := ligand_of_sorted canonicalCurrent ([1, 5, 6, 7] : List (Fin 46)) sorted rfl i
  fin_cases i <;> simpa using h

theorem observed (i : Fin 4) :
    certified.spatialPointAt? (canon.ligandAtomAt canonicalCurrent i) = some (points i) := by
  rw [canonical_ligands]
  fin_cases i <;> rfl

theorem canonical_calibrated :
    ActualPhysicalCalibratedCoordinates certified canon (coordinateCfg certified) canonicalCurrent :=
  coordinateCfg_calibrated certified canonicalCurrent points observed (by decide +kernel)

noncomputable section

theorem detectedFrameReindex :
    ∃ tau : canon.Center → Equiv.Perm (Fin 4), canon.reindexFrames tau = physical :=
  certified.exists_reindexFrames_detectedMultiCenterMolecule (m := canon) rfl rfl

def frameChange : canon.Center → Equiv.Perm (Fin 4) := Classical.choose detectedFrameReindex
theorem frameChange_spec : canon.reindexFrames frameChange = physical :=
  Classical.choose_spec detectedFrameReindex

def cfg : physical.Configuration :=
  Eq.mp (congrArg MultiCenterMolecule.Configuration frameChange_spec)
    (canon.reindexConfiguration frameChange (coordinateCfg certified))

def current : physical.Center := ⟨(2 : Fin 46), by
  change (2 : Fin 46) ∈ graph.tetrahedralCenterSet
  rw [detected_inventory]
  decide⟩

private theorem current_transfer :
    Eq.mp (congrArg MultiCenterMolecule.Center frameChange_spec) canonicalCurrent = current := by
  have center_val {m n : MultiCenterMolecule (Fin 46)} (h : m = n) (c : m.Center) :
      (Eq.mp (congrArg MultiCenterMolecule.Center h) c).1 = c.1 := by cases h; rfl
  exact Subtype.ext (center_val frameChange_spec canonicalCurrent)

private theorem calibration_reindexed :
    ActualPhysicalCalibratedCoordinates certified (canon.reindexFrames frameChange)
      (canon.reindexConfiguration frameChange (coordinateCfg certified)) canonicalCurrent := by
  obtain ⟨P, seen, nonzero, sign⟩ := canonical_calibrated
  refine ⟨fun i => P (frameChange canonicalCurrent i), ?_, ?_, ?_⟩
  · intro i
    rw [MultiCenterMolecule.reindexFrames_ligandAtomAt]
    exact seen _
  · exact cartesianOrientedVolume_perm_ne_zero P (frameChange canonicalCurrent) nonzero
  · have vec : ∀ k : Fin 4,
        RationalTetrahedralPermutation.pointVector (P 0) (P 1) (P 2) (P 3) k = P k := by
      intro k
      fin_cases k <;> rfl
    have volume : RationalTetrahedralPermutation.permutedOrientedVolume
        (P 0) (P 1) (P 2) (P 3) (frameChange canonicalCurrent) =
        orientedVolume (P (frameChange canonicalCurrent 0)) (P (frameChange canonicalCurrent 1))
          (P (frameChange canonicalCurrent 2)) (P (frameChange canonicalCurrent 3)) := by
      simp only [RationalTetrahedralPermutation.permutedOrientedVolume, vec]
    rw [← volume, rationalVolumeSign_permutedOrientedVolume, sign,
      MultiCenterMolecule.configurationSign_reindexConfiguration]

theorem calibrated : ActualPhysicalCalibratedCoordinates certified physical cfg current := by
  have transport {m n : MultiCenterMolecule (Fin 46)} (h : m = n)
      (configuration : m.Configuration) (c : m.Center)
      (hcal : ActualPhysicalCalibratedCoordinates certified m configuration c) :
      ActualPhysicalCalibratedCoordinates certified n
        (Eq.mp (congrArg MultiCenterMolecule.Configuration h) configuration)
        (Eq.mp (congrArg MultiCenterMolecule.Center h) c) := by
    cases h
    exact hcal
  simpa only [cfg, current_transfer] using transport frameChange_spec
    (canon.reindexConfiguration frameChange (coordinateCfg certified)) canonicalCurrent
    calibration_reindexed

/-- The carrier target, frame and raw readback are constructed from actual reachability. -/
def shortcutData : OccurrenceData certified mol current shortcutNode :=
  Classical.choice (occurrenceData_exists certified mol structure_agreement admissible supported
    single_bonded current shortcutNode shortcut_reached rfl rfl)

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCalibration

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCalibration.canonical_ligands
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCalibration.observed
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCalibration.canonical_calibrated
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCalibration.detectedFrameReindex
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCalibration.frameChange_spec
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCalibration.calibrated
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCalibration.shortcutData
