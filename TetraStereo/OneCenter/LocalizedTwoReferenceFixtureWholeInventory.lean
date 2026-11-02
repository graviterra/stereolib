import TetraStereo.OneCenter.LocalizedTwoReferenceFixturePhysicalInstance
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Exact whole-molecule inventory for the two-reference fixture

The nine positions below are proved to be the actual canonical detector enumeration.  No
occurrence carrier or auxiliary fixed point is evaluated to establish this finite inventory.
-/

namespace TetraStereo.OneCenter.LocalizedTwoReferenceFixtureWholeInventory

open CertifiedLocalizedCIPInput
open LocalizedTwoReferencePseudoasymmetryFixture
open LocalizedTwoReferenceFixturePhysicalInstance

abbrev Center := input.certified.TetrahedralCenter

def rootCenter : Center := ⟨rootP.1, rootP.2⟩

def centers : List Center :=
  [rootCenter, FixtureInventory.center4, FixtureInventory.center7,
    FixtureInventory.center11, FixtureInventory.center14, FixtureInventory.center19,
    FixtureInventory.center22, FixtureInventory.center26, FixtureInventory.center29]

theorem canonicalCenterIndices :
    input.certified.canonicalTetrahedralCenters.map (fun center => center.1.1) =
      [0, 4, 7, 11, 14, 19, 22, 26, 29] := by
  unfold canonicalTetrahedralCenters
  simp only [List.map_map, Function.comp_def, List.attach_map_val]
  change (FixtureInventory.Input.tetrahedralCenterSet.sort (· ≤ ·)).map Fin.val = _
  rw [FixtureInventory.detectedCenterSet]
  let xs : List FixtureInventory.Atom :=
    [FixtureInventory.fixtureAtom 0, FixtureInventory.fixtureAtom 4,
      FixtureInventory.fixtureAtom 7, FixtureInventory.fixtureAtom 11,
      FixtureInventory.fixtureAtom 14, FixtureInventory.fixtureAtom 19,
      FixtureInventory.fixtureAtom 22, FixtureInventory.fixtureAtom 26,
      FixtureInventory.fixtureAtom 29]
  have hset : xs.toFinset =
      {FixtureInventory.fixtureAtom 0, FixtureInventory.fixtureAtom 4,
        FixtureInventory.fixtureAtom 7, FixtureInventory.fixtureAtom 11,
        FixtureInventory.fixtureAtom 14, FixtureInventory.fixtureAtom 19,
        FixtureInventory.fixtureAtom 22, FixtureInventory.fixtureAtom 26,
        FixtureInventory.fixtureAtom 29} := by simp [xs]
  have hn : xs.Nodup := by decide +kernel
  have hs : xs.Pairwise (· ≤ ·) := by decide +kernel
  rw [← hset, (List.toFinset_sort (· ≤ ·) hn).2 hs]
  rfl

theorem canonicalCenters : input.certified.canonicalTetrahedralCenters = centers := by
  apply (List.map_inj_right (f := fun center : Center => center.1.1)
    (fun _ _ h => Subtype.ext (Fin.ext h))).mp
  exact canonicalCenterIndices

theorem all_detected_centers (center : Center) : center ∈ centers := by
  rw [← canonicalCenters]
  exact (input.certified.mem_canonicalTetrahedralCenters_iff center).2 center.2

theorem center_count : input.certified.canonicalTetrahedralCenters.length = 9 := by
  rw [canonicalCenters]
  rfl

theorem center_indices_nodup :
    (input.certified.canonicalTetrahedralCenters.map (fun center => center.1.1)).Nodup := by
  rw [canonicalCenterIndices]
  decide

end TetraStereo.OneCenter.LocalizedTwoReferenceFixtureWholeInventory

assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixtureWholeInventory.canonicalCenterIndices
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixtureWholeInventory.canonicalCenters
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixtureWholeInventory.all_detected_centers
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixtureWholeInventory.center_count
assert_kernel_only TetraStereo.OneCenter.LocalizedTwoReferenceFixtureWholeInventory.center_indices_nodup
