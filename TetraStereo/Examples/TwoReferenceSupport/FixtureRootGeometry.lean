import TetraStereo.OneCenter.LocalizedTwoReferencePseudoasymmetryFixture
import TetraStereo.OneCenter.LocalizedPhysicalDomainAdapters
import TetraStereo.OneCenter.AuthoritativeLocalizedTetrahedralDescriptor
import TetraStereo.KernelOnly
import TetraStereo.Examples.TwoReferenceSupport.FixtureInventory
import TetraStereo.Examples.TwoReferenceSupport.FixtureGeometry

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace FixtureRootGeometry

open TetraStereo.OneCenter
open TetraStereo.OneCenter.LocalizedTwoReferencePseudoasymmetryFixture

abbrev Input := FixtureInventory.Input
abbrev Atom := FixtureInventory.Atom

/-- The actual detected root atom, obtained from the fixture inventory theorem. -/
def rootCenter : Input.TetrahedralCenter :=
  ⟨FixtureInventory.fixtureAtom 0, by
    rw [FixtureInventory.detectedCenterSet]
    simp⟩

def rootAtoms : List Atom :=
  [FixtureInventory.fixtureAtom 1, FixtureInventory.fixtureAtom 2,
    FixtureInventory.fixtureAtom 3, FixtureInventory.fixtureAtom 18]

theorem sort_of_toFinset_eq (a : Atom) (xs : List Atom)
    (hset : xs.toFinset = Input.moleculeGraph.neighborFinset a)
    (hnodup : xs.Nodup) (hsorted : xs.Pairwise (· ≤ ·)) :
    (Input.moleculeGraph.neighborFinset a).sort (· ≤ ·) = xs := by
  rw [← hset]
  exact (List.toFinset_sort (r := (· ≤ ·)) (l := xs) hnodup).mpr hsorted

/-- The root's actual adjacency in the fixture graph, without a hand-built alternate graph. -/
theorem rootNeighborFinset :
    Input.moleculeGraph.neighborFinset (FixtureInventory.fixtureAtom 0) =
      ({FixtureInventory.fixtureAtom 1, FixtureInventory.fixtureAtom 2,
        FixtureInventory.fixtureAtom 3, FixtureInventory.fixtureAtom 18} : Finset Atom) := by
  ext a
  rw [MoleculeGraph.mem_neighborFinset]
  fin_cases a <;> decide +kernel

/-- Canonical neighbor sorting is certified by the sort-free `toFinset_sort` characterization. -/
theorem rootCanonicalNeighborList : Input.canonicalNeighborList rootCenter = rootAtoms := by
  unfold CertifiedLocalizedCIPInput.canonicalNeighborList rootCenter
  apply sort_of_toFinset_eq
  · rw [rootNeighborFinset]
    decide +kernel
  · decide +kernel
  · decide +kernel

theorem canonicalLigandAtom_zero :
    Input.canonicalLigandAtom rootCenter 0 = FixtureInventory.fixtureAtom 1 := by
  simp [CertifiedLocalizedCIPInput.canonicalLigandAtom, rootCanonicalNeighborList, rootAtoms]

theorem canonicalLigandAtom_one :
    Input.canonicalLigandAtom rootCenter 1 = FixtureInventory.fixtureAtom 2 := by
  simp [CertifiedLocalizedCIPInput.canonicalLigandAtom, rootCanonicalNeighborList, rootAtoms]

theorem canonicalLigandAtom_two :
    Input.canonicalLigandAtom rootCenter 2 = FixtureInventory.fixtureAtom 3 := by
  simp [CertifiedLocalizedCIPInput.canonicalLigandAtom, rootCanonicalNeighborList, rootAtoms]

theorem canonicalLigandAtom_three :
    Input.canonicalLigandAtom rootCenter 3 = FixtureInventory.fixtureAtom 18 := by
  simp [CertifiedLocalizedCIPInput.canonicalLigandAtom, rootCanonicalNeighborList, rootAtoms]

def rootPoint0 : CartesianPoint3 := { x := 0, y := 0, z := 150 }
def rootPoint1 : CartesianPoint3 := { x := 0, y := -141, z := -50 }
def rootPoint2 : CartesianPoint3 := { x := 130, y := 65, z := -39 }
def rootPoint3 : CartesianPoint3 := { x := -130, y := 65, z := -39 }

def canonicalPointAt : Fin 4 → CartesianPoint3
  | 0 => rootPoint0
  | 1 => rootPoint1
  | 2 => rootPoint2
  | _ => rootPoint3

theorem spatialRootPoint0 :
    Input.spatialPointAt? (FixtureInventory.fixtureAtom 1) = some rootPoint0 := by
  change FixtureGeometry.pointAt 1 = some rootPoint0
  norm_num [FixtureGeometry.pointAt, CertifiedLocalizedCIPInput.spatialPointAt?,
    input, localizedSource, certifiedSource, source, rootPoint0]

theorem spatialRootPoint1 :
    Input.spatialPointAt? (FixtureInventory.fixtureAtom 2) = some rootPoint1 := by
  change FixtureGeometry.pointAt 2 = some rootPoint1
  norm_num [FixtureGeometry.pointAt, CertifiedLocalizedCIPInput.spatialPointAt?,
    input, localizedSource, certifiedSource, source, rootPoint1]

theorem spatialRootPoint2 :
    Input.spatialPointAt? (FixtureInventory.fixtureAtom 3) = some rootPoint2 := by
  change FixtureGeometry.pointAt 3 = some rootPoint2
  norm_num [FixtureGeometry.pointAt, CertifiedLocalizedCIPInput.spatialPointAt?,
    input, localizedSource, certifiedSource, source, rootPoint2]

theorem spatialRootPoint3 :
    Input.spatialPointAt? (FixtureInventory.fixtureAtom 18) = some rootPoint3 := by
  change FixtureGeometry.pointAt 18 = some rootPoint3
  norm_num [FixtureGeometry.pointAt, CertifiedLocalizedCIPInput.spatialPointAt?,
    input, localizedSource, certifiedSource, source, rootPoint3]

theorem actualCanonicalRootCoordinates :
    Input.ActualCanonicalRootCoordinates rootCenter := by
  refine ⟨canonicalPointAt, ?_, ?_⟩
  · intro i
    fin_cases i
    · change Input.spatialPointAt? (Input.canonicalLigandAtom rootCenter 0) = some rootPoint0
      rw [canonicalLigandAtom_zero]
      exact spatialRootPoint0
    · change Input.spatialPointAt? (Input.canonicalLigandAtom rootCenter 1) = some rootPoint1
      rw [canonicalLigandAtom_one]
      exact spatialRootPoint1
    · change Input.spatialPointAt? (Input.canonicalLigandAtom rootCenter 2) = some rootPoint2
      rw [canonicalLigandAtom_two]
      exact spatialRootPoint2
    · change Input.spatialPointAt? (Input.canonicalLigandAtom rootCenter 3) = some rootPoint3
      rw [canonicalLigandAtom_three]
      exact spatialRootPoint3
  · norm_num [canonicalPointAt, CartesianPoint3.orientedVolume,
      rootPoint0, rootPoint1, rootPoint2, rootPoint3]

theorem rootCanonicalVolume :
    FixtureGeometry.volumeAt [1, 2, 3, 18] = some 10308740 := by
  norm_num [FixtureGeometry.volumeAt, FixtureGeometry.pointsAt,
    FixtureGeometry.pointAt, CertifiedLocalizedCIPInput.spatialPointAt?,
    input, localizedSource, certifiedSource, source,
    CartesianPoint3.orientedVolume]

/-- Geometric candidate order with chlorine, the first nitrogen, the second nitrogen, and hydrogen.
This names a coordinate order only; it does not assert how the nitrogen branches are ranked. -/
def rootCandidateOrder : List (Fin 33) := [2, 3, 18, 1]

/-- The candidate order after exchanging the constitutionally tied nitrogen branches. -/
def rootCandidateOrderSwappedNitrogens : List (Fin 33) := [2, 18, 3, 1]

theorem rootCandidateVolume :
    FixtureGeometry.volumeAt rootCandidateOrder = some (-10308740) := by
  norm_num [FixtureGeometry.volumeAt, FixtureGeometry.pointsAt,
    FixtureGeometry.pointAt, CertifiedLocalizedCIPInput.spatialPointAt?,
    input, localizedSource, certifiedSource, source, rootCandidateOrder,
    CartesianPoint3.orientedVolume]

theorem rootCandidateVolume_swappedNitrogens :
    FixtureGeometry.volumeAt rootCandidateOrderSwappedNitrogens = some 10308740 := by
  norm_num [FixtureGeometry.volumeAt, FixtureGeometry.pointsAt,
    FixtureGeometry.pointAt, CertifiedLocalizedCIPInput.spatialPointAt?,
    input, localizedSource, certifiedSource, source, rootCandidateOrderSwappedNitrogens,
    CartesianPoint3.orientedVolume]

theorem rootCandidateDescriptor :
    FixtureGeometry.descriptorAt rootCandidateOrder = some RS.R := by
  rw [FixtureGeometry.descriptorAt_eq_of_volume _ _ rootCandidateVolume]
  norm_num [CertifiedLocalizedCIPInput.descriptorOfOrientedVolume?]

theorem rootCandidateDescriptor_swappedNitrogens :
    FixtureGeometry.descriptorAt rootCandidateOrderSwappedNitrogens = some RS.S := by
  rw [FixtureGeometry.descriptorAt_eq_of_volume _ _ rootCandidateVolume_swappedNitrogens]
  norm_num [CertifiedLocalizedCIPInput.descriptorOfOrientedVolume?]

theorem rootCandidateProductionDescriptor :
    (FixtureGeometry.pointsAt rootCandidateOrder).bind
      CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints? = some RS.R := by
  rw [← FixtureGeometry.descriptorAt_eq_priority_ordered_list]
  exact rootCandidateDescriptor

theorem rootCandidateProductionDescriptor_swappedNitrogens :
    (FixtureGeometry.pointsAt rootCandidateOrderSwappedNitrogens).bind
      CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints? = some RS.S := by
  rw [← FixtureGeometry.descriptorAt_eq_priority_ordered_list]
  exact rootCandidateDescriptor_swappedNitrogens

end FixtureRootGeometry

assert_kernel_only FixtureRootGeometry.rootNeighborFinset
assert_kernel_only FixtureRootGeometry.rootCanonicalNeighborList
assert_kernel_only FixtureRootGeometry.actualCanonicalRootCoordinates
assert_kernel_only FixtureRootGeometry.rootCanonicalVolume
assert_kernel_only FixtureRootGeometry.rootCandidateVolume
assert_kernel_only FixtureRootGeometry.rootCandidateVolume_swappedNitrogens
assert_kernel_only FixtureRootGeometry.rootCandidateProductionDescriptor
assert_kernel_only FixtureRootGeometry.rootCandidateProductionDescriptor_swappedNitrogens
