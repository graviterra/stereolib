import TetraStereo.Examples.TwoReferenceSupport.FixtureInventory
import TetraStereo.Examples.TwoReferenceSupport.FixtureGeometry
import TetraStereo.Examples.TwoReferenceSupport.FixtureRigidity
import TetraStereo.OneCenter.LocalizedRootZAutomorphismLabelCovariance
import TetraStereo.OneCenter.LocalizedPhysicalDomainAdapters
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace FixtureCalibration

open TetraStereo.OneCenter
open FixtureInventory
open FixtureGeometry
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.OneCenter.LocalizedTwoReferencePseudoasymmetryFixture

noncomputable abbrev Physical := Input.detectedMultiCenterMolecule

def reverseFrame : Equiv.Perm (Fin 4) := Equiv.swap 0 1

theorem reverseFrame_sign : permHandedness reverseFrame = -1 := by
  simp [reverseFrame]

/-- The actual detector's executable neighbor order is the ascending source-atom order.  These
lists are candidates only; the `canonicalNeighborListN` theorems below identify them with the
real finite graph sort. -/
def canonicalAtoms4 : List Atom := atomList ([3, 5, 6, 7] : List (Fin 33))
def canonicalAtoms7 : List Atom := atomList ([4, 8, 9, 10] : List (Fin 33))
def canonicalAtoms11 : List Atom := atomList ([3, 12, 13, 14] : List (Fin 33))
def canonicalAtoms14 : List Atom := atomList ([11, 15, 16, 17] : List (Fin 33))
def canonicalAtoms19 : List Atom := atomList ([18, 20, 21, 22] : List (Fin 33))
def canonicalAtoms22 : List Atom := atomList ([19, 23, 24, 25] : List (Fin 33))
def canonicalAtoms26 : List Atom := atomList ([18, 27, 28, 29] : List (Fin 33))
def canonicalAtoms29 : List Atom := atomList ([26, 30, 31, 32] : List (Fin 33))

private theorem sort_of_toFinset_eq (a : Atom) (xs : List Atom)
    (hset : xs.toFinset = Input.moleculeGraph.neighborFinset a)
    (hnodup : xs.Nodup) (hsorted : xs.Pairwise (· ≤ ·)) :
    (Input.moleculeGraph.neighborFinset a).sort (· ≤ ·) = xs := by
  rw [← hset]
  exact (List.toFinset_sort (r := (· ≤ ·)) (l := xs) hnodup).mpr hsorted

theorem canonicalNeighborList4 :
    Input.canonicalNeighborList center4 = canonicalAtoms4 := by
  unfold CertifiedLocalizedCIPInput.canonicalNeighborList
  apply sort_of_toFinset_eq
  · change canonicalAtoms4.toFinset =
      Input.moleculeGraph.neighborFinset (fixtureAtom 4)
    rw [graphNeighbors4]
    decide +kernel
  · decide +kernel
  · decide +kernel

theorem canonicalNeighborList7 :
    Input.canonicalNeighborList center7 = canonicalAtoms7 := by
  unfold CertifiedLocalizedCIPInput.canonicalNeighborList
  apply sort_of_toFinset_eq
  · change canonicalAtoms7.toFinset =
      Input.moleculeGraph.neighborFinset (fixtureAtom 7)
    rw [graphNeighbors7]
    decide +kernel
  · decide +kernel
  · decide +kernel

theorem canonicalNeighborList11 :
    Input.canonicalNeighborList center11 = canonicalAtoms11 := by
  unfold CertifiedLocalizedCIPInput.canonicalNeighborList
  apply sort_of_toFinset_eq
  · change canonicalAtoms11.toFinset =
      Input.moleculeGraph.neighborFinset (fixtureAtom 11)
    rw [graphNeighbors11]
    decide +kernel
  · decide +kernel
  · decide +kernel

theorem canonicalNeighborList14 :
    Input.canonicalNeighborList center14 = canonicalAtoms14 := by
  unfold CertifiedLocalizedCIPInput.canonicalNeighborList
  apply sort_of_toFinset_eq
  · change canonicalAtoms14.toFinset =
      Input.moleculeGraph.neighborFinset (fixtureAtom 14)
    rw [graphNeighbors14]
    decide +kernel
  · decide +kernel
  · decide +kernel

theorem canonicalNeighborList19 :
    Input.canonicalNeighborList center19 = canonicalAtoms19 := by
  unfold CertifiedLocalizedCIPInput.canonicalNeighborList
  apply sort_of_toFinset_eq
  · change canonicalAtoms19.toFinset =
      Input.moleculeGraph.neighborFinset (fixtureAtom 19)
    rw [graphNeighbors19]
    decide +kernel
  · decide +kernel
  · decide +kernel

theorem canonicalNeighborList22 :
    Input.canonicalNeighborList center22 = canonicalAtoms22 := by
  unfold CertifiedLocalizedCIPInput.canonicalNeighborList
  apply sort_of_toFinset_eq
  · change canonicalAtoms22.toFinset =
      Input.moleculeGraph.neighborFinset (fixtureAtom 22)
    rw [graphNeighbors22]
    decide +kernel
  · decide +kernel
  · decide +kernel

theorem canonicalNeighborList26 :
    Input.canonicalNeighborList center26 = canonicalAtoms26 := by
  unfold CertifiedLocalizedCIPInput.canonicalNeighborList
  apply sort_of_toFinset_eq
  · change canonicalAtoms26.toFinset =
      Input.moleculeGraph.neighborFinset (fixtureAtom 26)
    rw [graphNeighbors26]
    decide +kernel
  · decide +kernel
  · decide +kernel

theorem canonicalNeighborList29 :
    Input.canonicalNeighborList center29 = canonicalAtoms29 := by
  unfold CertifiedLocalizedCIPInput.canonicalNeighborList
  apply sort_of_toFinset_eq
  · change canonicalAtoms29.toFinset =
      Input.moleculeGraph.neighborFinset (fixtureAtom 29)
    rw [graphNeighbors29]
    decide +kernel
  · decide +kernel
  · decide +kernel

/-- Canonical-frame parities inferred from the exact priority-frame volumes and the odd
permutation between descending-Z and ascending source-atom order at each center. -/
noncomputable def canonicalConfiguration :
    Input.canonicalDetectedMultiCenterMolecule.Configuration := fun c =>
  if c.val.val = 11 ∨ c.val.val = 19 ∨ c.val.val = 22 ∨ c.val.val = 29
  then reverseFrame else 1

/-- The physical configuration compensates for the actual detector enumeration's per-center
reindexing.  Its canonical reindex is the measured canonical configuration above. -/
noncomputable def actualConfiguration : Physical.Configuration := fun c =>
  canonicalConfiguration c * (Input.canonicalLigandReindex c)⁻¹

theorem canonicalReindex_actualConfiguration :
    Input.canonicalReindexConfiguration actualConfiguration = canonicalConfiguration := by
  funext c
  simp [actualConfiguration, CertifiedLocalizedCIPInput.canonicalReindexConfiguration,
    mul_assoc]

/-- A canonical coordinate frame transports to the detected molecule's actual ligand enumeration
through its certified canonical reindex. This is the finite calibration bridge: the physical
configuration is chosen so its canonical reindex is the calibrated canonical frame. -/
theorem actualCalibration_of_canonicalFrame
    (center : Input.TetrahedralCenter)
    (rigid : ConstitutionallyRigid Physical ⟨center.1, center.2⟩)
    (pointAt : Fin 4 → CartesianPoint3)
    (observed : ∀ i, Input.spatialPointAt? (Input.canonicalLigandAtom center i) =
      some (pointAt i))
    (nonzero : CartesianPoint3.orientedVolume (pointAt 0) (pointAt 1)
      (pointAt 2) (pointAt 3) ≠ 0)
    (signEq : rationalVolumeSign
      (CartesianPoint3.orientedVolume (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3)) =
        permHandedness (canonicalConfiguration center)) :
    ActualPhysicalGeneralRigidCalibratedCenter Input Physical actualConfiguration
      ⟨center.1, center.2⟩ := by
  let beta := Input.canonicalLigandReindex (⟨center.1, center.2⟩ : Physical.Center)
  let physicalPointAt : Fin 4 → CartesianPoint3 := fun i => pointAt (beta i)
  have hvec : ∀ k : Fin 4,
      RationalTetrahedralPermutation.pointVector (pointAt 0) (pointAt 1)
        (pointAt 2) (pointAt 3) k = pointAt k := by
    intro k
    fin_cases k <;> rfl
  have hpermuted : RationalTetrahedralPermutation.permutedOrientedVolume
      (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3) beta =
      CartesianPoint3.orientedVolume (pointAt (beta 0)) (pointAt (beta 1))
        (pointAt (beta 2)) (pointAt (beta 3)) := by
    simp only [RationalTetrahedralPermutation.permutedOrientedVolume, hvec]
  have hvol : CartesianPoint3.orientedVolume (physicalPointAt 0) (physicalPointAt 1)
      (physicalPointAt 2) (physicalPointAt 3) =
      RationalTetrahedralPermutation.permutedOrientedVolume
        (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3) beta := by
    simpa [physicalPointAt] using hpermuted.symm
  have hbeta : canonicalConfiguration center = actualConfiguration
      ⟨center.1, center.2⟩ * beta := by
    have h := congrFun canonicalReindex_actualConfiguration
      (⟨center.1, center.2⟩ : Physical.Center)
    simpa [CertifiedLocalizedCIPInput.canonicalReindexConfiguration, beta] using h.symm
  refine ⟨rigid, physicalPointAt, ?_, ?_, ?_⟩
  · intro i
    rw [CertifiedLocalizedCIPInput.canonicalLigandReindex_spec]
    exact observed (beta i)
  · exact cartesianOrientedVolume_perm_ne_zero pointAt beta nonzero
  · rw [hvol, rationalVolumeSign_permutedOrientedVolume, signEq, hbeta]
    simp only [permHandedness_mul, MultiCenterMolecule.configurationSign]
    rw [mul_assoc, permHandedness_mul_self, mul_one]
/-- The canonical executable enumeration at center 4, certified from its actual graph
neighbor finset rather than assumed from the priority list. -/
theorem canonicalLigands4 (i : Fin 4) :
    Input.canonicalLigandAtom center4 i =
      (match i with
       | 0 => fixtureAtom (3 : Fin 33)
       | 1 => fixtureAtom (5 : Fin 33)
       | 2 => fixtureAtom (6 : Fin 33)
       | _ => fixtureAtom (7 : Fin 33)) := by
  fin_cases i <;>
    simp [CertifiedLocalizedCIPInput.canonicalLigandAtom, canonicalNeighborList4,
      canonicalAtoms4, atomList]

def canonicalPoint4 : Fin 4 → CartesianPoint3
  | 0 => (FixtureGeometry.pointAt (3 : Fin 33)).getD ({ x := 0, y := 0, z := 0 } : CartesianPoint3)
  | 1 => (FixtureGeometry.pointAt (5 : Fin 33)).getD ({ x := 0, y := 0, z := 0 } : CartesianPoint3)
  | 2 => (FixtureGeometry.pointAt (6 : Fin 33)).getD ({ x := 0, y := 0, z := 0 } : CartesianPoint3)
  | _ => (FixtureGeometry.pointAt (7 : Fin 33)).getD ({ x := 0, y := 0, z := 0 } : CartesianPoint3)

theorem canonicalObserved4 :
    ∀ i, Input.spatialPointAt? (Input.canonicalLigandAtom center4 i) =
      some (canonicalPoint4 i) := by
  intro i
  rw [canonicalLigands4]
  fin_cases i <;>
    norm_num [canonicalPoint4, FixtureGeometry.pointAt,
      CertifiedLocalizedCIPInput.spatialPointAt?, input, localizedSource, certifiedSource,
      source, fixtureAtom]

theorem canonicalVolume4 :
    CartesianPoint3.orientedVolume (canonicalPoint4 0) (canonicalPoint4 1)
      (canonicalPoint4 2) (canonicalPoint4 3) = 5205250 := by
  norm_num [canonicalPoint4, FixtureGeometry.pointAt,
    CertifiedLocalizedCIPInput.spatialPointAt?, input, localizedSource, certifiedSource,
    source, CartesianPoint3.orientedVolume]

theorem canonicalSign4 :
    rationalVolumeSign
      (CartesianPoint3.orientedVolume (canonicalPoint4 0) (canonicalPoint4 1)
        (canonicalPoint4 2) (canonicalPoint4 3)) =
      permHandedness (canonicalConfiguration center4) := by
  rw [canonicalVolume4]
  rw [rationalVolumeSign_of_pos
    (by norm_num : (0 : ℚ) < 5205250)]
  simp [canonicalConfiguration, center4, fixtureAtom]

/-- The canonical executable enumeration at center 7, certified from its actual graph
neighbor finset rather than assumed from the priority list. -/
theorem canonicalLigands7 (i : Fin 4) :
    Input.canonicalLigandAtom center7 i =
      (match i with
       | 0 => fixtureAtom (4 : Fin 33)
       | 1 => fixtureAtom (8 : Fin 33)
       | 2 => fixtureAtom (9 : Fin 33)
       | _ => fixtureAtom (10 : Fin 33)) := by
  fin_cases i <;>
    simp [CertifiedLocalizedCIPInput.canonicalLigandAtom, canonicalNeighborList7,
      canonicalAtoms7, atomList]

def canonicalPoint7 : Fin 4 → CartesianPoint3
  | 0 => (FixtureGeometry.pointAt (4 : Fin 33)).getD ({ x := 0, y := 0, z := 0 } : CartesianPoint3)
  | 1 => (FixtureGeometry.pointAt (8 : Fin 33)).getD ({ x := 0, y := 0, z := 0 } : CartesianPoint3)
  | 2 => (FixtureGeometry.pointAt (9 : Fin 33)).getD ({ x := 0, y := 0, z := 0 } : CartesianPoint3)
  | _ => (FixtureGeometry.pointAt (10 : Fin 33)).getD ({ x := 0, y := 0, z := 0 } : CartesianPoint3)

theorem canonicalObserved7 :
    ∀ i, Input.spatialPointAt? (Input.canonicalLigandAtom center7 i) =
      some (canonicalPoint7 i) := by
  intro i
  rw [canonicalLigands7]
  fin_cases i <;>
    norm_num [canonicalPoint7, FixtureGeometry.pointAt,
      CertifiedLocalizedCIPInput.spatialPointAt?, input, localizedSource, certifiedSource,
      source, fixtureAtom]

theorem canonicalVolume7 :
    CartesianPoint3.orientedVolume (canonicalPoint7 0) (canonicalPoint7 1)
      (canonicalPoint7 2) (canonicalPoint7 3) = 5222963 := by
  norm_num [canonicalPoint7, FixtureGeometry.pointAt,
    CertifiedLocalizedCIPInput.spatialPointAt?, input, localizedSource, certifiedSource,
    source, CartesianPoint3.orientedVolume]

theorem canonicalSign7 :
    rationalVolumeSign
      (CartesianPoint3.orientedVolume (canonicalPoint7 0) (canonicalPoint7 1)
        (canonicalPoint7 2) (canonicalPoint7 3)) =
      permHandedness (canonicalConfiguration center7) := by
  rw [canonicalVolume7]
  rw [rationalVolumeSign_of_pos
    (by norm_num : (0 : ℚ) < 5222963)]
  simp [canonicalConfiguration, center7, fixtureAtom]

/-- The canonical executable enumeration at center 11, certified from its actual graph
neighbor finset rather than assumed from the priority list. -/
theorem canonicalLigands11 (i : Fin 4) :
    Input.canonicalLigandAtom center11 i =
      (match i with
       | 0 => fixtureAtom (3 : Fin 33)
       | 1 => fixtureAtom (12 : Fin 33)
       | 2 => fixtureAtom (13 : Fin 33)
       | _ => fixtureAtom (14 : Fin 33)) := by
  fin_cases i <;>
    simp [CertifiedLocalizedCIPInput.canonicalLigandAtom, canonicalNeighborList11,
      canonicalAtoms11, atomList]

def canonicalPoint11 : Fin 4 → CartesianPoint3
  | 0 => (FixtureGeometry.pointAt (3 : Fin 33)).getD ({ x := 0, y := 0, z := 0 } : CartesianPoint3)
  | 1 => (FixtureGeometry.pointAt (12 : Fin 33)).getD ({ x := 0, y := 0, z := 0 } : CartesianPoint3)
  | 2 => (FixtureGeometry.pointAt (13 : Fin 33)).getD ({ x := 0, y := 0, z := 0 } : CartesianPoint3)
  | _ => (FixtureGeometry.pointAt (14 : Fin 33)).getD ({ x := 0, y := 0, z := 0 } : CartesianPoint3)

theorem canonicalObserved11 :
    ∀ i, Input.spatialPointAt? (Input.canonicalLigandAtom center11 i) =
      some (canonicalPoint11 i) := by
  intro i
  rw [canonicalLigands11]
  fin_cases i <;>
    norm_num [canonicalPoint11, FixtureGeometry.pointAt,
      CertifiedLocalizedCIPInput.spatialPointAt?, input, localizedSource, certifiedSource,
      source, fixtureAtom]

theorem canonicalVolume11 :
    CartesianPoint3.orientedVolume (canonicalPoint11 0) (canonicalPoint11 1)
      (canonicalPoint11 2) (canonicalPoint11 3) = -5196264 := by
  norm_num [canonicalPoint11, FixtureGeometry.pointAt,
    CertifiedLocalizedCIPInput.spatialPointAt?, input, localizedSource, certifiedSource,
    source, CartesianPoint3.orientedVolume]

theorem canonicalSign11 :
    rationalVolumeSign
      (CartesianPoint3.orientedVolume (canonicalPoint11 0) (canonicalPoint11 1)
        (canonicalPoint11 2) (canonicalPoint11 3)) =
      permHandedness (canonicalConfiguration center11) := by
  rw [canonicalVolume11]
  rw [rationalVolumeSign_of_neg
    (by norm_num : (-5196264 : ℚ) < 0)]
  simp [canonicalConfiguration, center11, fixtureAtom, reverseFrame]

/-- The canonical executable enumeration at center 14, certified from its actual graph
neighbor finset rather than assumed from the priority list. -/
theorem canonicalLigands14 (i : Fin 4) :
    Input.canonicalLigandAtom center14 i =
      (match i with
       | 0 => fixtureAtom (11 : Fin 33)
       | 1 => fixtureAtom (15 : Fin 33)
       | 2 => fixtureAtom (16 : Fin 33)
       | _ => fixtureAtom (17 : Fin 33)) := by
  fin_cases i <;>
    simp [CertifiedLocalizedCIPInput.canonicalLigandAtom, canonicalNeighborList14,
      canonicalAtoms14, atomList]

def canonicalPoint14 : Fin 4 → CartesianPoint3
  | 0 => (FixtureGeometry.pointAt (11 : Fin 33)).getD ({ x := 0, y := 0, z := 0 } : CartesianPoint3)
  | 1 => (FixtureGeometry.pointAt (15 : Fin 33)).getD ({ x := 0, y := 0, z := 0 } : CartesianPoint3)
  | 2 => (FixtureGeometry.pointAt (16 : Fin 33)).getD ({ x := 0, y := 0, z := 0 } : CartesianPoint3)
  | _ => (FixtureGeometry.pointAt (17 : Fin 33)).getD ({ x := 0, y := 0, z := 0 } : CartesianPoint3)

theorem canonicalObserved14 :
    ∀ i, Input.spatialPointAt? (Input.canonicalLigandAtom center14 i) =
      some (canonicalPoint14 i) := by
  intro i
  rw [canonicalLigands14]
  fin_cases i <;>
    norm_num [canonicalPoint14, FixtureGeometry.pointAt,
      CertifiedLocalizedCIPInput.spatialPointAt?, input, localizedSource, certifiedSource,
      source, fixtureAtom]

theorem canonicalVolume14 :
    CartesianPoint3.orientedVolume (canonicalPoint14 0) (canonicalPoint14 1)
      (canonicalPoint14 2) (canonicalPoint14 3) = 5212558 := by
  norm_num [canonicalPoint14, FixtureGeometry.pointAt,
    CertifiedLocalizedCIPInput.spatialPointAt?, input, localizedSource, certifiedSource,
    source, CartesianPoint3.orientedVolume]

theorem canonicalSign14 :
    rationalVolumeSign
      (CartesianPoint3.orientedVolume (canonicalPoint14 0) (canonicalPoint14 1)
        (canonicalPoint14 2) (canonicalPoint14 3)) =
      permHandedness (canonicalConfiguration center14) := by
  rw [canonicalVolume14]
  rw [rationalVolumeSign_of_pos
    (by norm_num : (0 : ℚ) < 5212558)]
  simp [canonicalConfiguration, center14, fixtureAtom]

/-- The canonical executable enumeration at center 19, certified from its actual graph
neighbor finset rather than assumed from the priority list. -/
theorem canonicalLigands19 (i : Fin 4) :
    Input.canonicalLigandAtom center19 i =
      (match i with
       | 0 => fixtureAtom (18 : Fin 33)
       | 1 => fixtureAtom (20 : Fin 33)
       | 2 => fixtureAtom (21 : Fin 33)
       | _ => fixtureAtom (22 : Fin 33)) := by
  fin_cases i <;>
    simp [CertifiedLocalizedCIPInput.canonicalLigandAtom, canonicalNeighborList19,
      canonicalAtoms19, atomList]

def canonicalPoint19 : Fin 4 → CartesianPoint3
  | 0 => (FixtureGeometry.pointAt (18 : Fin 33)).getD ({ x := 0, y := 0, z := 0 } : CartesianPoint3)
  | 1 => (FixtureGeometry.pointAt (20 : Fin 33)).getD ({ x := 0, y := 0, z := 0 } : CartesianPoint3)
  | 2 => (FixtureGeometry.pointAt (21 : Fin 33)).getD ({ x := 0, y := 0, z := 0 } : CartesianPoint3)
  | _ => (FixtureGeometry.pointAt (22 : Fin 33)).getD ({ x := 0, y := 0, z := 0 } : CartesianPoint3)

theorem canonicalObserved19 :
    ∀ i, Input.spatialPointAt? (Input.canonicalLigandAtom center19 i) =
      some (canonicalPoint19 i) := by
  intro i
  rw [canonicalLigands19]
  fin_cases i <;>
    norm_num [canonicalPoint19, FixtureGeometry.pointAt,
      CertifiedLocalizedCIPInput.spatialPointAt?, input, localizedSource, certifiedSource,
      source, fixtureAtom]

theorem canonicalVolume19 :
    CartesianPoint3.orientedVolume (canonicalPoint19 0) (canonicalPoint19 1)
      (canonicalPoint19 2) (canonicalPoint19 3) = -5205250 := by
  norm_num [canonicalPoint19, FixtureGeometry.pointAt,
    CertifiedLocalizedCIPInput.spatialPointAt?, input, localizedSource, certifiedSource,
    source, CartesianPoint3.orientedVolume]

theorem canonicalSign19 :
    rationalVolumeSign
      (CartesianPoint3.orientedVolume (canonicalPoint19 0) (canonicalPoint19 1)
        (canonicalPoint19 2) (canonicalPoint19 3)) =
      permHandedness (canonicalConfiguration center19) := by
  rw [canonicalVolume19]
  rw [rationalVolumeSign_of_neg
    (by norm_num : (-5205250 : ℚ) < 0)]
  simp [canonicalConfiguration, center19, fixtureAtom, reverseFrame]

/-- The canonical executable enumeration at center 22, certified from its actual graph
neighbor finset rather than assumed from the priority list. -/
theorem canonicalLigands22 (i : Fin 4) :
    Input.canonicalLigandAtom center22 i =
      (match i with
       | 0 => fixtureAtom (19 : Fin 33)
       | 1 => fixtureAtom (23 : Fin 33)
       | 2 => fixtureAtom (24 : Fin 33)
       | _ => fixtureAtom (25 : Fin 33)) := by
  fin_cases i <;>
    simp [CertifiedLocalizedCIPInput.canonicalLigandAtom, canonicalNeighborList22,
      canonicalAtoms22, atomList]

def canonicalPoint22 : Fin 4 → CartesianPoint3
  | 0 => (FixtureGeometry.pointAt (19 : Fin 33)).getD ({ x := 0, y := 0, z := 0 } : CartesianPoint3)
  | 1 => (FixtureGeometry.pointAt (23 : Fin 33)).getD ({ x := 0, y := 0, z := 0 } : CartesianPoint3)
  | 2 => (FixtureGeometry.pointAt (24 : Fin 33)).getD ({ x := 0, y := 0, z := 0 } : CartesianPoint3)
  | _ => (FixtureGeometry.pointAt (25 : Fin 33)).getD ({ x := 0, y := 0, z := 0 } : CartesianPoint3)

theorem canonicalObserved22 :
    ∀ i, Input.spatialPointAt? (Input.canonicalLigandAtom center22 i) =
      some (canonicalPoint22 i) := by
  intro i
  rw [canonicalLigands22]
  fin_cases i <;>
    norm_num [canonicalPoint22, FixtureGeometry.pointAt,
      CertifiedLocalizedCIPInput.spatialPointAt?, input, localizedSource, certifiedSource,
      source, fixtureAtom]

theorem canonicalVolume22 :
    CartesianPoint3.orientedVolume (canonicalPoint22 0) (canonicalPoint22 1)
      (canonicalPoint22 2) (canonicalPoint22 3) = -5222963 := by
  norm_num [canonicalPoint22, FixtureGeometry.pointAt,
    CertifiedLocalizedCIPInput.spatialPointAt?, input, localizedSource, certifiedSource,
    source, CartesianPoint3.orientedVolume]

theorem canonicalSign22 :
    rationalVolumeSign
      (CartesianPoint3.orientedVolume (canonicalPoint22 0) (canonicalPoint22 1)
        (canonicalPoint22 2) (canonicalPoint22 3)) =
      permHandedness (canonicalConfiguration center22) := by
  rw [canonicalVolume22]
  rw [rationalVolumeSign_of_neg
    (by norm_num : (-5222963 : ℚ) < 0)]
  simp [canonicalConfiguration, center22, fixtureAtom, reverseFrame]

/-- The canonical executable enumeration at center 26, certified from its actual graph
neighbor finset rather than assumed from the priority list. -/
theorem canonicalLigands26 (i : Fin 4) :
    Input.canonicalLigandAtom center26 i =
      (match i with
       | 0 => fixtureAtom (18 : Fin 33)
       | 1 => fixtureAtom (27 : Fin 33)
       | 2 => fixtureAtom (28 : Fin 33)
       | _ => fixtureAtom (29 : Fin 33)) := by
  fin_cases i <;>
    simp [CertifiedLocalizedCIPInput.canonicalLigandAtom, canonicalNeighborList26,
      canonicalAtoms26, atomList]

def canonicalPoint26 : Fin 4 → CartesianPoint3
  | 0 => (FixtureGeometry.pointAt (18 : Fin 33)).getD ({ x := 0, y := 0, z := 0 } : CartesianPoint3)
  | 1 => (FixtureGeometry.pointAt (27 : Fin 33)).getD ({ x := 0, y := 0, z := 0 } : CartesianPoint3)
  | 2 => (FixtureGeometry.pointAt (28 : Fin 33)).getD ({ x := 0, y := 0, z := 0 } : CartesianPoint3)
  | _ => (FixtureGeometry.pointAt (29 : Fin 33)).getD ({ x := 0, y := 0, z := 0 } : CartesianPoint3)

theorem canonicalObserved26 :
    ∀ i, Input.spatialPointAt? (Input.canonicalLigandAtom center26 i) =
      some (canonicalPoint26 i) := by
  intro i
  rw [canonicalLigands26]
  fin_cases i <;>
    norm_num [canonicalPoint26, FixtureGeometry.pointAt,
      CertifiedLocalizedCIPInput.spatialPointAt?, input, localizedSource, certifiedSource,
      source, fixtureAtom]

theorem canonicalVolume26 :
    CartesianPoint3.orientedVolume (canonicalPoint26 0) (canonicalPoint26 1)
      (canonicalPoint26 2) (canonicalPoint26 3) = 5196264 := by
  norm_num [canonicalPoint26, FixtureGeometry.pointAt,
    CertifiedLocalizedCIPInput.spatialPointAt?, input, localizedSource, certifiedSource,
    source, CartesianPoint3.orientedVolume]

theorem canonicalSign26 :
    rationalVolumeSign
      (CartesianPoint3.orientedVolume (canonicalPoint26 0) (canonicalPoint26 1)
        (canonicalPoint26 2) (canonicalPoint26 3)) =
      permHandedness (canonicalConfiguration center26) := by
  rw [canonicalVolume26]
  rw [rationalVolumeSign_of_pos
    (by norm_num : (0 : ℚ) < 5196264)]
  simp [canonicalConfiguration, center26, fixtureAtom]

/-- The canonical executable enumeration at center 29, certified from its actual graph
neighbor finset rather than assumed from the priority list. -/
theorem canonicalLigands29 (i : Fin 4) :
    Input.canonicalLigandAtom center29 i =
      (match i with
       | 0 => fixtureAtom (26 : Fin 33)
       | 1 => fixtureAtom (30 : Fin 33)
       | 2 => fixtureAtom (31 : Fin 33)
       | _ => fixtureAtom (32 : Fin 33)) := by
  fin_cases i <;>
    simp [CertifiedLocalizedCIPInput.canonicalLigandAtom, canonicalNeighborList29,
      canonicalAtoms29, atomList]

def canonicalPoint29 : Fin 4 → CartesianPoint3
  | 0 => (FixtureGeometry.pointAt (26 : Fin 33)).getD ({ x := 0, y := 0, z := 0 } : CartesianPoint3)
  | 1 => (FixtureGeometry.pointAt (30 : Fin 33)).getD ({ x := 0, y := 0, z := 0 } : CartesianPoint3)
  | 2 => (FixtureGeometry.pointAt (31 : Fin 33)).getD ({ x := 0, y := 0, z := 0 } : CartesianPoint3)
  | _ => (FixtureGeometry.pointAt (32 : Fin 33)).getD ({ x := 0, y := 0, z := 0 } : CartesianPoint3)

theorem canonicalObserved29 :
    ∀ i, Input.spatialPointAt? (Input.canonicalLigandAtom center29 i) =
      some (canonicalPoint29 i) := by
  intro i
  rw [canonicalLigands29]
  fin_cases i <;>
    norm_num [canonicalPoint29, FixtureGeometry.pointAt,
      CertifiedLocalizedCIPInput.spatialPointAt?, input, localizedSource, certifiedSource,
      source, fixtureAtom]

theorem canonicalVolume29 :
    CartesianPoint3.orientedVolume (canonicalPoint29 0) (canonicalPoint29 1)
      (canonicalPoint29 2) (canonicalPoint29 3) = -5212558 := by
  norm_num [canonicalPoint29, FixtureGeometry.pointAt,
    CertifiedLocalizedCIPInput.spatialPointAt?, input, localizedSource, certifiedSource,
    source, CartesianPoint3.orientedVolume]

theorem canonicalSign29 :
    rationalVolumeSign
      (CartesianPoint3.orientedVolume (canonicalPoint29 0) (canonicalPoint29 1)
        (canonicalPoint29 2) (canonicalPoint29 3)) =
      permHandedness (canonicalConfiguration center29) := by
  rw [canonicalVolume29]
  rw [rationalVolumeSign_of_neg
    (by norm_num : (-5212558 : ℚ) < 0)]
  simp [canonicalConfiguration, center29, fixtureAtom, reverseFrame]
/-- Actual detected-enumeration calibration at nonroot center 4; the coordinate enumeration
is transported from the exact canonical atom readbacks by the certified per-center reindex. -/
theorem actualCalibration4 :
    ActualPhysicalGeneralRigidCalibratedCenter Input Physical actualConfiguration
      ⟨center4.1, center4.2⟩ :=
  actualCalibration_of_canonicalFrame center4 FixtureRigidity.rigid4
    canonicalPoint4 canonicalObserved4
    (by rw [canonicalVolume4]; norm_num) canonicalSign4

/-- Actual detected-enumeration calibration at nonroot center 7; the coordinate enumeration
is transported from the exact canonical atom readbacks by the certified per-center reindex. -/
theorem actualCalibration7 :
    ActualPhysicalGeneralRigidCalibratedCenter Input Physical actualConfiguration
      ⟨center7.1, center7.2⟩ :=
  actualCalibration_of_canonicalFrame center7 FixtureRigidity.rigid7
    canonicalPoint7 canonicalObserved7
    (by rw [canonicalVolume7]; norm_num) canonicalSign7

/-- Actual detected-enumeration calibration at nonroot center 11; the coordinate enumeration
is transported from the exact canonical atom readbacks by the certified per-center reindex. -/
theorem actualCalibration11 :
    ActualPhysicalGeneralRigidCalibratedCenter Input Physical actualConfiguration
      ⟨center11.1, center11.2⟩ :=
  actualCalibration_of_canonicalFrame center11 FixtureRigidity.rigid11
    canonicalPoint11 canonicalObserved11
    (by rw [canonicalVolume11]; norm_num) canonicalSign11

/-- Actual detected-enumeration calibration at nonroot center 14; the coordinate enumeration
is transported from the exact canonical atom readbacks by the certified per-center reindex. -/
theorem actualCalibration14 :
    ActualPhysicalGeneralRigidCalibratedCenter Input Physical actualConfiguration
      ⟨center14.1, center14.2⟩ :=
  actualCalibration_of_canonicalFrame center14 FixtureRigidity.rigid14
    canonicalPoint14 canonicalObserved14
    (by rw [canonicalVolume14]; norm_num) canonicalSign14

/-- Actual detected-enumeration calibration at nonroot center 19; the coordinate enumeration
is transported from the exact canonical atom readbacks by the certified per-center reindex. -/
theorem actualCalibration19 :
    ActualPhysicalGeneralRigidCalibratedCenter Input Physical actualConfiguration
      ⟨center19.1, center19.2⟩ :=
  actualCalibration_of_canonicalFrame center19 FixtureRigidity.rigid19
    canonicalPoint19 canonicalObserved19
    (by rw [canonicalVolume19]; norm_num) canonicalSign19

/-- Actual detected-enumeration calibration at nonroot center 22; the coordinate enumeration
is transported from the exact canonical atom readbacks by the certified per-center reindex. -/
theorem actualCalibration22 :
    ActualPhysicalGeneralRigidCalibratedCenter Input Physical actualConfiguration
      ⟨center22.1, center22.2⟩ :=
  actualCalibration_of_canonicalFrame center22 FixtureRigidity.rigid22
    canonicalPoint22 canonicalObserved22
    (by rw [canonicalVolume22]; norm_num) canonicalSign22

/-- Actual detected-enumeration calibration at nonroot center 26; the coordinate enumeration
is transported from the exact canonical atom readbacks by the certified per-center reindex. -/
theorem actualCalibration26 :
    ActualPhysicalGeneralRigidCalibratedCenter Input Physical actualConfiguration
      ⟨center26.1, center26.2⟩ :=
  actualCalibration_of_canonicalFrame center26 FixtureRigidity.rigid26
    canonicalPoint26 canonicalObserved26
    (by rw [canonicalVolume26]; norm_num) canonicalSign26

/-- Actual detected-enumeration calibration at nonroot center 29; the coordinate enumeration
is transported from the exact canonical atom readbacks by the certified per-center reindex. -/
theorem actualCalibration29 :
    ActualPhysicalGeneralRigidCalibratedCenter Input Physical actualConfiguration
      ⟨center29.1, center29.2⟩ :=
  actualCalibration_of_canonicalFrame center29 FixtureRigidity.rigid29
    canonicalPoint29 canonicalObserved29
    (by rw [canonicalVolume29]; norm_num) canonicalSign29

/-- Calibration data for a priority-ordered actual fixture frame.  This packages only the exact
source-coordinate volume and its matching configuration sign; the accepted inventory separately
proves that the order is the actual neighbor set and that its atomic numbers are distinct. -/
structure PriorityCalibration (order : List (Fin 33)) (volume : ℚ)
    (frame : Equiv.Perm (Fin 4)) : Prop where
  readback : volumeAt order = some volume
  nonzero : volume ≠ 0
  sign_agrees : rationalVolumeSign volume = permHandedness frame

/-- A successful exact volume readback entails that every coordinate lookup in the ordered list
was available. The returned point list is retained explicitly for later frame construction. -/
theorem pointsAt_available_of_volumeAt_eq_some {order : List (Fin 33)} {volume : ℚ}
    (h : volumeAt order = some volume) : ∃ points, pointsAt order = some points := by
  unfold volumeAt at h
  cases hp : pointsAt order with
  | none => simp [hp] at h
  | some points => exact ⟨points, rfl⟩

theorem points4_available : ∃ points, pointsAt atoms4 = some points :=
  pointsAt_available_of_volumeAt_eq_some volume4

theorem points7_available : ∃ points, pointsAt atoms7 = some points :=
  pointsAt_available_of_volumeAt_eq_some volume7

theorem points11_available : ∃ points, pointsAt atoms11 = some points :=
  pointsAt_available_of_volumeAt_eq_some volume11

theorem points14_available : ∃ points, pointsAt atoms14 = some points :=
  pointsAt_available_of_volumeAt_eq_some volume14

theorem points19_available : ∃ points, pointsAt atoms19 = some points :=
  pointsAt_available_of_volumeAt_eq_some volume19

theorem points22_available : ∃ points, pointsAt atoms22 = some points :=
  pointsAt_available_of_volumeAt_eq_some volume22

theorem points26_available : ∃ points, pointsAt atoms26 = some points :=
  pointsAt_available_of_volumeAt_eq_some volume26

theorem points29_available : ∃ points, pointsAt atoms29 = some points :=
  pointsAt_available_of_volumeAt_eq_some volume29

theorem calibration4 : PriorityCalibration atoms4 (-5205250) reverseFrame := by
  refine ⟨volume4, by norm_num, ?_⟩
  rw [rationalVolumeSign_of_neg (by norm_num : (-5205250 : ℚ) < 0), reverseFrame_sign]

theorem calibration7 : PriorityCalibration atoms7 (-5222963) reverseFrame := by
  refine ⟨volume7, by norm_num, ?_⟩
  rw [rationalVolumeSign_of_neg (by norm_num : (-5222963 : ℚ) < 0), reverseFrame_sign]

theorem calibration11 : PriorityCalibration atoms11 5196264 (1 : Equiv.Perm (Fin 4)) := by
  refine ⟨volume11, by norm_num, ?_⟩
  rw [rationalVolumeSign_of_pos (by norm_num : (0 : ℚ) < 5196264)]
  simp

theorem calibration14 : PriorityCalibration atoms14 (-5212558) reverseFrame := by
  refine ⟨volume14, by norm_num, ?_⟩
  rw [rationalVolumeSign_of_neg (by norm_num : (-5212558 : ℚ) < 0), reverseFrame_sign]

theorem calibration19 : PriorityCalibration atoms19 5205250 (1 : Equiv.Perm (Fin 4)) := by
  refine ⟨volume19, by norm_num, ?_⟩
  rw [rationalVolumeSign_of_pos (by norm_num : (0 : ℚ) < 5205250)]
  simp

theorem calibration22 : PriorityCalibration atoms22 5222963 (1 : Equiv.Perm (Fin 4)) := by
  refine ⟨volume22, by norm_num, ?_⟩
  rw [rationalVolumeSign_of_pos (by norm_num : (0 : ℚ) < 5222963)]
  simp

theorem calibration26 : PriorityCalibration atoms26 (-5196264) reverseFrame := by
  refine ⟨volume26, by norm_num, ?_⟩
  rw [rationalVolumeSign_of_neg (by norm_num : (-5196264 : ℚ) < 0), reverseFrame_sign]

theorem calibration29 : PriorityCalibration atoms29 5212558 (1 : Equiv.Perm (Fin 4)) := by
  refine ⟨volume29, by norm_num, ?_⟩
  rw [rationalVolumeSign_of_pos (by norm_num : (0 : ℚ) < 5212558)]
  simp

end FixtureCalibration

assert_kernel_only FixtureCalibration.reverseFrame_sign
assert_kernel_only FixtureCalibration.canonicalNeighborList4
assert_kernel_only FixtureCalibration.canonicalNeighborList7
assert_kernel_only FixtureCalibration.canonicalNeighborList11
assert_kernel_only FixtureCalibration.canonicalNeighborList14
assert_kernel_only FixtureCalibration.canonicalNeighborList19
assert_kernel_only FixtureCalibration.canonicalNeighborList22
assert_kernel_only FixtureCalibration.canonicalNeighborList26
assert_kernel_only FixtureCalibration.canonicalNeighborList29
assert_kernel_only FixtureCalibration.canonicalReindex_actualConfiguration
assert_kernel_only FixtureCalibration.actualCalibration_of_canonicalFrame
assert_kernel_only FixtureCalibration.canonicalLigands4
assert_kernel_only FixtureCalibration.canonicalLigands7
assert_kernel_only FixtureCalibration.canonicalLigands11
assert_kernel_only FixtureCalibration.canonicalLigands14
assert_kernel_only FixtureCalibration.canonicalLigands19
assert_kernel_only FixtureCalibration.canonicalLigands22
assert_kernel_only FixtureCalibration.canonicalLigands26
assert_kernel_only FixtureCalibration.canonicalLigands29
assert_kernel_only FixtureCalibration.canonicalObserved4
assert_kernel_only FixtureCalibration.canonicalObserved7
assert_kernel_only FixtureCalibration.canonicalObserved11
assert_kernel_only FixtureCalibration.canonicalObserved14
assert_kernel_only FixtureCalibration.canonicalObserved19
assert_kernel_only FixtureCalibration.canonicalObserved22
assert_kernel_only FixtureCalibration.canonicalObserved26
assert_kernel_only FixtureCalibration.canonicalObserved29
assert_kernel_only FixtureCalibration.canonicalVolume4
assert_kernel_only FixtureCalibration.canonicalVolume7
assert_kernel_only FixtureCalibration.canonicalVolume11
assert_kernel_only FixtureCalibration.canonicalVolume14
assert_kernel_only FixtureCalibration.canonicalVolume19
assert_kernel_only FixtureCalibration.canonicalVolume22
assert_kernel_only FixtureCalibration.canonicalVolume26
assert_kernel_only FixtureCalibration.canonicalVolume29
assert_kernel_only FixtureCalibration.canonicalSign4
assert_kernel_only FixtureCalibration.canonicalSign7
assert_kernel_only FixtureCalibration.canonicalSign11
assert_kernel_only FixtureCalibration.canonicalSign14
assert_kernel_only FixtureCalibration.canonicalSign19
assert_kernel_only FixtureCalibration.canonicalSign22
assert_kernel_only FixtureCalibration.canonicalSign26
assert_kernel_only FixtureCalibration.canonicalSign29
assert_kernel_only FixtureCalibration.actualCalibration4
assert_kernel_only FixtureCalibration.actualCalibration7
assert_kernel_only FixtureCalibration.actualCalibration11
assert_kernel_only FixtureCalibration.actualCalibration14
assert_kernel_only FixtureCalibration.actualCalibration19
assert_kernel_only FixtureCalibration.actualCalibration22
assert_kernel_only FixtureCalibration.actualCalibration26
assert_kernel_only FixtureCalibration.actualCalibration29
assert_kernel_only FixtureCalibration.pointsAt_available_of_volumeAt_eq_some
assert_kernel_only FixtureCalibration.points4_available
assert_kernel_only FixtureCalibration.points7_available
assert_kernel_only FixtureCalibration.points11_available
assert_kernel_only FixtureCalibration.points14_available
assert_kernel_only FixtureCalibration.points19_available
assert_kernel_only FixtureCalibration.points22_available
assert_kernel_only FixtureCalibration.points26_available
assert_kernel_only FixtureCalibration.points29_available
assert_kernel_only FixtureCalibration.calibration4
assert_kernel_only FixtureCalibration.calibration7
assert_kernel_only FixtureCalibration.calibration11
assert_kernel_only FixtureCalibration.calibration14
assert_kernel_only FixtureCalibration.calibration19
assert_kernel_only FixtureCalibration.calibration22
assert_kernel_only FixtureCalibration.calibration26
assert_kernel_only FixtureCalibration.calibration29
