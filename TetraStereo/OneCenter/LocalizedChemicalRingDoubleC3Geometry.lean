import TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Physical
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! The physical distinction of the two cyclic branches is read from actual coordinates.
All centers are the certified degree-four inventory and all ligand frames are its canonical
enumerations. No generated auxiliary labels or runtime ordering are assumed. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Geometry

open LocalizedChemicalRingDoubleC3Input LocalizedChemicalRingDoubleC3Physical
open LocalizedActualPhysicalBranchDecision RootedTetrahedralBranchSymmetry
open LocalizedRecursiveAuxiliaryPhysicalDomain

def points0 : Fin 4 → CartesianPoint3 := ![point 0 0 0, point 1 0 0, point 0 1 0, point 0 0 1]
def pointsL : Fin 4 → CartesianPoint3 := ![point 0 1 0, point 2 1 0, point 0 3 0, point 0 1 2]
def pointsR (opposite : Bool) : Fin 4 → CartesianPoint3 :=
  ![point 0 0 1, point 3 0 1,
    if opposite then point 0 0 4 else point 0 3 1,
    if opposite then point 0 3 1 else point 0 0 4]

theorem observed0 (opposite : Bool) (i : Fin 4) :
    (certified opposite).spatialPointAt? (canon.ligandAtomAt center0 i) = some (points0 i) := by
  rw [ligands0]
  fin_cases i <;> rfl
theorem observedL (opposite : Bool) (i : Fin 4) :
    (certified opposite).spatialPointAt? (canon.ligandAtomAt centerL i) = some (pointsL i) := by
  rw [ligandsL]
  fin_cases i <;> rfl
theorem observedR (opposite : Bool) (i : Fin 4) :
    (certified opposite).spatialPointAt? (canon.ligandAtomAt centerR i) = some (pointsR opposite i) := by
  rw [ligandsR]
  fin_cases i <;> rfl

theorem volume0 (opposite : Bool) : coordinateVolume? (certified opposite) center0 = some (-1) := by
  have obs : ∀ i, (certified opposite).spatialPointAt?
      ((actualCanonicalMolecule (certified opposite)).ligandAtomAt center0 i) = some (points0 i) :=
    observed0 opposite
  simp only [coordinateVolume?, obs, Option.bind_eq_bind, Option.bind_some]
  norm_num [points0, point, CartesianPoint3.orientedVolume, Matrix.cons_val_two, Matrix.cons_val_three]
theorem volumeL (opposite : Bool) : coordinateVolume? (certified opposite) centerL = some (-8) := by
  have obs : ∀ i, (certified opposite).spatialPointAt?
      ((actualCanonicalMolecule (certified opposite)).ligandAtomAt centerL i) = some (pointsL i) :=
    observedL opposite
  simp only [coordinateVolume?, obs, Option.bind_eq_bind, Option.bind_some]
  norm_num [pointsL, point, CartesianPoint3.orientedVolume, Matrix.cons_val_two, Matrix.cons_val_three]
theorem volumeR (opposite : Bool) :
    coordinateVolume? (certified opposite) centerR = some (if opposite then 27 else -27) := by
  have obs : ∀ i, (certified opposite).spatialPointAt?
      ((actualCanonicalMolecule (certified opposite)).ligandAtomAt centerR i) = some (pointsR opposite i) :=
    observedR opposite
  simp only [coordinateVolume?, obs, Option.bind_eq_bind, Option.bind_some]
  cases opposite <;>
    norm_num [pointsR, point, CartesianPoint3.orientedVolume, Matrix.cons_val_two, Matrix.cons_val_three]

def canonicalCfg (opposite : Bool) : canon.Configuration := coordinateCfg (certified opposite)

theorem canonical_calibrated (opposite : Bool) (c : canon.Center) :
    ActualPhysicalCalibratedCoordinates (certified opposite) canon (canonicalCfg opposite) c := by
  rcases center_cases c with same | same | same
  · subst c
    exact coordinateCfg_calibrated (certified opposite) center0 points0 (observed0 opposite)
      (by decide +kernel)
  · subst c
    exact coordinateCfg_calibrated (certified opposite) centerL pointsL (observedL opposite)
      (by decide +kernel)
  · subst c
    exact coordinateCfg_calibrated (certified opposite) centerR (pointsR opposite) (observedR opposite)
      (by cases opposite <;> decide +kernel)

theorem left_sign (opposite : Bool) : canon.configurationSign (canonicalCfg opposite) centerL = -1 := by
  norm_num [MultiCenterMolecule.configurationSign, canonicalCfg, coordinateCfg, volumeL, permHandedness,
    Equiv.Perm.sign_swap (show (0 : Fin 4) ≠ 1 by decide)]
theorem right_sign (opposite : Bool) :
    canon.configurationSign (canonicalCfg opposite) centerR = if opposite then 1 else -1 := by
  cases opposite <;>
    norm_num [MultiCenterMolecule.configurationSign, canonicalCfg, coordinateCfg, volumeR,
      permHandedness, Equiv.Perm.sign_swap (show (0 : Fin 4) ≠ 1 by decide)]

/-- The coordinate change makes the two cyclic branches mirror-related but not properly
equivalent under the independent physical relation. -/
theorem opposite_enantiomorphic : Enantiomorphic canon (canonicalCfg true) center0 2 3 :=
  enantiomorphic_of_opposite (canonicalCfg true) (by rw [left_sign, right_sign]; norm_num)

theorem equal_proper : ProperTransport canon (canonicalCfg false) center0 2 3 :=
  (proper_transport_iff (canonicalCfg false)).mpr (by rw [left_sign, right_sign]; rfl)

private theorem pair_cases (cfg : canon.Configuration) (i j : Fin 4) (sense : Bool)
    (transport : BranchTransport canon cfg center0 i j sense) :
    i = j ∨ (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) := by
  obtain ⟨e, fixed, sent, _⟩ := transport
  have atoms := canon.ligandAtomAt_ligandPermAt e center0 i
  rw [fixed, sent] at atoms
  let graphAut : graph.Aut :=
    ⟨(e : Equiv.Perm (certified false).Atom), MultiCenterMolecule.Aut.mem_molAut (m := canon) e⟩
  have z := MoleculeGraph.Aut.atomZ_eq (m := graph) graphAut (canon.ligandAtomAt center0 i)
  change graph.atomZ ((e : Equiv.Perm (certified false).Atom) (canon.ligandAtomAt center0 i)) =
    graph.atomZ (canon.ligandAtomAt center0 i) at z
  rw [← atoms, ligands0, ligands0] at z
  have finite : ∀ i j : Fin 4, graph.atomZ (frame0 j) = graph.atomZ (frame0 i) →
      i = j ∨ (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) := by decide +kernel
  exact finite i j z

theorem opposite_proper_distinct :
    canon.PairwiseProperDistinguishable (canonicalCfg true) center0 := by
  intro i j different proper
  rcases pair_cases (canonicalCfg true) i j false proper with same | pair | pair
  · exact different same
  · obtain ⟨rfl, rfl⟩ := pair
    exact opposite_enantiomorphic.2.2 proper
  · obtain ⟨rfl, rfl⟩ := pair
    exact (enantiomorphic_symm canon (canonicalCfg true) center0 opposite_enantiomorphic).2.2 proper

theorem opposite_pair_iff (i j : Fin 4) :
    Enantiomorphic canon (canonicalCfg true) center0 i j ↔
      (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) := by
  constructor
  · intro pair
    rcases pair_cases (canonicalCfg true) i j true pair.2.1 with same | direct | reverse
    · exact False.elim (pair.1 same)
    · exact Or.inl direct
    · exact Or.inr reverse
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact opposite_enantiomorphic
    · exact enantiomorphic_symm canon (canonicalCfg true) center0 opposite_enantiomorphic

theorem opposite_pair_count : physicalEnantiomorphicPairCount canon (canonicalCfg true) center0 = 1 := by
  classical
  unfold physicalEnantiomorphicPairCount
  rw [sourceEnantiomorphicPairCount_congr _
    (fun i j : Fin 4 => (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2)) (fun i j _ => opposite_pair_iff i j)]
  norm_num [sourceEnantiomorphicPairCount, Fin.ext_iff]

end TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Geometry

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Geometry.canonical_calibrated
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Geometry.left_sign
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Geometry.right_sign
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Geometry.opposite_enantiomorphic
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Geometry.equal_proper
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Geometry.opposite_proper_distinct
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Geometry.opposite_pair_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Geometry.opposite_pair_count
