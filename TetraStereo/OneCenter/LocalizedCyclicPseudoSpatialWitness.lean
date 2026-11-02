import TetraStereo.OneCenter.LocalizedCyclicPseudoInputWitness
import TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry
import TetraStereo.OneCenter.AuthoritativeLocalizedTetrahedralDescriptor
import TetraStereo.KernelOnly
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

/-!
# Physical mirror of the cyclic pseudoasymmetry candidate

The molecule is the admitted nine-atom triangle of
`LocalizedCyclicPseudoInputWitness`. Coordinates are chosen so that the graph mirror
`(x, y, z) ↦ (x, -y, z)` is a Euclidean reflection. Ligands are the executable ascending
index enumeration `canonicalLigandAtom`, not the choice enumeration. The local frames
below are calibrated to the signs of those canonical oriented volumes. No CIP letter is
read off: Rule 5 and `referenceState` are not evaluated.
-/

namespace TetraStereo.OneCenter.LocalizedCyclicPseudoSpatialWitness

open TetraStereo.OneCenter
open AuthoritativeChemicalInput
open CartesianPoint3
open RootedTetrahedralBranchSymmetry
open LocalizedCyclicPseudoInputWitness

def point (x y z : ℚ) : CartesianPoint3 := { x := x, y := y, z := z }

def P0 : CartesianPoint3 := point 0 0 0
def P1 : CartesianPoint3 := point 2 0 (-1)
def P2 : CartesianPoint3 := point 2 2 0
def P3 : CartesianPoint3 := point 4 3 1
def P4 : CartesianPoint3 := point 2 (-2) 0
def P5 : CartesianPoint3 := point 0 0 2
def P6 : CartesianPoint3 := point 3 3 (-1)
def P7 : CartesianPoint3 := point 3 (-3) (-1)
def P8 : CartesianPoint3 := point 4 (-3) 1

def positions : List CartesianPoint3 := [P0, P1, P2, P3, P4, P5, P6, P7, P8]

def pseudoSpatialSource : AuthoritativeChemicalInput :=
  { pseudoSource with spatial? := some { positions := positions } }

theorem spatial_molecule : pseudoSpatialSource.molecule = pseudoSource.molecule := rfl

theorem spatial_structurallyWellFormed :
    pseudoSpatialSource.structurallyWellFormed? = true := by
  decide +kernel

theorem spatial_graphReady :
    pseudoSpatialSource.molecule.localizedCIPGraphReady? = true := by
  simpa [spatial_molecule] using source_graphReady

def pseudoSpatialCertifiedAuthority : CertifiedAuthoritativeChemicalInput :=
  { input := pseudoSpatialSource
    structurallyWellFormed :=
      (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff pseudoSpatialSource).mp
        spatial_structurallyWellFormed }

def pseudoSpatialCertified : CertifiedLocalizedCIPInput :=
  { certified := pseudoSpatialCertifiedAuthority
    graphReady :=
      (pseudoSpatialSource.molecule.localizedCIPGraphReady?_eq_true_iff).mp spatial_graphReady }

noncomputable def canon : MultiCenterMolecule (Fin 9) where
  mol := graph
  centers := pseudoCertified.tetrahedralCenterSet
  ligandAtom := fun c hc i => pseudoCertified.canonicalLigandAtom ⟨c, hc⟩ i
  ligandAtom_adj := by
    intro c hc i
    exact pseudoCertified.canonicalLigandAtom_adj ⟨c, hc⟩ i
  ligandAtom_injective := by
    intro c hc
    exact pseudoCertified.canonicalLigandAtom_injective ⟨c, hc⟩
  ligandAtom_surjective := by
    intro c hc v hv
    obtain ⟨index, hindex⟩ :=
      (pseudoCertified.canonicalLigandNeighbor_bijective ⟨c, hc⟩).2 ⟨v, hv⟩
    exact ⟨index, congrArg Subtype.val hindex⟩

theorem canon_centers : canon.centers = graph.tetrahedralCenterSet := rfl

def rootCenter : canon.Center := ⟨0, (degree_four_iff 0).mpr (Or.inl rfl)⟩
def armCenter : canon.Center := ⟨2, (degree_four_iff 2).mpr (Or.inr (Or.inl rfl))⟩
def closingCenter : canon.Center := ⟨4, (degree_four_iff 4).mpr (Or.inr (Or.inr rfl))⟩

private theorem sorted_of_neighbors (center : Fin 9) (atoms : List (Fin 9))
    (nodup : atoms.Nodup) (pairwise : atoms.Pairwise (· ≤ ·))
    (members : ∀ atom : Fin 9, graph.Adj center atom ↔ atom ∈ atoms) :
    (graph.neighborFinset center).sort (· ≤ ·) = atoms := by
  have finsetEq : graph.neighborFinset center = atoms.toFinset := by
    ext atom
    simp only [MoleculeGraph.mem_neighborFinset, List.mem_toFinset]
    exact members atom
  rw [finsetEq]
  exact ((List.toFinset_sort (· ≤ ·) nodup).mpr pairwise)

private theorem root_sorted :
    (graph.neighborFinset 0).sort (· ≤ ·) = [1, 2, 4, 5] :=
  sorted_of_neighbors 0 [1, 2, 4, 5] (by decide) (by decide) fun atom => by
    rw [adj_root]
    simp [List.mem_cons]

private theorem arm_sorted :
    (graph.neighborFinset 2).sort (· ≤ ·) = [0, 3, 4, 6] :=
  sorted_of_neighbors 2 [0, 3, 4, 6] (by decide) (by decide) fun atom => by
    rw [adj_arm]
    simp [List.mem_cons]

private theorem closing_sorted :
    (graph.neighborFinset 4).sort (· ≤ ·) = [0, 2, 7, 8] :=
  sorted_of_neighbors 4 [0, 2, 7, 8] (by decide) (by decide) fun atom => by
    rw [adj_closing]
    simp [List.mem_cons]

private theorem ligand_of_sorted (center : canon.Center) (sorted : List (Fin 9))
    (hlist : (pseudoCertified.moleculeGraph.neighborFinset center.1).sort (· ≤ ·) = sorted)
    (hlength : sorted.length = 4) (index : Fin 4) :
    canon.ligandAtomAt center index =
      sorted.get (Fin.cast hlength.symm index) := by
  unfold canon MultiCenterMolecule.ligandAtomAt CertifiedLocalizedCIPInput.canonicalLigandAtom
    CertifiedLocalizedCIPInput.canonicalNeighborList
  simp [hlist]
  rfl

theorem root_ligands :
    canon.ligandAtomAt rootCenter 0 = 1 ∧ canon.ligandAtomAt rootCenter 1 = 2 ∧
      canon.ligandAtomAt rootCenter 2 = 4 ∧ canon.ligandAtomAt rootCenter 3 = 5 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using ligand_of_sorted rootCenter [1, 2, 4, 5] root_sorted rfl 0
  · simpa using ligand_of_sorted rootCenter [1, 2, 4, 5] root_sorted rfl 1
  · simpa using ligand_of_sorted rootCenter [1, 2, 4, 5] root_sorted rfl 2
  · simpa using ligand_of_sorted rootCenter [1, 2, 4, 5] root_sorted rfl 3

theorem arm_ligands :
    canon.ligandAtomAt armCenter 0 = 0 ∧ canon.ligandAtomAt armCenter 1 = 3 ∧
      canon.ligandAtomAt armCenter 2 = 4 ∧ canon.ligandAtomAt armCenter 3 = 6 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using ligand_of_sorted armCenter [0, 3, 4, 6] arm_sorted rfl 0
  · simpa using ligand_of_sorted armCenter [0, 3, 4, 6] arm_sorted rfl 1
  · simpa using ligand_of_sorted armCenter [0, 3, 4, 6] arm_sorted rfl 2
  · simpa using ligand_of_sorted armCenter [0, 3, 4, 6] arm_sorted rfl 3

theorem closing_ligands :
    canon.ligandAtomAt closingCenter 0 = 0 ∧ canon.ligandAtomAt closingCenter 1 = 2 ∧
      canon.ligandAtomAt closingCenter 2 = 7 ∧ canon.ligandAtomAt closingCenter 3 = 8 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using ligand_of_sorted closingCenter [0, 2, 7, 8] closing_sorted rfl 0
  · simpa using ligand_of_sorted closingCenter [0, 2, 7, 8] closing_sorted rfl 1
  · simpa using ligand_of_sorted closingCenter [0, 2, 7, 8] closing_sorted rfl 2
  · simpa using ligand_of_sorted closingCenter [0, 2, 7, 8] closing_sorted rfl 3

/-- Local frames whose signs equal the canonical-enumeration volume signs. -/
def pseudoCfg : canon.Configuration :=
  fun center => if center.1 = 2 then Equiv.swap 0 1 else 1

theorem root_configurationSign : canon.configurationSign pseudoCfg rootCenter = 1 := by
  simp [MultiCenterMolecule.configurationSign, pseudoCfg, rootCenter, permHandedness_one]

theorem arm_configurationSign : canon.configurationSign pseudoCfg armCenter = -1 := by
  simp [MultiCenterMolecule.configurationSign, pseudoCfg, armCenter, permHandedness_swap]

theorem closing_configurationSign : canon.configurationSign pseudoCfg closingCenter = 1 := by
  simp [MultiCenterMolecule.configurationSign, pseudoCfg, closingCenter, permHandedness_one]

theorem root_volume : orientedVolume P1 P2 P4 P5 = 8 := by
  simp only [orientedVolume, P1, P2, P4, P5, point]
  norm_num

theorem arm_volume : orientedVolume P0 P3 P4 P6 = -26 := by
  simp only [orientedVolume, P0, P3, P4, P6, point]
  norm_num

theorem closing_volume : orientedVolume P0 P2 P7 P8 = 26 := by
  simp only [orientedVolume, P0, P2, P7, P8, point]
  norm_num

theorem root_calibrated :
    canon.configurationSign pseudoCfg rootCenter =
      if orientedVolume P1 P2 P4 P5 < 0 then (-1 : ℝ) else 1 := by
  rw [root_volume, root_configurationSign]
  norm_num

theorem arm_calibrated :
    canon.configurationSign pseudoCfg armCenter =
      if orientedVolume P0 P3 P4 P6 < 0 then (-1 : ℝ) else 1 := by
  rw [arm_volume, arm_configurationSign]
  norm_num

theorem closing_calibrated :
    canon.configurationSign pseudoCfg closingCenter =
      if orientedVolume P0 P2 P7 P8 < 0 then (-1 : ℝ) else 1 := by
  rw [closing_volume, closing_configurationSign]
  norm_num

def reflect (p : CartesianPoint3) : CartesianPoint3 :=
  { x := p.x, y := -p.y, z := p.z }

/-- The coordinate table is the graph mirror realized by reflection through the xz-plane. -/
theorem coordinate_mirror (atom : Fin 9) :
    reflect (positions.get (Fin.cast (by rfl) atom)) =
      positions.get (Fin.cast (by rfl) (mirrorPerm atom)) := by
  fin_cases atom <;> rfl

private theorem mirror_preserves : canon.PreservesCenters mirrorPerm := by
  intro atom
  rw [canon_centers]
  rw [degree_four_iff atom, degree_four_iff (mirrorPerm atom)]
  fin_cases atom <;> simp [mirrorPerm_apply, mirrorFun]

def canonMirror : canon.Aut :=
  ⟨mirrorPerm, ⟨mirror_isAutomorphism, mirror_preserves⟩⟩

private def graphAutOf (automorphism : canon.Aut) : graph.Aut :=
  ⟨automorphism.1, automorphism.2.1⟩

theorem canon_automorphism_dichotomy (automorphism : canon.Aut) :
    automorphism = 1 ∨ automorphism = canonMirror := by
  rcases automorphism_dichotomy (graphAutOf automorphism) with identity | mirrored
  · left
    apply Subtype.ext
    exact identity
  · right
    apply Subtype.ext
    exact mirrored

private def rootSlotPerm : Equiv.Perm (Fin 4) := Equiv.swap 1 2

private def armSlotFun : Fin 4 → Fin 4
  | 0 => 0
  | 1 => 3
  | 2 => 1
  | 3 => 2

private def armSlotInv : Fin 4 → Fin 4
  | 0 => 0
  | 1 => 2
  | 2 => 3
  | 3 => 1

private def armSlotPerm : Equiv.Perm (Fin 4) where
  toFun := armSlotFun
  invFun := armSlotInv
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

private def closingSlotPerm : Equiv.Perm (Fin 4) := armSlotPerm⁻¹

private theorem rootSlotPerm_sign : permHandedness rootSlotPerm = -1 := by
  simp [rootSlotPerm, permHandedness, Equiv.Perm.sign_swap (by decide : (1 : Fin 4) ≠ 2)]

private theorem armSlotPerm_decomposition :
    armSlotPerm = Equiv.swap 1 2 * Equiv.swap 1 3 := by
  ext i
  fin_cases i <;> simp [armSlotPerm, armSlotFun, Equiv.swap_apply_def]

private theorem armSlotPerm_sign : permHandedness armSlotPerm = 1 := by
  rw [armSlotPerm_decomposition, permHandedness_mul]
  simp [permHandedness, Equiv.Perm.sign_swap (by decide : (1 : Fin 4) ≠ 3),
    Equiv.Perm.sign_swap (by decide : (1 : Fin 4) ≠ 2)]

private theorem closingSlotPerm_sign : permHandedness closingSlotPerm = 1 := by
  simp [closingSlotPerm, permHandedness_inv, armSlotPerm_sign]

private theorem centerPerm_root :
    canon.centerPerm canonMirror rootCenter = rootCenter :=
  (centerPerm_eq_iff canon canonMirror rootCenter).mpr rfl

private theorem centerPerm_arm :
    canon.centerPerm canonMirror armCenter = closingCenter := by
  apply Subtype.ext
  simp [MultiCenterMolecule.centerPerm, canonMirror, armCenter, closingCenter, mirrorFun]

private theorem centerPerm_closing :
    canon.centerPerm canonMirror closingCenter = armCenter := by
  apply Subtype.ext
  simp [MultiCenterMolecule.centerPerm, canonMirror, armCenter, closingCenter, mirrorFun]

private theorem mirror_root_perm :
    canon.ligandPermAt canonMirror rootCenter = rootSlotPerm := by
  ext i
  apply congrArg Fin.val
  apply canon.ligandAtomAt_injective rootCenter
  have transported := canon.ligandAtomAt_ligandPermAt (e := canonMirror) (c := rootCenter) i
  rw [centerPerm_root] at transported
  rw [transported]
  fin_cases i <;> simp [canonMirror, mirrorFun, rootSlotPerm, Equiv.swap_apply_def, root_ligands]

private theorem mirror_arm_perm :
    canon.ligandPermAt canonMirror armCenter = armSlotPerm := by
  ext i
  apply congrArg Fin.val
  apply canon.ligandAtomAt_injective closingCenter
  have transported := canon.ligandAtomAt_ligandPermAt (e := canonMirror) (c := armCenter) i
  rw [centerPerm_arm] at transported
  rw [transported]
  fin_cases i <;> simp [canonMirror, mirrorFun, armSlotPerm, armSlotFun, arm_ligands, closing_ligands]

private theorem mirror_closing_perm :
    canon.ligandPermAt canonMirror closingCenter = closingSlotPerm := by
  ext i
  apply congrArg Fin.val
  apply canon.ligandAtomAt_injective armCenter
  have transported := canon.ligandAtomAt_ligandPermAt (e := canonMirror) (c := closingCenter) i
  rw [centerPerm_closing] at transported
  rw [transported]
  fin_cases i
  · have slot : closingSlotPerm 0 = 0 := rfl
    simp [slot, canonMirror, mirrorFun, closing_ligands, arm_ligands]
  · have slot : closingSlotPerm 1 = 2 := rfl
    simp [slot, canonMirror, mirrorFun, closing_ligands, arm_ligands]
  · have slot : closingSlotPerm 2 = 3 := rfl
    simp [slot, canonMirror, mirrorFun, closing_ligands, arm_ligands]
  · have slot : closingSlotPerm 3 = 1 := rfl
    simp [slot, canonMirror, mirrorFun, closing_ligands, arm_ligands]

theorem mirror_root_slot :
    canon.ligandPermAt canonMirror rootCenter 1 = 2 := by
  simp [mirror_root_perm, rootSlotPerm]

theorem mirror_handedness_arm :
    permHandedness (canon.ligandPermAt canonMirror armCenter) = 1 := by
  simp [mirror_arm_perm, armSlotPerm_sign]

theorem mirror_handedness_closing :
    permHandedness (canon.ligandPermAt canonMirror closingCenter) = 1 := by
  simp [mirror_closing_perm, closingSlotPerm_sign]

private theorem root_not_reached {index : Fin 4}
    (reached : LigandBranchReaches canon rootCenter index rootCenter.1) : False := by
  rcases reached with ⟨walk, avoid⟩
  exact avoid walk.end_mem_support

private theorem reach_arm :
    LigandBranchReaches canon rootCenter 1 armCenter.1 := by
  have start : canon.ligandAtomAt rootCenter 1 = armCenter.1 := root_ligands.2.1
  simpa [start] using ligandBranchReaches_self canon rootCenter 1

private theorem reach_closing :
    LigandBranchReaches canon rootCenter 1 closingCenter.1 := by
  have start : canon.ligandAtomAt rootCenter 1 = (2 : Fin 9) := root_ligands.2.1
  unfold LigandBranchReaches
  rw [start]
  refine ⟨SimpleGraph.Walk.cons ?edge SimpleGraph.Walk.nil, ?avoid⟩
  · exact (graph.underlyingSimpleGraph_adj 2 4).mpr ((adj_arm 4).mpr (by simp))
  · intro member
    simp [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] at member
    rcases member with equal | equal <;> exact absurd equal (by decide)

theorem mirror_transport :
    MirrorTransport canon pseudoCfg rootCenter 1 2 := by
  refine ⟨canonMirror, centerPerm_root, mirror_root_slot, ?signs⟩
  intro center reached
  have membership := (degree_four_iff center.1).mp center.2
  rcases membership with rootEq | armEq | closingEq
  · exfalso
    rcases reached with ⟨walk, avoid⟩
    exact avoid (by simpa [rootEq] using walk.end_mem_support)
  · have centerEq : center = armCenter := Subtype.ext armEq
    have imageEq : canon.centerPerm canonMirror armCenter = closingCenter := by
      simpa [centerEq] using centerPerm_arm
    rw [centerEq, imageEq, arm_configurationSign, closing_configurationSign,
      mirror_handedness_arm]
    norm_num
  · have centerEq : center = closingCenter := Subtype.ext closingEq
    have imageEq : canon.centerPerm canonMirror closingCenter = armCenter := by
      simpa [centerEq] using centerPerm_closing
    rw [centerEq, imageEq, arm_configurationSign, closing_configurationSign,
      mirror_handedness_closing]
    norm_num

private theorem identity_root_slot (automorphism : canon.Aut)
    (identity : automorphism = 1) :
    canon.ligandPermAt automorphism rootCenter 1 = 1 := by
  rw [identity]
  simp [canon.ligandPermAt_one, Equiv.Perm.one_apply]

theorem not_proper_transport :
    ¬ ProperTransport canon pseudoCfg rootCenter 1 2 := by
  intro transport
  rcases transport with ⟨automorphism, _fixed, sends, signs⟩
  rcases canon_automorphism_dichotomy automorphism with identity | mirrored
  · rw [identity_root_slot automorphism identity] at sends
    exact absurd sends (by decide : (1 : Fin 4) ≠ 2)
  · have reached := reach_arm
    have equation := signs armCenter reached
    rw [mirrored, centerPerm_arm, arm_configurationSign, closing_configurationSign,
      mirror_handedness_arm] at equation
    norm_num at equation

theorem enantiomorphic_ring_carbons :
    Enantiomorphic canon pseudoCfg rootCenter 1 2 :=
  ⟨by decide, mirror_transport, not_proper_transport⟩

private theorem reach_arm_from_closing_slot :
    LigandBranchReaches canon rootCenter 2 armCenter.1 := by
  have start : canon.ligandAtomAt rootCenter 2 = (4 : Fin 9) := root_ligands.2.2.1
  unfold LigandBranchReaches
  rw [start]
  refine ⟨SimpleGraph.Walk.cons ?edge SimpleGraph.Walk.nil, ?avoid⟩
  · exact (graph.underlyingSimpleGraph_adj 4 2).mpr ((adj_closing 2).mpr (by simp))
  · intro member
    simp [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil] at member
    rcases member with equal | equal <;> exact absurd equal (by decide)

theorem not_pairwise_disjoint :
    ¬ PairwiseDisjointLigandBranches canon rootCenter := by
  intro disjoint
  exact disjoint 1 2 (by decide) armCenter.1 reach_arm reach_arm_from_closing_slot

/-- A non-root center fixed by a multi-center automorphism is fixed ligandwise. -/
theorem nonroot_constitutionally_rigid (automorphism : canon.Aut) :
    (canon.centerPerm automorphism armCenter = armCenter →
      canon.ligandPermAt automorphism armCenter = 1) ∧
    (canon.centerPerm automorphism closingCenter = closingCenter →
      canon.ligandPermAt automorphism closingCenter = 1) := by
  constructor
  · intro fixed
    ext index
    simp only [Equiv.Perm.one_apply]
    apply congrArg Fin.val
    apply canon.ligandAtomAt_injective armCenter
    have transported :=
      canon.ligandAtomAt_ligandPermAt (e := automorphism) (c := armCenter) index
    rw [fixed] at transported
    have neighborFixed :=
      (nonroot_rigid (graphAutOf automorphism)).1
        ((centerPerm_eq_iff canon automorphism armCenter).mp fixed)
        (canon.ligandAtomAt armCenter index)
        (canon.ligandAtomAt_adj armCenter index)
    simp only [graphAutOf] at neighborFixed
    rw [neighborFixed] at transported
    exact transported
  · intro fixed
    ext index
    simp only [Equiv.Perm.one_apply]
    apply congrArg Fin.val
    apply canon.ligandAtomAt_injective closingCenter
    have transported :=
      canon.ligandAtomAt_ligandPermAt (e := automorphism) (c := closingCenter) index
    rw [fixed] at transported
    have neighborFixed :=
      (nonroot_rigid (graphAutOf automorphism)).2
        ((centerPerm_eq_iff canon automorphism closingCenter).mp fixed)
        (canon.ligandAtomAt closingCenter index)
        (canon.ligandAtomAt_adj closingCenter index)
    simp only [graphAutOf] at neighborFixed
    rw [neighborFixed] at transported
    exact transported

end TetraStereo.OneCenter.LocalizedCyclicPseudoSpatialWitness

assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoSpatialWitness.spatial_structurallyWellFormed
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoSpatialWitness.spatial_graphReady
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoSpatialWitness.root_volume
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoSpatialWitness.arm_volume
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoSpatialWitness.closing_volume
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoSpatialWitness.root_calibrated
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoSpatialWitness.arm_calibrated
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoSpatialWitness.closing_calibrated
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoSpatialWitness.coordinate_mirror
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoSpatialWitness.enantiomorphic_ring_carbons
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoSpatialWitness.not_pairwise_disjoint
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoSpatialWitness.nonroot_constitutionally_rigid
