import TetraStereo.OneCenter.LocalizedCyclicPseudoInputWitness
import TetraStereo.OneCenter.MultiCenterConfiguration
import TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry
import TetraStereo.OneCenter.LocalizedAcyclicPhysicalPseudoFidelity
import TetraStereo.KernelOnly
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

/-!
# Symmetric cyclic fixture for recursive auxiliary stereochemistry

This is the explicit F-to-Cl edit of the certified nine-atom single-bond triangle. Its three
ring carbons have matching Cl/H substituent pairs. No descriptor labels or runtime keys are
supplied here.
-/

namespace TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixture

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.SemanticMolecule
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.OneCenter.MoleculeGraph
open TetraStereo.OneCenter.LocalizedCyclicPseudoInputWitness
open TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry
open TetraStereo.OneCenter.CartesianPoint3

def point (x y z : ℚ) : CartesianPoint3 := { x := x, y := y, z := z }

def P0 : CartesianPoint3 := point 0 0 0
def P1 : CartesianPoint3 := point (-3) (-3) (-3)
def P2 : CartesianPoint3 := point 2 0 0
def P3 : CartesianPoint3 := point (-3) (-3) (-2)
def P4 : CartesianPoint3 := point 0 2 0
def P5 : CartesianPoint3 := point (-3) (-2) (-3)
def P6 : CartesianPoint3 := point (-3) (-3) (-1)
def P7 : CartesianPoint3 := point (-3) (-3) 0
def P8 : CartesianPoint3 := point (-3) (-2) (-2)

def positions : List CartesianPoint3 := [P0, P1, P2, P3, P4, P5, P6, P7, P8]

def symmetricSource : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := [carbon, chlorine, carbon, chlorine, carbon, hydrogen, hydrogen,
          hydrogen, chlorine]
        interactions :=
          [singleBond 0 1, singleBond 0 2, singleBond 0 4, singleBond 0 5,
            singleBond 2 3, singleBond 2 4, singleBond 2 6, singleBond 4 7,
            singleBond 4 8] }
    spatial? := some { positions := positions } }

theorem source_structurallyWellFormed : symmetricSource.structurallyWellFormed? = true := by
  decide +kernel

theorem source_graphReady : symmetricSource.molecule.localizedCIPGraphReady? = true := by
  decide +kernel

theorem source_spatiallyWellFormed : symmetricSource.SpatialIndicesWellFormed := by
  change positions.length = 9
  decide +kernel

def symmetricCertifiedAuthority : CertifiedAuthoritativeChemicalInput :=
  { input := symmetricSource
    structurallyWellFormed :=
      (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff symmetricSource).mp
        source_structurallyWellFormed }

def symmetricCertified : CertifiedLocalizedCIPInput :=
  { certified := symmetricCertifiedAuthority
    graphReady :=
      (symmetricSource.molecule.localizedCIPGraphReady?_eq_true_iff).mp source_graphReady }

theorem atomCount_eq : symmetricSource.molecule.atomCount = 9 := rfl

abbrev graph : MoleculeGraph (Fin 9) := symmetricCertified.moleculeGraph

theorem simple_bonded : graph.SimpleBonded := by
  intro left right adjacent
  fin_cases left <;> fin_cases right <;> first
    | exact absurd adjacent (by decide)
    | decide

theorem atomZ_cases (atom : Fin 9) :
    (graph.atomZ atom = 6 ↔ atom = 0 ∨ atom = 2 ∨ atom = 4) ∧
    (graph.atomZ atom = 17 ↔ atom = 1 ∨ atom = 3 ∨ atom = 8) ∧
    (graph.atomZ atom = 1 ↔ atom = 5 ∨ atom = 6 ∨ atom = 7) := by
  fin_cases atom <;> decide

theorem adj_root (atom : Fin 9) :
    graph.Adj 0 atom ↔ atom = 1 ∨ atom = 2 ∨ atom = 4 ∨ atom = 5 := by
  fin_cases atom <;> decide

theorem adj_arm (atom : Fin 9) :
    graph.Adj 2 atom ↔ atom = 0 ∨ atom = 3 ∨ atom = 4 ∨ atom = 6 := by
  fin_cases atom <;> decide

theorem adj_closing (atom : Fin 9) :
    graph.Adj 4 atom ↔ atom = 0 ∨ atom = 2 ∨ atom = 7 ∨ atom = 8 := by
  fin_cases atom <;> decide

theorem degree_four_iff (atom : Fin 9) :
    atom ∈ graph.tetrahedralCenterSet ↔ atom = 0 ∨ atom = 2 ∨ atom = 4 := by
  fin_cases atom <;> decide

theorem detected_inventory : graph.tetrahedralCenterSet = {0, 2, 4} := by
  ext atom
  simpa [Finset.mem_insert, Finset.mem_singleton] using degree_four_iff atom

/-! ## Explicit S3 symmetries -/

def swap02Fun (atom : Fin 9) : Fin 9 :=
  if atom = 0 then 2 else if atom = 2 then 0
  else if atom = 1 then 3 else if atom = 3 then 1
  else if atom = 5 then 6 else if atom = 6 then 5 else atom

def swap24Fun (atom : Fin 9) : Fin 9 :=
  if atom = 2 then 4 else if atom = 4 then 2
  else if atom = 3 then 8 else if atom = 8 then 3
  else if atom = 6 then 7 else if atom = 7 then 6 else atom

def swap04Fun (atom : Fin 9) : Fin 9 :=
  if atom = 0 then 4 else if atom = 4 then 0
  else if atom = 1 then 8 else if atom = 8 then 1
  else if atom = 5 then 7 else if atom = 7 then 5 else atom

private theorem swap02_involutive : Function.Involutive swap02Fun := by
  intro atom
  fin_cases atom <;> rfl

private theorem swap24_involutive : Function.Involutive swap24Fun := by
  intro atom
  fin_cases atom <;> rfl

private theorem swap04_involutive : Function.Involutive swap04Fun := by
  intro atom
  fin_cases atom <;> rfl

def swap02 : Equiv.Perm (Fin 9) where
  toFun := swap02Fun
  invFun := swap02Fun
  left_inv := swap02_involutive
  right_inv := swap02_involutive

def swap24 : Equiv.Perm (Fin 9) where
  toFun := swap24Fun
  invFun := swap24Fun
  left_inv := swap24_involutive
  right_inv := swap24_involutive

def swap04 : Equiv.Perm (Fin 9) where
  toFun := swap04Fun
  invFun := swap04Fun
  left_inv := swap04_involutive
  right_inv := swap04_involutive

theorem swap02_isAutomorphism : graph.IsAutomorphism swap02 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro atom <;> fin_cases atom <;> decide

theorem swap24_isAutomorphism : graph.IsAutomorphism swap24 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro atom <;> fin_cases atom <;> decide

theorem swap04_isAutomorphism : graph.IsAutomorphism swap04 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro atom <;> fin_cases atom <;> decide

theorem swap02_centers :
    ∀ atom, atom ∈ graph.tetrahedralCenterSet ↔ swap02 atom ∈ graph.tetrahedralCenterSet := by
  intro atom
  rw [degree_four_iff atom, degree_four_iff (swap02 atom)]
  fin_cases atom <;> decide

theorem swap24_centers :
    ∀ atom, atom ∈ graph.tetrahedralCenterSet ↔ swap24 atom ∈ graph.tetrahedralCenterSet := by
  intro atom
  rw [degree_four_iff atom, degree_four_iff (swap24 atom)]
  fin_cases atom <;> decide

theorem swap04_centers :
    ∀ atom, atom ∈ graph.tetrahedralCenterSet ↔ swap04 atom ∈ graph.tetrahedralCenterSet := by
  intro atom
  rw [degree_four_iff atom, degree_four_iff (swap04 atom)]
  fin_cases atom <;> decide

/-! ## The certified canonical frame -/

noncomputable def canon : MultiCenterMolecule (Fin 9) where
  mol := graph
  centers := symmetricCertified.tetrahedralCenterSet
  ligandAtom := fun c hc i => symmetricCertified.canonicalLigandAtom ⟨c, hc⟩ i
  ligandAtom_adj := by
    intro c hc i
    exact symmetricCertified.canonicalLigandAtom_adj ⟨c, hc⟩ i
  ligandAtom_injective := by
    intro c hc
    exact symmetricCertified.canonicalLigandAtom_injective ⟨c, hc⟩
  ligandAtom_surjective := by
    intro c hc v hv
    obtain ⟨i, hi⟩ := (symmetricCertified.canonicalLigandNeighbor_bijective ⟨c, hc⟩).2 ⟨v, hv⟩
    exact ⟨i, congrArg Subtype.val hi⟩

theorem canon_centers : canon.centers = graph.tetrahedralCenterSet := rfl

def center0 : canon.Center := ⟨0, (degree_four_iff 0).mpr (Or.inl rfl)⟩
def center2 : canon.Center := ⟨2, (degree_four_iff 2).mpr (Or.inr (Or.inl rfl))⟩
def center4 : canon.Center := ⟨4, (degree_four_iff 4).mpr (Or.inr (Or.inr rfl))⟩

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

private theorem sorted0 :
    (graph.neighborFinset 0).sort (· ≤ ·) = [1, 2, 4, 5] :=
  sorted_of_neighbors 0 [1, 2, 4, 5] (by decide) (by decide) fun a => by
    rw [adj_root]
    simp [List.mem_cons]

private theorem sorted2 :
    (graph.neighborFinset 2).sort (· ≤ ·) = [0, 3, 4, 6] :=
  sorted_of_neighbors 2 [0, 3, 4, 6] (by decide) (by decide) fun a => by
    rw [adj_arm]
    simp [List.mem_cons]

private theorem sorted4 :
    (graph.neighborFinset 4).sort (· ≤ ·) = [0, 2, 7, 8] :=
  sorted_of_neighbors 4 [0, 2, 7, 8] (by decide) (by decide) fun a => by
    rw [adj_closing]
    simp [List.mem_cons]

private theorem ligand_of_sorted (center : canon.Center) (sorted : List (Fin 9))
    (hlist : (symmetricCertified.moleculeGraph.neighborFinset center.1).sort (· ≤ ·) = sorted)
    (hlength : sorted.length = 4) (index : Fin 4) :
    canon.ligandAtomAt center index = sorted.get (Fin.cast hlength.symm index) := by
  unfold canon MultiCenterMolecule.ligandAtomAt CertifiedLocalizedCIPInput.canonicalLigandAtom
    CertifiedLocalizedCIPInput.canonicalNeighborList
  simp [hlist]
  rfl

theorem ligands0 :
    canon.ligandAtomAt center0 0 = 1 ∧ canon.ligandAtomAt center0 1 = 2 ∧
      canon.ligandAtomAt center0 2 = 4 ∧ canon.ligandAtomAt center0 3 = 5 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simpa using ligand_of_sorted center0 [1, 2, 4, 5] sorted0 rfl _

theorem ligands2 :
    canon.ligandAtomAt center2 0 = 0 ∧ canon.ligandAtomAt center2 1 = 3 ∧
      canon.ligandAtomAt center2 2 = 4 ∧ canon.ligandAtomAt center2 3 = 6 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simpa using ligand_of_sorted center2 [0, 3, 4, 6] sorted2 rfl _

theorem ligands4 :
    canon.ligandAtomAt center4 0 = 0 ∧ canon.ligandAtomAt center4 1 = 2 ∧
      canon.ligandAtomAt center4 2 = 7 ∧ canon.ligandAtomAt center4 3 = 8 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simpa using ligand_of_sorted center4 [0, 2, 7, 8] sorted4 rfl _

def auto02 : canon.Aut := ⟨swap02, ⟨swap02_isAutomorphism, swap02_centers⟩⟩
def auto24 : canon.Aut := ⟨swap24, ⟨swap24_isAutomorphism, swap24_centers⟩⟩
def auto04 : canon.Aut := ⟨swap04, ⟨swap04_isAutomorphism, swap04_centers⟩⟩

theorem auto02_center0 : canon.centerPerm auto02 center0 = center2 := by
  apply Subtype.ext
  rfl

theorem auto24_center0 : canon.centerPerm auto24 center0 = center0 := by
  apply Subtype.ext
  rfl

theorem auto04_center0 : canon.centerPerm auto04 center0 = center4 := by
  apply Subtype.ext
  rfl

theorem auto02_center2 : canon.centerPerm auto02 center2 = center0 := by
  apply Subtype.ext
  rfl

theorem auto24_center2 : canon.centerPerm auto24 center2 = center4 := by
  apply Subtype.ext
  rfl

theorem auto04_center2 : canon.centerPerm auto04 center2 = center2 := by
  apply Subtype.ext
  rfl

theorem auto02_center4 : canon.centerPerm auto02 center4 = center4 := by
  apply Subtype.ext
  rfl

theorem auto24_center4 : canon.centerPerm auto24 center4 = center2 := by
  apply Subtype.ext
  rfl

theorem auto04_center4 : canon.centerPerm auto04 center4 = center0 := by
  apply Subtype.ext
  rfl

private theorem ligandPerm_eq (e : canon.Aut) (source target : canon.Center)
    (centerMap : canon.centerPerm e source = target)
    (slot : Fin 4 → Fin 4)
    (atomMap : ∀ i, canon.ligandAtomAt target (slot i) = e.val (canon.ligandAtomAt source i)) :
    canon.ligandPermAt e source = slot := by
  ext i
  have transported := canon.ligandAtomAt_ligandPermAt (e := e) (c := source) i
  rw [centerMap] at transported
  have indices : canon.ligandPermAt e source i = slot i :=
    canon.ligandAtomAt_injective target (transported.trans (atomMap i).symm)
  exact congrArg Fin.val indices

private def slots02at0 : Fin 4 → Fin 4 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3
private def slots02at2 : Fin 4 → Fin 4 | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2
private def slots02at4 : Fin 4 → Fin 4 | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1
private def slots24at0 : Fin 4 → Fin 4 | 0 => 0 | 1 => 2 | 2 => 1 | 3 => 3
private def slots24at2 : Fin 4 → Fin 4 | 0 => 2 | 1 => 1 | 2 => 0 | 3 => 3
private def slots24at4 : Fin 4 → Fin 4 | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0
private def slots04at0 : Fin 4 → Fin 4 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3
private def slots04at2 : Fin 4 → Fin 4 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3
private def slots04at4 : Fin 4 → Fin 4 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3

theorem slotMap24at0 :
    (canon.ligandPermAt auto24 center0 : Fin 4 → Fin 4) = slots24at0 := by
  exact ligandPerm_eq auto24 center0 center0 (by simpa [MultiCenterMolecule.centerPerm] using auto24_center0)
    slots24at0 (by
      intro i
      fin_cases i <;> simp [slots24at0, auto24, swap24, swap24Fun, ligands0])

theorem slotMap04at2 :
    (canon.ligandPermAt auto04 center2 : Fin 4 → Fin 4) = slots24at2 := by
  exact ligandPerm_eq auto04 center2 center2 (by simpa [MultiCenterMolecule.centerPerm] using auto04_center2)
    slots24at2 (by
      intro i
      fin_cases i <;> simp [slots24at2, auto04, swap04, swap04Fun, ligands2])

theorem slotMap02at4 :
    (canon.ligandPermAt auto02 center4 : Fin 4 → Fin 4) = slots04at4 := by
  exact ligandPerm_eq auto02 center4 center4 (by simpa [MultiCenterMolecule.centerPerm] using auto02_center4)
    slots04at4 (by
      intro i
      fin_cases i <;> simp [slots04at4, auto02, swap02, swap02Fun, ligands4])

private def slotMap24_2 : Fin 4 → Fin 4 | 0 => 0 | 1 => 3 | 2 => 1 | 3 => 2
private def slotMap24_4 : Fin 4 → Fin 4 | 0 => 0 | 1 => 2 | 2 => 3 | 3 => 1
private def slotMap04_0 : Fin 4 → Fin 4 | 0 => 3 | 1 => 1 | 2 => 0 | 3 => 2
private def slotMap04_4 : Fin 4 → Fin 4 | 0 => 2 | 1 => 1 | 2 => 3 | 3 => 0
private def slotMap02_0 : Fin 4 → Fin 4 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3
private def slotMap02_2 : Fin 4 → Fin 4 | 0 => 1 | 1 => 0 | 2 => 2 | 3 => 3

theorem slotMap24at2 :
    (canon.ligandPermAt auto24 center2 : Fin 4 → Fin 4) = slotMap24_2 := by
  exact ligandPerm_eq auto24 center2 center4 auto24_center2 slotMap24_2 (by
    intro i; fin_cases i <;> simp [slotMap24_2, auto24, swap24, swap24Fun, ligands2, ligands4])

theorem slotMap24at4 :
    (canon.ligandPermAt auto24 center4 : Fin 4 → Fin 4) = slotMap24_4 := by
  exact ligandPerm_eq auto24 center4 center2 auto24_center4 slotMap24_4 (by
    intro i; fin_cases i <;> simp [slotMap24_4, auto24, swap24, swap24Fun, ligands4, ligands2])

theorem slotMap04at0 :
    (canon.ligandPermAt auto04 center0 : Fin 4 → Fin 4) = slotMap04_0 := by
  exact ligandPerm_eq auto04 center0 center4 auto04_center0 slotMap04_0 (by
    intro i; fin_cases i <;> simp [slotMap04_0, auto04, swap04, swap04Fun, ligands0, ligands4])

theorem slotMap04at4 :
    (canon.ligandPermAt auto04 center4 : Fin 4 → Fin 4) = slotMap04_4 := by
  exact ligandPerm_eq auto04 center4 center0 auto04_center4 slotMap04_4 (by
    intro i; fin_cases i <;> simp [slotMap04_4, auto04, swap04, swap04Fun, ligands4, ligands0])

theorem slotMap02at0 :
    (canon.ligandPermAt auto02 center0 : Fin 4 → Fin 4) = slotMap02_0 := by
  exact ligandPerm_eq auto02 center0 center2 auto02_center0 slotMap02_0 (by
    intro i; fin_cases i <;> simp [slotMap02_0, auto02, swap02, swap02Fun, ligands0, ligands2])

theorem slotMap02at2 :
    (canon.ligandPermAt auto02 center2 : Fin 4 → Fin 4) = slotMap02_2 := by
  exact ligandPerm_eq auto02 center2 center0 auto02_center2 slotMap02_2 (by
    intro i; fin_cases i <;> simp [slotMap02_2, auto02, swap02, swap02Fun, ligands2, ligands0])

private theorem permParity24at2 : permHandedness (canon.ligandPermAt auto24 center2) = 1 := by
  have h : canon.ligandPermAt auto24 center2 = Equiv.swap 1 2 * Equiv.swap 1 3 := by
    ext i
    rw [slotMap24at2]
    fin_cases i <;> rfl
  rw [h, permHandedness_mul]
  simp [permHandedness, Equiv.Perm.sign_swap (by decide : (1 : Fin 4) ≠ 2),
    Equiv.Perm.sign_swap (by decide : (1 : Fin 4) ≠ 3)]

private theorem permParity24at4 : permHandedness (canon.ligandPermAt auto24 center4) = 1 := by
  have h : canon.ligandPermAt auto24 center4 = Equiv.swap 1 3 * Equiv.swap 1 2 := by
    ext i
    rw [slotMap24at4]
    fin_cases i <;> rfl
  rw [h, permHandedness_mul]
  simp [permHandedness, Equiv.Perm.sign_swap (by decide : (1 : Fin 4) ≠ 3),
    Equiv.Perm.sign_swap (by decide : (1 : Fin 4) ≠ 2)]

private theorem permParity04at0 : permHandedness (canon.ligandPermAt auto04 center0) = 1 := by
  have h : canon.ligandPermAt auto04 center0 = Equiv.swap 0 2 * Equiv.swap 0 3 := by
    ext i
    rw [slotMap04at0]
    fin_cases i <;> rfl
  rw [h, permHandedness_mul]
  simp [permHandedness, Equiv.Perm.sign_swap (by decide : (0 : Fin 4) ≠ 2),
    Equiv.Perm.sign_swap (by decide : (0 : Fin 4) ≠ 3)]

private theorem permParity04at4 : permHandedness (canon.ligandPermAt auto04 center4) = 1 := by
  have h : canon.ligandPermAt auto04 center4 = Equiv.swap 0 3 * Equiv.swap 0 2 := by
    ext i
    rw [slotMap04at4]
    fin_cases i <;> rfl
  rw [h, permHandedness_mul]
  simp [permHandedness, Equiv.Perm.sign_swap (by decide : (0 : Fin 4) ≠ 3),
    Equiv.Perm.sign_swap (by decide : (0 : Fin 4) ≠ 2)]

private theorem permParity02at0 : permHandedness (canon.ligandPermAt auto02 center0) = -1 := by
  have h : canon.ligandPermAt auto02 center0 = Equiv.swap 0 1 := by
    ext i
    rw [slotMap02at0]
    fin_cases i <;> rfl
  rw [h]
  simp [permHandedness, Equiv.Perm.sign_swap (by decide : (0 : Fin 4) ≠ 1)]

private theorem permParity02at2 : permHandedness (canon.ligandPermAt auto02 center2) = -1 := by
  have h : canon.ligandPermAt auto02 center2 = Equiv.swap 0 1 := by
    ext i
    rw [slotMap02at2]
    fin_cases i <;> rfl
  rw [h]
  simp [permHandedness, Equiv.Perm.sign_swap (by decide : (0 : Fin 4) ≠ 1)]

theorem center0_not_constitutionallyRigid : ¬ ConstitutionallyRigid canon center0 := by
  intro rigid
  have h := rigid auto24 (by simpa [MultiCenterMolecule.centerPerm] using auto24_center0)
  have h12 := congrArg (fun p : Equiv.Perm (Fin 4) => p 1) h
  have hne : canon.ligandPermAt auto24 center0 1 ≠ 1 := by
    change ((canon.ligandPermAt auto24 center0 : Fin 4 → Fin 4) 1) ≠ 1
    rw [slotMap24at0]
    decide
  exact hne h12

theorem center2_not_constitutionallyRigid : ¬ ConstitutionallyRigid canon center2 := by
  intro rigid
  have h := rigid auto04 (by simpa [MultiCenterMolecule.centerPerm] using auto04_center2)
  have h02 := congrArg (fun p : Equiv.Perm (Fin 4) => p 0) h
  have hne : canon.ligandPermAt auto04 center2 0 ≠ 0 := by
    change ((canon.ligandPermAt auto04 center2 : Fin 4 → Fin 4) 0) ≠ 0
    rw [slotMap04at2]
    decide
  exact hne h02

theorem center4_not_constitutionallyRigid : ¬ ConstitutionallyRigid canon center4 := by
  intro rigid
  have h := rigid auto02 (by simpa [MultiCenterMolecule.centerPerm] using auto02_center4)
  have h01 := congrArg (fun p : Equiv.Perm (Fin 4) => p 0) h
  have hne : canon.ligandPermAt auto02 center4 0 ≠ 0 := by
    change ((canon.ligandPermAt auto02 center4 : Fin 4 → Fin 4) 0) ≠ 0
    rw [slotMap02at4]
    decide
  exact hne h01

/-! ## One calibrated physical configuration -/

def calibratedCfg : canon.Configuration := fun center =>
  if center.1 = 4 then Equiv.swap 0 1 else 1

theorem cfgSign0 : canon.configurationSign calibratedCfg center0 = 1 := by
  simp [MultiCenterMolecule.configurationSign, calibratedCfg, center0, permHandedness_one]

theorem cfgSign2 : canon.configurationSign calibratedCfg center2 = 1 := by
  simp [MultiCenterMolecule.configurationSign, calibratedCfg, center2, permHandedness_one]

theorem cfgSign4 : canon.configurationSign calibratedCfg center4 = -1 := by
  simp [MultiCenterMolecule.configurationSign, calibratedCfg, center4, permHandedness_swap]

theorem volume0 : orientedVolume P1 P2 P4 P5 = 6 := by
  norm_num [orientedVolume, P1, P2, P4, P5, point]

theorem volume2 : orientedVolume P0 P3 P4 P6 = 6 := by
  norm_num [orientedVolume, P0, P3, P4, P6, point]

theorem volume4 : orientedVolume P0 P2 P7 P8 = -12 := by
  norm_num [orientedVolume, P0, P2, P7, P8, point]

theorem all_frame_volumes_nonzero :
    orientedVolume P1 P2 P4 P5 ≠ 0 ∧
    orientedVolume P0 P3 P4 P6 ≠ 0 ∧
    orientedVolume P0 P2 P7 P8 ≠ 0 := by
  rw [volume0, volume2, volume4]
  norm_num

theorem cfg_calibrated0 :
    canon.configurationSign calibratedCfg center0 =
      if orientedVolume P1 P2 P4 P5 < 0 then (-1 : ℝ) else 1 := by
  rw [volume0, cfgSign0]
  norm_num

theorem cfg_calibrated2 :
    canon.configurationSign calibratedCfg center2 =
      if orientedVolume P0 P3 P4 P6 < 0 then (-1 : ℝ) else 1 := by
  rw [volume2, cfgSign2]
  norm_num

theorem cfg_calibrated4 :
    canon.configurationSign calibratedCfg center4 =
      if orientedVolume P0 P2 P7 P8 < 0 then (-1 : ℝ) else 1 := by
  rw [volume4, cfgSign4]
  norm_num

private theorem edge02 : graph.underlyingSimpleGraph.Adj 0 2 :=
  (graph.underlyingSimpleGraph_adj 0 2).mpr ((adj_root 2).mpr (by simp))

private theorem edge04 : graph.underlyingSimpleGraph.Adj 0 4 :=
  (graph.underlyingSimpleGraph_adj 0 4).mpr ((adj_root 4).mpr (by simp))

private theorem edge24 : graph.underlyingSimpleGraph.Adj 2 4 :=
  (graph.underlyingSimpleGraph_adj 2 4).mpr ((adj_arm 4).mpr (by simp))

private theorem notReachedRoot (root : canon.Center) (i : Fin 4)
    (reached : LigandBranchReaches canon root i root.1) : False := by
  rcases reached with ⟨walk, avoid⟩
  exact avoid walk.end_mem_support

private theorem reaches20 : LigandBranchReaches canon center0 1 center2.1 := by
  unfold LigandBranchReaches
  rw [ligands0.2.1]
  refine ⟨SimpleGraph.Walk.nil, ?_⟩
  simp [center0, center2]

private theorem reaches40 : LigandBranchReaches canon center0 1 center4.1 := by
  unfold LigandBranchReaches
  rw [ligands0.2.1]
  refine ⟨SimpleGraph.Walk.cons edge24 SimpleGraph.Walk.nil, ?_⟩
  simp [center0, center4]

private theorem reaches02 : LigandBranchReaches canon center2 0 center0.1 := by
  unfold LigandBranchReaches
  rw [ligands2.1]
  refine ⟨SimpleGraph.Walk.nil, ?_⟩
  simp [center0, center2]

private theorem reaches42 : LigandBranchReaches canon center2 0 center4.1 := by
  unfold LigandBranchReaches
  rw [ligands2.1]
  refine ⟨SimpleGraph.Walk.cons edge04 SimpleGraph.Walk.nil, ?_⟩
  simp [center2, center4]

private theorem reaches04 : LigandBranchReaches canon center4 0 center0.1 := by
  unfold LigandBranchReaches
  rw [ligands4.1]
  refine ⟨SimpleGraph.Walk.nil, ?_⟩
  simp [center0, center4]

private theorem reaches24 : LigandBranchReaches canon center4 0 center2.1 := by
  unfold LigandBranchReaches
  rw [ligands4.1]
  refine ⟨SimpleGraph.Walk.cons edge02 SimpleGraph.Walk.nil, ?_⟩
  simp [center2, center4]

theorem mirrorTransportAt0 : MirrorTransport canon calibratedCfg center0 1 2 := by
  refine ⟨auto24, ?_, ?_, ?_⟩
  · exact auto24_center0
  · change (canon.ligandPermAt auto24 center0 : Fin 4 → Fin 4) 1 = 2
    rw [slotMap24at0]
    rfl
  · intro d reached
    have members := (degree_four_iff d.1).mp d.2
    rcases members with hr | h2 | h4
    · have heq : d = center0 := Subtype.ext hr
      subst d
      exact False.elim (notReachedRoot center0 1 reached)
    · have heq : d = center2 := Subtype.ext h2
      subst d
      rw [auto24_center2, cfgSign2, cfgSign4, permParity24at2]
      norm_num
    · have heq : d = center4 := Subtype.ext h4
      subst d
      rw [auto24_center4, cfgSign4, cfgSign2, permParity24at4]
      norm_num

theorem mirrorTransportAt2 : MirrorTransport canon calibratedCfg center2 0 2 := by
  refine ⟨auto04, ?_, ?_, ?_⟩
  · exact auto04_center2
  · change (canon.ligandPermAt auto04 center2 : Fin 4 → Fin 4) 0 = 2
    rw [slotMap04at2]
    rfl
  · intro d reached
    have members := (degree_four_iff d.1).mp d.2
    rcases members with h0 | hr | h4
    · have heq : d = center0 := Subtype.ext h0
      subst d
      rw [auto04_center0, cfgSign0, cfgSign4, permParity04at0]
      norm_num
    · have heq : d = center2 := Subtype.ext hr
      subst d
      exact False.elim (notReachedRoot center2 0 reached)
    · have heq : d = center4 := Subtype.ext h4
      subst d
      rw [auto04_center4, cfgSign4, cfgSign0, permParity04at4]
      norm_num

theorem mirrorTransportAt4 : MirrorTransport canon calibratedCfg center4 0 1 := by
  refine ⟨auto02, ?_, ?_, ?_⟩
  · exact auto02_center4
  · change (canon.ligandPermAt auto02 center4 : Fin 4 → Fin 4) 0 = 1
    rw [slotMap02at4]
    rfl
  · intro d reached
    have members := (degree_four_iff d.1).mp d.2
    rcases members with h0 | h2 | hr
    · have heq : d = center0 := Subtype.ext h0
      subst d
      rw [auto02_center0, cfgSign0, cfgSign2, permParity02at0]
      norm_num
    · have heq : d = center2 := Subtype.ext h2
      subst d
      rw [auto02_center2, cfgSign2, cfgSign0, permParity02at2]
      norm_num
    · have heq : d = center4 := Subtype.ext hr
      subst d
      exact False.elim (notReachedRoot center4 0 reached)

end TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixture

assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixture.source_structurallyWellFormed
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixture.source_graphReady
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixture.simple_bonded
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixture.detected_inventory
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixture.swap02_isAutomorphism
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixture.swap24_isAutomorphism
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixture.swap04_isAutomorphism
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixture.source_spatiallyWellFormed
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixture.center0_not_constitutionallyRigid
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixture.center2_not_constitutionallyRigid
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixture.center4_not_constitutionallyRigid
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixture.all_frame_volumes_nonzero
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixture.cfg_calibrated0
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixture.cfg_calibrated2
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixture.cfg_calibrated4
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixture.mirrorTransportAt0
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixture.mirrorTransportAt2
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixture.mirrorTransportAt4
