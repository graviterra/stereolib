import TetraStereo.OneCenter.AuthoritativeLocalizedCIPAnalysis
import TetraStereo.KernelOnly
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 4096

/-!
# Admitted single-bond cyclic pseudoasymmetry candidate

Nine explicit atoms and one triangle `0–2–4–0`. Atom `8` is chlorine, where the
accepted nine-atom ring had a second hydrogen on atom `4`. The root carries
fluorine and hydrogen. Each other ring carbon carries one chlorine and one
hydrogen.

The graph automorphism exchanges `2 ↔ 4`, `3 ↔ 8`, and `6 ↔ 7`, and fixes
`0`, `1`, and `5`. Both non-root degree-four centers are rigid under that group.
The root is not. No descriptor and no coordinate is read here.
-/

namespace TetraStereo.OneCenter.LocalizedCyclicPseudoInputWitness

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.SemanticMolecule
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.OneCenter.MoleculeGraph

def element (atomicNumber : ℕ) (positive : 0 < atomicNumber)
    (bounded : atomicNumber ≤ 118) : PeriodicElement :=
  { atomicNumber := atomicNumber, positive := positive, atMost118 := bounded }

def carbon : SemanticAtom := { element := element 6 (by decide) (by decide) }
def hydrogen : SemanticAtom := { element := element 1 (by decide) (by decide) }
def fluorine : SemanticAtom := { element := element 9 (by decide) (by decide) }
def chlorine : SemanticAtom := { element := element 17 (by decide) (by decide) }

def singleBond (left right : ℕ) : SemanticInteraction :=
  { participants := [left, right], kind := .covalent 1 }

/-- Root `0` with fluorine `1` and hydrogen `5`; arm `2` with chlorine `3` and
hydrogen `6`; closing carbon `4` with hydrogen `7` and chlorine `8`. -/
def pseudoSource : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := [carbon, fluorine, carbon, chlorine, carbon, hydrogen, hydrogen,
          hydrogen, chlorine]
        interactions :=
          [singleBond 0 1, singleBond 0 2, singleBond 0 4, singleBond 0 5,
            singleBond 2 3, singleBond 2 4, singleBond 2 6, singleBond 4 7,
            singleBond 4 8] } }

theorem source_structurallyWellFormed : pseudoSource.structurallyWellFormed? = true := by
  decide +kernel

theorem source_graphReady : pseudoSource.molecule.localizedCIPGraphReady? = true := by
  decide +kernel

def pseudoCertifiedAuthority : CertifiedAuthoritativeChemicalInput :=
  { input := pseudoSource
    structurallyWellFormed :=
      (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff pseudoSource).mp
        source_structurallyWellFormed }

def pseudoCertified : CertifiedLocalizedCIPInput :=
  { certified := pseudoCertifiedAuthority
    graphReady :=
      (pseudoSource.molecule.localizedCIPGraphReady?_eq_true_iff).mp source_graphReady }

theorem atomCount_eq : pseudoSource.molecule.atomCount = 9 := rfl

abbrev graph : MoleculeGraph (Fin 9) := pseudoCertified.moleculeGraph

theorem simple_bonded : graph.SimpleBonded := by
  intro left right adjacent
  fin_cases left <;> fin_cases right <;> first
    | exact absurd adjacent (by decide)
    | decide

theorem z_fluorine (atom : Fin 9) : graph.atomZ atom = 9 ↔ atom = 1 := by
  fin_cases atom <;> decide

theorem z_carbon (atom : Fin 9) : graph.atomZ atom = 6 ↔ atom = 0 ∨ atom = 2 ∨ atom = 4 := by
  fin_cases atom <;> decide

theorem z_chlorine (atom : Fin 9) : graph.atomZ atom = 17 ↔ atom = 3 ∨ atom = 8 := by
  fin_cases atom <;> decide

theorem z_hydrogen (atom : Fin 9) : graph.atomZ atom = 1 ↔ atom = 5 ∨ atom = 6 ∨ atom = 7 := by
  fin_cases atom <;> decide

theorem adj_fluorine (atom : Fin 9) : graph.Adj 1 atom ↔ atom = 0 := by
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

/-- The detected inventory is exactly the triangle. -/
theorem detected_inventory :
    graph.tetrahedralCenterSet = {0, 2, 4} := by
  ext atom
  simpa [Finset.mem_insert, Finset.mem_singleton] using degree_four_iff atom

def mirrorFun (atom : Fin 9) : Fin 9 :=
  if atom = 2 then 4
  else if atom = 4 then 2
  else if atom = 3 then 8
  else if atom = 8 then 3
  else if atom = 6 then 7
  else if atom = 7 then 6
  else atom

theorem mirrorFun_involutive : Function.Involutive mirrorFun := by
  intro atom
  fin_cases atom <;> rfl

def mirrorPerm : Equiv.Perm (Fin 9) where
  toFun := mirrorFun
  invFun := mirrorFun
  left_inv := mirrorFun_involutive
  right_inv := mirrorFun_involutive

@[simp] theorem mirrorPerm_apply (atom : Fin 9) : mirrorPerm atom = mirrorFun atom := rfl

theorem mirror_fixes_root : mirrorPerm 0 = 0 := rfl
theorem mirror_fixes_fluorine : mirrorPerm 1 = 1 := rfl
theorem mirror_fixes_rootHydrogen : mirrorPerm 5 = 5 := rfl
theorem mirror_swaps_carbons : mirrorPerm 2 = 4 ∧ mirrorPerm 4 = 2 := ⟨rfl, rfl⟩
theorem mirror_swaps_chlorines : mirrorPerm 3 = 8 ∧ mirrorPerm 8 = 3 := ⟨rfl, rfl⟩
theorem mirror_swaps_hydrogens : mirrorPerm 6 = 7 ∧ mirrorPerm 7 = 6 := ⟨rfl, rfl⟩

theorem mirror_isAutomorphism : graph.IsAutomorphism mirrorPerm := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro atom
    fin_cases atom <;> decide
  · intro atom
    fin_cases atom <;> decide
  · intro atom
    fin_cases atom <;> decide
  · intro left right
    fin_cases left <;> fin_cases right <;> decide

def mirrorAut : graph.Aut := ⟨mirrorPerm, mirror_isAutomorphism⟩

private theorem aut_fixes_fluorine (automorphism : graph.Aut) :
    (automorphism : Equiv.Perm (Fin 9)) 1 = 1 := by
  have preserved := MoleculeGraph.Aut.atomZ_eq (m := graph) automorphism (1 : Fin 9)
  have fluorine : graph.atomZ 1 = 9 := (z_fluorine 1).mpr rfl
  rw [fluorine] at preserved
  exact (z_fluorine _).mp preserved

private theorem aut_fixes_root (automorphism : graph.Aut) :
    (automorphism : Equiv.Perm (Fin 9)) 0 = 0 := by
  have adjacent : graph.Adj 1 0 := (adj_fluorine 0).mpr rfl
  have image := (MoleculeGraph.Aut.adj_iff (m := graph) automorphism 1 0).mpr adjacent
  rw [aut_fixes_fluorine automorphism] at image
  exact (adj_fluorine _).mp image

private theorem transport (automorphism : graph.Aut) {center atom : Fin 9}
    (adjacent : graph.Adj center atom) :
    graph.Adj ((automorphism : Equiv.Perm (Fin 9)) center)
      ((automorphism : Equiv.Perm (Fin 9)) atom) :=
  (MoleculeGraph.Aut.adj_iff (m := graph) automorphism center atom).mpr adjacent

private theorem preservedZ (automorphism : graph.Aut) (atom : Fin 9) :
    graph.atomZ ((automorphism : Equiv.Perm (Fin 9)) atom) = graph.atomZ atom :=
  MoleculeGraph.Aut.atomZ_eq (m := graph) automorphism atom

private theorem image_carbon (automorphism : graph.Aut) :
    (automorphism : Equiv.Perm (Fin 9)) 2 = 2 ∨
      (automorphism : Equiv.Perm (Fin 9)) 2 = 4 := by
  have image := transport automorphism ((adj_root 2).mpr (by simp))
  rw [aut_fixes_root automorphism] at image
  have member := (adj_root _).mp image
  have six : graph.atomZ ((automorphism : Equiv.Perm (Fin 9)) 2) = 6 := by
    rw [preservedZ automorphism 2]
    exact (z_carbon 2).mpr (by simp)
  rcases member with equal | member
  · rw [equal] at six
    exact absurd six (by decide)
  · rcases member with equal | member
    · exact Or.inl equal
    · rcases member with equal | equal
      · exact Or.inr equal
      · rw [equal] at six
        exact absurd six (by decide)

private theorem distinct_images (automorphism : graph.Aut) {left right : Fin 9}
    (different : left ≠ right) :
    (automorphism : Equiv.Perm (Fin 9)) left ≠
      (automorphism : Equiv.Perm (Fin 9)) right := by
  intro equal
  exact different (Equiv.injective (automorphism : Equiv.Perm (Fin 9)) equal)

private theorem image_other_carbon (automorphism : graph.Aut)
    (swapped : (automorphism : Equiv.Perm (Fin 9)) 2 = 4) :
    (automorphism : Equiv.Perm (Fin 9)) 4 = 2 := by
  have image := transport automorphism ((adj_root 4).mpr (by simp))
  rw [aut_fixes_root automorphism] at image
  have member := (adj_root _).mp image
  have six : graph.atomZ ((automorphism : Equiv.Perm (Fin 9)) 4) = 6 := by
    rw [preservedZ automorphism 4]
    exact (z_carbon 4).mpr (by simp)
  have notFluorine : (automorphism : Equiv.Perm (Fin 9)) 4 ≠ 1 := by
    intro equal
    rw [equal] at six
    exact absurd six (by decide)
  have notHydrogen : (automorphism : Equiv.Perm (Fin 9)) 4 ≠ 5 := by
    intro equal
    rw [equal] at six
    exact absurd six (by decide)
  have notFixed : (automorphism : Equiv.Perm (Fin 9)) 4 ≠ 4 := by
    intro equal
    have same : (automorphism : Equiv.Perm (Fin 9)) 4 =
        (automorphism : Equiv.Perm (Fin 9)) 2 := by rw [equal, swapped]
    exact (by decide : (4 : Fin 9) ≠ 2) (Equiv.injective _ same)
  rcases member with equal | member
  · exact (notFluorine equal).elim
  · rcases member with equal | member
    · exact equal
    · rcases member with equal | equal
      · exact (notFixed equal).elim
      · exact (notHydrogen equal).elim

private theorem neighbor_z (center atom target : Fin 9) (z : ℕ)
    (specification : ∀ neighbor : Fin 9, graph.Adj center neighbor →
      graph.atomZ neighbor = z → neighbor = target)
    (automorphism : graph.Aut)
    (centerImage : (automorphism : Equiv.Perm (Fin 9)) center = center)
    (adjacent : graph.Adj center atom) (atomic : graph.atomZ atom = z) :
    (automorphism : Equiv.Perm (Fin 9)) atom = target := by
  have image := transport automorphism adjacent
  rw [centerImage] at image
  have atomicImage : graph.atomZ ((automorphism : Equiv.Perm (Fin 9)) atom) = z := by
    rw [preservedZ automorphism atom, atomic]
  exact specification _ image atomicImage

private theorem arm_chlorine_unique (neighbor : Fin 9) :
    graph.Adj 2 neighbor → graph.atomZ neighbor = 17 → neighbor = 3 := by
  intro adjacent atomic
  rcases (adj_arm neighbor).mp adjacent with rfl | rfl | rfl | rfl
  · exact absurd atomic (by decide)
  · rfl
  · exact absurd atomic (by decide)
  · exact absurd atomic (by decide)

private theorem arm_hydrogen_unique (neighbor : Fin 9) :
    graph.Adj 2 neighbor → graph.atomZ neighbor = 1 → neighbor = 6 := by
  intro adjacent atomic
  rcases (adj_arm neighbor).mp adjacent with rfl | rfl | rfl | rfl
  · exact absurd atomic (by decide)
  · exact absurd atomic (by decide)
  · exact absurd atomic (by decide)
  · rfl

private theorem closing_chlorine_unique (neighbor : Fin 9) :
    graph.Adj 4 neighbor → graph.atomZ neighbor = 17 → neighbor = 8 := by
  intro adjacent atomic
  rcases (adj_closing neighbor).mp adjacent with rfl | rfl | rfl | rfl
  · exact absurd atomic (by decide)
  · exact absurd atomic (by decide)
  · exact absurd atomic (by decide)
  · rfl

private theorem closing_hydrogen_unique (neighbor : Fin 9) :
    graph.Adj 4 neighbor → graph.atomZ neighbor = 1 → neighbor = 7 := by
  intro adjacent atomic
  rcases (adj_closing neighbor).mp adjacent with rfl | rfl | rfl | rfl
  · exact absurd atomic (by decide)
  · exact absurd atomic (by decide)
  · rfl
  · exact absurd atomic (by decide)

private theorem root_hydrogen_unique (neighbor : Fin 9) :
    graph.Adj 0 neighbor → graph.atomZ neighbor = 1 → neighbor = 5 := by
  intro adjacent atomic
  rcases (adj_root neighbor).mp adjacent with rfl | rfl | rfl | rfl
  · exact absurd atomic (by decide)
  · exact absurd atomic (by decide)
  · exact absurd atomic (by decide)
  · rfl

private theorem fixes_root_hydrogen (automorphism : graph.Aut) :
    (automorphism : Equiv.Perm (Fin 9)) 5 = 5 :=
  neighbor_z 0 5 5 1 root_hydrogen_unique automorphism (aut_fixes_root automorphism)
    ((adj_root 5).mpr (by simp)) ((z_hydrogen 5).mpr (by simp))

private theorem fixes_arm_chlorine (automorphism : graph.Aut)
    (fixed : (automorphism : Equiv.Perm (Fin 9)) 2 = 2) :
    (automorphism : Equiv.Perm (Fin 9)) 3 = 3 :=
  neighbor_z 2 3 3 17 arm_chlorine_unique automorphism fixed
    ((adj_arm 3).mpr (by simp)) ((z_chlorine 3).mpr (by simp))

private theorem fixes_arm_hydrogen (automorphism : graph.Aut)
    (fixed : (automorphism : Equiv.Perm (Fin 9)) 2 = 2) :
    (automorphism : Equiv.Perm (Fin 9)) 6 = 6 :=
  neighbor_z 2 6 6 1 arm_hydrogen_unique automorphism fixed
    ((adj_arm 6).mpr (by simp)) ((z_hydrogen 6).mpr (by simp))

private theorem fixes_closing_chlorine (automorphism : graph.Aut)
    (fixed : (automorphism : Equiv.Perm (Fin 9)) 4 = 4) :
    (automorphism : Equiv.Perm (Fin 9)) 8 = 8 :=
  neighbor_z 4 8 8 17 closing_chlorine_unique automorphism fixed
    ((adj_closing 8).mpr (by simp)) ((z_chlorine 8).mpr (by simp))

private theorem fixes_closing_hydrogen (automorphism : graph.Aut)
    (fixed : (automorphism : Equiv.Perm (Fin 9)) 4 = 4) :
    (automorphism : Equiv.Perm (Fin 9)) 7 = 7 :=
  neighbor_z 4 7 7 1 closing_hydrogen_unique automorphism fixed
    ((adj_closing 7).mpr (by simp)) ((z_hydrogen 7).mpr (by simp))

private theorem fixes_other_carbon (automorphism : graph.Aut)
    (fixed : (automorphism : Equiv.Perm (Fin 9)) 2 = 2) :
    (automorphism : Equiv.Perm (Fin 9)) 4 = 4 := by
  have image := transport automorphism ((adj_root 4).mpr (by simp))
  rw [aut_fixes_root automorphism] at image
  have member := (adj_root _).mp image
  have six : graph.atomZ ((automorphism : Equiv.Perm (Fin 9)) 4) = 6 := by
    rw [preservedZ automorphism 4]
    exact (z_carbon 4).mpr (by simp)
  have notFluorine : (automorphism : Equiv.Perm (Fin 9)) 4 ≠ 1 := by
    intro equal
    rw [equal] at six
    exact absurd six (by decide)
  have notHydrogen : (automorphism : Equiv.Perm (Fin 9)) 4 ≠ 5 := by
    intro equal
    rw [equal] at six
    exact absurd six (by decide)
  have notArm : (automorphism : Equiv.Perm (Fin 9)) 4 ≠ 2 := by
    intro equal
    have same : (automorphism : Equiv.Perm (Fin 9)) 4 =
        (automorphism : Equiv.Perm (Fin 9)) 2 := by rw [equal, fixed]
    exact (by decide : (4 : Fin 9) ≠ 2) (Equiv.injective _ same)
  rcases member with equal | member
  · exact (notFluorine equal).elim
  · rcases member with equal | member
    · exact (notArm equal).elim
    · rcases member with equal | equal
      · exact equal
      · exact (notHydrogen equal).elim

private theorem swaps_arm_chlorine (automorphism : graph.Aut)
    (swapped : (automorphism : Equiv.Perm (Fin 9)) 2 = 4) :
    (automorphism : Equiv.Perm (Fin 9)) 3 = 8 := by
  have image := transport automorphism ((adj_arm 3).mpr (by simp))
  rw [swapped] at image
  have atomic : graph.atomZ ((automorphism : Equiv.Perm (Fin 9)) 3) = 17 := by
    rw [preservedZ automorphism 3]
    exact (z_chlorine 3).mpr (by simp)
  exact closing_chlorine_unique _ image atomic

private theorem swaps_closing_chlorine (automorphism : graph.Aut)
    (returned : (automorphism : Equiv.Perm (Fin 9)) 4 = 2) :
    (automorphism : Equiv.Perm (Fin 9)) 8 = 3 := by
  have image := transport automorphism ((adj_closing 8).mpr (by simp))
  rw [returned] at image
  have atomic : graph.atomZ ((automorphism : Equiv.Perm (Fin 9)) 8) = 17 := by
    rw [preservedZ automorphism 8]
    exact (z_chlorine 8).mpr (by simp)
  exact arm_chlorine_unique _ image atomic

private theorem swaps_arm_hydrogen (automorphism : graph.Aut)
    (swapped : (automorphism : Equiv.Perm (Fin 9)) 2 = 4) :
    (automorphism : Equiv.Perm (Fin 9)) 6 = 7 := by
  have image := transport automorphism ((adj_arm 6).mpr (by simp))
  rw [swapped] at image
  have atomic : graph.atomZ ((automorphism : Equiv.Perm (Fin 9)) 6) = 1 := by
    rw [preservedZ automorphism 6]
    exact (z_hydrogen 6).mpr (by simp)
  exact closing_hydrogen_unique _ image atomic

private theorem swaps_closing_hydrogen (automorphism : graph.Aut)
    (returned : (automorphism : Equiv.Perm (Fin 9)) 4 = 2) :
    (automorphism : Equiv.Perm (Fin 9)) 7 = 6 := by
  have image := transport automorphism ((adj_closing 7).mpr (by simp))
  rw [returned] at image
  have atomic : graph.atomZ ((automorphism : Equiv.Perm (Fin 9)) 7) = 1 := by
    rw [preservedZ automorphism 7]
    exact (z_hydrogen 7).mpr (by simp)
  exact arm_hydrogen_unique _ image atomic

/-- Every constitutional automorphism is the identity or the stated mirror. -/
theorem automorphism_dichotomy (automorphism : graph.Aut) :
    (automorphism : Equiv.Perm (Fin 9)) = 1 ∨
      (automorphism : Equiv.Perm (Fin 9)) = mirrorPerm := by
  rcases image_carbon automorphism with fixed | swapped
  · left
    have closingFixed := fixes_other_carbon automorphism fixed
    have pointwise : ∀ atom : Fin 9, (automorphism : Equiv.Perm (Fin 9)) atom = atom := by
      intro atom
      fin_cases atom
      · exact aut_fixes_root automorphism
      · exact aut_fixes_fluorine automorphism
      · exact fixed
      · exact fixes_arm_chlorine automorphism fixed
      · exact closingFixed
      · exact fixes_root_hydrogen automorphism
      · exact fixes_arm_hydrogen automorphism fixed
      · exact fixes_closing_hydrogen automorphism closingFixed
      · exact fixes_closing_chlorine automorphism closingFixed
    ext atom
    simp only [Equiv.Perm.one_apply]
    exact congrArg Fin.val (pointwise atom)
  · right
    have returned := image_other_carbon automorphism swapped
    have pointwise : ∀ atom : Fin 9,
        (automorphism : Equiv.Perm (Fin 9)) atom = mirrorPerm atom := by
      intro atom
      fin_cases atom
      · exact aut_fixes_root automorphism
      · exact aut_fixes_fluorine automorphism
      · rw [mirrorPerm_apply]; exact swapped
      · rw [mirrorPerm_apply]; exact swaps_arm_chlorine automorphism swapped
      · rw [mirrorPerm_apply]; exact returned
      · rw [mirrorPerm_apply]; exact fixes_root_hydrogen automorphism
      · rw [mirrorPerm_apply]; exact swaps_arm_hydrogen automorphism swapped
      · rw [mirrorPerm_apply]; exact swaps_closing_hydrogen automorphism returned
      · rw [mirrorPerm_apply]; exact swaps_closing_chlorine automorphism returned
    ext atom
    exact congrArg Fin.val (pointwise atom)

/-- An automorphism fixing either non-root ring carbon fixes all four of its neighbors. -/
theorem nonroot_rigid (automorphism : graph.Aut) :
    ((automorphism : Equiv.Perm (Fin 9)) 2 = 2 →
      ∀ neighbor, graph.Adj 2 neighbor →
        (automorphism : Equiv.Perm (Fin 9)) neighbor = neighbor) ∧
    ((automorphism : Equiv.Perm (Fin 9)) 4 = 4 →
      ∀ neighbor, graph.Adj 4 neighbor →
        (automorphism : Equiv.Perm (Fin 9)) neighbor = neighbor) := by
  constructor
  · intro fixed _neighbor _adjacent
    rcases automorphism_dichotomy automorphism with identity | mirrored
    · rw [identity]
      simp [Equiv.Perm.one_apply]
    · rw [mirrored, mirrorPerm_apply] at fixed
      exact absurd fixed (by decide : mirrorFun 2 ≠ 2)
  · intro fixed _neighbor _adjacent
    rcases automorphism_dichotomy automorphism with identity | mirrored
    · rw [identity]
      simp [Equiv.Perm.one_apply]
    · rw [mirrored, mirrorPerm_apply] at fixed
      exact absurd fixed (by decide : mirrorFun 4 ≠ 4)

/-- The root mirror fixes the root and moves both ring-carbon ligands. -/
theorem root_not_rigid :
    (mirrorAut : Equiv.Perm (Fin 9)) 0 = 0 ∧
      (mirrorAut : Equiv.Perm (Fin 9)) 2 = 4 ∧
      (mirrorAut : Equiv.Perm (Fin 9)) 4 = 2 := by
  exact ⟨rfl, rfl, rfl⟩

private theorem edge_root_closing : graph.underlyingSimpleGraph.Adj 0 4 :=
  (graph.underlyingSimpleGraph_adj 0 4).mpr ((adj_root 4).mpr (by simp))

private theorem edge_closing_arm : graph.underlyingSimpleGraph.Adj 4 2 :=
  (graph.underlyingSimpleGraph_adj 4 2).mpr ((adj_closing 2).mpr (by simp))

private theorem edge_arm_root : graph.underlyingSimpleGraph.Adj 2 0 :=
  (graph.underlyingSimpleGraph_adj 2 0).mpr ((adj_arm 0).mpr (by simp))

private def triangle : graph.underlyingSimpleGraph.Walk 0 0 :=
  SimpleGraph.Walk.cons edge_root_closing
    (SimpleGraph.Walk.cons edge_closing_arm
      (SimpleGraph.Walk.cons edge_arm_root SimpleGraph.Walk.nil))

theorem not_acyclic : ¬ graph.Acyclic := by
  intro acyclic
  refine acyclic triangle ?_
  rw [SimpleGraph.Walk.isCycle_def, SimpleGraph.Walk.isTrail_def]
  simp [triangle, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
    SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil]

end TetraStereo.OneCenter.LocalizedCyclicPseudoInputWitness

assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoInputWitness.source_structurallyWellFormed
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoInputWitness.source_graphReady
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoInputWitness.simple_bonded
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoInputWitness.detected_inventory
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoInputWitness.mirror_isAutomorphism
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoInputWitness.automorphism_dichotomy
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoInputWitness.nonroot_rigid
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoInputWitness.root_not_rigid
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCyclicPseudoInputWitness.not_acyclic
