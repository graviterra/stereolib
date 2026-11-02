import TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixture
import TetraStereo.OneCenter.PhysicalEnantiomorphicPairCountReindexing
import TetraStereo.OneCenter.RootedBranchFrameReindexInvariance
import TetraStereo.OneCenter.MultiCenterSymmetry
import TetraStereo.KernelOnly
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 8192

/-!
# Physical branch transport for the symmetric cyclic fixture

This module closes the finite stabilizer calculation for the explicit symmetric ring fixture. It
does not evaluate the production auxiliary reader or claim generated CIP labels.
-/

namespace TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixturePhysical

noncomputable section

open TetraStereo.OneCenter
open TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixture
open TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry

private def graphAut (e : canon.Aut) : graph.Aut := ⟨e.val, e.property.1⟩

private theorem autZ (e : canon.Aut) (atom : Fin 9) :
    graph.atomZ (e.val atom) = graph.atomZ atom :=
  MoleculeGraph.Aut.atomZ_eq (m := graph) (graphAut e) atom

private theorem autAdj (e : canon.Aut) {a b : Fin 9} (h : graph.Adj a b) :
    graph.Adj (e.val a) (e.val b) :=
  (MoleculeGraph.Aut.adj_iff (m := graph) (graphAut e) a b).mpr h

private theorem root0_slot_swap_forces_auto24 (e : canon.Aut)
    (fixed : canon.centerPerm e center0 = center0)
    (moves : canon.ligandPermAt e center0 1 = 2) : e = auto24 := by
  have e0 : e.val 0 = 0 := congrArg Subtype.val fixed
  have transported := canon.ligandAtomAt_ligandPermAt (e := e) (c := center0) 1
  rw [fixed, moves, ligands0.2.1, ligands0.2.2.1] at transported
  have e2 : e.val 2 = 4 := transported.symm
  have e4_mem : e.val 4 ∈ canon.centers := by
    apply (MultiCenterMolecule.Aut.mem_centers_iff (m := canon) (e := e) 4).mp
    rw [canon_centers, detected_inventory]
    simp
  rw [canon_centers, detected_inventory] at e4_mem
  simp only [Finset.mem_insert, Finset.mem_singleton] at e4_mem
  have e4_ne0 : e.val 4 ≠ 0 := by
    intro h
    have inj := e.val.injective (h.trans e0.symm)
    exact absurd inj (by decide)
  have e4_ne4 : e.val 4 ≠ 4 := by
    intro h
    have inj := e.val.injective (h.trans e2.symm)
    exact absurd inj (by decide)
  have e4 : e.val 4 = 2 := by
    rcases e4_mem with h0 | h2 | h4
    · exact False.elim (e4_ne0 h0)
    · exact h2
    · exact False.elim (e4_ne4 h4)
  have e1_adj : graph.Adj 0 (e.val 1) := by
    simpa [e0] using autAdj e ((adj_root 1).mpr (by simp))
  have e5_adj : graph.Adj 0 (e.val 5) := by
    simpa [e0] using autAdj e ((adj_root 5).mpr (by simp))
  have e1_z : graph.atomZ (e.val 1) = 17 := by
    rw [autZ]
    exact (atomZ_cases 1).2.1.mpr (by simp)
  have e5_z : graph.atomZ (e.val 5) = 1 := by
    rw [autZ]
    exact (atomZ_cases 5).2.2.mpr (by simp)
  have e1 : e.val 1 = 1 := by
    rcases (atomZ_cases (e.val 1)).2.1.mp e1_z with h1 | h3 | h8
    · exact h1
    · have hbad : ¬ graph.Adj 0 3 := by decide
      exact False.elim (hbad (by simpa [h3] using e1_adj))
    · have hbad : ¬ graph.Adj 0 8 := by decide
      exact False.elim (hbad (by simpa [h8] using e1_adj))
  have e5 : e.val 5 = 5 := by
    rcases (atomZ_cases (e.val 5)).2.2.mp e5_z with h5 | h6 | h7
    · exact h5
    · have hbad : ¬ graph.Adj 0 6 := by decide
      exact False.elim (hbad (by simpa [h6] using e5_adj))
    · have hbad : ¬ graph.Adj 0 7 := by decide
      exact False.elim (hbad (by simpa [h7] using e5_adj))
  have e3_adj : graph.Adj 4 (e.val 3) := by
    simpa [e2] using autAdj e ((adj_arm 3).mpr (by simp))
  have e6_adj : graph.Adj 4 (e.val 6) := by
    simpa [e2] using autAdj e ((adj_arm 6).mpr (by simp))
  have e3_z : graph.atomZ (e.val 3) = 17 := by
    rw [autZ]
    exact (atomZ_cases 3).2.1.mpr (by simp)
  have e6_z : graph.atomZ (e.val 6) = 1 := by
    rw [autZ]
    exact (atomZ_cases 6).2.2.mpr (by simp)
  have e3 : e.val 3 = 8 := by
    rcases (atomZ_cases (e.val 3)).2.1.mp e3_z with h1 | h3 | h8
    · have hbad : ¬ graph.Adj 4 1 := by decide
      exact False.elim (hbad (by simpa [h1] using e3_adj))
    · have hbad : ¬ graph.Adj 4 3 := by decide
      exact False.elim (hbad (by simpa [h3] using e3_adj))
    · exact h8
  have e6 : e.val 6 = 7 := by
    rcases (atomZ_cases (e.val 6)).2.2.mp e6_z with h5 | h6 | h7
    · have hbad : ¬ graph.Adj 4 5 := by decide
      exact False.elim (hbad (by simpa [h5] using e6_adj))
    · have hbad : ¬ graph.Adj 4 6 := by decide
      exact False.elim (hbad (by simpa [h6] using e6_adj))
    · exact h7
  have e7_adj : graph.Adj 2 (e.val 7) := by
    simpa [e4] using autAdj e ((adj_closing 7).mpr (by simp))
  have e8_adj : graph.Adj 2 (e.val 8) := by
    simpa [e4] using autAdj e ((adj_closing 8).mpr (by simp))
  have e7_z : graph.atomZ (e.val 7) = 1 := by
    rw [autZ]
    exact (atomZ_cases 7).2.2.mpr (by simp)
  have e8_z : graph.atomZ (e.val 8) = 17 := by
    rw [autZ]
    exact (atomZ_cases 8).2.1.mpr (by simp)
  have e7 : e.val 7 = 6 := by
    rcases (atomZ_cases (e.val 7)).2.2.mp e7_z with h5 | h6 | h7
    · have hbad : ¬ graph.Adj 2 5 := by decide
      exact False.elim (hbad (by simpa [h5] using e7_adj))
    · exact h6
    · have hbad : ¬ graph.Adj 2 7 := by decide
      exact False.elim (hbad (by simpa [h7] using e7_adj))
  have e8 : e.val 8 = 3 := by
    rcases (atomZ_cases (e.val 8)).2.1.mp e8_z with h1 | h3 | h8
    · have hbad : ¬ graph.Adj 2 1 := by decide
      exact False.elim (hbad (by simpa [h1] using e8_adj))
    · exact h3
    · have hbad : ¬ graph.Adj 2 8 := by decide
      exact False.elim (hbad (by simpa [h8] using e8_adj))
  apply Subtype.ext
  apply Equiv.ext
  intro atom
  change e.val atom = swap24Fun atom
  fin_cases atom <;> simp_all [swap24Fun]

private theorem auto02_square : auto02 * auto02 = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro atom
  fin_cases atom <;> rfl

private theorem auto04_square : auto04 * auto04 = 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro atom
  fin_cases atom <;> rfl

private theorem conjugate02_auto24 : auto02 * auto24 * auto02 = auto04 := by
  apply Subtype.ext
  apply Equiv.ext
  intro atom
  fin_cases atom <;> rfl

private theorem conjugate04_auto24 : auto04 * auto24 * auto04 = auto02 := by
  apply Subtype.ext
  apply Equiv.ext
  intro atom
  fin_cases atom <;> rfl

private theorem root2_slot_swap_forces_auto04 (e : canon.Aut)
    (fixed : canon.centerPerm e center2 = center2)
    (moves : canon.ligandPermAt e center2 0 = 2) : e = auto04 := by
  have e2 : e.val 2 = 2 := congrArg Subtype.val fixed
  have transported := canon.ligandAtomAt_ligandPermAt (e := e) (c := center2) 0
  rw [fixed, moves, ligands2.1, ligands2.2.2.1] at transported
  have e0 : e.val 0 = 4 := transported.symm
  let f := auto02 * e * auto02
  have f0 : f.val 0 = 0 := by
    change auto02.val (e.val (auto02.val 0)) = 0
    simp [auto02, swap02, swap02Fun, e2]
  have f2 : f.val 2 = 4 := by
    change auto02.val (e.val (auto02.val 2)) = 4
    simp [auto02, swap02, swap02Fun, e0]
  have ffix : canon.centerPerm f center0 = center0 := by
    apply Subtype.ext
    exact f0
  have fmoves : canon.ligandPermAt f center0 1 = 2 := by
    have t := canon.ligandAtomAt_ligandPermAt (e := f) (c := center0) 1
    rw [ffix] at t
    apply canon.ligandAtomAt_injective center0
    simpa [ligands0, f2] using t
  have hf := root0_slot_swap_forces_auto24 f ffix fmoves
  have recover : auto02 * f * auto02 = e := by
    dsimp [f]
    rw [show auto02 * (auto02 * e * auto02) * auto02 = (auto02 * auto02) * e * (auto02 * auto02) by simp [mul_assoc]]
    rw [auto02_square]
    simp
  rw [← recover, hf, conjugate02_auto24]

private theorem root4_slot_swap_forces_auto02 (e : canon.Aut)
    (fixed : canon.centerPerm e center4 = center4)
    (moves : canon.ligandPermAt e center4 0 = 1) : e = auto02 := by
  have e4 : e.val 4 = 4 := congrArg Subtype.val fixed
  have transported := canon.ligandAtomAt_ligandPermAt (e := e) (c := center4) 0
  rw [fixed, moves, ligands4.1, ligands4.2.1] at transported
  have e0 : e.val 0 = 2 := transported.symm
  let f := auto04 * e * auto04
  have f0 : f.val 0 = 0 := by
    change auto04.val (e.val (auto04.val 0)) = 0
    simp [auto04, swap04, swap04Fun, e4]
  have f2 : f.val 2 = 4 := by
    have e2 : e.val 2 = 0 := by
      have hmem : e.val 2 ∈ canon.centers := by
        apply (MultiCenterMolecule.Aut.mem_centers_iff (m := canon) (e := e) 2).mp
        rw [canon_centers, detected_inventory]
        simp
      rw [canon_centers, detected_inventory] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      have hne2 : e.val 2 ≠ 2 := by
        intro h
        have hinj := e.val.injective (h.trans e0.symm)
        exact absurd hinj (by decide)
      have hne4 : e.val 2 ≠ 4 := by
        intro h
        have hinj := e.val.injective (h.trans e4.symm)
        exact absurd hinj (by decide)
      rcases hmem with h0 | h2 | h4
      · exact h0
      · exact False.elim (hne2 h2)
      · exact False.elim (hne4 h4)
    change auto04.val (e.val (auto04.val 2)) = 4
    simp [auto04, swap04, swap04Fun, e2]
  have ffix : canon.centerPerm f center0 = center0 := by
    apply Subtype.ext
    exact f0
  have fmoves : canon.ligandPermAt f center0 1 = 2 := by
    have t := canon.ligandAtomAt_ligandPermAt (e := f) (c := center0) 1
    rw [ffix] at t
    apply canon.ligandAtomAt_injective center0
    simpa [ligands0, f2] using t
  have hf := root0_slot_swap_forces_auto24 f ffix fmoves
  have recover : auto04 * f * auto04 = e := by
    dsimp [f]
    rw [show auto04 * (auto04 * e * auto04) * auto04 = (auto04 * auto04) * e * (auto04 * auto04) by simp [mul_assoc]]
    rw [auto04_square]
    simp
  rw [← recover, hf, conjugate04_auto24]

private theorem reachCenter0to2 : LigandBranchReaches canon center0 1 center2.1 := by
  unfold LigandBranchReaches
  rw [ligands0.2.1]
  refine ⟨SimpleGraph.Walk.nil, ?_⟩
  simp [center0, center2]

private theorem reachCenter2to0 : LigandBranchReaches canon center2 0 center0.1 := by
  unfold LigandBranchReaches
  rw [ligands2.1]
  refine ⟨SimpleGraph.Walk.nil, ?_⟩
  simp [center0, center2]

private theorem reachCenter4to0 : LigandBranchReaches canon center4 0 center0.1 := by
  unfold LigandBranchReaches
  rw [ligands4.1]
  refine ⟨SimpleGraph.Walk.nil, ?_⟩
  simp [center0, center4]

private theorem slotParity24at2 :
    permHandedness (canon.ligandPermAt auto24 center2) = 1 := by
  have h : canon.ligandPermAt auto24 center2 = Equiv.swap 1 2 * Equiv.swap 1 3 := by
    ext i
    rw [slotMap24at2]
    fin_cases i <;> rfl
  rw [h, permHandedness_mul]
  simp [permHandedness, Equiv.Perm.sign_swap (by decide : (1 : Fin 4) ≠ 2),
    Equiv.Perm.sign_swap (by decide : (1 : Fin 4) ≠ 3)]

theorem notProperAt0 : ¬ ProperTransport canon calibratedCfg center0 1 2 := by
  rintro ⟨e, fixed, moves, signs⟩
  have he : e = auto24 := root0_slot_swap_forces_auto24 e fixed moves
  subst e
  have equation := signs center2 reachCenter0to2
  rw [auto24_center2, cfgSign2, cfgSign4, slotParity24at2] at equation
  norm_num at equation

private theorem slotParity04at0 :
    permHandedness (canon.ligandPermAt auto04 center0) = 1 := by
  have h : canon.ligandPermAt auto04 center0 = Equiv.swap 0 2 * Equiv.swap 0 3 := by
    ext i
    rw [slotMap04at0]
    fin_cases i <;> rfl
  rw [h, permHandedness_mul]
  simp [permHandedness, Equiv.Perm.sign_swap (by decide : (0 : Fin 4) ≠ 2),
    Equiv.Perm.sign_swap (by decide : (0 : Fin 4) ≠ 3)]

private theorem slotParity02at0 :
    permHandedness (canon.ligandPermAt auto02 center0) = -1 := by
  have h : canon.ligandPermAt auto02 center0 = Equiv.swap 0 1 := by
    ext i
    rw [slotMap02at0]
    fin_cases i <;> rfl
  rw [h]
  simp [permHandedness, Equiv.Perm.sign_swap (by decide : (0 : Fin 4) ≠ 1)]

theorem notProperAt2 : ¬ ProperTransport canon calibratedCfg center2 0 2 := by
  rintro ⟨e, fixed, moves, signs⟩
  have he := root2_slot_swap_forces_auto04 e fixed moves
  have equation := signs center0 reachCenter2to0
  rw [he, auto04_center0, cfgSign0, cfgSign4, slotParity04at0] at equation
  norm_num at equation

theorem notProperAt4 : ¬ ProperTransport canon calibratedCfg center4 0 1 := by
  rintro ⟨e, fixed, moves, signs⟩
  have he := root4_slot_swap_forces_auto02 e fixed moves
  have equation := signs center0 reachCenter4to0
  rw [he, auto02_center0, cfgSign0, cfgSign2, slotParity02at0] at equation
  norm_num at equation

private theorem rootSlotZ (i : Fin 4) :
    graph.atomZ (canon.ligandAtomAt center0 i) = ![17, 6, 6, 1] i := by
  fin_cases i
  · simpa [ligands0.1] using (atomZ_cases 1).2.1.mpr (by simp)
  · simpa [ligands0.2.1] using (atomZ_cases 2).1.mpr (Or.inr (Or.inl rfl))
  · simpa [ligands0.2.2.1] using (atomZ_cases 4).1.mpr (Or.inr (Or.inr rfl))
  · simpa [ligands0.2.2.2] using (atomZ_cases 5).2.2.mpr (by simp)

private theorem rootSlotZ_equal_implies (i j : Fin 4)
    (hz : graph.atomZ (canon.ligandAtomAt center0 i) =
      graph.atomZ (canon.ligandAtomAt center0 j)) :
    i = j ∨ ((i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1)) := by
  have hz' : (![17, 6, 6, 1] : Fin 4 → ℕ) i = ![17, 6, 6, 1] j := by
    rw [← rootSlotZ i, ← rootSlotZ j]
    exact hz
  fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff]

private theorem rootLigandZInvariant (e : canon.Aut)
    (fixed : canon.centerPerm e center0 = center0) (i : Fin 4) :
    graph.atomZ (canon.ligandAtomAt center0 (canon.ligandPermAt e center0 i)) =
      graph.atomZ (canon.ligandAtomAt center0 i) := by
  have action := canon.ligandAtomAt_ligandPermAt (e := e) (c := center0) i
  rw [fixed] at action
  rw [action]
  exact autZ e (canon.ligandAtomAt center0 i)

private theorem proper_root_slotZ (i j : Fin 4)
    (hproper : ProperTransport canon calibratedCfg center0 i j) :
    graph.atomZ (canon.ligandAtomAt center0 j) =
      graph.atomZ (canon.ligandAtomAt center0 i) := by
  rcases hproper with ⟨e, fixed, sends, _⟩
  have hz := rootLigandZInvariant e fixed i
  simpa [sends] using hz

theorem pairwiseProperAt0 : MultiCenterMolecule.PairwiseProperDistinguishable canon calibratedCfg center0 := by
  intro i j hij hproper
  have hz := proper_root_slotZ i j hproper
  rcases rootSlotZ_equal_implies j i hz with heq | hpair
  · exact hij heq.symm
  · rcases hpair with ⟨hj, hi⟩ | ⟨hj, hi⟩
    · subst j
      subst i
      exact notProperAt0 (branchTransport_inverse canon calibratedCfg center0 hproper)
    · subst j
      subst i
      exact notProperAt0 hproper


private theorem rootLigandZInvariantAt (root : canon.Center) (e : canon.Aut)
    (fixed : canon.centerPerm e root = root) (i : Fin 4) :
    graph.atomZ (canon.ligandAtomAt root (canon.ligandPermAt e root i)) =
      graph.atomZ (canon.ligandAtomAt root i) := by
  have action := canon.ligandAtomAt_ligandPermAt (e := e) (c := root) i
  rw [fixed] at action
  rw [action]
  exact autZ e (canon.ligandAtomAt root i)

private theorem slotZ2 (i : Fin 4) :
    graph.atomZ (canon.ligandAtomAt center2 i) = ![6,17,6,1] i := by
  fin_cases i
  · simpa [ligands2.1] using (atomZ_cases 0).1.mpr (Or.inl rfl)
  · simpa [ligands2.2.1] using (atomZ_cases 3).2.1.mpr (Or.inr (Or.inl rfl))
  · simpa [ligands2.2.2.1] using (atomZ_cases 4).1.mpr (Or.inr (Or.inr rfl))
  · simpa [ligands2.2.2.2] using (atomZ_cases 6).2.2.mpr (Or.inr (Or.inl rfl))

private theorem slotZ4 (i : Fin 4) :
    graph.atomZ (canon.ligandAtomAt center4 i) = ![6,6,1,17] i := by
  fin_cases i
  · simpa [ligands4.1] using (atomZ_cases 0).1.mpr (Or.inl rfl)
  · simpa [ligands4.2.1] using (atomZ_cases 2).1.mpr (Or.inr (Or.inl rfl))
  · simpa [ligands4.2.2.1] using (atomZ_cases 7).2.2.mpr (Or.inr (Or.inr rfl))
  · simpa [ligands4.2.2.2] using (atomZ_cases 8).2.1.mpr (Or.inr (Or.inr rfl))

private theorem tiedAt2 (i j : Fin 4) (h : graph.atomZ (canon.ligandAtomAt center2 i) = graph.atomZ (canon.ligandAtomAt center2 j)) :
    i = j ∨ ((i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0)) := by
  have h' : (![6,17,6,1] : Fin 4 → ℕ) i = ![6,17,6,1] j := by rw [← slotZ2 i, ← slotZ2 j]; exact h
  fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff]

private theorem tiedAt4 (i j : Fin 4) (h : graph.atomZ (canon.ligandAtomAt center4 i) = graph.atomZ (canon.ligandAtomAt center4 j)) :
    i = j ∨ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) := by
  have h' : (![6,6,1,17] : Fin 4 → ℕ) i = ![6,6,1,17] j := by rw [← slotZ4 i, ← slotZ4 j]; exact h
  fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff]

private theorem properZAt2 (i j : Fin 4) (h : ProperTransport canon calibratedCfg center2 i j) :
    graph.atomZ (canon.ligandAtomAt center2 j) = graph.atomZ (canon.ligandAtomAt center2 i) := by
  rcases h with ⟨e, fixed, sends, _⟩
  simpa [sends] using rootLigandZInvariantAt center2 e fixed i

private theorem properZAt4 (i j : Fin 4) (h : ProperTransport canon calibratedCfg center4 i j) :
    graph.atomZ (canon.ligandAtomAt center4 j) = graph.atomZ (canon.ligandAtomAt center4 i) := by
  rcases h with ⟨e, fixed, sends, _⟩
  simpa [sends] using rootLigandZInvariantAt center4 e fixed i

theorem pairwiseProperAt2 : MultiCenterMolecule.PairwiseProperDistinguishable canon calibratedCfg center2 := by
  intro i j hij hp
  rcases tiedAt2 j i (properZAt2 i j hp) with heq | ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact hij heq.symm
  · subst j; subst i; exact notProperAt2 (branchTransport_inverse canon calibratedCfg center2 hp)
  · subst j; subst i; exact notProperAt2 hp

theorem pairwiseProperAt4 : MultiCenterMolecule.PairwiseProperDistinguishable canon calibratedCfg center4 := by
  intro i j hij hp
  rcases tiedAt4 j i (properZAt4 i j hp) with heq | ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact hij heq.symm
  · subst j; subst i; exact notProperAt4 (branchTransport_inverse canon calibratedCfg center4 hp)
  · subst j; subst i; exact notProperAt4 hp

private theorem mirrorZAt (root : canon.Center) (i j : Fin 4)
    (h : MirrorTransport canon calibratedCfg root i j) :
    graph.atomZ (canon.ligandAtomAt root j) = graph.atomZ (canon.ligandAtomAt root i) := by
  rcases h with ⟨e, fixed, sends, _⟩
  simpa [sends] using rootLigandZInvariantAt root e fixed i

private theorem enantPairsAt0 {i j : Fin 4}
    (h : Enantiomorphic canon calibratedCfg center0 i j) :
    (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) := by
  rcases h with ⟨hij, hm, _⟩
  rcases rootSlotZ_equal_implies i j (mirrorZAt center0 i j hm).symm with heq | hp
  · exact False.elim (hij heq)
  · exact hp

private theorem enantPairsAt2 {i j : Fin 4}
    (h : Enantiomorphic canon calibratedCfg center2 i j) :
    (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) := by
  rcases h with ⟨hij, hm, _⟩
  rcases tiedAt2 i j (mirrorZAt center2 i j hm).symm with heq | hp
  · exact False.elim (hij heq)
  · exact hp

private theorem enantPairsAt4 {i j : Fin 4}
    (h : Enantiomorphic canon calibratedCfg center4 i j) :
    (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) := by
  rcases h with ⟨hij, hm, _⟩
  rcases tiedAt4 i j (mirrorZAt center4 i j hm).symm with heq | hp
  · exact False.elim (hij heq)
  · exact hp

theorem physicalPairCountAt0 :
    physicalEnantiomorphicPairCount canon calibratedCfg center0 = 1 := by
  rw [physicalEnantiomorphicPairCount_eq_one_iff]
  refine ⟨1, 2, by decide, ⟨by decide, mirrorTransportAt0, notProperAt0⟩, ?_⟩
  intro i j _ h
  rcases enantPairsAt0 h with hpair | hpair
  · exact Or.inl hpair
  · exact Or.inr hpair

theorem physicalPairCountAt2 :
    physicalEnantiomorphicPairCount canon calibratedCfg center2 = 1 := by
  rw [physicalEnantiomorphicPairCount_eq_one_iff]
  refine ⟨0, 2, by decide, ⟨by decide, mirrorTransportAt2, notProperAt2⟩, ?_⟩
  intro i j _ h
  rcases enantPairsAt2 h with hpair | hpair
  · exact Or.inl hpair
  · exact Or.inr hpair

theorem physicalPairCountAt4 :
    physicalEnantiomorphicPairCount canon calibratedCfg center4 = 1 := by
  rw [physicalEnantiomorphicPairCount_eq_one_iff]
  refine ⟨0, 1, by decide, ⟨by decide, mirrorTransportAt4, notProperAt4⟩, ?_⟩
  intro i j _ h
  rcases enantPairsAt4 h with hpair | hpair
  · exact Or.inl hpair
  · exact Or.inr hpair



end
end TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixturePhysical

assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixturePhysical.root0_slot_swap_forces_auto24
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixturePhysical.root2_slot_swap_forces_auto04
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixturePhysical.root4_slot_swap_forces_auto02
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixturePhysical.notProperAt0
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixturePhysical.notProperAt2
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixturePhysical.notProperAt4
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixturePhysical.pairwiseProperAt0
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixturePhysical.pairwiseProperAt2
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixturePhysical.pairwiseProperAt4
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixturePhysical.physicalPairCountAt0
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixturePhysical.physicalPairCountAt2
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixturePhysical.physicalPairCountAt4
