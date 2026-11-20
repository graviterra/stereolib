import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCoveringSymmetry
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherExchangeSign
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

/-!
Finite symmetry facts of the 46-atom reference-orbit input used by the root consensus proof.

* `rho` rotates the three lower spokes 5 -> 6 -> 7. It fixes root 0, atom 1, every upper
  atom 26..45 and the centers 2, 3, 4, acting by a three-cycle at 2, 3 and 4. Hence it is
  physically proper at every detected center for every configuration.
* `twist` exchanges both root pairs 28/29 and 30/31. It is the identity on atoms 0..27 and
  40, 41, so it acts trivially at centers 2, 3, 4, and it is odd at center 26.
* Every graph symmetry fixing 0 and 28 and sending 30 to 31 fixes center 2 and is odd there.
  This is the lower-gadget coupling: such a map must exchange centers 3 and 4.

All statements are graph/configuration facts. No evaluator output or label is asserted.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusSymmetry

open LocalizedChemicalRingReferenceOrbitInput LocalizedChemicalRingReferenceOrbitCalibration
open LocalizedChemicalRingReferenceOrbitStabilizer LocalizedChemicalRingTwoFixedNeighbors
open LocalizedChemicalRingReferenceOrbitCoveringSymmetry (four_pins_rigid)
open LocalizedPhysicalMarkedParityCompleteness

private def rhoFun (a : Fin 46) : Fin 46 :=
  ![0, 1, 2, 3, 4, 6, 7, 5, 9, 10, 8, 12, 13, 11, 17, 16, 19, 18, 14, 15, 23, 22, 25, 24, 20, 21,
    26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45] a

private def rhoInvFun (a : Fin 46) : Fin 46 :=
  ![0, 1, 2, 3, 4, 7, 5, 6, 10, 8, 9, 13, 11, 12, 18, 19, 15, 14, 17, 16, 24, 25, 21, 20, 23, 22,
    26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45] a

def rho : Equiv.Perm (Fin 46) where
  toFun := rhoFun
  invFun := rhoInvFun
  left_inv := by intro a; fin_cases a <;> rfl
  right_inv := by intro a; fin_cases a <;> rfl

theorem rho_graph : graph.IsAutomorphism rho := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro a <;> fin_cases a <;> decide +kernel

def rhoGraphAut : graph.Aut := ⟨rho, rho_graph⟩

private def twistFun (a : Fin 46) : Fin 46 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
    26, 27, 29, 28, 31, 30, 33, 32, 35, 34, 37, 36, 39, 38, 40, 41, 45, 44, 43, 42] a

def twist : Equiv.Perm (Fin 46) where
  toFun := twistFun
  invFun := twistFun
  left_inv := by intro a; fin_cases a <;> rfl
  right_inv := by intro a; fin_cases a <;> rfl

theorem twist_graph : graph.IsAutomorphism twist := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro a <;> fin_cases a <;> decide +kernel

def twistGraphAut : graph.Aut := ⟨twist, twist_graph⟩

theorem twist_square : twist * twist = 1 := by
  apply Equiv.ext
  intro a
  fin_cases a <;> rfl

theorem twist_actions :
    twist 0 = 0 ∧ twist 28 = 29 ∧ twist 29 = 28 ∧ twist 30 = 31 ∧ twist 31 = 30 ∧
      twist 32 = 33 ∧ twist 34 = 35 ∧ twist 27 = 27 ∧ twist 26 = 26 ∧ twist 1 = 1 ∧
      ∀ a : Fin 46, a.val < 28 → twist a = a := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro a bound
  fin_cases a <;> first | rfl | (simp at bound)

/-! ## Exchanges fixing the O16 reference -/

private def exchangeFun (k : Fin 3) (a : Fin 46) : Fin 46 :=
  match k.val with
  | 0 => ![0, 1, 2, 4, 3, 5, 7, 6, 8, 10, 9, 11, 13, 12, 15, 14, 18, 19, 16, 17, 21, 20, 24, 25, 22, 23,
      26, 27, 28, 29, 31, 30, 32, 33, 35, 34, 36, 37, 39, 38, 41, 40, 43, 42, 45, 44] a
  | 1 => ![0, 1, 2, 4, 3, 6, 5, 7, 9, 8, 10, 12, 11, 13, 16, 17, 14, 15, 19, 18, 22, 23, 20, 21, 25, 24,
      26, 27, 28, 29, 31, 30, 32, 33, 35, 34, 36, 37, 39, 38, 41, 40, 43, 42, 45, 44] a
  | _ => ![0, 1, 2, 4, 3, 7, 6, 5, 10, 9, 8, 13, 12, 11, 19, 18, 17, 16, 15, 14, 25, 24, 23, 22, 21, 20,
      26, 27, 28, 29, 31, 30, 32, 33, 35, 34, 36, 37, 39, 38, 41, 40, 43, 42, 45, 44] a

def exchange (k : Fin 3) : Equiv.Perm (Fin 46) where
  toFun := exchangeFun k
  invFun := exchangeFun k
  left_inv := by intro a; fin_cases k <;> fin_cases a <;> rfl
  right_inv := by intro a; fin_cases k <;> fin_cases a <;> rfl

theorem exchange_graph (k : Fin 3) : graph.IsAutomorphism (exchange k) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro a <;> fin_cases k <;> fin_cases a <;> decide +kernel

private def exchangeAut (k : Fin 3) : graph.Aut := ⟨exchange k, exchange_graph k⟩

theorem exchange_actions (k : Fin 3) :
    exchange k 0 = 0 ∧ exchange k 28 = 28 ∧ exchange k 30 = 31 ∧
      exchange k 5 = (![5, 6, 7] : Fin 3 → Fin 46) k ∧
      exchange k 2 = 2 ∧ exchange k 1 = 1 := by
  fin_cases k <;> decide +kernel

private theorem spoke_image (e : graph.Aut) :
    e.val (5 : Fin 46) = 5 ∨ e.val (5 : Fin 46) = 6 ∨ e.val (5 : Fin 46) = 7 := by
  have spoke : ∀ a : Fin 46, graph.atomZ a = graph.atomZ 5 → graph.atomMass a = graph.atomMass 5 →
      (∃ b : Fin 46, graph.Adj a b ∧ graph.atomZ b = graph.atomZ 8 ∧
        graph.atomMass b = graph.atomMass 8) →
      (∃ b : Fin 46, graph.Adj a b ∧ graph.atomZ b = graph.atomZ 11 ∧
        graph.atomMass b = graph.atomMass 11) → a = 5 ∨ a = 6 ∨ a = 7 := by
    intro a
    fin_cases a <;> decide +kernel
  apply spoke
  · exact MoleculeGraph.Aut.atomZ_eq (m := graph) e 5
  · exact MoleculeGraph.Aut.atomMass_eq (m := graph) e 5
  · exact ⟨e.val 8, (MoleculeGraph.Aut.adj_iff (m := graph) e 5 8).mpr (by decide +kernel),
      MoleculeGraph.Aut.atomZ_eq (m := graph) e 8, MoleculeGraph.Aut.atomMass_eq (m := graph) e 8⟩
  · exact ⟨e.val 11, (MoleculeGraph.Aut.adj_iff (m := graph) e 5 11).mpr (by decide +kernel),
      MoleculeGraph.Aut.atomZ_eq (m := graph) e 11, MoleculeGraph.Aut.atomMass_eq (m := graph) e 11⟩

private theorem equal_exchange (e : graph.Aut) (k : Fin 3)
    (rootFixed : e.val (0 : Fin 46) = (0 : Fin 46))
    (markFixed : e.val (28 : Fin 46) = (28 : Fin 46))
    (entry : e.val (30 : Fin 46) = (31 : Fin 46))
    (spoke : e.val (5 : Fin 46) = exchange k 5) : e.val = exchange k := by
  let h : graph.Aut := (exchangeAut k)⁻¹ * e
  have normalized (a : Fin 46) (same : e.val a = exchange k a) : h.val a = a := by
    change (exchange k).symm (e.val a) = a
    rw [same]
    exact (exchange k).symm_apply_apply a
  have actions := exchange_actions k
  have identity := four_pins_rigid h
    (normalized 0 (rootFixed.trans actions.1.symm))
    (normalized 28 (markFixed.trans actions.2.1.symm))
    (normalized 30 (entry.trans actions.2.2.1.symm))
    (normalized 5 spoke)
  apply Equiv.ext
  intro a
  have atAtom := congrArg (fun f : Equiv.Perm (Fin 46) => f a) identity
  change (exchange k).symm (e.val a) = a at atAtom
  have result := congrArg (exchange k) atAtom
  simpa only [Equiv.apply_symm_apply] using result

/-- Complete classification of the O18-exchanges fixing root 0 and reference 28. -/
theorem other_exchange_classification (e : graph.Aut)
    (rootFixed : e.val (0 : Fin 46) = (0 : Fin 46))
    (markFixed : e.val (28 : Fin 46) = (28 : Fin 46))
    (entry : e.val (30 : Fin 46) = (31 : Fin 46)) :
    ∃ k : Fin 3, e.val = exchange k := by
  rcases spoke_image e with spoke | spoke | spoke
  · exact ⟨0, equal_exchange e 0 rootFixed markFixed entry spoke⟩
  · exact ⟨1, equal_exchange e 1 rootFixed markFixed entry spoke⟩
  · exact ⟨2, equal_exchange e 2 rootFixed markFixed entry spoke⟩

private theorem exchange_local_actions (k : Fin 3) :
    ∃ fixed moved : Fin 46, (1 : Fin 46) ≠ fixed ∧ graph.Adj 2 fixed ∧
      exchange k fixed = fixed ∧ graph.Adj 2 moved ∧ exchange k moved ≠ moved := by
  fin_cases k
  · exact ⟨5, 6, by decide, by decide +kernel, rfl, by decide +kernel, by decide⟩
  · exact ⟨7, 5, by decide, by decide +kernel, rfl, by decide +kernel, by decide⟩
  · exact ⟨6, 5, by decide, by decide +kernel, rfl, by decide +kernel, by decide⟩

noncomputable section

def rhoAut : physical.Aut := graph.detectedMultiCenterAutOfGraphAut rhoGraphAut
def twistAut : physical.Aut := graph.detectedMultiCenterAutOfGraphAut twistGraphAut

/-- For a fixed center, the relative sign is the local ligand-permutation parity. -/
theorem relativeSign_of_fixed (cfg : physical.Configuration) (e : physical.Aut) (d : physical.Center)
    (fixed : physical.centerPerm e d = d) :
    relativeSign physical cfg e d = permHandedness (physical.ligandPermAt e d) := by
  unfold relativeSign transportedSign
  rw [fixed]
  have square : physical.configurationSign cfg d * physical.configurationSign cfg d = 1 :=
    permHandedness_mul_self (cfg d)
  calc physical.configurationSign cfg d * permHandedness (physical.ligandPermAt e d) *
        physical.configurationSign cfg d
      = (physical.configurationSign cfg d * physical.configurationSign cfg d) *
          permHandedness (physical.ligandPermAt e d) := by ring
    _ = permHandedness (physical.ligandPermAt e d) := by rw [square]; ring

private theorem sign_of_one_fixed (p : Equiv.Perm (Fin 4)) (i : Fin 4) (fixed : p i = i)
    (moved : ∀ j, j ≠ i → p j ≠ j) : Equiv.Perm.sign p = 1 := by
  have finite : ∀ (p : Equiv.Perm (Fin 4)) (i : Fin 4), p i = i → (∀ j, j ≠ i → p j ≠ j) →
      Equiv.Perm.sign p = 1 := by decide +kernel
  exact finite p i fixed moved

/-- A symmetry fixing a center and exactly one of its neighbors acts evenly there. -/
theorem local_even_of_one_fixed (e : physical.Aut) (c : physical.Center)
    (centerFixed : e.val c.1 = c.1) (anchor : Fin 46) (anchorAdjacent : physical.mol.Adj c.1 anchor)
    (anchorFixed : e.val anchor = anchor)
    (moved : ∀ atom, physical.mol.Adj c.1 atom → atom ≠ anchor → e.val atom ≠ atom) :
    physical.centerPerm e c = c ∧ permHandedness (physical.ligandPermAt e c) = 1 := by
  have fixed : physical.centerPerm e c = c := Subtype.ext centerFixed
  refine ⟨fixed, ?_⟩
  obtain ⟨i, hi⟩ := physical.ligandAtomAt_surjective c anchor anchorAdjacent
  have fixesI : physical.ligandPermAt e c i = i := by
    apply physical.ligandAtomAt_injective c
    have transported := physical.ligandAtomAt_ligandPermAt e c i
    rw [fixed, hi, anchorFixed] at transported
    exact transported.trans hi.symm
  have movesJ : ∀ j, j ≠ i → physical.ligandPermAt e c j ≠ j := by
    intro j different same
    have transported := physical.ligandAtomAt_ligandPermAt e c j
    rw [fixed, same] at transported
    have adjacent := physical.ligandAtomAt_adj c j
    have notAnchor : (physical.ligandAtomAt c j : Fin 46) ≠ anchor := by
      intro equal
      exact different (physical.ligandAtomAt_injective c (equal.trans hi.symm))
    exact moved _ adjacent notAnchor transported.symm
  have sign := sign_of_one_fixed _ i fixesI movesJ
  simp [permHandedness, sign]

/-- A symmetry fixing a center and all of its neighbors acts as the identity there. -/
theorem local_trivial_of_all_fixed (e : physical.Aut) (c : physical.Center)
    (centerFixed : e.val c.1 = c.1)
    (neighbors : ∀ atom, physical.mol.Adj c.1 atom → e.val atom = atom) :
    physical.centerPerm e c = c ∧ permHandedness (physical.ligandPermAt e c) = 1 := by
  have fixed : physical.centerPerm e c = c := Subtype.ext centerFixed
  refine ⟨fixed, ?_⟩
  have trivial : physical.ligandPermAt e c = 1 := by
    apply Equiv.ext
    intro j
    apply physical.ligandAtomAt_injective c
    have transported := physical.ligandAtomAt_ligandPermAt e c j
    rw [fixed, neighbors _ (physical.ligandAtomAt_adj c j)] at transported
    exact transported
  rw [trivial, permHandedness_one]

private theorem center_cases (d : physical.Center) :
    d.1 = (0 : Fin 46) ∨ d.1 = (2 : Fin 46) ∨ d.1 = (3 : Fin 46) ∨ d.1 = (4 : Fin 46) ∨
      d.1 = (26 : Fin 46) := by
  obtain ⟨a, member⟩ := d
  change a ∈ graph.tetrahedralCenterSet at member
  rw [detected_inventory] at member
  simp only [Finset.mem_insert, Finset.mem_singleton] at member
  exact member

/-- The spoke rotation is physically proper at every detected center, for every configuration. -/
theorem rho_relativeSign (cfg : physical.Configuration) (d : physical.Center) :
    relativeSign physical cfg rhoAut d = 1 := by
  have localAction : physical.centerPerm rhoAut d = d ∧
      permHandedness (physical.ligandPermAt rhoAut d) = 1 := by
    rcases center_cases d with h | h | h | h | h
    · apply local_trivial_of_all_fixed rhoAut d (by rw [h]; rfl)
      intro atom adjacent
      rw [h] at adjacent
      revert adjacent
      fin_cases atom <;> first | (intro; rfl) | (intro adjacent; exact absurd adjacent (by decide +kernel))
    · apply local_even_of_one_fixed rhoAut d (by rw [h]; rfl) 1 (by rw [h]; decide +kernel) rfl
      intro atom adjacent different
      rw [h] at adjacent
      revert adjacent different
      fin_cases atom <;> first
        | (intro adjacent; exact absurd adjacent (by decide +kernel))
        | (intro _ different; exact absurd rfl different)
        | (intro _ _; decide)
    · apply local_even_of_one_fixed rhoAut d (by rw [h]; rfl) 40 (by rw [h]; decide +kernel) rfl
      intro atom adjacent different
      rw [h] at adjacent
      revert adjacent different
      fin_cases atom <;> first
        | (intro adjacent; exact absurd adjacent (by decide +kernel))
        | (intro _ different; exact absurd rfl different)
        | (intro _ _; decide)
    · apply local_even_of_one_fixed rhoAut d (by rw [h]; rfl) 41 (by rw [h]; decide +kernel) rfl
      intro atom adjacent different
      rw [h] at adjacent
      revert adjacent different
      fin_cases atom <;> first
        | (intro adjacent; exact absurd adjacent (by decide +kernel))
        | (intro _ different; exact absurd rfl different)
        | (intro _ _; decide)
    · apply local_trivial_of_all_fixed rhoAut d (by rw [h]; rfl)
      intro atom adjacent
      rw [h] at adjacent
      revert adjacent
      fin_cases atom <;> first | (intro; rfl) | (intro adjacent; exact absurd adjacent (by decide +kernel))
  rw [relativeSign_of_fixed cfg rhoAut d localAction.1, localAction.2]

/-- The double exchange acts trivially at centers 2, 3 and 4 (and at the root). -/
theorem twist_relativeSign_lower (cfg : physical.Configuration) (d : physical.Center)
    (lower : d.1 ≠ (26 : Fin 46)) : relativeSign physical cfg twistAut d = 1 := by
  have localAction : physical.centerPerm twistAut d = d ∧
      permHandedness (physical.ligandPermAt twistAut d) = 1 := by
    rcases center_cases d with h | h | h | h | h
    · -- the root is fixed, and its ligands are exchanged in two pairs
      have fixed : physical.centerPerm twistAut d = d :=
        Subtype.ext (show twistAut.val d.1 = d.1 by rw [h]; rfl)
      refine ⟨fixed, ?_⟩
      obtain ⟨i28, h28⟩ := physical.ligandAtomAt_surjective d (28 : Fin 46) (by rw [h]; decide +kernel)
      obtain ⟨i29, h29⟩ := physical.ligandAtomAt_surjective d (29 : Fin 46) (by rw [h]; decide +kernel)
      obtain ⟨i30, h30⟩ := physical.ligandAtomAt_surjective d (30 : Fin 46) (by rw [h]; decide +kernel)
      obtain ⟨i31, h31⟩ := physical.ligandAtomAt_surjective d (31 : Fin 46) (by rw [h]; decide +kernel)
      have image (i : Fin 4) (a b : Fin 46) (ha : (physical.ligandAtomAt d i : Fin 46) = a)
          (j : Fin 4) (hb : (physical.ligandAtomAt d j : Fin 46) = b) (move : twist a = b) :
          physical.ligandPermAt twistAut d i = j := by
        apply physical.ligandAtomAt_injective d
        have transported := physical.ligandAtomAt_ligandPermAt twistAut d i
        rw [fixed, ha] at transported
        exact transported.trans (move.trans hb.symm)
      have p28 := image i28 28 29 h28 i29 h29 rfl
      have p29 := image i29 29 28 h29 i28 h28 rfl
      have p30 := image i30 30 31 h30 i31 h31 rfl
      have p31 := image i31 31 30 h31 i30 h30 rfl
      have distinct : ∀ (x y : Fin 4) (a b : Fin 46), (physical.ligandAtomAt d x : Fin 46) = a →
          (physical.ligandAtomAt d y : Fin 46) = b → a ≠ b → x ≠ y := by
        intro x y a b hx hy ne same
        exact ne (hx.symm.trans ((congrArg (fun z => (physical.ligandAtomAt d z : Fin 46)) same).trans hy))
      have finite : ∀ (p : Equiv.Perm (Fin 4)) (a b c e : Fin 4), a ≠ b → a ≠ c → a ≠ e → b ≠ c →
          b ≠ e → c ≠ e → p a = b → p b = a → p c = e → p e = c → Equiv.Perm.sign p = 1 := by
        decide +kernel
      have sign := finite _ i28 i29 i30 i31
        (distinct _ _ _ _ h28 h29 (by decide)) (distinct _ _ _ _ h28 h30 (by decide))
        (distinct _ _ _ _ h28 h31 (by decide)) (distinct _ _ _ _ h29 h30 (by decide))
        (distinct _ _ _ _ h29 h31 (by decide)) (distinct _ _ _ _ h30 h31 (by decide))
        p28 p29 p30 p31
      simp [permHandedness, sign]
    · apply local_trivial_of_all_fixed twistAut d (by rw [h]; rfl)
      intro atom adjacent
      rw [h] at adjacent
      revert adjacent
      fin_cases atom <;> first | (intro; rfl) | (intro adjacent; exact absurd adjacent (by decide +kernel))
    · apply local_trivial_of_all_fixed twistAut d (by rw [h]; rfl)
      intro atom adjacent
      rw [h] at adjacent
      revert adjacent
      fin_cases atom <;> first | (intro; rfl) | (intro adjacent; exact absurd adjacent (by decide +kernel))
    · apply local_trivial_of_all_fixed twistAut d (by rw [h]; rfl)
      intro atom adjacent
      rw [h] at adjacent
      revert adjacent
      fin_cases atom <;> first | (intro; rfl) | (intro adjacent; exact absurd adjacent (by decide +kernel))
    · exact absurd h lower
  rw [relativeSign_of_fixed cfg twistAut d localAction.1, localAction.2]

/-- The double exchange reverses center 26 for every configuration. -/
theorem twist_relativeSign_other (cfg : physical.Configuration) :
    physical.centerPerm twistAut LocalizedChemicalRingReferenceOrbitAllCalibration.otherCurrent =
        LocalizedChemicalRingReferenceOrbitAllCalibration.otherCurrent ∧
      relativeSign physical cfg twistAut LocalizedChemicalRingReferenceOrbitAllCalibration.otherCurrent = -1 := by
  have odd := local_odd_of_two_fixed_neighbors physical twistAut
    LocalizedChemicalRingReferenceOrbitAllCalibration.otherCurrent (by rfl)
    (1 : Fin 46) (27 : Fin 46) (by decide) (by decide +kernel) (by decide +kernel) rfl rfl
    ⟨(34 : Fin 46), by decide +kernel, by decide⟩
  refine ⟨odd.1, ?_⟩
  rw [relativeSign_of_fixed cfg twistAut _ odd.1, odd.2]

/-- Every exchange of the O18 arms that fixes root 0 and reference 28 reverses center 2,
for every configuration. -/
theorem other_exchange_lower_negative (cfg : physical.Configuration) (e : physical.Aut)
    (rootFixed : e.val (0 : Fin 46) = (0 : Fin 46))
    (markFixed : e.val (28 : Fin 46) = (28 : Fin 46))
    (entry : e.val (30 : Fin 46) = (31 : Fin 46)) :
    physical.centerPerm e current = current ∧ relativeSign physical cfg e current = -1 := by
  obtain ⟨k, same⟩ := other_exchange_classification ⟨e.val, e.2.1⟩ rootFixed markFixed entry
  have actions := exchange_actions k
  obtain ⟨fixed, moved, distinct, adjacent, fixedEq, moveAdjacent, moveNe⟩ :=
    exchange_local_actions k
  have odd := local_odd_of_two_fixed_neighbors physical e current
    (by change e.val (2 : Fin 46) = (2 : Fin 46); rw [same]; exact actions.2.2.2.2.1)
    (1 : Fin 46) fixed distinct (by decide +kernel) adjacent
    (by rw [same]; exact actions.2.2.2.2.2) (by rw [same]; exact fixedEq)
    ⟨moved, moveAdjacent, by rw [same]; exact moveNe⟩
  refine ⟨odd.1, ?_⟩
  rw [relativeSign_of_fixed cfg e current odd.1, odd.2]

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusSymmetry

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusSymmetry.rho_graph
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusSymmetry.twist_graph
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusSymmetry.twist_square
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusSymmetry.twist_actions
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusSymmetry.exchange_graph
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusSymmetry.exchange_actions
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusSymmetry.other_exchange_classification
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusSymmetry.relativeSign_of_fixed
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusSymmetry.local_even_of_one_fixed
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusSymmetry.local_trivial_of_all_fixed
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusSymmetry.rho_relativeSign
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusSymmetry.twist_relativeSign_lower
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusSymmetry.twist_relativeSign_other
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusSymmetry.other_exchange_lower_negative
