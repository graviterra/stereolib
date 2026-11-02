import TetraStereo.Examples.PseudoasymmetricTrihydroxyglutaricAcid
import TetraStereo.OneCenter.OfficialBranchPerception
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace TetraStereo
namespace Examples
namespace PseudoasymmetricTrihydroxyglutaricAcid

open OneCenter
open Prod.Lex
open Atom

/-!
  Terminal descriptor seeds for the trihydroxyglutaric-acid benchmark.

  ## Calibration note

  The source calibration maps determinant handedness `-1 ↦ R` and `+1 ↦ S`
  (`RS.ofHandedness`).  The left terminal center in `cfg` carries local sign `+1`, hence its
  CIP configuration descriptor is `S`; the right terminal center carries `-1`, hence `R`.  The
  historical declaration names ending in `_R`/`_S` are preserved below as aliases with corrected
  statements.  Unowned call sites (`V01ClaimPackage`, later `PublicAPI`/exports) must expect the
  corrected `S`/`R` seed values.
-/

private noncomputable abbrev leftOneCenter : OneCenterMolecule Atom :=
  multi.toOneCenterMolecule leftCenter

private def terminalLigandZ : Fin 4 → AtomicNumber :=
  ![8, 6, 6, 1]

private def oxygenLabel : MoleculeGraph.AtomLabel := toLex (8, 0)
private def carbonLabel : MoleculeGraph.AtomLabel := toLex (6, 0)
private def hydrogenLabel : MoleculeGraph.AtomLabel := toLex (1, 0)

private theorem left_cipKeyCycleCut_head? (i : Fin 4) :
    (leftOneCenter.cipKeyCycleCut i).head? = some (toLex (terminalLigandZ i, 0)) := by
  fin_cases i <;>
    simp [leftOneCenter, MultiCenterMolecule.toOneCenterMolecule, leftCenter, multi,
      MultiCenterMolecule.ligandAtomAt, ligandAt, mol, atomZ, terminalLigandZ,
      OneCenterMolecule.cipKeyCycleCut, MoleculeGraph.cipKeyFromCycleCut_head?]

private theorem rawChildren_left_carboxyl_perm :
    (mol.rawCIPChildren c2 carboxylL).Perm [carboxylLO1, carboxylLO1, carboxylLO2] := by
  rw [MoleculeGraph.rawCIPChildren]
  rw [List.perm_iff_count]
  intro a
  cases a <;> simp [MoleculeGraph.count_rawCIPNeighborListWithMultiplicity_eq_bond, mol, bond]

private theorem rawChildren_left_chain_perm :
    (mol.rawCIPChildren c2 c3).Perm [c4, o3, h3] := by
  rw [MoleculeGraph.rawCIPChildren]
  rw [List.perm_iff_count]
  intro a
  cases a <;> simp [MoleculeGraph.count_rawCIPNeighborListWithMultiplicity_eq_bond, mol, bond]

private theorem rawCIPSortDescLabel_eq_of_perm {xs ys : List MoleculeGraph.AtomLabel}
    (h : xs.Perm ys) :
    MoleculeGraph.rawCIPSortDescLabel xs = MoleculeGraph.rawCIPSortDescLabel ys := by
  classical
  let r : MoleculeGraph.AtomLabel → MoleculeGraph.AtomLabel → Prop := fun a b => b ≤ a
  haveI : IsTrans MoleculeGraph.AtomLabel r :=
    ⟨by intro a b c hab hbc; exact le_trans hbc hab⟩
  haveI : Std.Total r :=
    ⟨by intro a b; simpa [r, or_comm] using (le_total a b)⟩
  haveI : Std.Antisymm r :=
    ⟨by intro a b hab hba; exact le_antisymm hba hab⟩
  have hxperm : (MoleculeGraph.rawCIPSortDescLabel xs).Perm xs := by
    simpa [MoleculeGraph.rawCIPSortDescLabel] using
      (List.mergeSort_perm xs (fun a b => decide (b ≤ a)))
  have hyperm : (MoleculeGraph.rawCIPSortDescLabel ys).Perm ys := by
    simpa [MoleculeGraph.rawCIPSortDescLabel] using
      (List.mergeSort_perm ys (fun a b => decide (b ≤ a)))
  have hperm : (MoleculeGraph.rawCIPSortDescLabel xs).Perm
      (MoleculeGraph.rawCIPSortDescLabel ys) :=
    hxperm.trans (h.trans hyperm.symm)
  have hxpair : (MoleculeGraph.rawCIPSortDescLabel xs).Pairwise r := by
    simpa [MoleculeGraph.rawCIPSortDescLabel, r] using (List.pairwise_mergeSort' (r := r) xs)
  have hypair : (MoleculeGraph.rawCIPSortDescLabel ys).Pairwise r := by
    simpa [MoleculeGraph.rawCIPSortDescLabel, r] using (List.pairwise_mergeSort' (r := r) ys)
  exact (List.Perm.eq_of_pairwise' hxpair hypair hperm)

private theorem secondLayerLabels_left_carboxyl :
    MoleculeGraph.rawCIPSortDescLabel
      ((mol.cycleCutNextFrontier
        [({ parent := c2, current := carboxylL, seen := {c2} } :
          MoleculeGraph.CIPState Atom)]).map fun s => mol.rawCIPAtomLabel s.current) =
      [oxygenLabel, oxygenLabel, oxygenLabel] := by
  rw [MoleculeGraph.cycleCutNextFrontier_eq]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [MoleculeGraph.cycleCutChildren_eq_of_current_notMem_seen]
  · simp only
    have hinput :
        (List.map
          (fun s => mol.rawCIPAtomLabel s.current)
          (List.map
            (fun c => ({ parent := carboxylL, current := c, seen := insert carboxylL {c2} } :
              MoleculeGraph.CIPState Atom))
            ((mol.rawCIPNeighborListWithMultiplicity carboxylL).erase c2))).Perm
          [oxygenLabel, oxygenLabel, oxygenLabel] := by
      simpa [MoleculeGraph.rawCIPChildren, MoleculeGraph.rawCIPAtomLabel, mol, atomZ,
        oxygenLabel] using
        (rawChildren_left_carboxyl_perm.map fun c => mol.rawCIPAtomLabel c)
    rw [rawCIPSortDescLabel_eq_of_perm hinput,
      MoleculeGraph.rawCIPSortDescLabel_eq_insertionSort]
    decide
  · simp

private theorem secondLayerLabels_left_chain :
    MoleculeGraph.rawCIPSortDescLabel
      ((mol.cycleCutNextFrontier
        [({ parent := c2, current := c3, seen := {c2} } :
          MoleculeGraph.CIPState Atom)]).map fun s => mol.rawCIPAtomLabel s.current) =
      [oxygenLabel, carbonLabel, hydrogenLabel] := by
  rw [MoleculeGraph.cycleCutNextFrontier_eq]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [MoleculeGraph.cycleCutChildren_eq_of_current_notMem_seen]
  · simp only
    have hinput :
        (List.map
          (fun s => mol.rawCIPAtomLabel s.current)
          (List.map
            (fun c => ({ parent := c3, current := c, seen := insert c3 {c2} } :
              MoleculeGraph.CIPState Atom))
            ((mol.rawCIPNeighborListWithMultiplicity c3).erase c2))).Perm
          [carbonLabel, oxygenLabel, hydrogenLabel] := by
      simpa [MoleculeGraph.rawCIPChildren, MoleculeGraph.rawCIPAtomLabel, mol, atomZ,
        oxygenLabel, carbonLabel, hydrogenLabel] using
        (rawChildren_left_chain_perm.map fun c => mol.rawCIPAtomLabel c)
    rw [rawCIPSortDescLabel_eq_of_perm hinput,
      MoleculeGraph.rawCIPSortDescLabel_eq_insertionSort]
    decide
  · simp

private theorem left_cipKeyCycleCut_tail_head?_carboxyl :
    (leftOneCenter.cipKeyCycleCut (1 : Fin 4)).tail.head? = some oxygenLabel := by
  rw [OneCenterMolecule.cipKeyCycleCut]
  rw [MoleculeGraph.cipKeyFromCycleCut_eq_cycleCutKeyAux]
  have hcard : Fintype.card Atom = 15 := by decide
  rw [hcard]
  norm_num
  rw [MoleculeGraph.cycleCutKeyAux_succ]
  simp [leftOneCenter, MultiCenterMolecule.toOneCenterMolecule, leftCenter, multi,
    MultiCenterMolecule.ligandAtomAt, ligandAt, mol, MoleculeGraph.rawCIPSortDescLabel]
  rw [MoleculeGraph.cycleCutKeyAux_succ]
  have hsecond := secondLayerLabels_left_carboxyl
  simp [mol] at hsecond
  rw [hsecond]
  rfl

private theorem left_cipKeyCycleCut_tail_tail_head?_carboxyl :
    (leftOneCenter.cipKeyCycleCut (1 : Fin 4)).tail.tail.head? = some oxygenLabel := by
  rw [OneCenterMolecule.cipKeyCycleCut]
  rw [MoleculeGraph.cipKeyFromCycleCut_eq_cycleCutKeyAux]
  have hcard : Fintype.card Atom = 15 := by decide
  rw [hcard]
  norm_num
  rw [MoleculeGraph.cycleCutKeyAux_succ]
  simp [leftOneCenter, MultiCenterMolecule.toOneCenterMolecule, leftCenter, multi,
    MultiCenterMolecule.ligandAtomAt, ligandAt, mol, MoleculeGraph.rawCIPSortDescLabel]
  rw [MoleculeGraph.cycleCutKeyAux_succ]
  have hsecond := secondLayerLabels_left_carboxyl
  simp [mol] at hsecond
  rw [hsecond]
  rfl

private theorem left_cipKeyCycleCut_tail_head?_chain :
    (leftOneCenter.cipKeyCycleCut (2 : Fin 4)).tail.head? = some oxygenLabel := by
  rw [OneCenterMolecule.cipKeyCycleCut]
  rw [MoleculeGraph.cipKeyFromCycleCut_eq_cycleCutKeyAux]
  have hcard : Fintype.card Atom = 15 := by decide
  rw [hcard]
  norm_num
  rw [MoleculeGraph.cycleCutKeyAux_succ]
  simp [leftOneCenter, MultiCenterMolecule.toOneCenterMolecule, leftCenter, multi,
    MultiCenterMolecule.ligandAtomAt, ligandAt, mol, MoleculeGraph.rawCIPSortDescLabel]
  rw [MoleculeGraph.cycleCutKeyAux_succ]
  have hsecond := secondLayerLabels_left_chain
  simp [mol] at hsecond
  rw [hsecond]
  rfl

private theorem left_cipKeyCycleCut_tail_tail_head?_chain :
    (leftOneCenter.cipKeyCycleCut (2 : Fin 4)).tail.tail.head? = some carbonLabel := by
  rw [OneCenterMolecule.cipKeyCycleCut]
  rw [MoleculeGraph.cipKeyFromCycleCut_eq_cycleCutKeyAux]
  have hcard : Fintype.card Atom = 15 := by decide
  rw [hcard]
  norm_num
  rw [MoleculeGraph.cycleCutKeyAux_succ]
  simp [leftOneCenter, MultiCenterMolecule.toOneCenterMolecule, leftCenter, multi,
    MultiCenterMolecule.ligandAtomAt, ligandAt, mol, MoleculeGraph.rawCIPSortDescLabel]
  rw [MoleculeGraph.cycleCutKeyAux_succ]
  have hsecond := secondLayerLabels_left_chain
  simp [mol] at hsecond
  rw [hsecond]
  rfl

private theorem left_cipKeyCycleCut_eq_cons_tail (i : Fin 4) :
    leftOneCenter.cipKeyCycleCut i =
      toLex (terminalLigandZ i, 0) :: (leftOneCenter.cipKeyCycleCut i).tail := by
  apply List.eq_cons_of_mem_head?
  simp [left_cipKeyCycleCut_head?]

private theorem left_cipKeyCycleCut_tail_eq_cons_tail_of_tail_head?
    {i : Fin 4} {a : MoleculeGraph.AtomLabel}
    (h : (leftOneCenter.cipKeyCycleCut i).tail.head? = some a) :
    (leftOneCenter.cipKeyCycleCut i).tail =
      a :: (leftOneCenter.cipKeyCycleCut i).tail.tail := by
  apply List.eq_cons_of_mem_head?
  exact h

private theorem left_cipKeyCycleCut_tail_tail_eq_cons_tail_of_tail_tail_head?
    {i : Fin 4} {a : MoleculeGraph.AtomLabel}
    (h : (leftOneCenter.cipKeyCycleCut i).tail.tail.head? = some a) :
    (leftOneCenter.cipKeyCycleCut i).tail.tail =
      a :: (leftOneCenter.cipKeyCycleCut i).tail.tail.tail := by
  apply List.eq_cons_of_mem_head?
  exact h

private theorem left_cipKeyCycleCut_lt_of_terminalLigandZ_lt {i j : Fin 4}
    (h : terminalLigandZ i < terminalLigandZ j) :
    leftOneCenter.cipKeyCycleCut i < leftOneCenter.cipKeyCycleCut j := by
  classical
  have hi := left_cipKeyCycleCut_eq_cons_tail i
  have hj := left_cipKeyCycleCut_eq_cons_tail j
  have hlabel : (toLex (terminalLigandZ i, 0) : MoleculeGraph.AtomLabel) <
      toLex (terminalLigandZ j, 0) :=
    (Prod.Lex.toLex_lt_toLex).2 (Or.inl h)
  have hlex :
      List.Lex (· < ·)
        (toLex (terminalLigandZ i, 0) :: (leftOneCenter.cipKeyCycleCut i).tail)
        (toLex (terminalLigandZ j, 0) :: (leftOneCenter.cipKeyCycleCut j).tail) :=
    List.Lex.rel hlabel
  have hlt :
      (toLex (terminalLigandZ i, 0) :: (leftOneCenter.cipKeyCycleCut i).tail) <
        (toLex (terminalLigandZ j, 0) :: (leftOneCenter.cipKeyCycleCut j).tail) :=
    (List.lt_iff_lex_lt _ _).2 hlex
  exact lt_of_lt_of_eq (lt_of_eq_of_lt hi hlt) hj.symm

private theorem left_cipKeyCycleCut_chain_lt_carboxyl :
    leftOneCenter.cipKeyCycleCut (2 : Fin 4) < leftOneCenter.cipKeyCycleCut (1 : Fin 4) := by
  classical
  have hcarboxylHead :
      leftOneCenter.cipKeyCycleCut (1 : Fin 4) =
        carbonLabel :: (leftOneCenter.cipKeyCycleCut (1 : Fin 4)).tail := by
    simpa [terminalLigandZ, carbonLabel] using left_cipKeyCycleCut_eq_cons_tail (1 : Fin 4)
  have hchainHead :
      leftOneCenter.cipKeyCycleCut (2 : Fin 4) =
        carbonLabel :: (leftOneCenter.cipKeyCycleCut (2 : Fin 4)).tail := by
    simpa [terminalLigandZ, carbonLabel] using left_cipKeyCycleCut_eq_cons_tail (2 : Fin 4)
  have hcarboxylTail :=
    left_cipKeyCycleCut_tail_eq_cons_tail_of_tail_head?
      left_cipKeyCycleCut_tail_head?_carboxyl
  have hchainTail :=
    left_cipKeyCycleCut_tail_eq_cons_tail_of_tail_head?
      left_cipKeyCycleCut_tail_head?_chain
  have hcarboxylTailTail :=
    left_cipKeyCycleCut_tail_tail_eq_cons_tail_of_tail_tail_head?
      left_cipKeyCycleCut_tail_tail_head?_carboxyl
  have hchainTailTail :=
    left_cipKeyCycleCut_tail_tail_eq_cons_tail_of_tail_tail_head?
      left_cipKeyCycleCut_tail_tail_head?_chain
  have hlabel : carbonLabel < oxygenLabel := by
    have h : (toLex ((6 : ℕ), 0) : MoleculeGraph.AtomLabel) < toLex (8, 0) :=
      (Prod.Lex.toLex_lt_toLex).2 (Or.inl (by decide : (6 : ℕ) < 8))
    simpa [carbonLabel, oxygenLabel] using h
  have hlexThird :
      List.Lex (· < ·)
        (carbonLabel :: (leftOneCenter.cipKeyCycleCut (2 : Fin 4)).tail.tail.tail)
        (oxygenLabel :: (leftOneCenter.cipKeyCycleCut (1 : Fin 4)).tail.tail.tail) :=
    List.Lex.rel hlabel
  have hlexSecond :
      List.Lex (· < ·)
        (oxygenLabel :: carbonLabel :: (leftOneCenter.cipKeyCycleCut (2 : Fin 4)).tail.tail.tail)
        (oxygenLabel :: oxygenLabel :: (leftOneCenter.cipKeyCycleCut (1 : Fin 4)).tail.tail.tail) :=
    List.Lex.cons hlexThird
  have hlex :
      List.Lex (· < ·)
        (carbonLabel :: oxygenLabel :: carbonLabel ::
          (leftOneCenter.cipKeyCycleCut (2 : Fin 4)).tail.tail.tail)
        (carbonLabel :: oxygenLabel :: oxygenLabel ::
          (leftOneCenter.cipKeyCycleCut (1 : Fin 4)).tail.tail.tail) :=
    List.Lex.cons hlexSecond
  have hlt :
      (carbonLabel :: oxygenLabel :: carbonLabel ::
          (leftOneCenter.cipKeyCycleCut (2 : Fin 4)).tail.tail.tail) <
        (carbonLabel :: oxygenLabel :: oxygenLabel ::
          (leftOneCenter.cipKeyCycleCut (1 : Fin 4)).tail.tail.tail) :=
    (List.lt_iff_lex_lt _ _).2 hlex
  calc
    leftOneCenter.cipKeyCycleCut (2 : Fin 4)
        = carbonLabel :: oxygenLabel :: carbonLabel ::
            (leftOneCenter.cipKeyCycleCut (2 : Fin 4)).tail.tail.tail := by
            rw [hchainHead, hchainTail, hchainTailTail]
            rfl
    _ < carbonLabel :: oxygenLabel :: oxygenLabel ::
          (leftOneCenter.cipKeyCycleCut (1 : Fin 4)).tail.tail.tail := hlt
    _ = leftOneCenter.cipKeyCycleCut (1 : Fin 4) := by
            rw [hcarboxylHead, hcarboxylTail, hcarboxylTailTail]
            rfl

private noncomputable def leftKeyWithTieCycleCut
    (i : Fin 4) : (List MoleculeGraph.AtomLabel) ×ₗ (Fin 4) :=
  toLex (leftOneCenter.cipKeyCycleCut i, i)

private def leftDescRelCycleCut (i j : Fin 4) : Prop :=
  leftKeyWithTieCycleCut j ≤ leftKeyWithTieCycleCut i

private theorem leftKeyWithTieCycleCut_injective : Function.Injective leftKeyWithTieCycleCut := by
  intro i j hij
  have : (leftOneCenter.cipKeyCycleCut i, i) =
      (leftOneCenter.cipKeyCycleCut j, j) := toLex.injective hij
  exact congrArg Prod.snd this

private instance : Std.Antisymm leftDescRelCycleCut :=
  ⟨by
    intro a b hab hba
    apply leftKeyWithTieCycleCut_injective
    dsimp [leftDescRelCycleCut] at hab hba
    exact le_antisymm hba hab⟩

private noncomputable instance : DecidableRel leftDescRelCycleCut := by
  intro i j
  dsimp [leftDescRelCycleCut, leftKeyWithTieCycleCut]
  infer_instance

private instance : IsTrans (Fin 4) leftDescRelCycleCut :=
  ⟨by
    intro a b c hab hbc
    dsimp [leftDescRelCycleCut] at hab hbc ⊢
    exact le_trans hbc hab⟩

private instance : Std.Total leftDescRelCycleCut :=
  ⟨by
    intro a b
    dsimp [leftDescRelCycleCut]
    simpa [or_comm] using (le_total (leftKeyWithTieCycleCut b) (leftKeyWithTieCycleCut a))⟩

private theorem leftDescRelCycleCut_of_cipKey_lt {i j : Fin 4}
    (h : leftOneCenter.cipKeyCycleCut j < leftOneCenter.cipKeyCycleCut i) :
    leftDescRelCycleCut i j := by
  dsimp [leftDescRelCycleCut, leftKeyWithTieCycleCut]
  have hlt :
      (toLex (leftOneCenter.cipKeyCycleCut j, j) :
          (List MoleculeGraph.AtomLabel) ×ₗ (Fin 4)) <
        toLex (leftOneCenter.cipKeyCycleCut i, i) :=
    (Prod.Lex.toLex_lt_toLex).2 (Or.inl h)
  exact le_of_lt hlt

private theorem left_pairwise_expected_cipOrderCycleCut :
    ([0, 1, 2, 3] : List (Fin 4)).Pairwise leftDescRelCycleCut := by
  refine (List.pairwise_cons).2 ?_
  constructor
  · intro a ha
    simp at ha
    rcases ha with rfl | rfl | rfl
    · exact leftDescRelCycleCut_of_cipKey_lt
        (left_cipKeyCycleCut_lt_of_terminalLigandZ_lt (i := (1 : Fin 4)) (j := 0)
          (by decide))
    · exact leftDescRelCycleCut_of_cipKey_lt
        (left_cipKeyCycleCut_lt_of_terminalLigandZ_lt (i := (2 : Fin 4)) (j := 0)
          (by decide))
    · exact leftDescRelCycleCut_of_cipKey_lt
        (left_cipKeyCycleCut_lt_of_terminalLigandZ_lt (i := (3 : Fin 4)) (j := 0)
          (by decide))
  · refine (List.pairwise_cons).2 ?_
    constructor
    · intro a ha
      simp at ha
      rcases ha with rfl | rfl
      · exact leftDescRelCycleCut_of_cipKey_lt left_cipKeyCycleCut_chain_lt_carboxyl
      · exact leftDescRelCycleCut_of_cipKey_lt
          (left_cipKeyCycleCut_lt_of_terminalLigandZ_lt (i := (3 : Fin 4)) (j := 1)
            (by decide))
    · refine (List.pairwise_cons).2 ?_
      constructor
      · intro a ha
        simp at ha
        rcases ha with rfl
        exact leftDescRelCycleCut_of_cipKey_lt
          (left_cipKeyCycleCut_lt_of_terminalLigandZ_lt (i := (3 : Fin 4)) (j := 2)
            (by decide))
      · simp

private theorem left_perm_expected_cipOrderCycleCut :
    ([0, 1, 2, 3] : List (Fin 4)).Perm (List.finRange 4) := by
  decide

theorem left_cipOrderDescriptorAt_eq_expected :
    multi.cipOrderDescriptorAt leftCenter = [0, 1, 2, 3] := by
  classical
  have hpairOrder : leftOneCenter.cipOrderCycleCut.Pairwise leftDescRelCycleCut := by
    simpa [OneCenterMolecule.cipOrderCycleCut, leftDescRelCycleCut,
      leftKeyWithTieCycleCut, leftOneCenter] using
      (List.pairwise_mergeSort' (r := leftDescRelCycleCut) (l := List.finRange 4))
  have hperm : leftOneCenter.cipOrderCycleCut.Perm ([0, 1, 2, 3] : List (Fin 4)) :=
    (leftOneCenter.cipOrderCycleCut_perm_finRange).trans left_perm_expected_cipOrderCycleCut.symm
  have horder : leftOneCenter.cipOrderCycleCut = [0, 1, 2, 3] :=
    (List.Perm.eq_of_pairwise' hpairOrder left_pairwise_expected_cipOrderCycleCut hperm)
  simpa [MultiCenterMolecule.cipOrderDescriptorAt, MultiCenterMolecule.cipOrderCycleCutAt,
    leftOneCenter] using horder

private theorem left_cipOrderCycleCut_eq_expected :
    leftOneCenter.cipOrderCycleCut = [0, 1, 2, 3] := by
  simpa [MultiCenterMolecule.cipOrderDescriptorAt, MultiCenterMolecule.cipOrderCycleCutAt,
    leftOneCenter] using left_cipOrderDescriptorAt_eq_expected

theorem left_cipPermutationDescriptorAt_eq_one :
    multi.cipPermutationDescriptorAt leftCenter = 1 := by
  classical
  ext i
  fin_cases i <;>
    simp [MultiCenterMolecule.cipPermutationDescriptorAt,
      MultiCenterMolecule.cipPermutationCycleCutAt,
      OneCenterMolecule.cipPermutationCycleCut,
      left_cipOrderCycleCut_eq_expected]

theorem left_resolvedCIPDescriptorAt : multi.ResolvedCIPDescriptorAt leftCenter := by
  intro i j hkey
  fin_cases i <;> fin_cases j
  · rfl
  · exact False.elim ((ne_of_gt
      (left_cipKeyCycleCut_lt_of_terminalLigandZ_lt (i := (1 : Fin 4)) (j := 0)
        (by decide))) hkey)
  · exact False.elim ((ne_of_gt
      (left_cipKeyCycleCut_lt_of_terminalLigandZ_lt (i := (2 : Fin 4)) (j := 0)
        (by decide))) hkey)
  · exact False.elim ((ne_of_gt
      (left_cipKeyCycleCut_lt_of_terminalLigandZ_lt (i := (3 : Fin 4)) (j := 0)
        (by decide))) hkey)
  · exact False.elim ((ne_of_lt
      (left_cipKeyCycleCut_lt_of_terminalLigandZ_lt (i := (1 : Fin 4)) (j := 0)
        (by decide))) hkey)
  · rfl
  · exact False.elim ((ne_of_gt left_cipKeyCycleCut_chain_lt_carboxyl) hkey)
  · exact False.elim ((ne_of_gt
      (left_cipKeyCycleCut_lt_of_terminalLigandZ_lt (i := (3 : Fin 4)) (j := 1)
        (by decide))) hkey)
  · exact False.elim ((ne_of_lt
      (left_cipKeyCycleCut_lt_of_terminalLigandZ_lt (i := (2 : Fin 4)) (j := 0)
        (by decide))) hkey)
  · exact False.elim ((ne_of_lt left_cipKeyCycleCut_chain_lt_carboxyl) hkey)
  · rfl
  · exact False.elim ((ne_of_gt
      (left_cipKeyCycleCut_lt_of_terminalLigandZ_lt (i := (3 : Fin 4)) (j := 2)
        (by decide))) hkey)
  · exact False.elim ((ne_of_lt
      (left_cipKeyCycleCut_lt_of_terminalLigandZ_lt (i := (3 : Fin 4)) (j := 0)
        (by decide))) hkey)
  · exact False.elim ((ne_of_lt
      (left_cipKeyCycleCut_lt_of_terminalLigandZ_lt (i := (3 : Fin 4)) (j := 1)
        (by decide))) hkey)
  · exact False.elim ((ne_of_lt
      (left_cipKeyCycleCut_lt_of_terminalLigandZ_lt (i := (3 : Fin 4)) (j := 2)
        (by decide))) hkey)
  · rfl

private theorem centerPerm_flipAut_left :
    multi.centerPerm flipAut leftCenter = rightCenter := by
  apply Subtype.ext
  simp [leftCenter, rightCenter, multi, flipAut, flipPerm, flip, MultiCenterMolecule.centerPerm]

theorem right_resolvedCIPDescriptorAt : multi.ResolvedCIPDescriptorAt rightCenter := by
  simpa [centerPerm_flipAut_left] using
    (multi.stereogenicByCIPCycleCutAt_centerPerm (e := flipAut) (c := leftCenter)
      left_resolvedCIPDescriptorAt)

theorem right_cipPermutationDescriptorAt_eq_one :
    multi.cipPermutationDescriptorAt rightCenter = 1 := by
  have htransport :=
    multi.cipPermutationCycleCutAt_centerPerm_of_stereogenicByCIPCycleCutAt
      (e := flipAut) (c := leftCenter) (hst := left_resolvedCIPDescriptorAt)
  simpa [MultiCenterMolecule.cipPermutationDescriptorAt, centerPerm_flipAut_left,
    ligandPermAt_flipAut_left, left_cipPermutationDescriptorAt_eq_one] using htransport

/-- The left cycle-cut CIP permutation is the identity, stated without the descriptor alias. -/
private theorem left_cipPermutationCycleCutAt_eq_one :
    multi.cipPermutationCycleCutAt leftCenter = 1 :=
  left_cipPermutationDescriptorAt_eq_one

/-- The right cycle-cut CIP permutation is the identity, stated without the descriptor alias. -/
private theorem right_cipPermutationCycleCutAt_eq_one :
    multi.cipPermutationCycleCutAt rightCenter = 1 :=
  right_cipPermutationDescriptorAt_eq_one

/-- Local handedness at the left terminal center, unfolded to `permHandedness`. -/
private theorem permHandedness_cfg_left : permHandedness (cfg leftCenter) = 1 := by
  exact cfg_sign_left

/-- Local handedness at the right terminal center, unfolded to `permHandedness`. -/
private theorem permHandedness_cfg_right : permHandedness (cfg rightCenter) = -1 := by
  exact cfg_sign_right

/-- Corrected source calibration at the left terminal center: local sign `+1` reads as `S`. -/
theorem left_cipConfigurationRSDescriptor_eq_S :
    multi.cipConfigurationRSDescriptor cfg leftCenter = RS.S := by
  have hsign : multi.cipConfigurationSignCycleCut cfg leftCenter = 1 := by
    simp [left_cipPermutationCycleCutAt_eq_one]
  show RS.ofHandedness (multi.cipConfigurationSignCycleCut cfg leftCenter) = RS.S
  rw [hsign]
  exact RS.ofHandedness_one

/-- Corrected source calibration at the right terminal center: local sign `-1` reads as `R`. -/
theorem right_cipConfigurationRSDescriptor_eq_R :
    multi.cipConfigurationRSDescriptor cfg rightCenter = RS.R := by
  have hsign : multi.cipConfigurationSignCycleCut cfg rightCenter = -1 := by
    simp [right_cipPermutationCycleCutAt_eq_one]
  show RS.ofHandedness (multi.cipConfigurationSignCycleCut cfg rightCenter) = RS.R
  rw [hsign]
  exact RS.ofHandedness_neg_one

/-- Historical name preserved with its statement corrected to the source calibration.  The left
terminal descriptor is now `S`, not `R`. -/
theorem left_cipConfigurationRSDescriptor_eq_R :
    multi.cipConfigurationRSDescriptor cfg leftCenter = RS.S :=
  left_cipConfigurationRSDescriptor_eq_S

/-- Historical name preserved with its statement corrected to the source calibration.  The right
terminal descriptor is now `R`, not `S`. -/
theorem right_cipConfigurationRSDescriptor_eq_S :
    multi.cipConfigurationRSDescriptor cfg rightCenter = RS.R :=
  right_cipConfigurationRSDescriptor_eq_R




theorem left_right_cipConfigurationRSDescriptor_ne :
    multi.cipConfigurationRSDescriptor cfg leftCenter ≠
      multi.cipConfigurationRSDescriptor cfg rightCenter := by
  rw [left_cipConfigurationRSDescriptor_eq_S, right_cipConfigurationRSDescriptor_eq_R]
  intro h
  cases h

theorem safeDescriptorSeedState_rs_left_eq_some_S :
    safeDescriptorSeedState.rs leftCenter = some RS.S := by
  have h := DescriptorDiscoveryState.seedResolvedDescriptorRS?_rs_eq_some_of_resolved
    (m := multi) (cfg := cfg) (c := leftCenter) left_resolvedCIPDescriptorAt
  simpa [safeDescriptorSeedState, left_cipConfigurationRSDescriptor_eq_S] using h

theorem safeDescriptorSeedState_rs_right_eq_some_R :
    safeDescriptorSeedState.rs rightCenter = some RS.R := by
  have h := DescriptorDiscoveryState.seedResolvedDescriptorRS?_rs_eq_some_of_resolved
    (m := multi) (cfg := cfg) (c := rightCenter) right_resolvedCIPDescriptorAt
  simpa [safeDescriptorSeedState, right_cipConfigurationRSDescriptor_eq_R] using h

/-- Historical name preserved with its statement corrected: the left terminal seed is now `S`. -/
theorem safeDescriptorSeedState_rs_left_eq_some_R :
    safeDescriptorSeedState.rs leftCenter = some RS.S :=
  safeDescriptorSeedState_rs_left_eq_some_S

/-- Historical name preserved with its statement corrected: the right terminal seed is now `R`. -/
theorem safeDescriptorSeedState_rs_right_eq_some_S :
    safeDescriptorSeedState.rs rightCenter = some RS.R :=
  safeDescriptorSeedState_rs_right_eq_some_R

@[simp] theorem safeDescriptorSeedState_pseudo_left_eq_none :
    safeDescriptorSeedState.pseudo leftCenter = none := by
  rfl

@[simp] theorem safeDescriptorSeedState_pseudo_right_eq_none :
    safeDescriptorSeedState.pseudo rightCenter = none := by
  rfl

/-- Branch perception finds the left terminal descriptor by walking the middle center's left
side ligand, then converts it into official Rule-5 context automatically.  Under the source
calibration that descriptor is `S`. -/
theorem middle_safeSeed_officialBranchContext_left_eq_ofRS_S :
    multi.officialBranchContextWithin safeDescriptorSeedState middleCenter (1 : Fin 4) 0 =
      CIPRuleEngine.OfficialLigandRuleContext.ofRS RS.S := by
  have hsource :
      multi.centerOfAtomExcept? middleCenter (multi.ligandAtomAt middleCenter (1 : Fin 4)) =
        some leftCenter := by
    simp [MultiCenterMolecule.centerOfAtomExcept?, MultiCenterMolecule.centerOfAtom?,
      middleCenter, leftCenter, multi, centerSet, MultiCenterMolecule.ligandAtomAt, ligandAt]
  simp [MultiCenterMolecule.officialBranchContextWithin,
    MultiCenterMolecule.branchLigandEvidenceWithin, evidenceOfDescriptorSources,
    MultiCenterMolecule.branchDescriptorSourcesWithin, MultiCenterMolecule.branchSourcesWithin,
    MultiCenterMolecule.branchSourcesFrom, hsource, DescriptorDiscoveryState.perceivedDescriptorAt?,
    firstDistinctDescriptorSourcePair?, PerceivedLigandEvidence.toOfficialLigandRuleContext,
    PerceivedLigandEvidence.rule3Geometry?, PerceivedLigandEvidence.rule4aKind?,
    PerceivedLigandEvidence.rule4bPair?, PerceivedLigandEvidence.rule4cDescriptor?,
    PerceivedDescriptor.rule3Geometry?, PerceivedDescriptor.rule4aKind?,
    PerceivedDescriptor.rule4cDescriptor?, PerceivedDescriptor.rule5Descriptor?,
    PerceivedLigandEvidence.rule5Descriptor?, CIPRuleEngine.OfficialLigandRuleContext.ofRS,
    CIPRuleEngine.OfficialLigandRuleContext.ofRule5Descriptor, OfficialRule5Descriptor.ofRS,
    safeDescriptorSeedState_pseudo_left_eq_none, safeDescriptorSeedState_rs_left_eq_some_S]

theorem middle_safeSeed_officialBranchContext_left_rule5_S :
    (multi.officialBranchContextWithin safeDescriptorSeedState middleCenter (1 : Fin 4) 0).rule5Descriptor? =
      some OfficialRule5Descriptor.descriptorS := by
  simp [middle_safeSeed_officialBranchContext_left_eq_ofRS_S]

/-- Branch perception finds the right terminal descriptor by walking the middle center's right
side ligand, then converts it into official Rule-5 context automatically.  Under the source
calibration that descriptor is `R`. -/
theorem middle_safeSeed_officialBranchContext_right_eq_ofRS_R :
    multi.officialBranchContextWithin safeDescriptorSeedState middleCenter (2 : Fin 4) 0 =
      CIPRuleEngine.OfficialLigandRuleContext.ofRS RS.R := by
  have hsource :
      multi.centerOfAtomExcept? middleCenter (multi.ligandAtomAt middleCenter (2 : Fin 4)) =
        some rightCenter := by
    simp [MultiCenterMolecule.centerOfAtomExcept?, MultiCenterMolecule.centerOfAtom?,
      middleCenter, rightCenter, multi, centerSet, MultiCenterMolecule.ligandAtomAt, ligandAt]
  simp [MultiCenterMolecule.officialBranchContextWithin,
    MultiCenterMolecule.branchLigandEvidenceWithin, evidenceOfDescriptorSources,
    MultiCenterMolecule.branchDescriptorSourcesWithin, MultiCenterMolecule.branchSourcesWithin,
    MultiCenterMolecule.branchSourcesFrom, hsource, DescriptorDiscoveryState.perceivedDescriptorAt?,
    firstDistinctDescriptorSourcePair?, PerceivedLigandEvidence.toOfficialLigandRuleContext,
    PerceivedLigandEvidence.rule3Geometry?, PerceivedLigandEvidence.rule4aKind?,
    PerceivedLigandEvidence.rule4bPair?, PerceivedLigandEvidence.rule4cDescriptor?,
    PerceivedDescriptor.rule3Geometry?, PerceivedDescriptor.rule4aKind?,
    PerceivedDescriptor.rule4cDescriptor?, PerceivedDescriptor.rule5Descriptor?,
    PerceivedLigandEvidence.rule5Descriptor?, CIPRuleEngine.OfficialLigandRuleContext.ofRS,
    CIPRuleEngine.OfficialLigandRuleContext.ofRule5Descriptor, OfficialRule5Descriptor.ofRS,
    safeDescriptorSeedState_pseudo_right_eq_none, safeDescriptorSeedState_rs_right_eq_some_R]

theorem middle_safeSeed_officialBranchContext_right_rule5_R :
    (multi.officialBranchContextWithin safeDescriptorSeedState middleCenter (2 : Fin 4) 0).rule5Descriptor? =
      some OfficialRule5Descriptor.descriptorR := by
  simp [middle_safeSeed_officialBranchContext_right_eq_ofRS_R]

noncomputable def middleSafeSeedOfficialBranchContext :
    multi.Center → Fin 4 → CIPRuleEngine.OfficialLigandRuleContext :=
  fun center i => multi.officialBranchContextWithin safeDescriptorSeedState center i 0

/-- Official Rule-5 comparison of the middle side ligands.  The left branch carries `S`, the right
branch carries `R`, so the official ordering is now `lt` (`S` before `R`).  This matches the
trace-level `middle_rule5PairTrace_outcome`. -/
private theorem compareOfficialContextTrace_ofRS_S_R :
    cipTraceOutcome
      (CIPRuleEngine.compareOfficialContextTrace
        (CIPRuleEngine.OfficialLigandRuleContext.ofRS RS.S)
        (CIPRuleEngine.OfficialLigandRuleContext.ofRS RS.R)) =
      Ordering.lt := by
  rfl

private theorem compareKeyThenOfficialCertificate_rule5_S_R_of_key_eq
    {leftKey rightKey : List MoleculeGraph.AtomLabel}
    (h : cipTraceOutcome (CIPRuleEngine.compareKeyTrace leftKey rightKey) = Ordering.eq) :
    (CIPRuleEngine.compareKeyThenOfficialCertificate leftKey rightKey
      (CIPRuleEngine.OfficialLigandRuleContext.ofRS RS.S)
      (CIPRuleEngine.OfficialLigandRuleContext.ofRS RS.R)).outcome =
      Ordering.lt := by
  rw [CIPRuleEngine.compareKeyThenOfficialCertificate_outcome,
    CIPRuleEngine.compareKeyThenOfficialTrace_outcome_of_key_eq h]
  exact compareOfficialContextTrace_ofRS_S_R

/-- The middle side-ligand comparison is now discharged by molecule-wide branch perception feeding
official Rule 5, rather than by manually supplying ligand evidence.  After the source-calibration
correction the outcome is `lt`. -/
theorem middle_safeSeed_officialBranchCompare_left_right_outcome_lt :
    (multi.cipRuleCompareOfficialDescriptorAt middleSafeSeedOfficialBranchContext
      middleCenter (1 : Fin 4) (2 : Fin 4)).outcome = Ordering.lt := by
  simpa [MultiCenterMolecule.cipRuleCompareOfficialDescriptorAt, middleSafeSeedOfficialBranchContext,
    middle_safeSeed_officialBranchContext_left_eq_ofRS_S,
    middle_safeSeed_officialBranchContext_right_eq_ofRS_R] using
    compareKeyThenOfficialCertificate_rule5_S_R_of_key_eq
      (leftKey := multi.cipKeyDescriptorAt middleCenter (1 : Fin 4))
      (rightKey := multi.cipKeyDescriptorAt middleCenter (2 : Fin 4))
      middle_side_key_trace_tied

/-- Historical name preserved with its statement corrected: the official middle comparison is
`lt`, not `gt`. -/
theorem middle_safeSeed_officialBranchCompare_left_right_outcome_gt :
    (multi.cipRuleCompareOfficialDescriptorAt middleSafeSeedOfficialBranchContext
      middleCenter (1 : Fin 4) (2 : Fin 4)).outcome = Ordering.lt :=
  middle_safeSeed_officialBranchCompare_left_right_outcome_lt

theorem middleRule5DiscoveryTask_ready_safeDescriptorSeed :
    middleRule5DiscoveryTask.Ready safeDescriptorSeedState := by
  exact middleRule5DiscoveryTask_ready_safeDescriptorSeed_of_terminal_resolved
    left_resolvedCIPDescriptorAt right_resolvedCIPDescriptorAt

theorem middleRule5DiscoveryTask_resolveFromSafeDescriptorSeed :
    middleRule5DiscoveryTask.resolveFromState? safeDescriptorSeedState =
      some middleDiscoveryResult := by
  have h := middleRule5DiscoveryTask_resolvesFromSafeDescriptorSeed_of_terminal_resolved
    left_resolvedCIPDescriptorAt right_resolvedCIPDescriptorAt
    left_right_cipConfigurationRSDescriptor_ne
  simpa [middleDiscoveryResult, left_cipConfigurationRSDescriptor_eq_S,
    right_cipConfigurationRSDescriptor_eq_R] using h

def middleRule5TaskSpec : Rule5TaskSpec multi cfg middleCenter where
  leftLigand := 1
  rightLigand := 2
  leftSource := leftCenter
  rightSource := rightCenter
  keyTie := middle_side_key_trace_tied

@[simp] theorem middleRule5TaskSpec_toTask :
    middleRule5TaskSpec.toTask = middleRule5DiscoveryTask :=
  rfl

noncomputable def pseudoasymmetricRule5TaskSelector : Rule5TaskSelector multi cfg :=
  pathRule5TaskSelectorWithin multi cfg 0

theorem pseudoasymmetricRule5TaskSelector_spec_middle :
    pseudoasymmetricRule5TaskSelector.spec? middleCenter = some middleRule5TaskSpec := by
  have h0 :
      multi.centerOfAtomExcept? middleCenter (multi.ligandAtomAt middleCenter (0 : Fin 4)) =
        none := by
    simp [MultiCenterMolecule.centerOfAtomExcept?, MultiCenterMolecule.centerOfAtom?,
      middleCenter, multi, centerSet, MultiCenterMolecule.ligandAtomAt, ligandAt]
  have h1 :
      multi.centerOfAtomExcept? middleCenter (multi.ligandAtomAt middleCenter (1 : Fin 4)) =
        some leftCenter := by
    simp [MultiCenterMolecule.centerOfAtomExcept?, MultiCenterMolecule.centerOfAtom?,
      middleCenter, leftCenter, multi, centerSet, MultiCenterMolecule.ligandAtomAt, ligandAt]
  have h2 :
      multi.centerOfAtomExcept? middleCenter (multi.ligandAtomAt middleCenter (2 : Fin 4)) =
        some rightCenter := by
    simp [MultiCenterMolecule.centerOfAtomExcept?, MultiCenterMolecule.centerOfAtom?,
      middleCenter, rightCenter, multi, centerSet, MultiCenterMolecule.ligandAtomAt, ligandAt]
  simp [pseudoasymmetricRule5TaskSelector, pathRule5TaskSelectorWithin,
    pathRule5TaskSpecWithin?, firstSome, directRule5PairCandidates, h0, h1, h2,
    middleRule5TaskSpec, middle_side_key_trace_tied]

noncomputable def middleExtractedSafeResolution :
    Rule5DiscoverySchedule.SafeTaskResolution pseudoasymmetricRule5TaskSelector.schedule :=
  pseudoasymmetricRule5TaskSelector.safeResolutionAtOfResolvedSources middleRule5TaskSpec
    pseudoasymmetricRule5TaskSelector_spec_middle
    left_resolvedCIPDescriptorAt right_resolvedCIPDescriptorAt
    (by simpa [middleRule5TaskSpec] using left_right_cipConfigurationRSDescriptor_ne)

theorem pseudoasymmetricRule5TaskSelector_runOnce_fixedPoint :
    pseudoasymmetricRule5TaskSelector.schedule.runOnce.FixedPointForRule5Tasks
      pseudoasymmetricRule5TaskSelector.schedule.tasks :=
  pseudoasymmetricRule5TaskSelector.schedule_runOnce_fixedPoint

theorem pseudoasymmetricRule5TaskSelector_runOnce_middle_pseudo_eq_some_r :
    pseudoasymmetricRule5TaskSelector.schedule.runOnce.pseudo middleCenter = some PseudoRS.r := by
  have h :=
    pseudoasymmetricRule5TaskSelector.schedule_runOnce_pseudo_eq_some_of_safeResolution
      middleExtractedSafeResolution
  have h' :
      pseudoasymmetricRule5TaskSelector.schedule.runOnce.pseudo middleCenter =
        some middleDiscoveryResult.descriptor := by
    simpa [middleExtractedSafeResolution, Rule5TaskSelector.safeResolutionAtOfResolvedSources,
      Rule5DiscoverySchedule.safeTaskResolutionOfResolvedSources, middleRule5TaskSpec_toTask,
      middleRule5DiscoveryTask, left_cipConfigurationRSDescriptor_eq_S,
      right_cipConfigurationRSDescriptor_eq_R, middleDiscoveryResult] using h
  simpa [middleDiscoveryResult_descriptor_eq_r] using h'

/-- The fully automatic path-perception state runs the branch-walking Rule-5 selector and writes
the middle lowercase descriptor. -/
theorem officialBranchPerceptionStateWithin_zero_middle_pseudo_eq_some_r :
    (multi.officialBranchPerceptionStateWithin cfg 0).pseudo middleCenter = some PseudoRS.r := by
  simpa [MultiCenterMolecule.officialBranchPerceptionStateWithin,
    pseudoasymmetricRule5TaskSelector] using
    pseudoasymmetricRule5TaskSelector_runOnce_middle_pseudo_eq_some_r

/-- After automatic path perception has discovered the middle lowercase descriptor, walking from
the left terminal center into the middle center produces official Rule-4c context automatically. -/
theorem left_officialBranchContextFromPaths_middleLigand_rule4c_r :
    (multi.officialBranchContextFromPathsWithin cfg 0 leftCenter (2 : Fin 4)).rule4cDescriptor? =
      some OfficialPseudoasymmetricDescriptor.r := by
  have hsource :
      multi.centerOfAtomExcept? leftCenter (multi.ligandAtomAt leftCenter (2 : Fin 4)) =
        some middleCenter := by
    simp [MultiCenterMolecule.centerOfAtomExcept?, MultiCenterMolecule.centerOfAtom?,
      leftCenter, middleCenter, multi, centerSet, MultiCenterMolecule.ligandAtomAt, ligandAt]
  simp [MultiCenterMolecule.officialBranchContextFromPathsWithin,
    MultiCenterMolecule.officialBranchContextWithin, MultiCenterMolecule.branchLigandEvidenceWithin,
    evidenceOfDescriptorSources, MultiCenterMolecule.branchDescriptorSourcesWithin,
    MultiCenterMolecule.branchSourcesWithin, MultiCenterMolecule.branchSourcesFrom, hsource,
    DescriptorDiscoveryState.perceivedDescriptorAt?,
    officialBranchPerceptionStateWithin_zero_middle_pseudo_eq_some_r,
    firstDistinctDescriptorSourcePair?, PerceivedLigandEvidence.toOfficialLigandRuleContext,
    PerceivedLigandEvidence.rule3Geometry?, PerceivedLigandEvidence.rule4aKind?,
    PerceivedLigandEvidence.rule4bPair?, PerceivedLigandEvidence.rule4cDescriptor?,
    PerceivedDescriptor.rule3Geometry?, PerceivedDescriptor.rule4aKind?,
    PerceivedDescriptor.rule4cDescriptor?]

noncomputable def middleSafeSeedRule5Schedule : Rule5DiscoverySchedule multi cfg :=
  pseudoasymmetricRule5TaskSelector.schedule

noncomputable def middleSafeSeedScheduledResolution :
    Rule5DiscoverySchedule.SafeTaskResolution middleSafeSeedRule5Schedule :=
  middleExtractedSafeResolution

theorem middleSafeSeedRule5Schedule_targetsNodup :
    middleSafeSeedRule5Schedule.TargetsNodup := by
  simpa [middleSafeSeedRule5Schedule] using
    pseudoasymmetricRule5TaskSelector.schedule_targetsNodup

theorem middleSafeSeedRule5Schedule_runOnce_fixedPoint :
    middleSafeSeedRule5Schedule.runOnce.FixedPointForRule5Tasks
      middleSafeSeedRule5Schedule.tasks := by
  simpa [middleSafeSeedRule5Schedule] using
    pseudoasymmetricRule5TaskSelector_runOnce_fixedPoint

/-- The concrete pseudoasymmetric Rule-5 schedule has reached an executable fixed point after its
first pass: running the same chemistry again changes no descriptor fact. -/
theorem middleSafeSeedRule5Schedule_runOnce_idempotent :
    middleSafeSeedRule5Schedule.runOnceFrom middleSafeSeedRule5Schedule.runOnce =
      middleSafeSeedRule5Schedule.runOnce := by
  exact middleSafeSeedRule5Schedule.runOnceFrom_runOnce_eq_of_targetsNodup_safe
    middleSafeSeedRule5Schedule_targetsNodup

noncomputable def afterMiddleSafeDescriptorDiscoveryState : DescriptorDiscoveryState multi cfg :=
  safeDescriptorSeedState.applyRule5Task middleRule5DiscoveryTask

theorem afterMiddleSafeDescriptorDiscoveryState_middle_pseudo_eq_some_r :
    afterMiddleSafeDescriptorDiscoveryState.pseudo middleCenter = some PseudoRS.r := by
  have h :=
    DescriptorDiscoveryState.applyRule5Task_pseudo_eq_some_of_resolveFromState?_eq_some
      (state := safeDescriptorSeedState) (task := middleRule5DiscoveryTask)
      (result := middleDiscoveryResult) middleRule5DiscoveryTask_resolveFromSafeDescriptorSeed
  simpa [afterMiddleSafeDescriptorDiscoveryState, middleDiscoveryResult_descriptor_eq_r] using h

noncomputable def middleSafeSeedGlobalDiscoveryCertificate :
    Rule5GlobalDiscoveryCertificate multi cfg where
  initial := safeDescriptorSeedState
  task := middleRule5DiscoveryTask
  result := middleDiscoveryResult
  resolved_from_initial := middleRule5DiscoveryTask_resolveFromSafeDescriptorSeed
  finalState := afterMiddleSafeDescriptorDiscoveryState
  finalState_eq := rfl
  final_pseudo := by
    simpa [middleRule5DiscoveryTask, middleDiscoveryResult_descriptor_eq_r] using
      afterMiddleSafeDescriptorDiscoveryState_middle_pseudo_eq_some_r
  achiral := achiralConfigurationBySymmetry

/-- Historical declaration name retained with the corrected source-calibrated statement. -/
theorem middle_safeSeed_officialBranchContext_left_eq_ofRS_R :
    multi.officialBranchContextWithin safeDescriptorSeedState middleCenter (1 : Fin 4) 0 =
      CIPRuleEngine.OfficialLigandRuleContext.ofRS RS.S :=
  middle_safeSeed_officialBranchContext_left_eq_ofRS_S

/-- Historical declaration name retained with the corrected source-calibrated statement. -/
theorem middle_safeSeed_officialBranchContext_left_rule5_R :
    (multi.officialBranchContextWithin safeDescriptorSeedState middleCenter (1 : Fin 4) 0).rule5Descriptor? =
      some OfficialRule5Descriptor.descriptorS :=
  middle_safeSeed_officialBranchContext_left_rule5_S

/-- Historical declaration name retained with the corrected source-calibrated statement. -/
theorem middle_safeSeed_officialBranchContext_right_eq_ofRS_S :
    multi.officialBranchContextWithin safeDescriptorSeedState middleCenter (2 : Fin 4) 0 =
      CIPRuleEngine.OfficialLigandRuleContext.ofRS RS.R :=
  middle_safeSeed_officialBranchContext_right_eq_ofRS_R

/-- Historical declaration name retained with the corrected source-calibrated statement. -/
theorem middle_safeSeed_officialBranchContext_right_rule5_S :
    (multi.officialBranchContextWithin safeDescriptorSeedState middleCenter (2 : Fin 4) 0).rule5Descriptor? =
      some OfficialRule5Descriptor.descriptorR :=
  middle_safeSeed_officialBranchContext_right_rule5_R

end PseudoasymmetricTrihydroxyglutaricAcid
end Examples
end TetraStereo
