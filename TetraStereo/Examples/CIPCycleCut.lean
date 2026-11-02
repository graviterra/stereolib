import TetraStereo.OneCenter.CIPCycleCut
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.FinCases

set_option autoImplicit false

namespace TetraStereo
namespace Examples

open OneCenter

/-!
  A tiny cyclic-graph sanity check for the cycle-cut CIP key.

  We attach a cyclopropyl-like carbon fragment (a 3-cycle) as one ligand and keep the other three
  ligands at distinct atomic numbers, so the sorted order is decided by the first atom label alone.
-/

namespace CycloToy

abbrev Atom := Option (Fin 6)

/-- Atomic numbers of the non-center atoms: ring carbons `0,1,2`, then Br/Cl/F as `3,4,5`. -/
def atomZSome : Fin 6 → AtomicNumber :=
  ![6, 6, 6, 35, 17, 9]

/-- Atomic numbers of the four ligands, indexed compatibly with `oneCenter.ligandAtom`. -/
def ligandZ : Fin 4 → AtomicNumber :=
  ![6, 35, 17, 9]

private def ringEdge (i j : Fin 6) : Prop :=
  (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
    (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
    (i = 2 ∧ j = 0) ∨ (i = 0 ∧ j = 2)

private def centerNeighbor (i : Fin 6) : Prop :=
  i = 0 ∨ i = 3 ∨ i = 4 ∨ i = 5

private instance (i : Fin 6) : Decidable (centerNeighbor i) := by
  dsimp [centerNeighbor]
  infer_instance

private instance (i j : Fin 6) : Decidable (ringEdge i j) := by
  dsimp [ringEdge]
  infer_instance

def bond : Atom → Atom → BondOrder
  | none, some i => if centerNeighbor i then 1 else 0
  | some i, none => if centerNeighbor i then 1 else 0
  | some i, some j => if ringEdge i j then 1 else 0
  | none, none => 0

def mol : MoleculeGraph Atom where
  atomZ
    | none => 6
    | some i => atomZSome i
  bond := bond
  bond_symm := by
    intro u v
    cases u with
    | none =>
        cases v with
        | none =>
            simp [bond]
        | some j =>
            simp [bond, centerNeighbor]
    | some i =>
        cases v with
        | none =>
            simp [bond, centerNeighbor]
        | some j =>
            fin_cases i <;> fin_cases j <;> simp [bond, ringEdge]
  bond_self := by
    intro u
    cases u with
    | none =>
        simp [bond]
    | some i =>
        fin_cases i <;> simp [bond, ringEdge]

def oneCenter : OneCenterMolecule Atom where
  mol := mol
  center := none
  ligandAtom
    | 0 => some 0
    | 1 => some 3
    | 2 => some 4
    | 3 => some 5
  ligandAtom_adj := by
    intro i
    fin_cases i <;> simp [MoleculeGraph.Adj, mol, bond, centerNeighbor]
  ligandAtom_injective := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
  ligandAtom_surjective := by
    intro v hv
    cases v with
    | none =>
        simp [MoleculeGraph.Adj, mol, bond] at hv
    | some j =>
        fin_cases j <;>
          simp [MoleculeGraph.Adj, mol, bond, centerNeighbor] at hv ⊢ <;>
          first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩

/-! ### Cycle-cut CIP order -/

open Prod.Lex

noncomputable section

private def keyWithTie (i : Fin 4) : (List MoleculeGraph.AtomLabel) ×ₗ (Fin 4) :=
  toLex (oneCenter.cipKeyCycleCut i, i)

private def descRel (i j : Fin 4) : Prop :=
  keyWithTie j ≤ keyWithTie i

private theorem keyWithTie_injective : Function.Injective keyWithTie := by
  intro i j hij
  have : (oneCenter.cipKeyCycleCut i, i) = (oneCenter.cipKeyCycleCut j, j) := toLex.injective hij
  exact congrArg Prod.snd this

private instance : Std.Antisymm descRel :=
  ⟨by
    intro a b hab hba
    apply keyWithTie_injective
    dsimp [descRel] at hab hba
    exact le_antisymm hba hab⟩

private instance : DecidableRel descRel := by
  intro i j
  dsimp [descRel, keyWithTie]
  infer_instance

private instance : IsTrans (Fin 4) descRel :=
  ⟨by
    intro a b c hab hbc
    dsimp [descRel] at hab hbc ⊢
    exact le_trans hbc hab⟩

private instance : Std.Total descRel :=
  ⟨by
    intro a b
    dsimp [descRel]
    simpa [or_comm] using (le_total (keyWithTie b) (keyWithTie a))⟩

private theorem cipKey_head? (i : Fin 4) :
    (oneCenter.cipKeyCycleCut i).head? = some (toLex (ligandZ i, 0)) := by
  fin_cases i <;> simp [OneCenterMolecule.cipKeyCycleCut, oneCenter, mol, ligandZ, atomZSome,
    MoleculeGraph.cipKeyFromCycleCut_head?]

private theorem cipKey_eq_cons_tail (i : Fin 4) :
    oneCenter.cipKeyCycleCut i = toLex (ligandZ i, 0) :: (oneCenter.cipKeyCycleCut i).tail := by
  apply List.eq_cons_of_mem_head?
  simp [cipKey_head?]

private theorem cipKey_lt_of_ligandZ_lt {i j : Fin 4} (h : ligandZ i < ligandZ j) :
    oneCenter.cipKeyCycleCut i < oneCenter.cipKeyCycleCut j := by
  classical
  have hi := cipKey_eq_cons_tail (i := i)
  have hj := cipKey_eq_cons_tail (i := j)
  have hlabel : (toLex (ligandZ i, 0) : MoleculeGraph.AtomLabel) < toLex (ligandZ j, 0) :=
    (Prod.Lex.toLex_lt_toLex).2 (Or.inl h)
  have hlex :
      List.Lex (· < ·)
        (toLex (ligandZ i, 0) :: (oneCenter.cipKeyCycleCut i).tail)
        (toLex (ligandZ j, 0) :: (oneCenter.cipKeyCycleCut j).tail) :=
    List.Lex.rel hlabel
  have hlt :
      (toLex (ligandZ i, 0) :: (oneCenter.cipKeyCycleCut i).tail) <
        (toLex (ligandZ j, 0) :: (oneCenter.cipKeyCycleCut j).tail) :=
    (List.lt_iff_lex_lt _ _).2 hlex
  exact lt_of_lt_of_eq (lt_of_eq_of_lt hi hlt) hj.symm

private theorem descRel_of_ligandZ_lt {i j : Fin 4} (h : ligandZ j < ligandZ i) : descRel i j := by
  dsimp [descRel, keyWithTie]
  have hkey : oneCenter.cipKeyCycleCut j < oneCenter.cipKeyCycleCut i :=
    cipKey_lt_of_ligandZ_lt (i := j) (j := i) h
  have hlt :
      (toLex (oneCenter.cipKeyCycleCut j, j) : (List MoleculeGraph.AtomLabel) ×ₗ (Fin 4)) <
        toLex (oneCenter.cipKeyCycleCut i, i) :=
    (Prod.Lex.toLex_lt_toLex).2 (Or.inl hkey)
  exact le_of_lt hlt

private theorem pairwise_expected_cipOrder : ([1, 2, 3, 0] : List (Fin 4)).Pairwise descRel := by
  refine (List.pairwise_cons).2 ?_
  constructor
  · intro a ha
    simp at ha
    rcases ha with rfl | rfl | rfl
    · exact descRel_of_ligandZ_lt (i := (1 : Fin 4)) (j := 2) (by decide)
    · exact descRel_of_ligandZ_lt (i := (1 : Fin 4)) (j := 3) (by decide)
    · exact descRel_of_ligandZ_lt (i := (1 : Fin 4)) (j := 0) (by decide)
  · refine (List.pairwise_cons).2 ?_
    constructor
    · intro a ha
      simp at ha
      rcases ha with rfl | rfl
      · exact descRel_of_ligandZ_lt (i := (2 : Fin 4)) (j := 3) (by decide)
      · exact descRel_of_ligandZ_lt (i := (2 : Fin 4)) (j := 0) (by decide)
    · refine (List.pairwise_cons).2 ?_
      constructor
      · intro a ha
        simp at ha
        rcases ha with rfl
        exact descRel_of_ligandZ_lt (i := (3 : Fin 4)) (j := 0) (by decide)
      · simp

private theorem perm_expected_cipOrder : ([1, 2, 3, 0] : List (Fin 4)).Perm (List.finRange 4) := by
  have hfin : (List.finRange 4 : List (Fin 4)) = [0, 1, 2, 3] := by
    decide
  have h30 : ([3, 0] : List (Fin 4)).Perm [0, 3] := by
    simpa using (List.Perm.swap (3 : Fin 4) (0 : Fin 4) []).symm
  have h : ([1, 2, 3, 0] : List (Fin 4)).Perm [0, 1, 2, 3] := by
    have h1 : ([1, 2, 3, 0] : List (Fin 4)).Perm [1, 2, 0, 3] := by
      simpa using List.Perm.cons (1 : Fin 4) (List.Perm.cons (2 : Fin 4) h30)
    have h2 : ([1, 2, 0, 3] : List (Fin 4)).Perm [1, 0, 2, 3] := by
      have h20 : ([2, 0, 3] : List (Fin 4)).Perm [0, 2, 3] := by
        simpa using (List.Perm.swap (2 : Fin 4) (0 : Fin 4) [3]).symm
      simpa using List.Perm.cons (1 : Fin 4) h20
    have h3 : ([1, 0, 2, 3] : List (Fin 4)).Perm [0, 1, 2, 3] := by
      simpa using (List.Perm.swap (1 : Fin 4) (0 : Fin 4) [2, 3]).symm
    exact List.Perm.trans (List.Perm.trans h1 h2) h3
  simpa [hfin] using h

theorem cipOrderCycleCut_eq_expected : oneCenter.cipOrderCycleCut = [1, 2, 3, 0] := by
  classical
  have hpairOrder : oneCenter.cipOrderCycleCut.Pairwise descRel := by
    simpa [OneCenterMolecule.cipOrderCycleCut, descRel] using
      (List.pairwise_mergeSort' (r := descRel) (l := List.finRange 4))
  have hperm : oneCenter.cipOrderCycleCut.Perm ([1, 2, 3, 0] : List (Fin 4)) :=
    (oneCenter.cipOrderCycleCut_perm_finRange).trans perm_expected_cipOrder.symm
  exact (List.Perm.eq_of_pairwise' hpairOrder pairwise_expected_cipOrder hperm)

theorem ligandZ_injective : Function.Injective ligandZ := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [ligandZ] at hij ⊢

theorem stereogenicByCIPCycleCut : oneCenter.StereogenicByCIPCycleCut := by
  intro i j hkey
  have hhead := congrArg List.head? hkey
  have hlabel :
      toLex (oneCenter.mol.atomZ (oneCenter.ligandAtom i), oneCenter.mol.atomMass (oneCenter.ligandAtom i)) =
        toLex (oneCenter.mol.atomZ (oneCenter.ligandAtom j), oneCenter.mol.atomMass (oneCenter.ligandAtom j)) := by
    exact
      Option.some.inj
        (by
          simpa [OneCenterMolecule.cipKeyCycleCut, oneCenter,
            MoleculeGraph.cipKeyFromCycleCut_head?] using hhead)
  have hpair :
      (oneCenter.mol.atomZ (oneCenter.ligandAtom i), oneCenter.mol.atomMass (oneCenter.ligandAtom i)) =
        (oneCenter.mol.atomZ (oneCenter.ligandAtom j), oneCenter.mol.atomMass (oneCenter.ligandAtom j)) :=
    toLex.injective hlabel
  have hz : ligandZ i = ligandZ j := by
    have hz' : oneCenter.mol.atomZ (oneCenter.ligandAtom i) =
        oneCenter.mol.atomZ (oneCenter.ligandAtom j) :=
      congrArg Prod.fst hpair
    fin_cases i <;> fin_cases j <;> simp [oneCenter, mol, ligandZ, atomZSome] at hz' ⊢
  exact ligandZ_injective hz

theorem cipPermutationCycleCut?_eq_some :
    oneCenter.cipPermutationCycleCut? = some oneCenter.cipPermutationCycleCut := by
  exact oneCenter.cipPermutationCycleCut?_eq_some_of_resolvedCIPCycleCut
    stereogenicByCIPCycleCut

theorem stereogenicByCIPDescriptor : oneCenter.StereogenicByCIPDescriptor :=
  stereogenicByCIPCycleCut

theorem cipPermutationDescriptor?_eq_some :
    oneCenter.cipPermutationDescriptor? = some oneCenter.cipPermutationDescriptor := by
  exact oneCenter.cipPermutationDescriptor?_eq_some_of_resolvedCIPDescriptor
    stereogenicByCIPDescriptor

theorem chiralBySymmetry_of_cycleCutCIP : oneCenter.ChiralBySymmetry :=
  oneCenter.chiralBySymmetry_of_stereogenicByCIPCycleCut stereogenicByCIPCycleCut

end

end CycloToy

end Examples
end TetraStereo
