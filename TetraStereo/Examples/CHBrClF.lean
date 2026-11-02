import TetraStereo.OneCenter.Orbit
import TetraStereo.OneCenter.Toy
import TetraStereo.OneCenter.ChiralityClass
import TetraStereo.OneCenter.RS
import Mathlib.Tactic.FinCases

set_option autoImplicit false

namespace TetraStereo
namespace Examples

open OneCenter
open OneCenter.TetrahedralGeometry

/-- The four distinct ligands of bromochlorofluoromethane. -/
inductive CHBrClFLigand
  | hydrogen
  | bromine
  | chlorine
  | fluorine
deriving DecidableEq, Repr

/-- Bromochlorofluoromethane is the archetypal one-center tetrahedral molecule with four
distinct ligands. -/
def bromochlorofluoromethane : TetrahedralCenter CHBrClFLigand where
  ligand
  | 0 => .hydrogen
  | 1 => .bromine
  | 2 => .chlorine
  | 3 => .fluorine
  injective_ligand := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢

/-- A canonical right-handed realization for bromochlorofluoromethane. -/
def bromochlorofluoromethaneRight : TetrahedralGeometry :=
  canonicalGeometry rightHandedFrame

/-- A canonical left-handed realization for bromochlorofluoromethane. -/
def bromochlorofluoromethaneLeft : TetrahedralGeometry :=
  canonicalGeometry leftHandedFrame

/-- The right-handed canonical realization packaged as a nondegenerate realization. -/
def bromochlorofluoromethaneRightRealization : TetrahedralGeometry.Realization :=
  ⟨bromochlorofluoromethaneRight, by
    change Nondegenerate (canonicalGeometry rightHandedFrame)
    exact canonicalGeometry_nondegenerate rightHandedFrame⟩

/-- The left-handed canonical realization packaged as a nondegenerate realization. -/
def bromochlorofluoromethaneLeftRealization : TetrahedralGeometry.Realization :=
  ⟨bromochlorofluoromethaneLeft, by
    change Nondegenerate (canonicalGeometry leftHandedFrame)
    exact canonicalGeometry_nondegenerate leftHandedFrame⟩

example : handedness bromochlorofluoromethaneRight = 1 := by
  simpa [bromochlorofluoromethaneRight, rightHandedFrame] using
    canonicalHandedness_matches_parity rightHandedFrame

example : handedness bromochlorofluoromethaneLeft = -1 := by
  simpa [bromochlorofluoromethaneLeft, leftHandedFrame] using
    canonicalHandedness_matches_parity leftHandedFrame

example :
    ∃! p : TetrahedralGeometry.InvertibleAffineCoordinates,
      p.1.realize = bromochlorofluoromethaneRight := by
  exact existsUnique_invertibleAffineCoordinates
    bromochlorofluoromethaneRightRealization

@[simp] theorem bromochlorofluoromethaneRightRealization_handedness :
    handedness bromochlorofluoromethaneRightRealization.1 = 1 := by
  simpa [bromochlorofluoromethaneRightRealization] using
    (show handedness bromochlorofluoromethaneRight = 1 by
      simpa [bromochlorofluoromethaneRight, rightHandedFrame] using
        canonicalHandedness_matches_parity rightHandedFrame)

@[simp] theorem bromochlorofluoromethaneLeftRealization_handedness :
    handedness bromochlorofluoromethaneLeftRealization.1 = -1 := by
  simpa [bromochlorofluoromethaneLeftRealization] using
    (show handedness bromochlorofluoromethaneLeft = -1 by
      simpa [bromochlorofluoromethaneLeft, leftHandedFrame] using
        canonicalHandedness_matches_parity leftHandedFrame)

theorem bromochlorofluoromethane_left_is_mirror_of_right :
    TetrahedralGeometry.Realization.OrientationReversingAffineEquivalent
      bromochlorofluoromethaneRightRealization bromochlorofluoromethaneLeftRealization := by
  exact (TetrahedralGeometry.Realization.orientationReversingAffineEquivalent_iff _ _).2 (by
    simp)

theorem bromochlorofluoromethane_right_left_orbits_distinct :
    ¬ TetrahedralGeometry.Realization.OrientationPreservingAffineEquivalent
        bromochlorofluoromethaneRightRealization bromochlorofluoromethaneLeftRealization := by
  intro h
  have hh :=
    (TetrahedralGeometry.Realization.orientationPreservingAffineEquivalent_iff _ _).1 h
  norm_num at hh

theorem bromochlorofluoromethane_realization_in_exactly_two_affine_orbits
    (g : TetrahedralGeometry.Realization) :
    TetrahedralGeometry.Realization.OrientationPreservingAffineEquivalent
        bromochlorofluoromethaneRightRealization g ∨
      TetrahedralGeometry.Realization.OrientationPreservingAffineEquivalent
        bromochlorofluoromethaneLeftRealization g := by
  rcases g.handedness_eq_one_or_eq_neg_one with hg | hg
  · left
    exact (TetrahedralGeometry.Realization.orientationPreservingAffineEquivalent_iff _ _).2 (by
      simp [hg])
  · right
    exact (TetrahedralGeometry.Realization.orientationPreservingAffineEquivalent_iff _ _).2 (by
      simp [hg])

theorem bromochlorofluoromethane_has_exactly_two_stereochemical_classes :
    ∃ a b : StereoQ, a ≠ b ∧ ∀ q : StereoQ, q = a ∨ q = b := by
  exact exactly_two_classes

example : Realization.classHandedness
    (Quotient.mk Realization.realizationSetoid bromochlorofluoromethaneRightRealization) =
      qPlus := by
  simp [Realization.classifyRealization]

example : Realization.classHandedness
    (Quotient.mk Realization.realizationSetoid bromochlorofluoromethaneLeftRealization) =
      qMinus := by
  simp [Realization.classifyRealization]
  norm_num

/-
  A tiny “molecule graph + CIP + R/S” sanity check for the same toy CHBrClF example.

  We model the carbon center as `none` and the four ligands as `some i : Option (Fin 4)`,
  using the same index convention as `bromochlorofluoromethane`.
-/

namespace CHBrClF

abbrev Atom := Option (Fin 4)

def ligandZ : Fin 4 → AtomicNumber :=
  ![1, 35, 17, 9]

def bond : Atom → Atom → BondOrder
  | none, some _ => 1
  | some _, none => 1
  | _, _ => 0

def mol : MoleculeGraph Atom where
  atomZ
    | none => 6
    | some i => ligandZ i
  bond := bond
  bond_symm := by
    intro u v
    cases u <;> cases v <;> simp [bond]
  bond_self := by
    intro u
    cases u <;> simp [bond]

def oneCenter : OneCenterMolecule Atom where
  mol := mol
  center := none
  ligandAtom i := some i
  ligandAtom_adj i := by
    simp [MoleculeGraph.Adj, mol, bond]
  ligandAtom_injective := by
    intro i j hij
    simpa using Option.some.inj hij
  ligandAtom_surjective := by
    intro v hv
    cases v with
    | none =>
        simp [MoleculeGraph.Adj, mol, bond] at hv
    | some j =>
        refine ⟨j, ?_⟩
        rfl

theorem ligandZ_injective : Function.Injective ligandZ := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp [ligandZ] at hij ⊢

theorem stereogenicByCIP : oneCenter.StereogenicByCIP := by
  intro i j hkey
  have hhead := congrArg List.head? hkey
  have hlabel :
      toLex (oneCenter.mol.atomZ (some i), oneCenter.mol.atomMass (some i)) =
        toLex (oneCenter.mol.atomZ (some j), oneCenter.mol.atomMass (some j)) := by
    exact
      Option.some.inj
        (by
          simpa [OneCenterMolecule.cipKey, oneCenter, mol, MoleculeGraph.cipKeyFrom_head?] using hhead)
  have hpair :
      (oneCenter.mol.atomZ (some i), oneCenter.mol.atomMass (some i)) =
        (oneCenter.mol.atomZ (some j), oneCenter.mol.atomMass (some j)) :=
    toLex.injective hlabel
  have hz : ligandZ i = ligandZ j := by
    have hz' : oneCenter.mol.atomZ (some i) = oneCenter.mol.atomZ (some j) :=
      congrArg Prod.fst hpair
    simpa [oneCenter, mol] using hz'
  exact ligandZ_injective hz

theorem cipPermutation?_eq_some :
    oneCenter.cipPermutation? = some oneCenter.cipPermutation := by
  exact oneCenter.cipPermutation?_eq_some_of_resolvedCIP stereogenicByCIP

theorem stereogenicByCIPCycleCut : oneCenter.StereogenicByCIPCycleCut := by
  intro i j hkey
  have hhead := congrArg List.head? hkey
  have hlabel :
      toLex (oneCenter.mol.atomZ (some i), oneCenter.mol.atomMass (some i)) =
        toLex (oneCenter.mol.atomZ (some j), oneCenter.mol.atomMass (some j)) := by
    exact
      Option.some.inj
        (by
          simpa [OneCenterMolecule.cipKeyCycleCut, oneCenter, mol,
            MoleculeGraph.cipKeyFromCycleCut_head?] using hhead)
  have hpair :
      (oneCenter.mol.atomZ (some i), oneCenter.mol.atomMass (some i)) =
        (oneCenter.mol.atomZ (some j), oneCenter.mol.atomMass (some j)) :=
    toLex.injective hlabel
  have hz : ligandZ i = ligandZ j := by
    have hz' : oneCenter.mol.atomZ (some i) = oneCenter.mol.atomZ (some j) :=
      congrArg Prod.fst hpair
    simpa [oneCenter, mol] using hz'
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

theorem rs_left_eq_swap_rs_right :
    oneCenter.rs bromochlorofluoromethaneLeftRealization =
      RS.swap (oneCenter.rs bromochlorofluoromethaneRightRealization) := by
  -- We do not compute the CIP permutation here; we only use that every permutation is even or odd.
  rcases permHandedness_eq_one_or_eq_neg_one oneCenter.cipPermutation with hσ | hσ
  · have hright :
        handedness (reindex bromochlorofluoromethaneRightRealization.1 oneCenter.cipPermutation) =
          1 := by
      simpa [bromochlorofluoromethaneRightRealization_handedness] using
        (TetrahedralGeometry.handedness_reindex_even
          bromochlorofluoromethaneRightRealization.1 oneCenter.cipPermutation hσ)
    have hleft :
        handedness (reindex bromochlorofluoromethaneLeftRealization.1 oneCenter.cipPermutation) =
          -1 := by
      simpa [bromochlorofluoromethaneLeftRealization_handedness] using
        (TetrahedralGeometry.handedness_reindex_even
          bromochlorofluoromethaneLeftRealization.1 oneCenter.cipPermutation hσ)
    simp [OneCenterMolecule.rs, RS.swap, hright, hleft]
  · have hright :
        handedness (reindex bromochlorofluoromethaneRightRealization.1 oneCenter.cipPermutation) =
          -1 := by
      simpa [bromochlorofluoromethaneRightRealization_handedness] using
        (TetrahedralGeometry.handedness_reindex_odd
          bromochlorofluoromethaneRightRealization.1 oneCenter.cipPermutation hσ)
    have hleft :
        handedness (reindex bromochlorofluoromethaneLeftRealization.1 oneCenter.cipPermutation) =
          1 := by
      simpa [bromochlorofluoromethaneLeftRealization_handedness] using
        (TetrahedralGeometry.handedness_reindex_odd
          bromochlorofluoromethaneLeftRealization.1 oneCenter.cipPermutation hσ)
    simp [OneCenterMolecule.rs, RS.swap, hright, hleft]

theorem rs_right_ne_rs_left :
    oneCenter.rs bromochlorofluoromethaneRightRealization ≠
      oneCenter.rs bromochlorofluoromethaneLeftRealization := by
  intro h
  have h' :
      oneCenter.rs bromochlorofluoromethaneRightRealization =
        RS.swap (oneCenter.rs bromochlorofluoromethaneRightRealization) := by
    calc
      oneCenter.rs bromochlorofluoromethaneRightRealization =
          oneCenter.rs bromochlorofluoromethaneLeftRealization := h
      _ = RS.swap (oneCenter.rs bromochlorofluoromethaneRightRealization) := by
          exact rs_left_eq_swap_rs_right
  cases hr : oneCenter.rs bromochlorofluoromethaneRightRealization <;>
    simp [RS.swap, hr] at h'

/-! ### Computing the CIP sorting parity for CHBrClF -/

open Prod.Lex

noncomputable section

private def keyWithTie (i : Fin 4) : (List MoleculeGraph.AtomLabel) ×ₗ (Fin 4) :=
  toLex (oneCenter.cipKey i, i)

private def descRel (i j : Fin 4) : Prop :=
  keyWithTie j ≤ keyWithTie i

private theorem keyWithTie_injective : Function.Injective keyWithTie := by
  intro i j hij
  have : (oneCenter.cipKey i, i) = (oneCenter.cipKey j, j) := toLex.injective hij
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
    (oneCenter.cipKey i).head? = some (toLex (ligandZ i, 0)) := by
  simp [OneCenterMolecule.cipKey, oneCenter, mol, MoleculeGraph.cipKeyFrom_head?]

private theorem cipKey_eq_cons_tail (i : Fin 4) :
    oneCenter.cipKey i = toLex (ligandZ i, 0) :: (oneCenter.cipKey i).tail := by
  apply List.eq_cons_of_mem_head?
  simp [cipKey_head?]

private theorem cipKey_lt_of_ligandZ_lt {i j : Fin 4} (h : ligandZ i < ligandZ j) :
    oneCenter.cipKey i < oneCenter.cipKey j := by
  classical
  have hi := cipKey_eq_cons_tail (i := i)
  have hj := cipKey_eq_cons_tail (i := j)
  have hlabel : (toLex (ligandZ i, 0) : MoleculeGraph.AtomLabel) < toLex (ligandZ j, 0) :=
    (Prod.Lex.toLex_lt_toLex).2 (Or.inl h)
  have hlex :
      List.Lex (· < ·)
        (toLex (ligandZ i, 0) :: (oneCenter.cipKey i).tail)
        (toLex (ligandZ j, 0) :: (oneCenter.cipKey j).tail) :=
    List.Lex.rel hlabel
  have hlt :
      (toLex (ligandZ i, 0) :: (oneCenter.cipKey i).tail) <
        (toLex (ligandZ j, 0) :: (oneCenter.cipKey j).tail) :=
    (List.lt_iff_lex_lt _ _).2 hlex
  exact lt_of_lt_of_eq (lt_of_eq_of_lt hi hlt) hj.symm

private theorem descRel_of_ligandZ_lt {i j : Fin 4} (h : ligandZ j < ligandZ i) : descRel i j := by
  dsimp [descRel, keyWithTie]
  have hkey : oneCenter.cipKey j < oneCenter.cipKey i :=
    cipKey_lt_of_ligandZ_lt (i := j) (j := i) h
  have hlt :
      (toLex (oneCenter.cipKey j, j) : (List MoleculeGraph.AtomLabel) ×ₗ (Fin 4)) <
        toLex (oneCenter.cipKey i, i) :=
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

theorem cipOrder_eq_expected : oneCenter.cipOrder = [1, 2, 3, 0] := by
  classical
  have hpairOrder : oneCenter.cipOrder.Pairwise descRel := by
    simpa [OneCenterMolecule.cipOrder, descRel] using
      (List.pairwise_mergeSort' (r := descRel) (l := List.finRange 4))
  have hperm : oneCenter.cipOrder.Perm ([1, 2, 3, 0] : List (Fin 4)) :=
    (oneCenter.cipOrder_perm_finRange).trans perm_expected_cipOrder.symm
  exact (List.Perm.eq_of_pairwise' hpairOrder pairwise_expected_cipOrder hperm)

def cipPermutation_expected : Equiv.Perm (Fin 4) :=
  (Equiv.swap (0 : Fin 4) 3) * (Equiv.swap (0 : Fin 4) 2) * (Equiv.swap (0 : Fin 4) 1)

theorem cipPermutation_eq_expected : oneCenter.cipPermutation = cipPermutation_expected := by
  classical
  ext i
  fin_cases i <;> simp [cipPermutation_expected, OneCenterMolecule.cipPermutation, cipOrder_eq_expected] <;> decide

theorem permHandedness_cipPermutation : permHandedness oneCenter.cipPermutation = -1 := by
  classical
  have hs02 : permHandedness (Equiv.swap (0 : Fin 4) 2) = -1 := by
    norm_num [permHandedness, Equiv.Perm.sign_swap (by decide : (0 : Fin 4) ≠ 2)]
  have hs03 : permHandedness (Equiv.swap (0 : Fin 4) 3) = -1 := by
    norm_num [permHandedness, Equiv.Perm.sign_swap (by decide : (0 : Fin 4) ≠ 3)]
  simp [cipPermutation_eq_expected, cipPermutation_expected, hs02, hs03, permHandedness_swap]

/-- Under the corrected tetrahedral calibration (negative oriented volume is `R`), the
canonical right-handed CHBrClF realization has odd CIP-normalized handedness `-1`, hence the
descriptor is `R`. -/
theorem rs_right_eq_R : oneCenter.rs bromochlorofluoromethaneRightRealization = RS.R := by
  have hσ : permHandedness oneCenter.cipPermutation = -1 := permHandedness_cipPermutation
  have hhand :
      handedness (reindex bromochlorofluoromethaneRightRealization.1 oneCenter.cipPermutation) = -1 := by
    simpa [bromochlorofluoromethaneRightRealization_handedness] using
      (TetrahedralGeometry.handedness_reindex_odd
        bromochlorofluoromethaneRightRealization.1 oneCenter.cipPermutation hσ)
  simp [OneCenterMolecule.rs, hhand]

/-- Historical API key retained for downstream imports.  Its statement follows the corrected
calibration (right realization `R`); the accurate name is `rs_right_eq_R`. -/
theorem rs_right_eq_S : oneCenter.rs bromochlorofluoromethaneRightRealization = RS.R :=
  rs_right_eq_R

theorem rs?_right_eq_some_R :
    oneCenter.rs? bromochlorofluoromethaneRightRealization = some RS.R := by
  simpa [rs_right_eq_R] using
    oneCenter.rs?_eq_some_rs_of_resolvedCIP stereogenicByCIP bromochlorofluoromethaneRightRealization

/-- Historical API key retained for downstream imports; the corrected value is `R`. -/
theorem rs?_right_eq_some_S :
    oneCenter.rs? bromochlorofluoromethaneRightRealization = some RS.R :=
  rs?_right_eq_some_R

theorem rsCycleCut?_right_eq_some_rsCycleCut :
    oneCenter.rsCycleCut? bromochlorofluoromethaneRightRealization =
      some (oneCenter.rsCycleCut bromochlorofluoromethaneRightRealization) := by
  exact oneCenter.rsCycleCut?_eq_some_rsCycleCut_of_resolvedCIPCycleCut
    stereogenicByCIPCycleCut bromochlorofluoromethaneRightRealization

theorem rsCIP?_right_eq_some_rsCIP :
    oneCenter.rsCIP? bromochlorofluoromethaneRightRealization =
      some (oneCenter.rsCIP bromochlorofluoromethaneRightRealization) := by
  exact oneCenter.rsCIP?_eq_some_rsCIP_of_resolvedCIPDescriptor
    stereogenicByCIPDescriptor bromochlorofluoromethaneRightRealization

/-- With even total CIP parity the canonical left-handed mirror realizes handedness `1`, which
the corrected calibration maps to `S`. -/
theorem rs_left_eq_S : oneCenter.rs bromochlorofluoromethaneLeftRealization = RS.S := by
  have hσ : permHandedness oneCenter.cipPermutation = -1 := permHandedness_cipPermutation
  have hhand :
      handedness (reindex bromochlorofluoromethaneLeftRealization.1 oneCenter.cipPermutation) = 1 := by
    simpa [bromochlorofluoromethaneLeftRealization_handedness] using
      (TetrahedralGeometry.handedness_reindex_odd
        bromochlorofluoromethaneLeftRealization.1 oneCenter.cipPermutation hσ)
  simp [OneCenterMolecule.rs, hhand]

/-- Historical API key retained for downstream imports.  Its statement follows the corrected
calibration (left realization `S`); the accurate name is `rs_left_eq_S`. -/
theorem rs_left_eq_R : oneCenter.rs bromochlorofluoromethaneLeftRealization = RS.S :=
  rs_left_eq_S

theorem rs?_left_eq_some_S :
    oneCenter.rs? bromochlorofluoromethaneLeftRealization = some RS.S := by
  simpa [rs_left_eq_S] using
    oneCenter.rs?_eq_some_rs_of_resolvedCIP stereogenicByCIP bromochlorofluoromethaneLeftRealization

/-- Historical API key retained for downstream imports; the corrected value is `S`. -/
theorem rs?_left_eq_some_R :
    oneCenter.rs? bromochlorofluoromethaneLeftRealization = some RS.S :=
  rs?_left_eq_some_S

theorem rsCycleCut?_left_eq_some_rsCycleCut :
    oneCenter.rsCycleCut? bromochlorofluoromethaneLeftRealization =
      some (oneCenter.rsCycleCut bromochlorofluoromethaneLeftRealization) := by
  exact oneCenter.rsCycleCut?_eq_some_rsCycleCut_of_resolvedCIPCycleCut
    stereogenicByCIPCycleCut bromochlorofluoromethaneLeftRealization

theorem rsCIP?_left_eq_some_rsCIP :
    oneCenter.rsCIP? bromochlorofluoromethaneLeftRealization =
      some (oneCenter.rsCIP bromochlorofluoromethaneLeftRealization) := by
  exact oneCenter.rsCIP?_eq_some_rsCIP_of_resolvedCIPDescriptor
    stereogenicByCIPDescriptor bromochlorofluoromethaneLeftRealization

end

end CHBrClF

end Examples
end TetraStereo
