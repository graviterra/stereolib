import TetraStereo.OneCenter.CIPSymmetry
import TetraStereo.Examples.CHBrClF
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace TetraStereo
namespace Examples

open OneCenter

/-!
  Small sanity checks for the symmetry-based chirality criterion.

  - Methane (`CH₄`) is *achiral by symmetry*: swapping two hydrogens is an odd symmetry.
  - Bromochlorofluoromethane (`CHBrClF`) is *chiral by symmetry*: distinct ligands force every
    center-fixing automorphism to be even (indeed trivial on ligands).
-/

namespace Methane

abbrev Atom := Option (Fin 4)

def bond : Atom → Atom → BondOrder
  | none, some _ => 1
  | some _, none => 1
  | _, _ => 0

def mol : MoleculeGraph Atom where
  atomZ
    | none => 6
    | some _ => 1
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

def swap01 : Equiv.Perm Atom :=
  Equiv.swap (some (0 : Fin 4)) (some 1)

theorem swap01_mem_Aut : swap01 ∈ oneCenter.mol.Aut := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v
    cases v with
    | none =>
        simp [oneCenter, mol, swap01, Equiv.swap_apply_of_ne_of_ne]
    | some i =>
        fin_cases i <;> simp [oneCenter, mol, swap01, Equiv.swap_apply_of_ne_of_ne]
  · intro v
    cases v <;> simp [oneCenter, mol, swap01, Equiv.swap_apply_of_ne_of_ne]
  · intro v
    rfl
  · intro u v
    cases u with
    | none =>
        cases v with
        | none =>
            simp [oneCenter, mol, bond, swap01, Equiv.swap_apply_of_ne_of_ne]
        | some j =>
            fin_cases j <;> simp [oneCenter, mol, bond, swap01, Equiv.swap_apply_of_ne_of_ne]
    | some i =>
        cases v with
        | none =>
            fin_cases i <;> simp [oneCenter, mol, bond, swap01, Equiv.swap_apply_of_ne_of_ne]
        | some j =>
            fin_cases i <;> fin_cases j <;> simp [oneCenter, mol, bond, swap01, Equiv.swap_apply_of_ne_of_ne]

def swap01CenterAut : oneCenter.CenterAut :=
  ⟨swap01, ⟨swap01_mem_Aut, by simp [oneCenter, swap01, Equiv.swap_apply_of_ne_of_ne]⟩⟩

theorem ligandPermHom_swap01 :
    oneCenter.ligandPermHom swap01CenterAut = Equiv.swap (0 : Fin 4) 1 := by
  classical
  ext i
  have hi :
      (oneCenter.ligandPermHom swap01CenterAut) i = (Equiv.swap (0 : Fin 4) 1) i := by
    apply oneCenter.ligandAtom_injective
    have hlig :
        oneCenter.ligandAtom ((oneCenter.ligandPermHom swap01CenterAut) i) =
          (swap01CenterAut : Equiv.Perm Atom) (oneCenter.ligandAtom i) := by
      change
        oneCenter.ligandAtom (oneCenter.ligandPerm swap01CenterAut i) =
          (swap01CenterAut : Equiv.Perm Atom) (oneCenter.ligandAtom i)
      exact oneCenter.ligandAtom_ligandPerm (e := swap01CenterAut) i
    -- `ligandAtom` is `some`, and `swap01` swaps `some 0` and `some 1`.
    rw [hlig]
    fin_cases i <;> simp [oneCenter, swap01CenterAut, swap01, Equiv.swap_apply_of_ne_of_ne]
  simpa using congrArg Fin.val hi

theorem achiralBySymmetry : oneCenter.AchiralBySymmetry := by
  refine ⟨swap01CenterAut, ?_⟩
  -- The induced ligand permutation is the transposition `(0 1)`.
  simp [ligandPermHom_swap01]

example : Subsingleton (oneCenter.StereoQ) :=
  oneCenter.subsingleton_stereoQ_of_achiralBySymmetry achiralBySymmetry

end Methane

namespace CHBrClF

open Examples.CHBrClF

theorem chiralBySymmetry : oneCenter.ChiralBySymmetry := by
  exact oneCenter.chiralBySymmetry_of_stereogenicByCIP stereogenicByCIP

example : ∃ a b : oneCenter.StereoQ, a ≠ b ∧ ∀ q : oneCenter.StereoQ, q = a ∨ q = b :=
  oneCenter.stereoQ_exactly_two_classes_of_stereogenicByCIP stereogenicByCIP

end CHBrClF

end Examples
end TetraStereo
