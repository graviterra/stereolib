import TetraStereo.OneCenter.MultiCenterConfiguration
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace TetraStereo
namespace Examples

open OneCenter

/-!
  A minimal two-center “meso” toy:

  - Two tetrahedral centers (`Bool`) each with four ligands (`Fin 4`),
  - a symmetry swapping the two centers and matching ligands by index,
  - a configuration with opposite local handedness at the two centers,
    which becomes equivalent to its mirror under that symmetry.

This models the group-theoretic shape of a meso compound: swapping the two stereocenters
identifies the configuration with its mirror image.
-/

namespace MesoToy

abbrev Atom := Bool ⊕ (Bool × Fin 4)

def centerSet : Finset Atom :=
  {Sum.inl false, Sum.inl true}

def bond : Atom → Atom → BondOrder
  | Sum.inl k, Sum.inr (k', _) => if k = k' then 1 else 0
  | Sum.inr (k', _), Sum.inl k => if k = k' then 1 else 0
  | _, _ => 0

def mol : MoleculeGraph Atom where
  atomZ := fun _ => 0
  bond := bond
  bond_symm := by
    intro u v
    cases u <;> cases v <;> simp [bond]
  bond_self := by
    intro u
    cases u <;> simp [bond]

def multi : MultiCenterMolecule Atom where
  mol := mol
  centers := centerSet
  ligandAtom := by
    intro c hc
    cases c with
    | inl k =>
        intro i
        exact Sum.inr (k, i)
    | inr p =>
        intro i
        simp [centerSet] at hc
  ligandAtom_adj := by
    intro c hc i
    cases c with
    | inl k =>
        -- The ligand enumeration is `inr (k,i)` and `bond` is `1` on matching center/ligand bits.
        simp [MoleculeGraph.Adj, mol, bond]
    | inr p =>
        simp [centerSet] at hc
  ligandAtom_injective := by
    intro c hc i j hij
    cases c with
    | inl k =>
        -- `inr (k,·)` is injective.
        simpa using congrArg Prod.snd (Sum.inr.inj hij)
    | inr p =>
        simp [centerSet] at hc
  ligandAtom_surjective := by
    intro c hc v hv
    cases c with
    | inl k =>
        cases v with
        | inl k' =>
            -- no center-center bonds
            simp [MoleculeGraph.Adj, mol, bond] at hv
        | inr p =>
            rcases p with ⟨k', i⟩
            -- adjacency forces `k = k'`
            have hk : k = k' := by
              by_cases h : k = k'
              · exact h
              · -- then bond is `0`, contradicting `0 < 0`
                simp [MoleculeGraph.Adj, mol, bond, h] at hv
            refine ⟨i, ?_⟩
            -- rewrite `k'` to `k`
            subst hk
            rfl
    | inr p =>
        simp [centerSet] at hc

def flip : Atom → Atom
  | Sum.inl k => Sum.inl (!k)
  | Sum.inr (k, i) => Sum.inr (!k, i)

theorem flip_involutive : Function.Involutive flip := by
  intro x
  cases x <;> simp [flip]

def flipPerm : Equiv.Perm Atom :=
  { toFun := flip
    invFun := flip
    left_inv := by
      intro x
      simpa using flip_involutive x
    right_inv := by
      intro x
      simpa using flip_involutive x }

theorem flipPerm_mem_molAut : flipPerm ∈ multi.mol.Aut := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v
    simp [multi, mol, flipPerm, flip]
  · intro v
    simp [multi, mol, flipPerm, flip]
  · intro v
    rfl
  · intro u v
    cases u with
    | inl k =>
        cases v with
        | inl k' =>
            simp [multi, mol, bond, flipPerm, flip]
        | inr p =>
            rcases p with ⟨k', i⟩
            cases k <;> cases k' <;> simp [multi, mol, bond, flipPerm, flip]
    | inr p =>
        cases v with
        | inl k =>
            rcases p with ⟨k', i⟩
            cases k <;> cases k' <;> simp [multi, mol, bond, flipPerm, flip]
        | inr q =>
            simp [multi, mol, bond, flipPerm, flip]

theorem flipPerm_preservesCenters : multi.PreservesCenters flipPerm := by
  intro c
  cases c with
  | inl k =>
      cases k <;> simp [multi, centerSet, flipPerm, flip]
  | inr p =>
      simp [multi, centerSet, flipPerm, flip]

def flipAut : multi.Aut :=
  ⟨flipPerm, ⟨flipPerm_mem_molAut, flipPerm_preservesCenters⟩⟩

theorem ligandPermAt_flipAut_eq_one (c : multi.Center) : multi.ligandPermAt flipAut c = 1 := by
  classical
  ext i
  have hi : multi.ligandPermAt flipAut c i = i := by
    apply multi.ligandAtomAt_injective (multi.centerPerm flipAut c)
    have hAtom :=
      multi.ligandAtomAt_ligandPermAt (e := flipAut) (c := c) i
    -- Reduce the transported ligand to the explicit flip of the center bit.
    calc
      multi.ligandAtomAt (multi.centerPerm flipAut c) (multi.ligandPermAt flipAut c i)
          = (flipAut : Equiv.Perm Atom) (multi.ligandAtomAt c i) := hAtom
      _ = multi.ligandAtomAt (multi.centerPerm flipAut c) i := by
            cases c with
            | mk c hc =>
                cases c with
                | inl k =>
                    -- `centerPerm` flips the center bit, and `ligandAtomAt` uses that bit.
                    simp [multi, flipAut, flipPerm, flip, MultiCenterMolecule.centerPerm]
                | inr p =>
                    simp [centerSet, multi] at hc
  simpa using congrArg Fin.val hi

def cfg : multi.Configuration :=
  fun c =>
    match c.1 with
    | Sum.inl false => 1
    | Sum.inl true => Equiv.swap (0 : Fin 4) 1
    | _ => 1

theorem cfg_sign (c : multi.Center) :
    multi.configurationSign cfg c =
      if c.1 = Sum.inl false then (1 : ℝ) else (-1 : ℝ) := by
  classical
  cases c with
  | mk c hc =>
      cases c with
      | inl k =>
          cases k <;> simp [cfg, MultiCenterMolecule.configurationSign, OneCenter.permHandedness]
      | inr p =>
          simp [centerSet, multi] at hc

theorem achiralConfigurationBySymmetry : multi.AchiralConfigurationBySymmetry cfg := by
  classical
  refine ⟨flipAut, ?_⟩
  funext c
  -- Abbreviate the center preimage under the symmetry-induced permutation of centers.
  let pre : multi.Center := ((multi.centerPerm flipAut)⁻¹ c)
  have hlig : permHandedness (multi.ligandPermAt flipAut pre) = 1 := by
    have h := congrArg permHandedness (ligandPermAt_flipAut_eq_one (c := pre))
    simpa using h
  have hswap : multi.configurationSign cfg pre = -multi.configurationSign cfg c := by
    cases c with
    | mk c hc =>
        cases c with
        | inl k =>
            cases k <;>
              simp [pre, cfg_sign, multi, flipAut, flipPerm, flip, MultiCenterMolecule.centerPerm]
        | inr p =>
            simp [centerSet, multi] at hc
  calc
    multi.configurationSign (flipAut • cfg) c
        = multi.configurationSign cfg pre * permHandedness (multi.ligandPermAt flipAut pre) := by
            simpa [pre] using (multi.configurationSign_smul (e := flipAut) (cfg := cfg) c)
    _ = multi.configurationSign cfg pre := by simp [hlig]
    _ = -multi.configurationSign cfg c := hswap
    _ = multi.configurationSign (multi.mirrorConfiguration cfg) c := by
          simpa using (multi.configurationSign_mirrorConfiguration (cfg := cfg) (c := c)).symm

end MesoToy

end Examples
end TetraStereo
