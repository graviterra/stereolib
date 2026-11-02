import TetraStereo.OneCenter.MultiCenterCIP
import TetraStereo.OneCenter.GraphStereoPipeline
import TetraStereo.OneCenter.MultiCenterRS
import TetraStereo.OneCenter.MultiCenterCIPRSRelations
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false

namespace TetraStereo
namespace Examples

open OneCenter

/-!
  A small two-center “organic” meso example (toy).

  We model `CH₃–CH(Cl)–CH(Cl)–CH₃` as:
  - two tetrahedral centers (`Bool`) connected by a single bond,
  - three additional ligands on each center: methyl carbon, chlorine, hydrogen,
  - a symmetry swapping the two halves of the molecule,
  - a configuration with opposite local handedness at the two centers,
    which is equivalent to its mirror under that symmetry (meso shape).

  This stays at the graph + parity layer; it is not yet a full CIP or geometric embedding.
-/

namespace DichloroButaneMesoToy

abbrev LigandKind := Fin 3

def methyl : LigandKind := 0
def chlorine : LigandKind := 1
def hydrogen : LigandKind := 2

abbrev Atom := Bool ⊕ (Bool × LigandKind)

def bond : Atom → Atom → BondOrder
  | Sum.inl k, Sum.inl k' => if k = k' then 0 else 1
  | Sum.inl k, Sum.inr (k', _) => if k = k' then 1 else 0
  | Sum.inr (k', _), Sum.inl k => if k = k' then 1 else 0
  | _, _ => 0

def ligandAtomAt (k : Bool) : Fin 4 → Atom
  | 0 => Sum.inl (!k)
  | 1 => Sum.inr (k, methyl)
  | 2 => Sum.inr (k, chlorine)
  | 3 => Sum.inr (k, hydrogen)

def mol : MoleculeGraph Atom where
  atomZ
    | Sum.inl _ => 6
    | Sum.inr (_, l) => if l = methyl then 6 else if l = chlorine then 17 else 1
  bond := bond
  bond_symm := by
    intro u v
    cases u <;> cases v <;> simp [bond, eq_comm]
  bond_self := by
    intro u
    cases u <;> simp [bond]

def centerSet : Finset Atom :=
  {Sum.inl false, Sum.inl true}

theorem tetrahedralCenterSet_eq_centerSet : mol.tetrahedralCenterSet = centerSet := by
  ext c
  cases c with
  | inl k =>
      cases k <;> decide
  | inr p =>
      rcases p with ⟨k, l⟩
      cases k <;> fin_cases l <;> decide

theorem detectedMultiCenterMolecule_centers_eq_centerSet :
    mol.detectedMultiCenterMolecule.centers = centerSet := by
  simpa [MoleculeGraph.detectedMultiCenterMolecule] using tetrahedralCenterSet_eq_centerSet

def detectedCenter (k : Bool) : mol.GraphCenter :=
  ⟨Sum.inl k, by simp [MoleculeGraph.detectedStereoSystem,
    MoleculeGraph.detectedMultiCenterMolecule, tetrahedralCenterSet_eq_centerSet, centerSet]⟩

def multi : MultiCenterMolecule Atom where
  mol := mol
  centers := centerSet
  ligandAtom := fun c _hc =>
    match c with
    | Sum.inl k => ligandAtomAt k
    | Sum.inr _ => fun _ => Sum.inl false
  ligandAtom_adj := by
    intro c hc i
    cases c with
    | inl k =>
        fin_cases i <;>
          simp [MoleculeGraph.Adj, mol, bond, ligandAtomAt, methyl, chlorine, hydrogen]
    | inr p =>
      simp [centerSet] at hc
  ligandAtom_injective := by
    intro c hc
    cases c with
    | inl k =>
        intro i j hij
        fin_cases i <;> fin_cases j <;> cases hij <;> rfl
    | inr p =>
      simp [centerSet] at hc
  ligandAtom_surjective := by
    intro c hc v hv
    cases c with
    | inl k =>
        cases v with
        | inl k' =>
            have hv' : (0 : ℕ) < mol.bond (Sum.inl k) (Sum.inl k') := by
              simpa [MoleculeGraph.Adj, mol] using hv
            have hn : k ≠ k' := by
              intro hEq
              have hv0 := hv'
              simp [mol, bond, hEq] at hv0
            have hk : k' = !k := by
              cases k <;> cases k' <;> simp at hn ⊢
            refine ⟨(0 : Fin 4), ?_⟩
            subst hk
            rfl
        | inr p =>
            rcases p with ⟨k', l⟩
            have hv' : (0 : ℕ) < mol.bond (Sum.inl k) (Sum.inr (k', l)) := by
              simpa [MoleculeGraph.Adj, mol] using hv
            have hk : k = k' := by
              by_cases hEq : k = k'
              · exact hEq
              · exfalso
                have hv0 := hv'
                simp [mol, bond, hEq] at hv0
            subst hk
            fin_cases l
            · refine ⟨(1 : Fin 4), ?_⟩
              rfl
            · refine ⟨(2 : Fin 4), ?_⟩
              rfl
            · refine ⟨(3 : Fin 4), ?_⟩
              rfl
    | inr p =>
      simp [centerSet] at hc

def flip : Atom → Atom
  | Sum.inl k => Sum.inl (!k)
  | Sum.inr (k, l) => Sum.inr (!k, l)

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
    cases v with
    | inl k =>
        simp [multi, mol, flipPerm, flip]
    | inr p =>
        rcases p with ⟨k, l⟩
        fin_cases l <;> simp [multi, mol, flipPerm, flip, methyl, chlorine]
  · intro v
    cases v <;> simp [multi, mol, flipPerm, flip]
  · intro v
    rfl
  · intro u v
    cases u <;> cases v <;> simp [multi, mol, bond, flipPerm, flip]

def flipGraphAut : mol.Aut :=
  ⟨flipPerm, by simpa [multi] using flipPerm_mem_molAut⟩

theorem flipPerm_preservesCenters : multi.PreservesCenters flipPerm := by
  intro c
  cases c with
  | inl k =>
      cases k <;> simp [multi, centerSet, flipPerm, flip]
  | inr p =>
      simp [multi, centerSet, flipPerm, flip]

def flipAut : multi.Aut :=
  ⟨flipPerm, ⟨flipPerm_mem_molAut, flipPerm_preservesCenters⟩⟩

def graphFlipStereoAut : mol.GraphStereoAut :=
  mol.graphStereoAutOfGraphAut flipGraphAut

theorem graphFlipStereoAut_center_false :
    mol.detectedStereoSystem.centerPerm graphFlipStereoAut (detectedCenter false) =
      detectedCenter true := by
  apply Subtype.ext
  simp [graphFlipStereoAut, MoleculeGraph.graphStereoAutOfGraphAut,
    MoleculeGraph.detectedMultiCenterAutOfGraphAut, MoleculeGraph.detectedStereoSystem,
    MultiCenterMolecule.centerPerm, detectedCenter, flipGraphAut, flipPerm, flip]

theorem graphFlipStereoAut_center_true :
    mol.detectedStereoSystem.centerPerm graphFlipStereoAut (detectedCenter true) =
      detectedCenter false := by
  apply Subtype.ext
  simp [graphFlipStereoAut, MoleculeGraph.graphStereoAutOfGraphAut,
    MoleculeGraph.detectedMultiCenterAutOfGraphAut, MoleculeGraph.detectedStereoSystem,
    MultiCenterMolecule.centerPerm, detectedCenter, flipGraphAut, flipPerm, flip]

theorem ligandPermAt_flipAut_eq_one (c : multi.Center) : multi.ligandPermAt flipAut c = 1 := by
  classical
  ext i
  have hi : multi.ligandPermAt flipAut c i = i := by
    apply multi.ligandAtomAt_injective (multi.centerPerm flipAut c)
    have hAtom :=
      multi.ligandAtomAt_ligandPermAt (e := flipAut) (c := c) i
    calc
      multi.ligandAtomAt (multi.centerPerm flipAut c) (multi.ligandPermAt flipAut c i)
          = (flipAut : Equiv.Perm Atom) (multi.ligandAtomAt c i) := hAtom
      _ = multi.ligandAtomAt (multi.centerPerm flipAut c) i := by
            cases c with
            | mk c hc =>
                cases c with
                | inl k =>
                    fin_cases i <;>
                      simp [MultiCenterMolecule.ligandAtomAt, multi, mol, centerSet, flipAut, flipPerm, flip, ligandAtomAt,
                        MultiCenterMolecule.centerPerm, methyl, chlorine, hydrogen]
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
              simp [pre, cfg_sign, multi, mol, centerSet, flipAut, flipPerm, flip,
                MultiCenterMolecule.centerPerm]
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

/-- Under the corrected calibration `configurationSign` `+1` maps to `S` and `-1` maps to `R`:
the mixed configuration has `S` at the `false` center and `R` at the `true` center. -/
theorem cfg_rs (c : multi.Center) :
    multi.configurationRS cfg c =
      if c.1 = Sum.inl false then RS.S else RS.R := by
  classical
  -- Reduce to the corresponding handedness sign; the `@[simp]` lemmas for `RS.ofHandedness`
  -- then compute the label.
  have hs := cfg_sign (c := c)
  by_cases h : c.1 = Sum.inl false
  · have : multi.configurationSign cfg c = (1 : ℝ) := by simpa [h] using hs
    simp [MultiCenterMolecule.configurationRS, MultiCenterMolecule.rsPatternOfSignPattern, h, this]
  · have : multi.configurationSign cfg c = (-1 : ℝ) := by simpa [h] using hs
    simp [MultiCenterMolecule.configurationRS, MultiCenterMolecule.rsPatternOfSignPattern, h, this]

theorem achiralConfigurationBySymmetry_rs :
    ∃ e : multi.Aut, multi.configurationRS (e • cfg) = multi.mirrorRSPattern (multi.configurationRS cfg) := by
  classical
  rcases achiralConfigurationBySymmetry with ⟨e, he⟩
  refine ⟨e, ?_⟩
  have heRS : multi.configurationRS (e • cfg) = multi.configurationRS (multi.mirrorConfiguration cfg) := by
    funext c
    have hc : multi.configurationSign (e • cfg) c = multi.configurationSign (multi.mirrorConfiguration cfg) c :=
      congrArg (fun s => s c) he
    simpa [MultiCenterMolecule.configurationRS, MultiCenterMolecule.rsPatternOfSignPattern] using
      congrArg RS.ofHandedness hc
  exact heRS.trans (multi.configurationRS_mirrorConfiguration (cfg := cfg))

/-!
  A “companion” configuration with the *same* local handedness at both centers.  In this toy,
  the only nontrivial molecular automorphism is the half-swap `flipAut`, which does *not* turn a
  same-sign pattern into its negation, so this configuration is `ChiralConfigurationBySymmetry`.
-/

def cfgSame : multi.Configuration :=
  fun _ => 1

theorem cfgSame_sign (c : multi.Center) : multi.configurationSign cfgSame c = 1 := by
  simp [cfgSame, MultiCenterMolecule.configurationSign, OneCenter.permHandedness]

private theorem image_ligand (e : multi.Aut) {k k' : Bool}
    (hCenter : (e : Equiv.Perm Atom) (Sum.inl k) = Sum.inl k') (l : LigandKind) :
    (e : Equiv.Perm Atom) (Sum.inr (k, l)) = Sum.inr (k', l) := by
  classical
  let eMol : mol.Aut :=
    ⟨(e : Equiv.Perm Atom),
      by
        -- `multi.mol = mol` by definition.
        simpa [multi] using (MultiCenterMolecule.Aut.mem_molAut (m := multi) e)⟩
  -- The image cannot be a center (since `e` preserves `centerSet` membership).
  have hnotCenter : (e : Equiv.Perm Atom) (Sum.inr (k, l)) ∉ centerSet := by
    intro hmem
    have hiff :
        ((e : Equiv.Perm Atom) (Sum.inr (k, l)) ∈ centerSet) ↔ (Sum.inr (k, l) ∈ centerSet) := by
      simpa [multi] using
        (MultiCenterMolecule.Aut.apply_mem_centers_iff (m := multi) (e := e) (c := Sum.inr (k, l)))
    have : ¬ (Sum.inr (k, l) ∈ centerSet) := by simp [centerSet]
    exact this (hiff.1 hmem)
  cases hY : (e : Equiv.Perm Atom) (Sum.inr (k, l)) with
  | inl b =>
      have : (Sum.inl b : Atom) ∈ centerSet := by cases b <;> simp [centerSet]
      exact (False.elim (hnotCenter (by simpa [hY] using this)))
  | inr p =>
      rcases p with ⟨b, l'⟩
      -- Identify `l'` from the atomic number.
      have hz : mol.atomZ (Sum.inr (b, l')) = mol.atomZ (Sum.inr (k, l)) := by
        have hz0 :
            mol.atomZ ((e : Equiv.Perm Atom) (Sum.inr (k, l))) = mol.atomZ (Sum.inr (k, l)) :=
          eMol.property.1 (Sum.inr (k, l))
        rw [hY] at hz0
        exact hz0
      have hl : l' = l := by
        fin_cases l <;> fin_cases l' <;>
          first
          | (simp; done)
          | (simp [mol, methyl, chlorine] at hz)
      subst l'
      -- Identify `b` from adjacency to the image center.
      have hAdj : mol.Adj ((e : Equiv.Perm Atom) (Sum.inl k)) (Sum.inr (b, l)) := by
        have hxAdj : mol.Adj (Sum.inl k) (Sum.inr (k, l)) := by
          simp [MoleculeGraph.Adj, mol, bond]
        have hxAdj' :
            mol.Adj ((e : Equiv.Perm Atom) (Sum.inl k)) ((e : Equiv.Perm Atom) (Sum.inr (k, l))) := by
          exact (MoleculeGraph.Aut.adj_iff (m := mol) eMol (Sum.inl k) (Sum.inr (k, l))).2 hxAdj
        simpa [hY] using hxAdj'
      have hAdj' : mol.Adj (Sum.inl k') (Sum.inr (b, l)) := by
        simpa [hCenter] using hAdj
      have hb : b = k' := by
        cases k' <;> cases b <;> simp [MoleculeGraph.Adj, mol, bond] at hAdj' ⊢
      subst hb
      simp

private theorem aut_eq_one_or_flipAut (e : multi.Aut) : e = 1 ∨ e = flipAut := by
  classical
  have hmem : (e : Equiv.Perm Atom) (Sum.inl false) ∈ centerSet := by
    have : (Sum.inl false : Atom) ∈ centerSet := by simp [centerSet]
    exact (MultiCenterMolecule.Aut.mem_centers_iff (m := multi) (e := e) (c := Sum.inl false)).1 this
  have hcases :
      (e : Equiv.Perm Atom) (Sum.inl false) = Sum.inl false ∨
        (e : Equiv.Perm Atom) (Sum.inl false) = Sum.inl true := by
    simpa [centerSet] using hmem
  rcases hcases with hfix | hswap
  · left
    ext v
    cases v with
    | inl k =>
        cases k with
        | false => simpa using hfix
        | true =>
            have : (e : Equiv.Perm Atom) (Sum.inl true) = Sum.inl true := by
              -- The other center must map to the other center (only two centers, and `e` is injective).
              have hmem' : (e : Equiv.Perm Atom) (Sum.inl true) ∈ centerSet := by
                have : (Sum.inl true : Atom) ∈ centerSet := by simp [centerSet]
                exact (MultiCenterMolecule.Aut.mem_centers_iff (m := multi) (e := e) (c := Sum.inl true)).1 this
              have hcases' :
                  (e : Equiv.Perm Atom) (Sum.inl true) = Sum.inl false ∨
                    (e : Equiv.Perm Atom) (Sum.inl true) = Sum.inl true := by
                simpa [centerSet] using hmem'
              rcases hcases' with h0 | h1
              · have : (Sum.inl true : Atom) = Sum.inl false := by
                  apply (e : Equiv.Perm Atom).injective
                  simpa [hfix] using h0
                cases this
              · exact h1
            simpa using this
    | inr p =>
        rcases p with ⟨k, l⟩
        cases k with
        | false =>
            have := image_ligand (e := e) (k := false) (k' := false) hfix l
            simpa using this
        | true =>
            have hCenterTrue : (e : Equiv.Perm Atom) (Sum.inl true) = Sum.inl true := by
              -- same as the center case above
              have hmem' : (e : Equiv.Perm Atom) (Sum.inl true) ∈ centerSet := by
                have : (Sum.inl true : Atom) ∈ centerSet := by simp [centerSet]
                exact (MultiCenterMolecule.Aut.mem_centers_iff (m := multi) (e := e) (c := Sum.inl true)).1 this
              have hcases' :
                  (e : Equiv.Perm Atom) (Sum.inl true) = Sum.inl false ∨
                    (e : Equiv.Perm Atom) (Sum.inl true) = Sum.inl true := by
                simpa [centerSet] using hmem'
              rcases hcases' with h0 | h1
              · have : (Sum.inl true : Atom) = Sum.inl false := by
                  apply (e : Equiv.Perm Atom).injective
                  simpa [hfix] using h0
                cases this
              · exact h1
            have := image_ligand (e := e) (k := true) (k' := true) hCenterTrue l
            simpa using this
  · right
    ext v
    cases v with
    | inl k =>
        cases k with
        | false =>
            simpa [flipAut, flipPerm, flip] using hswap
        | true =>
            have : (e : Equiv.Perm Atom) (Sum.inl true) = Sum.inl false := by
              -- Since `e false = true`, the other center must go to `false`.
              have hmem' : (e : Equiv.Perm Atom) (Sum.inl true) ∈ centerSet := by
                have : (Sum.inl true : Atom) ∈ centerSet := by simp [centerSet]
                exact (MultiCenterMolecule.Aut.mem_centers_iff (m := multi) (e := e) (c := Sum.inl true)).1 this
              have hcases' :
                  (e : Equiv.Perm Atom) (Sum.inl true) = Sum.inl false ∨
                    (e : Equiv.Perm Atom) (Sum.inl true) = Sum.inl true := by
                simpa [centerSet] using hmem'
              rcases hcases' with h0 | h1
              · exact h0
              · have : (Sum.inl true : Atom) = Sum.inl false := by
                  apply (e : Equiv.Perm Atom).injective
                  simpa [hswap] using h1
                cases this
            simpa [flipAut, flipPerm, flip] using this
    | inr p =>
        rcases p with ⟨k, l⟩
        cases k with
        | false =>
            have := image_ligand (e := e) (k := false) (k' := true) hswap l
            simpa [flipAut, flipPerm, flip] using this
        | true =>
            have hCenterTrue : (e : Equiv.Perm Atom) (Sum.inl true) = Sum.inl false := by
              -- same as the center case above
              have hmem' : (e : Equiv.Perm Atom) (Sum.inl true) ∈ centerSet := by
                have : (Sum.inl true : Atom) ∈ centerSet := by simp [centerSet]
                exact (MultiCenterMolecule.Aut.mem_centers_iff (m := multi) (e := e) (c := Sum.inl true)).1 this
              have hcases' :
                  (e : Equiv.Perm Atom) (Sum.inl true) = Sum.inl false ∨
                    (e : Equiv.Perm Atom) (Sum.inl true) = Sum.inl true := by
                simpa [centerSet] using hmem'
              rcases hcases' with h0 | h1
              · exact h0
              · have : (Sum.inl true : Atom) = Sum.inl false := by
                  apply (e : Equiv.Perm Atom).injective
                  simpa [hswap] using h1
                cases this
            have := image_ligand (e := e) (k := true) (k' := false) hCenterTrue l
            simpa [flipAut, flipPerm, flip] using this

theorem chiralConfigurationBySymmetry_cfgSame : multi.ChiralConfigurationBySymmetry cfgSame := by
  classical
  -- Reduce to the sign-pattern criterion.
  refine (multi.chiralConfigurationBySymmetry_iff_forall_smul_ne_neg (cfg := cfgSame)).2 ?_
  intro e
  rcases aut_eq_one_or_flipAut (e := e) with rfl | rfl
  · -- identity symmetry: `s ≠ -s`
    intro hs
    let c0 : multi.Center := ⟨Sum.inl false, by simp [multi, centerSet]⟩
    have := congrArg (fun s => s c0) hs
    simp [cfgSame_sign (c := c0)] at this
    have hne : (1 : ℝ) ≠ (-1 : ℝ) := by norm_num
    exact hne this
  · -- half-swap symmetry: still `s ≠ -s`
    intro hs
    let c0 : multi.Center := ⟨Sum.inl false, by simp [multi, centerSet]⟩
    have := congrArg (fun s => s c0) hs
    -- `flipAut` acts by permuting centers, but induces an even (indeed trivial) ligand permutation.
    have hlig : permHandedness (multi.ligandPermAt flipAut (((multi.centerPerm flipAut)⁻¹) c0)) = 1 := by
      have h := congrArg permHandedness (ligandPermAt_flipAut_eq_one (c := ((multi.centerPerm flipAut)⁻¹) c0))
      simpa using h
    have hlig' :
        permHandedness (multi.ligandPermAt flipAut ((Equiv.symm (multi.centerPerm flipAut)) c0)) = 1 := by
      simpa using hlig
    have hthis : (flipAut • multi.configurationSign cfgSame) c0 = -1 := by
      simpa [cfgSame_sign (c := c0)] using this
    have h1 : (flipAut • multi.configurationSign cfgSame) c0 = 1 := by
      change multi.smulSignPattern flipAut (multi.configurationSign cfgSame) c0 = 1
      simp [MultiCenterMolecule.smulSignPattern, cfgSame_sign, hlig']
    have hEq : (1 : ℝ) = (-1 : ℝ) := by
      exact h1.symm.trans hthis
    have hne : (1 : ℝ) ≠ (-1 : ℝ) := by norm_num
    exact hne hEq

/-!
  ### CIP and combinatorial `R/S` labels

  The symmetry-based achiral/chiral results above are purely parity-driven.

  Here we additionally compute the (simplified) CIP sorting permutation at each stereocenter and
  derive a per-center `R/S` label for the two configurations via the parity test
  `permHandedness (σ * cipPermutation)`.
-/

open Prod.Lex

noncomputable section

namespace CIP

/-- Atomic numbers of the four ligands (by index), for both stereocenters. -/
def ligandZ : Fin 4 → AtomicNumber :=
  ![6, 6, 17, 1]

private def center (k : Bool) : multi.Center :=
  ⟨Sum.inl k, by cases k <;> simp [multi, centerSet]⟩

private abbrev oneCenter (k : Bool) : OneCenterMolecule Atom :=
  multi.toOneCenterMolecule (center k)

private def keyWithTie (k : Bool) (i : Fin 4) : (List MoleculeGraph.AtomLabel) ×ₗ (Fin 4) :=
  toLex ((oneCenter k).cipKey i, i)

private def descRel (k : Bool) (i j : Fin 4) : Prop :=
  keyWithTie k j ≤ keyWithTie k i

private theorem keyWithTie_injective (k : Bool) : Function.Injective (keyWithTie k) := by
  intro i j hij
  have : ((oneCenter k).cipKey i, i) = ((oneCenter k).cipKey j, j) := toLex.injective hij
  exact congrArg Prod.snd this

private instance (k : Bool) : Std.Antisymm (descRel k) :=
  ⟨by
    intro a b hab hba
    apply keyWithTie_injective (k := k)
    dsimp [descRel] at hab hba
    exact le_antisymm hba hab⟩

private instance (k : Bool) : DecidableRel (descRel k) := by
  intro i j
  dsimp [descRel, keyWithTie]
  infer_instance

private instance (k : Bool) : IsTrans (Fin 4) (descRel k) :=
  ⟨by
    intro a b c hab hbc
    dsimp [descRel] at hab hbc ⊢
    exact le_trans hbc hab⟩

private instance (k : Bool) : Std.Total (descRel k) :=
  ⟨by
    intro a b
    dsimp [descRel]
    simpa [or_comm] using (le_total (keyWithTie k b) (keyWithTie k a))⟩

private theorem ligandZ_eq (k : Bool) (i : Fin 4) :
    (oneCenter k).mol.atomZ ((oneCenter k).ligandAtom i) = ligandZ i := by
  cases k <;> fin_cases i <;>
    simp [oneCenter, center, MultiCenterMolecule.toOneCenterMolecule, MultiCenterMolecule.ligandAtomAt,
      ligandZ, multi, mol, ligandAtomAt, methyl, chlorine, hydrogen]

private theorem cipKey_head? (k : Bool) (i : Fin 4) :
    ((oneCenter k).cipKey i).head? = some (toLex (ligandZ i, 0)) := by
  classical
  cases k <;> fin_cases i <;>
    simp [OneCenterMolecule.cipKey, oneCenter, center, MultiCenterMolecule.toOneCenterMolecule,
      MultiCenterMolecule.ligandAtomAt, MoleculeGraph.cipKeyFrom_head?, ligandZ, multi, mol, ligandAtomAt, methyl,
      chlorine, hydrogen]

private theorem cipKey_eq_cons_tail (k : Bool) (i : Fin 4) :
    (oneCenter k).cipKey i = toLex (ligandZ i, 0) :: ((oneCenter k).cipKey i).tail := by
  apply List.eq_cons_of_mem_head?
  simp [cipKey_head? (k := k) (i := i)]

private theorem cipKey_lt_of_ligandZ_lt (k : Bool) {i j : Fin 4} (h : ligandZ i < ligandZ j) :
    (oneCenter k).cipKey i < (oneCenter k).cipKey j := by
  classical
  have hi := cipKey_eq_cons_tail (k := k) (i := i)
  have hj := cipKey_eq_cons_tail (k := k) (i := j)
  have hlabel : (toLex (ligandZ i, 0) : MoleculeGraph.AtomLabel) < toLex (ligandZ j, 0) :=
    (Prod.Lex.toLex_lt_toLex).2 (Or.inl h)
  have hlex :
      List.Lex (· < ·)
        (toLex (ligandZ i, 0) :: ((oneCenter k).cipKey i).tail)
        (toLex (ligandZ j, 0) :: ((oneCenter k).cipKey j).tail) :=
    List.Lex.rel hlabel
  have hlt :
      (toLex (ligandZ i, 0) :: ((oneCenter k).cipKey i).tail) <
        (toLex (ligandZ j, 0) :: ((oneCenter k).cipKey j).tail) :=
    (List.lt_iff_lex_lt _ _).2 hlex
  exact lt_of_lt_of_eq (lt_of_eq_of_lt hi hlt) hj.symm

private theorem descRel_of_ligandZ_lt (k : Bool) {i j : Fin 4} (h : ligandZ j < ligandZ i) :
    descRel k i j := by
  dsimp [descRel, keyWithTie]
  have hkey : (oneCenter k).cipKey j < (oneCenter k).cipKey i :=
    cipKey_lt_of_ligandZ_lt (k := k) (i := j) (j := i) h
  have hlt :
      (toLex ((oneCenter k).cipKey j, j) : (List MoleculeGraph.AtomLabel) ×ₗ (Fin 4)) <
        toLex ((oneCenter k).cipKey i, i) :=
    (Prod.Lex.toLex_lt_toLex).2 (Or.inl hkey)
  exact le_of_lt hlt

private theorem cipKey_lt_methyl_lt_chain (k : Bool) :
    (oneCenter k).cipKey (1 : Fin 4) < (oneCenter k).cipKey (0 : Fin 4) := by
  classical
  -- The methyl carbon is a leaf away from the stereocenter, so its CIP key is a singleton.
  have hfin :
      (oneCenter k).mol.neighborFinset (Sum.inr (k, methyl)) = {Sum.inl k} := by
    ext v
    cases v with
    | inl val =>
        by_cases h : val = k
        · subst h
          simp [MoleculeGraph.mem_neighborFinset, MoleculeGraph.Adj, oneCenter, center,
            MultiCenterMolecule.toOneCenterMolecule, MultiCenterMolecule.ligandAtomAt,
            multi, mol, bond, methyl]
        · simp [MoleculeGraph.mem_neighborFinset, MoleculeGraph.Adj, oneCenter, center,
            MultiCenterMolecule.toOneCenterMolecule, MultiCenterMolecule.ligandAtomAt,
            multi, mol, bond, methyl, h]
    | inr p =>
        simp [MoleculeGraph.mem_neighborFinset, MoleculeGraph.Adj, oneCenter, center,
          MultiCenterMolecule.toOneCenterMolecule, MultiCenterMolecule.ligandAtomAt,
          multi, mol, bond, methyl]
  have hbond :
      (oneCenter k).mol.bond (Sum.inr (k, methyl)) (Sum.inl k) = 1 := by
    simp [oneCenter, center, MultiCenterMolecule.toOneCenterMolecule, multi, mol, bond, methyl]
  have hkeyM :
      (oneCenter k).cipKey (1 : Fin 4) = [toLex (ligandZ (1 : Fin 4), 0)] := by
    -- Unfold `cipKey` and apply the leaf lemma for `cipKeyFrom`.
    have hleaf :
        MoleculeGraph.cipKeyFrom (oneCenter k).mol (Sum.inl k) (Sum.inr (k, methyl)) =
          [toLex ((oneCenter k).mol.atomZ (Sum.inr (k, methyl)), (oneCenter k).mol.atomMass (Sum.inr (k, methyl)))] :=
      MoleculeGraph.cipKeyFrom_eq_singleton_of_neighborFinset_eq_singleton (m := (oneCenter k).mol)
        (center := Sum.inl k) (start := Sum.inr (k, methyl)) hfin hbond
    simpa [OneCenterMolecule.cipKey, oneCenter, center, MultiCenterMolecule.toOneCenterMolecule,
      MultiCenterMolecule.ligandAtomAt, ligandZ, multi, mol, bond, ligandAtomAt, methyl, chlorine, hydrogen] using hleaf
  have hlenC : 1 < ((oneCenter k).cipKey (0 : Fin 4)).length := by
    -- The carbon-chain ligand has a neighbor away from the stereocenter (its chlorine).
    have hlen :
        1 <
          (MoleculeGraph.cipKeyFrom (oneCenter k).mol (Sum.inl k) (Sum.inl (!k))).length :=
      MoleculeGraph.cipKeyFrom_length_gt_one_of_exists_adj_ne_center (m := (oneCenter k).mol)
        (center := Sum.inl k) (start := Sum.inl (!k))
        ⟨Sum.inr (!k, chlorine), by
          constructor
          · intro hEq
            cases hEq
          · simp [MoleculeGraph.Adj, oneCenter, center, MultiCenterMolecule.toOneCenterMolecule, multi, mol, bond,
              methyl, chlorine]⟩
    simpa [OneCenterMolecule.cipKey, oneCenter, center, multi, mol, ligandAtomAt, methyl, chlorine, hydrogen] using hlen
  -- Compare by lexicographic prefix: singleton key < key with the same head and a nonempty tail.
  have h0 := cipKey_eq_cons_tail (k := k) (i := (0 : Fin 4))
  cases ht : ((oneCenter k).cipKey (0 : Fin 4)).tail with
  | nil =>
      have : ((oneCenter k).cipKey (0 : Fin 4)).length = 1 := by
        have hkey : (oneCenter k).cipKey (0 : Fin 4) = toLex (ligandZ (0 : Fin 4), 0) :: [] := by
          simpa [ht] using h0
        simp [hkey]
      exact (Nat.not_lt_of_ge (Nat.le_of_eq this) hlenC).elim
  | cons t ts =>
      have h0' :
          (oneCenter k).cipKey (0 : Fin 4) = toLex (ligandZ (0 : Fin 4), 0) :: t :: ts := by
        simpa [ht] using h0
      have h1' :
          (oneCenter k).cipKey (1 : Fin 4) = toLex (ligandZ (0 : Fin 4), 0) :: [] := by
        -- both carbon ligands have `Z = 6`
        have hz : ligandZ (0 : Fin 4) = ligandZ (1 : Fin 4) := by decide
        simp [hkeyM, hz]
      have hlex :
          List.Lex (· < ·)
            (toLex (ligandZ (0 : Fin 4), 0) :: [])
            (toLex (ligandZ (0 : Fin 4), 0) :: t :: ts) :=
        List.Lex.cons List.Lex.nil
      have hlt :
          (toLex (ligandZ (0 : Fin 4), 0) :: []) <
            (toLex (ligandZ (0 : Fin 4), 0) :: t :: ts) :=
        (List.lt_iff_lex_lt _ _).2 hlex
      exact lt_of_eq_of_lt h1' (lt_of_lt_of_eq hlt h0'.symm)

private theorem descRel_methyl_lt_chain (k : Bool) : descRel k (0 : Fin 4) (1 : Fin 4) := by
  dsimp [descRel, keyWithTie]
  have hkey : (oneCenter k).cipKey (1 : Fin 4) < (oneCenter k).cipKey (0 : Fin 4) :=
    cipKey_lt_methyl_lt_chain (k := k)
  have hlt :
      (toLex ((oneCenter k).cipKey (1 : Fin 4), (1 : Fin 4)) :
          (List MoleculeGraph.AtomLabel) ×ₗ (Fin 4)) <
        toLex ((oneCenter k).cipKey (0 : Fin 4), (0 : Fin 4)) :=
    (Prod.Lex.toLex_lt_toLex).2 (Or.inl hkey)
  exact le_of_lt hlt

private theorem pairwise_expected_cipOrder (k : Bool) :
    ([2, 0, 1, 3] : List (Fin 4)).Pairwise (descRel k) := by
  refine (List.pairwise_cons).2 ?_
  constructor
  · intro a ha
    simp at ha
    rcases ha with rfl | rfl | rfl
    · exact descRel_of_ligandZ_lt (k := k) (i := (2 : Fin 4)) (j := (0 : Fin 4)) (by decide)
    · exact descRel_of_ligandZ_lt (k := k) (i := (2 : Fin 4)) (j := (1 : Fin 4)) (by decide)
    · exact descRel_of_ligandZ_lt (k := k) (i := (2 : Fin 4)) (j := (3 : Fin 4)) (by decide)
  · refine (List.pairwise_cons).2 ?_
    constructor
    · intro a ha
      simp at ha
      rcases ha with rfl | rfl
      · exact descRel_methyl_lt_chain (k := k)
      · exact descRel_of_ligandZ_lt (k := k) (i := (0 : Fin 4)) (j := (3 : Fin 4)) (by decide)
    · refine (List.pairwise_cons).2 ?_
      constructor
      · intro a ha
        simp at ha
        rcases ha with rfl
        exact descRel_of_ligandZ_lt (k := k) (i := (1 : Fin 4)) (j := (3 : Fin 4)) (by decide)
      · simp

private theorem perm_expected_cipOrder : ([2, 0, 1, 3] : List (Fin 4)).Perm (List.finRange 4) := by
  have hfin : (List.finRange 4 : List (Fin 4)) = [0, 1, 2, 3] := by
    decide
  have h02 : ([2, 0, 1, 3] : List (Fin 4)).Perm [0, 2, 1, 3] := by
    simpa using (List.Perm.swap (x := (2 : Fin 4)) (y := (0 : Fin 4)) [1, 3]).symm
  have h21 : ([2, 1, 3] : List (Fin 4)).Perm [1, 2, 3] := by
    simpa using (List.Perm.swap (x := (2 : Fin 4)) (y := (1 : Fin 4)) [3]).symm
  have hrest : ([0, 2, 1, 3] : List (Fin 4)).Perm [0, 1, 2, 3] := by
    simpa using List.Perm.cons (0 : Fin 4) h21
  have h : ([2, 0, 1, 3] : List (Fin 4)).Perm [0, 1, 2, 3] :=
    List.Perm.trans h02 hrest
  simpa [hfin] using h

theorem cipOrder_eq_expected (k : Bool) : (oneCenter k).cipOrder = [2, 0, 1, 3] := by
  classical
  have hpairOrder : (oneCenter k).cipOrder.Pairwise (descRel k) := by
    simpa [OneCenterMolecule.cipOrder, descRel] using
      (List.pairwise_mergeSort' (r := descRel k) (l := List.finRange 4))
  have hperm : (oneCenter k).cipOrder.Perm ([2, 0, 1, 3] : List (Fin 4)) :=
    ((oneCenter k).cipOrder_perm_finRange).trans perm_expected_cipOrder.symm
  exact (List.Perm.eq_of_pairwise' hpairOrder (pairwise_expected_cipOrder (k := k)) hperm)

def cipPermutation_expected : Equiv.Perm (Fin 4) :=
  (Equiv.swap (0 : Fin 4) 1) * (Equiv.swap (0 : Fin 4) 2)

theorem cipPermutation_eq_expected (k : Bool) :
    (oneCenter k).cipPermutation = cipPermutation_expected := by
  classical
  ext i
  fin_cases i <;>
    simp [cipPermutation_expected, OneCenterMolecule.cipPermutation, cipOrder_eq_expected (k := k)] <;> decide

theorem stereogenicByCIP (k : Bool) : (oneCenter k).StereogenicByCIP := by
  intro i j hkey
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals exfalso
  · exact (ne_of_lt (cipKey_lt_methyl_lt_chain (k := k))) hkey.symm
  · exact (ne_of_lt (cipKey_lt_of_ligandZ_lt (k := k) (i := (0 : Fin 4)) (j := 2) (by decide))) hkey
  · exact (ne_of_lt (cipKey_lt_of_ligandZ_lt (k := k) (i := (3 : Fin 4)) (j := 0) (by decide))) hkey.symm
  · exact (ne_of_lt (cipKey_lt_methyl_lt_chain (k := k))) hkey
  · exact (ne_of_lt (cipKey_lt_of_ligandZ_lt (k := k) (i := (1 : Fin 4)) (j := 2) (by decide))) hkey
  · exact (ne_of_lt (cipKey_lt_of_ligandZ_lt (k := k) (i := (3 : Fin 4)) (j := 1) (by decide))) hkey.symm
  · exact (ne_of_lt (cipKey_lt_of_ligandZ_lt (k := k) (i := (0 : Fin 4)) (j := 2) (by decide))) hkey.symm
  · exact (ne_of_lt (cipKey_lt_of_ligandZ_lt (k := k) (i := (1 : Fin 4)) (j := 2) (by decide))) hkey.symm
  · exact (ne_of_lt (cipKey_lt_of_ligandZ_lt (k := k) (i := (3 : Fin 4)) (j := 2) (by decide))) hkey.symm
  · exact (ne_of_lt (cipKey_lt_of_ligandZ_lt (k := k) (i := (3 : Fin 4)) (j := 0) (by decide))) hkey
  · exact (ne_of_lt (cipKey_lt_of_ligandZ_lt (k := k) (i := (3 : Fin 4)) (j := 1) (by decide))) hkey
  · exact (ne_of_lt (cipKey_lt_of_ligandZ_lt (k := k) (i := (3 : Fin 4)) (j := 2) (by decide))) hkey

theorem permHandedness_cipPermutation (k : Bool) : permHandedness (oneCenter k).cipPermutation = 1 := by
  classical
  have hs02 : permHandedness (Equiv.swap (0 : Fin 4) 2) = -1 := by
    norm_num [permHandedness, Equiv.Perm.sign_swap (by decide : (0 : Fin 4) ≠ 2)]
  -- `swap (0) 1` is `-1`, so the product is even.
  simp [cipPermutation_eq_expected (k := k), cipPermutation_expected, permHandedness_mul, hs02, permHandedness_swap]

theorem permHandedness_cipPermutationAt (k : Bool) :
    permHandedness (multi.cipPermutationAt (center k)) = 1 := by
  simpa [MultiCenterMolecule.cipPermutationAt, oneCenter, center] using permHandedness_cipPermutation (k := k)

end CIP

open OneCenter.RS

private theorem center_eq_false_or_true (c : multi.Center) :
    c = CIP.center false ∨ c = CIP.center true := by
  have hm : (c : Atom) ∈ centerSet := c.property
  dsimp [centerSet] at hm
  rcases (Finset.mem_insert.1 hm) with h | h
  · left
    apply Subtype.ext
    simpa [CIP.center] using h
  · right
    apply Subtype.ext
    simpa [CIP.center] using (Finset.mem_singleton.1 h)

private theorem center_false_ne_true : CIP.center false ≠ CIP.center true := by
  intro h
  have hv := congrArg Subtype.val h
  cases (Sum.inl.inj hv)

theorem allCentersResolvedByCIP : multi.AllCentersResolvedByCIP := by
  intro c
  rcases center_eq_false_or_true c with rfl | rfl
  · simpa [MultiCenterMolecule.StereogenicByCIPAt, CIP.oneCenter] using
      CIP.stereogenicByCIP false
  · simpa [MultiCenterMolecule.StereogenicByCIPAt, CIP.oneCenter] using
      CIP.stereogenicByCIP true

private theorem centerPerm_flipAut_false :
    multi.centerPerm flipAut (CIP.center false) = CIP.center true := by
  apply Subtype.ext
  simp [MultiCenterMolecule.centerPerm, CIP.center, multi, centerSet, flipAut, flipPerm, flip]

private theorem centerPerm_flipAut_true :
    multi.centerPerm flipAut (CIP.center true) = CIP.center false := by
  apply Subtype.ext
  simp [MultiCenterMolecule.centerPerm, CIP.center, multi, centerSet, flipAut, flipPerm, flip]

/-- A purely combinatorial `R/S` label at a center, computed from the CIP-normalized handedness. -/
def rsAt (cfg : multi.Configuration) (c : multi.Center) : RS :=
  RS.ofHandedness (multi.cipConfigurationSign cfg c)

/-- Under the corrected calibration, the CIP-normalized sign `+1` at the `false` center is `S`. -/
theorem rsAt_cfg_false_eq_S : rsAt cfg (CIP.center false) = RS.S := by
  have hperm : permHandedness (multi.cipPermutationAt (CIP.center false)) = 1 :=
    CIP.permHandedness_cipPermutationAt (k := false)
  have hcfg : multi.configurationSign cfg (CIP.center false) = (1 : ℝ) := by
    simpa [CIP.center] using (cfg_sign (c := CIP.center false))
  have hsign : multi.cipConfigurationSign cfg (CIP.center false) = 1 := by
    simp [hcfg, hperm]
  simp [rsAt, hsign]

/-- Historical API key retained for downstream imports; the corrected value is `S`. -/
theorem rsAt_cfg_false_eq_R : rsAt cfg (CIP.center false) = RS.S :=
  rsAt_cfg_false_eq_S

/-- Under the corrected calibration, the CIP-normalized sign `-1` at the `true` center is `R`. -/
theorem rsAt_cfg_true_eq_R : rsAt cfg (CIP.center true) = RS.R := by
  have hperm : permHandedness (multi.cipPermutationAt (CIP.center true)) = 1 :=
    CIP.permHandedness_cipPermutationAt (k := true)
  have hcfg : multi.configurationSign cfg (CIP.center true) = (-1 : ℝ) := by
    simpa [CIP.center] using (cfg_sign (c := CIP.center true))
  have hsign : multi.cipConfigurationSign cfg (CIP.center true) = -1 := by
    simp [hcfg, hperm]
  simp [rsAt, hsign]

/-- Historical API key retained for downstream imports; the corrected value is `R`. -/
theorem rsAt_cfg_true_eq_S : rsAt cfg (CIP.center true) = RS.R :=
  rsAt_cfg_true_eq_R

theorem rsAt_cfgSame_false_eq_S : rsAt cfgSame (CIP.center false) = RS.S := by
  have hperm : permHandedness (multi.cipPermutationAt (CIP.center false)) = 1 :=
    CIP.permHandedness_cipPermutationAt (k := false)
  have hsign : multi.cipConfigurationSign cfgSame (CIP.center false) = 1 := by
    simp [cfgSame_sign (c := CIP.center false), hperm]
  simp [rsAt, hsign]

/-- Historical API key retained for downstream imports; the corrected value is `S`. -/
theorem rsAt_cfgSame_false_eq_R : rsAt cfgSame (CIP.center false) = RS.S :=
  rsAt_cfgSame_false_eq_S

theorem rsAt_cfgSame_true_eq_S : rsAt cfgSame (CIP.center true) = RS.S := by
  have hperm : permHandedness (multi.cipPermutationAt (CIP.center true)) = 1 :=
    CIP.permHandedness_cipPermutationAt (k := true)
  have hsign : multi.cipConfigurationSign cfgSame (CIP.center true) = 1 := by
    simp [cfgSame_sign (c := CIP.center true), hperm]
  simp [rsAt, hsign]

/-- Historical API key retained for downstream imports; the corrected value is `S`. -/
theorem rsAt_cfgSame_true_eq_R : rsAt cfgSame (CIP.center true) = RS.S :=
  rsAt_cfgSame_true_eq_S

/-- The `RR` representative of the CIP-normalized two-center `R/S` quotient. -/
def cipRSPatternRR : multi.CipRSPattern :=
  multi.constantCipRSPattern RS.R

/-- The `SS` representative of the CIP-normalized two-center `R/S` quotient. -/
def cipRSPatternSS : multi.CipRSPattern :=
  multi.constantCipRSPattern RS.S

/-- The mixed `RS` representative; the half-swap symmetry also represents `SR`.

Under the corrected calibration the mixed configuration `cfg` is `S` at the `false` center and `R`
at the `true` center.  The two-center representative is therefore written with `R` at the `true`
center (`c₀`) and `S` at the `false` center (`c₁`); it agrees with `cfg` at both centers.  The
half-swap symmetry identifies it with the pattern `R` at `false` and `S` at `true`. -/
def cipRSPatternMixed : multi.CipRSPattern :=
  multi.twoCenterCipRSPattern (CIP.center true) (CIP.center false) RS.R RS.S

theorem cipConfigurationRS_cfg_eq_mixed :
    (⟨multi.cipConfigurationRS cfg⟩ : multi.CipRSPattern) = cipRSPatternMixed := by
  ext c
  rcases center_eq_false_or_true c with rfl | rfl
  · simpa [cipRSPatternMixed, MultiCenterMolecule.cipConfigurationRS,
      MultiCenterMolecule.rsPatternOfSignPattern, MultiCenterMolecule.twoCenterCipRSPattern, rsAt,
      CIP.center, center_false_ne_true] using rsAt_cfg_false_eq_S
  · simpa [cipRSPatternMixed, MultiCenterMolecule.cipConfigurationRS,
      MultiCenterMolecule.rsPatternOfSignPattern, MultiCenterMolecule.twoCenterCipRSPattern, rsAt,
      CIP.center] using rsAt_cfg_true_eq_R

theorem cipRSPatternOfConfiguration?_cfg_eq_some_mixed :
    multi.cipRSPatternOfConfiguration? cfg = some cipRSPatternMixed := by
  simpa [cipConfigurationRS_cfg_eq_mixed] using
    multi.cipRSPatternOfConfiguration?_eq_some_of_allCentersResolvedByCIP
      allCentersResolvedByCIP cfg

theorem cipConfigurationRS_cfgSame_eq_SS :
    (⟨multi.cipConfigurationRS cfgSame⟩ : multi.CipRSPattern) = cipRSPatternSS := by
  ext c
  rcases center_eq_false_or_true c with rfl | rfl
  · simpa [cipRSPatternSS, MultiCenterMolecule.cipConfigurationRS,
      MultiCenterMolecule.rsPatternOfSignPattern, rsAt] using rsAt_cfgSame_false_eq_S
  · simpa [cipRSPatternSS, MultiCenterMolecule.cipConfigurationRS,
      MultiCenterMolecule.rsPatternOfSignPattern, rsAt] using rsAt_cfgSame_true_eq_S

/-- Historical API key retained for downstream imports; the corrected pattern is `SS`. -/
theorem cipConfigurationRS_cfgSame_eq_RR :
    (⟨multi.cipConfigurationRS cfgSame⟩ : multi.CipRSPattern) = cipRSPatternSS :=
  cipConfigurationRS_cfgSame_eq_SS

theorem cipRSPatternOfConfiguration?_cfgSame_eq_some_SS :
    multi.cipRSPatternOfConfiguration? cfgSame = some cipRSPatternSS := by
  simpa [cipConfigurationRS_cfgSame_eq_SS] using
    multi.cipRSPatternOfConfiguration?_eq_some_of_allCentersResolvedByCIP
      allCentersResolvedByCIP cfgSame

/-- Historical API key retained for downstream imports; the corrected pattern is `SS`. -/
theorem cipRSPatternOfConfiguration?_cfgSame_eq_some_RR :
    multi.cipRSPatternOfConfiguration? cfgSame = some cipRSPatternSS :=
  cipRSPatternOfConfiguration?_cfgSame_eq_some_SS

theorem cipRSPatternRR_mirror_eq_SS : (-cipRSPatternRR : multi.CipRSPattern) = cipRSPatternSS := by
  ext c
  simp [cipRSPatternRR, cipRSPatternSS, RS.swap]

theorem cipRSPatternSS_mirror_eq_RR : (-cipRSPatternSS : multi.CipRSPattern) = cipRSPatternRR := by
  ext c
  simp [cipRSPatternRR, cipRSPatternSS, RS.swap]

theorem cipRSPatternMixed_mesoBySymmetry :
    multi.MesoCipRSPatternBySymmetry cipRSPatternMixed := by
  simpa [cipRSPatternMixed] using
    (multi.twoCenter_mixed_mesoBySwap (cR := CIP.center true) (cS := CIP.center false)
      center_false_ne_true.symm
      (fun c => (center_eq_false_or_true c).elim Or.inr Or.inl)
      flipAut centerPerm_flipAut_true centerPerm_flipAut_false)

theorem cipRSPatternMixed_achiralBySymmetry :
    multi.AchiralCipRSPatternBySymmetry cipRSPatternMixed :=
  cipRSPatternMixed_mesoBySymmetry

theorem cipRSPatternMixed_quotient_eq_mirror :
    (Quotient.mk'' cipRSPatternMixed : multi.CipRSPatternQ) = Quotient.mk'' (-cipRSPatternMixed) :=
  (multi.achiralCipRSPatternBySymmetry_iff_quotient_eq (s := cipRSPatternMixed)).1
    cipRSPatternMixed_achiralBySymmetry

theorem cipRSPatternRR_chiralBySymmetry :
    multi.ChiralCipRSPatternBySymmetry cipRSPatternRR := by
  simpa [cipRSPatternRR] using multi.constantR_chiralBySymmetry_of_center (CIP.center false)

theorem cipRSPatternSS_chiralBySymmetry :
    multi.ChiralCipRSPatternBySymmetry cipRSPatternSS := by
  simpa [cipRSPatternSS] using multi.constantS_chiralBySymmetry_of_center (CIP.center false)

theorem cipRSPatternRR_SS_enantiomericBySymmetry :
    multi.EnantiomericCipRSPatternsBySymmetry cipRSPatternRR cipRSPatternSS := by
  simpa [cipRSPatternRR, cipRSPatternSS] using
    multi.constantR_constantS_enantiomericBySymmetry_of_center (CIP.center false)

theorem cipRSPatternRR_mixed_diastereomericBySymmetry :
    multi.DiastereomericCipRSPatternsBySymmetry cipRSPatternRR cipRSPatternMixed := by
  simpa [cipRSPatternRR, cipRSPatternMixed] using
    (multi.constantR_diastereomeric_twoCenterMixed (cR := CIP.center true) (cS := CIP.center false)
      center_false_ne_true.symm)

theorem cipRSPatternSS_mixed_diastereomericBySymmetry :
    multi.DiastereomericCipRSPatternsBySymmetry cipRSPatternSS cipRSPatternMixed := by
  simpa [cipRSPatternSS, cipRSPatternMixed] using
    (multi.constantS_diastereomeric_twoCenterMixed (cR := CIP.center true) (cS := CIP.center false)
      center_false_ne_true.symm)

theorem cfg_mesoCipRSConfigurationBySymmetry :
    multi.MesoCipRSConfigurationBySymmetry cfg := by
  simpa [MultiCenterMolecule.MesoCipRSConfigurationBySymmetry,
    MultiCenterMolecule.cipRSPatternOfConfiguration, cipConfigurationRS_cfg_eq_mixed] using
    cipRSPatternMixed_mesoBySymmetry

theorem cfgSame_chiralCipRSConfigurationBySymmetry :
    multi.ChiralCipRSConfigurationBySymmetry cfgSame := by
  simpa [MultiCenterMolecule.ChiralCipRSConfigurationBySymmetry,
    MultiCenterMolecule.cipRSPatternOfConfiguration, cipConfigurationRS_cfgSame_eq_SS] using
    cipRSPatternSS_chiralBySymmetry

theorem cfgSame_mirror_enantiomericCipRSConfigurationsBySymmetry :
    multi.EnantiomericCipRSConfigurationsBySymmetry cfgSame (multi.mirrorConfiguration cfgSame) := by
  exact (multi.enantiomeric_cipRSConfigurations_self_mirror_iff_chiral (cfg := cfgSame)).2
    cfgSame_chiralCipRSConfigurationBySymmetry

theorem cfgSame_cfg_diastereomericCipRSConfigurationsBySymmetry :
    multi.DiastereomericCipRSConfigurationsBySymmetry cfgSame cfg := by
  simpa [MultiCenterMolecule.DiastereomericCipRSConfigurationsBySymmetry,
    MultiCenterMolecule.cipRSPatternOfConfiguration, cipConfigurationRS_cfgSame_eq_SS,
    cipConfigurationRS_cfg_eq_mixed] using
    cipRSPatternSS_mixed_diastereomericBySymmetry

theorem cipRSPatternRR_quotient_ne_mirror :
    (Quotient.mk'' cipRSPatternRR : multi.CipRSPatternQ) ≠ Quotient.mk'' (-cipRSPatternRR) :=
  (multi.chiralCipRSPatternBySymmetry_iff_quotient_ne (s := cipRSPatternRR)).1
    cipRSPatternRR_chiralBySymmetry

theorem cipRSPatternSS_quotient_ne_mirror :
    (Quotient.mk'' cipRSPatternSS : multi.CipRSPatternQ) ≠ Quotient.mk'' (-cipRSPatternSS) :=
  (multi.chiralCipRSPatternBySymmetry_iff_quotient_ne (s := cipRSPatternSS)).1
    cipRSPatternSS_chiralBySymmetry

/-- In this toy, the CIP-normalized `R/S` pattern quotient has exactly three symmetry classes:
`RR`, `SS`, and the mixed orbit `RS ~ SR`. -/
theorem cipRSPatternQ_exactly_three_classes :
    ∃ a b c : multi.CipRSPatternQ, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ ∀ q : multi.CipRSPatternQ, q = a ∨ q = b ∨ q = c := by
  classical
  -- Name the two centers.
  let cFalse : multi.Center := ⟨Sum.inl false, by simp [multi, centerSet]⟩
  let cTrue : multi.Center := ⟨Sum.inl true, by simp [multi, centerSet]⟩

  have center_cases : ∀ c : multi.Center, c = cFalse ∨ c = cTrue := by
    intro c
    have hm : (c : Atom) ∈ centerSet := c.property
    dsimp [centerSet] at hm
    rcases (Finset.mem_insert.1 hm) with h | h
    · left
      apply Subtype.ext
      simpa [cFalse] using h
    · right
      apply Subtype.ext
      simpa [cTrue] using (Finset.mem_singleton.1 h)

  -- Three representative patterns.
  let rsRR : multi.CipRSPattern := ⟨fun _ => RS.R⟩
  let rsSS : multi.CipRSPattern := ⟨fun _ => RS.S⟩
  let rsMixed : multi.CipRSPattern := ⟨fun c => if (c : Atom) = Sum.inl false then RS.R else RS.S⟩

  let qRR : multi.CipRSPatternQ := Quotient.mk'' rsRR
  let qSS : multi.CipRSPatternQ := Quotient.mk'' rsSS
  let qMixed : multi.CipRSPatternQ := Quotient.mk'' rsMixed

  have hcFalse : (cFalse : Atom) = Sum.inl false := rfl
  have hcTrue : (cTrue : Atom) = Sum.inl true := rfl
  have hcTrue_ne : (cTrue : Atom) ≠ Sum.inl false := by
    intro h
    cases (Sum.inl.inj h)

  have qRR_ne_qSS : qRR ≠ qSS := by
    intro h
    have hrel : MulAction.orbitRel multi.Aut multi.CipRSPattern rsRR rsSS := Quotient.exact h
    rcases (MulAction.mem_orbit_iff).1 ((MulAction.orbitRel_apply).1 hrel) with ⟨e, he⟩
    rcases aut_eq_one_or_flipAut (e := e) with rfl | rfl
    · have hval := congrArg (fun s => s cFalse) he
      change multi.smulCipRSPattern (1 : multi.Aut) rsSS cFalse = rsRR cFalse at hval
      simp [MultiCenterMolecule.smulCipRSPattern, rsRR, rsSS] at hval
    · have hval := congrArg (fun s => s cFalse) he
      change multi.smulCipRSPattern flipAut rsSS cFalse = rsRR cFalse at hval
      simp [MultiCenterMolecule.smulCipRSPattern, rsRR, rsSS] at hval

  have qRR_ne_qMixed : qRR ≠ qMixed := by
    intro h
    have hrel : MulAction.orbitRel multi.Aut multi.CipRSPattern rsRR rsMixed := Quotient.exact h
    rcases (MulAction.mem_orbit_iff).1 ((MulAction.orbitRel_apply).1 hrel) with ⟨e, he⟩
    rcases aut_eq_one_or_flipAut (e := e) with rfl | rfl
    · have hval := congrArg (fun s => s cTrue) he
      simp [rsRR, rsMixed, hcTrue] at hval
    · have hval := congrArg (fun s => s cFalse) he
      change multi.smulCipRSPattern flipAut rsMixed cFalse = rsRR cFalse at hval
      simp [MultiCenterMolecule.smulCipRSPattern, rsRR, rsMixed, hcTrue_ne, multi, centerSet, flipAut,
        flipPerm, flip, MultiCenterMolecule.centerPerm, cFalse, cTrue] at hval

  have qSS_ne_qMixed : qSS ≠ qMixed := by
    intro h
    have hrel : MulAction.orbitRel multi.Aut multi.CipRSPattern rsSS rsMixed := Quotient.exact h
    rcases (MulAction.mem_orbit_iff).1 ((MulAction.orbitRel_apply).1 hrel) with ⟨e, he⟩
    rcases aut_eq_one_or_flipAut (e := e) with rfl | rfl
    · have hval := congrArg (fun s => s cFalse) he
      simp [rsSS, rsMixed, hcFalse] at hval
    · have hval := congrArg (fun s => s cTrue) he
      change multi.smulCipRSPattern flipAut rsMixed cTrue = rsSS cTrue at hval
      simp [MultiCenterMolecule.smulCipRSPattern, rsSS, rsMixed, multi, centerSet, flipAut, flipPerm, flip,
        MultiCenterMolecule.centerPerm, cTrue] at hval

  refine ⟨qRR, qSS, qMixed, qRR_ne_qSS, qRR_ne_qMixed, qSS_ne_qMixed, ?_⟩
  intro q
  refine Quotient.inductionOn q ?_
  intro s
  -- Reduce to the values at the two centers.
  cases hF : s cFalse <;> cases hT : s cTrue
  · -- (R,R)
    left
    have hs : s = rsRR := by
      ext c
      rcases center_cases c with rfl | rfl
      · simpa [rsRR] using hF
      · simpa [rsRR] using hT
    simp [qRR, hs]
  · -- (R,S)
    right
    right
    have hs : s = rsMixed := by
      ext c
      rcases center_cases c with rfl | rfl
      · simpa [rsMixed, hcFalse] using hF
      · simpa [rsMixed, hcTrue, hcTrue_ne] using hT
    simp [qMixed, hs]
  · -- (S,R)
    right
    right
    apply Quotient.sound
    refine (MulAction.orbitRel_apply).2 ?_
    refine (MulAction.mem_orbit_iff).2 ?_
    refine ⟨flipAut, ?_⟩
    ext c
    rcases center_cases c with rfl | rfl
    · -- cFalse
      have : (flipAut • rsMixed) cFalse = RS.S := by
        -- `flipAut` swaps the two centers.
        change multi.smulCipRSPattern flipAut rsMixed cFalse = RS.S
        simp [MultiCenterMolecule.smulCipRSPattern, rsMixed, multi, centerSet, flipAut, flipPerm,
          flip, MultiCenterMolecule.centerPerm, cFalse]
      simpa [this] using hF.symm
    · -- cTrue
      have : (flipAut • rsMixed) cTrue = RS.R := by
        change multi.smulCipRSPattern flipAut rsMixed cTrue = RS.R
        simp [MultiCenterMolecule.smulCipRSPattern, rsMixed, multi, centerSet, flipAut, flipPerm,
          flip, MultiCenterMolecule.centerPerm, cTrue]
      simpa [this] using hT.symm
  · -- (S,S)
    right
    left
    have hs : s = rsSS := by
      ext c
      rcases center_cases c with rfl | rfl
      · simpa [rsSS] using hF
      · simpa [rsSS] using hT
    simp [qSS, hs]

end

end DichloroButaneMesoToy

end Examples
end TetraStereo
