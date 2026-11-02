import TetraStereo.OneCenter.MultiCenterConfiguration
import TetraStereo.KernelOnly
import Mathlib.Combinatorics.SimpleGraph.Walks.Maps
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Frame-aware rooted branch symmetry at a tetrahedral center

This module is the independent source-symmetry counterpart of a CIP rule-5 sort step.  It works
with the actual `MultiCenterMolecule.Configuration` of `TetraStereo.OneCenter.MultiCenterConfiguration`
and with automorphisms of the molecular graph.  No root-attachment parity, pseudoasymmetry
comparator, or label-opposition data is used.

The central relation `BranchTransport m cfg c i j mirror` asks for a graph automorphism `e` that

* fixes the root center `c` (`centerPerm e c = c`, in particular it fixes the root attachment),
* carries ligand index `i` to ligand index `j` at the root (`ligandPermAt e c i = j`), and
* for every center `d` lying in the ligand branch rooted at `i`, relates the local frame sign of
  the *transported* configuration `e • cfg` at the image center `centerPerm e d` to the sign of
  `cfg` at that image center by the global mirror factor.

The third condition is genuinely frame-aware: the local ligand permutation `ligandPermAt e d` is
present at every center.  In particular the parity of the root attachment is never consulted, and
only centers in the chosen ligand branch are constrained.
-/

namespace TetraStereo
namespace OneCenter
namespace RootedTetrahedralBranchSymmetry

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Stable definitions -/

/-- `LigandBranchReaches m c i v` holds when `v` can be reached from the ligand atom attached at
index `i` of the root center `c` by a walk of the underlying simple graph whose support avoids the
root center itself.  Thus this is reachability inside the ligand branch at `i` after deleting the
root. -/
def LigandBranchReaches (m : MultiCenterMolecule V) (c : m.Center) (i : Fin 4)
    (v : V) : Prop :=
  ∃ p : m.mol.underlyingSimpleGraph.Walk (m.ligandAtomAt c i) v,
    c.1 ∉ p.support

/-- Frame-aware rooted branch transport.

`BranchTransport m cfg c i j mirror` says that an automorphism `e` of the molecular graph fixes the
root center `c`, sends ligand index `i` to ligand index `j`, and realizes the global frame
relation prescribed by `mirror` simultaneously at every center of the ligand branch at `i`.

The local factor `permHandedness (ligandPermAt e d)` is the parity of the actual ligand
reindexing induced by `e` at `d`; by `configurationSign_mul_ligandPermAt` it is exactly the local
factor in `configurationSign (e • cfg) (centerPerm e d)`. -/
def BranchTransport (m : MultiCenterMolecule V) (cfg : m.Configuration) (c : m.Center)
    (i j : Fin 4) (mirror : Bool) : Prop :=
  ∃ e : m.Aut,
    m.centerPerm e c = c ∧
    m.ligandPermAt e c i = j ∧
      ∀ d : m.Center, LigandBranchReaches m c i d.1 →
        m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) =
          (if mirror then -1 else 1) * m.configurationSign cfg (m.centerPerm e d)

/-- Proper (non-mirror) branch transport. -/
def ProperTransport (m : MultiCenterMolecule V) (cfg : m.Configuration) (c : m.Center)
    (i j : Fin 4) : Prop :=
  BranchTransport m cfg c i j false

/-- Mirror (improper) branch transport. -/
def MirrorTransport (m : MultiCenterMolecule V) (cfg : m.Configuration) (c : m.Center)
    (i j : Fin 4) : Prop :=
  BranchTransport m cfg c i j true

/-- Two distinct ligand branches at the root are enantiomorphic when a mirror transport relates
them but no proper transport does. -/
def Enantiomorphic (m : MultiCenterMolecule V) (cfg : m.Configuration) (c : m.Center)
    (i j : Fin 4) : Prop :=
  i ≠ j ∧ MirrorTransport m cfg c i j ∧ ¬ ProperTransport m cfg c i j

/-- Pairwise disjoint ligand branches at a root: no vertex belongs to the deleted-root branch of
two distinct ligand indices.  This is the explicit structural domain needed for the chemical
reading of branch independence.  It is a hypothesis, not a theorem about arbitrary molecular
graphs (rings and axial units are not claimed to satisfy it). -/
def PairwiseDisjointLigandBranches (m : MultiCenterMolecule V) (c : m.Center) : Prop :=
  ∀ i j : Fin 4, i ≠ j → ∀ v : V,
    LigandBranchReaches m c i v → LigandBranchReaches m c j v → False

/-! ### Local frame transport -/

/-- The local factor appearing in `BranchTransport` is the actual configuration sign of the
transported configuration `e • cfg` at the image center.  This is the frame-awareness bridge and
uses the existing `configurationSign_smul` theorem. -/
theorem configurationSign_mul_ligandPermAt (m : MultiCenterMolecule V) (e : m.Aut)
    (cfg : m.Configuration) (d : m.Center) :
    m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) =
      m.configurationSign (e • cfg) (m.centerPerm e d) := by
  have h := m.configurationSign_smul (e := e) (cfg := cfg) (c := m.centerPerm e d)
  simpa [Equiv.symm_apply_apply] using h.symm

/-- Equivalent formulation of `BranchTransport` purely in terms of the transported configuration
sign at the image centers. -/
theorem branchTransport_iff_transportedSign (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (c : m.Center) (i j : Fin 4) (b : Bool) :
    BranchTransport m cfg c i j b ↔
      ∃ e : m.Aut,
        m.centerPerm e c = c ∧
        m.ligandPermAt e c i = j ∧
          ∀ d : m.Center, LigandBranchReaches m c i d.1 →
            m.configurationSign (e • cfg) (m.centerPerm e d) =
              (if b then -1 else 1) * m.configurationSign cfg (m.centerPerm e d) := by
  constructor
  · rintro ⟨e, hc, hi, hsign⟩
    refine ⟨e, hc, hi, fun d hd => ?_⟩
    rw [← configurationSign_mul_ligandPermAt (m := m) (e := e) (cfg := cfg) (d := d)]
    exact hsign d hd
  · rintro ⟨e, hc, hi, hsign⟩
    refine ⟨e, hc, hi, fun d hd => ?_⟩
    rw [configurationSign_mul_ligandPermAt (m := m) (e := e) (cfg := cfg) (d := d)]
    exact hsign d hd

/-! ### Elementary root and reachability facts -/

/-- Elimination principle for the disjoint-branch domain: a single vertex cannot lie in two
distinct ligand branches after the root has been deleted. -/
theorem pairwiseDisjointLigandBranches_elim (m : MultiCenterMolecule V) (c : m.Center)
    (h : PairwiseDisjointLigandBranches m c) {i j : Fin 4} (hij : i ≠ j) {v : V}
    (hi : LigandBranchReaches m c i v) (hj : LigandBranchReaches m c j v) : False :=
  h i j hij v hi hj

/-- A ligand atom is never the root center (the graph has no loops). -/
theorem ligandAtomAt_ne_center (m : MultiCenterMolecule V) (c : m.Center) (i : Fin 4) :
    m.ligandAtomAt c i ≠ c.1 := by
  intro h
  have hadj := m.ligandAtomAt_adj c i
  rw [h] at hadj
  have hloop : ¬ m.mol.Adj c.1 c.1 := by
    simp [MoleculeGraph.Adj, m.mol.bond_self]
  exact hloop hadj

/-- A ligand atom reaches itself inside its own branch by the trivial walk. -/
theorem ligandBranchReaches_self (m : MultiCenterMolecule V) (c : m.Center) (i : Fin 4) :
    LigandBranchReaches m c i (m.ligandAtomAt c i) := by
  refine ⟨SimpleGraph.Walk.nil, ?_⟩
  simp only [SimpleGraph.Walk.support_nil, List.mem_singleton]
  intro h
  exact ligandAtomAt_ne_center m c i h.symm

/-- Equality of centers is equality of their underlying atoms. -/
theorem centerPerm_eq_iff (m : MultiCenterMolecule V) (e : m.Aut) (c : m.Center) :
    m.centerPerm e c = c ↔ (e : Equiv.Perm V) c.1 = c.1 := by
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    simpa [MultiCenterMolecule.centerPerm] using h

/-- The inverse of a root-fixing automorphism also fixes the root. -/
theorem centerPerm_inv_eq (m : MultiCenterMolecule V) (e : m.Aut) (c : m.Center)
    (h : m.centerPerm e c = c) : m.centerPerm e⁻¹ c = c := by
  rw [centerPerm_eq_iff] at h ⊢
  have hinv := congrArg (fun x => ((e : Equiv.Perm V)⁻¹) x) h
  simpa using hinv.symm

/-- `centerPerm` sends inverses of automorphisms to inverse center permutations. -/
theorem centerPerm_inv_apply (m : MultiCenterMolecule V) (e : m.Aut) (d : m.Center) :
    m.centerPerm e⁻¹ d = (m.centerPerm e)⁻¹ d := by
  have h := congrArg (fun p : Equiv.Perm m.Center => p d) (m.centerPermHom.map_inv e)
  simpa [MultiCenterMolecule.centerPermHom] using h

/-- `centerPerm` is multiplicative at a center. -/
theorem centerPerm_mul_apply (m : MultiCenterMolecule V) (e f : m.Aut) (c : m.Center) :
    m.centerPerm (e * f) c = m.centerPerm e (m.centerPerm f c) := by
  have h := congrArg (fun p : Equiv.Perm m.Center => p c) (m.centerPermHom.map_mul e f)
  simpa [MultiCenterMolecule.centerPermHom] using h

/-- At the root, an automorphism carrying ligand index `i` to `j` carries the inverse index `j`
back to `i`. -/
theorem ligandPermAt_inv_apply (m : MultiCenterMolecule V) (e : m.Aut) (c : m.Center)
    (i j : Fin 4) (hc : m.centerPerm e c = c) (hi : m.ligandPermAt e c i = j) :
    m.ligandPermAt e⁻¹ c j = i := by
  have hmul := m.ligandPermAt_mul (e := e⁻¹) (f := e) (c := c)
  have hone : m.ligandPermAt (e⁻¹ * e) c = 1 := by
    simp [MultiCenterMolecule.ligandPermAt_one]
  rw [hone] at hmul
  -- `hmul : 1 = ligandPermAt e⁻¹ (centerPerm e c) * ligandPermAt e c`
  have hprod : m.ligandPermAt e⁻¹ c * m.ligandPermAt e c = 1 := by
    simpa [hc] using hmul.symm
  have happ := congrArg (fun p : Equiv.Perm (Fin 4) => p i) hprod
  simpa [hi] using happ

/-! ### Reachability under a root-fixing automorphism -/

/-- A root-fixing automorphism that sends ligand index `i` to `j` maps the ligand branch at `i`
into the ligand branch at `j`. -/
theorem ligandBranchReaches_map (m : MultiCenterMolecule V) {c : m.Center} {i j : Fin 4}
    {e : m.Aut} (hc : m.centerPerm e c = c) (hi : m.ligandPermAt e c i = j)
    {v : V} (h : LigandBranchReaches m c i v) :
    LigandBranchReaches m c j ((e : Equiv.Perm V) v) := by
  classical
  rcases h with ⟨p, hp⟩
  let f : m.mol.underlyingSimpleGraph →g m.mol.underlyingSimpleGraph :=
    { toFun := (e : Equiv.Perm V)
      map_rel' := by
        intro a b hab
        exact
          (MoleculeGraph.Aut.adj_iff (m := m.mol)
            (e := (⟨(e : Equiv.Perm V),
              MultiCenterMolecule.Aut.mem_molAut (m := m) e⟩ : m.mol.Aut)) a b).2 hab }
  have hstart : f (m.ligandAtomAt c i) = m.ligandAtomAt c j := by
    have h1 := m.ligandAtomAt_ligandPermAt (e := e) (c := c) (i := i)
    rw [hc, hi] at h1
    exact h1.symm
  refine ⟨(p.map f).copy hstart rfl, ?_⟩
  intro hmem
  rw [SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_map, List.mem_map] at hmem
  rcases hmem with ⟨x, hx, hex⟩
  apply hp
  have hce : (e : Equiv.Perm V) c.1 = c.1 := congrArg Subtype.val hc
  have hfx : f x = (e : Equiv.Perm V) x := rfl
  rw [hfx] at hex
  have hxce : x = c.1 := by
    calc x = ((e : Equiv.Perm V)⁻¹) ((e : Equiv.Perm V) x) := by simp
      _ = ((e : Equiv.Perm V)⁻¹) c.1 := by rw [hex]
      _ = c.1 := by
            have hinv := congrArg (fun y => ((e : Equiv.Perm V)⁻¹) y) hce
            simpa using hinv.symm
  rw [hxce] at hx
  exact hx

/-! ### Elementary sign algebra -/

/-- The two possible mirror factors multiply by XOR. -/
theorem mirrorFactor_mul (b b' : Bool) :
    (if b then (-1 : ℝ) else 1) * (if b' then (-1 : ℝ) else 1) =
      (if b ^^ b' then (-1 : ℝ) else 1) := by
  cases b <;> cases b' <;> simp [Bool.xor]

/-- Inverting the direction of a branch transport reverses the displayed sign equation. -/
private theorem sign_transport_algebra {A B H F : ℝ}
    (hA : A = 1 ∨ A = -1) (hB : B = 1 ∨ B = -1)
    (h : B * H = F * A) : A * H = F * B := by
  rcases hB with hB | hB
  · subst hB
    have h1 : H = F * A := by simpa using h
    rcases hA with hA | hA
    · subst hA
      calc (1 : ℝ) * H = H := by ring
        _ = F * 1 := h1
    · subst hA
      calc (-1 : ℝ) * H = -H := by ring
        _ = -(F * (-1)) := by rw [h1]
        _ = F * 1 := by ring
  · subst hB
    have h1 : H = -(F * A) := by
      calc H = -((-1 : ℝ) * H) := by ring
        _ = -(F * A) := by rw [h]
    rcases hA with hA | hA
    · subst hA
      calc (1 : ℝ) * H = H := by ring
        _ = -(F * 1) := h1
        _ = F * (-1) := by ring
    · subst hA
      calc (-1 : ℝ) * H = -H := by ring
        _ = -(-(F * (-1))) := by rw [h1]
        _ = F * (-1) := by ring

/-- Composing two branch transports multiplies their sign equations. -/
private theorem sign_compose_algebra {A B C He Hf F F' : ℝ}
    (hB : B = 1 ∨ B = -1)
    (h : A * He = F * B) (h' : B * Hf = F' * C) :
    A * (Hf * He) = (F * F') * C := by
  rcases hB with hB | hB
  · subst hB
    have h1 : A * He = F := by simpa using h
    have h2 : Hf = F' * C := by simpa using h'
    calc A * (Hf * He) = (A * He) * Hf := by ring
      _ = F * (F' * C) := by rw [h1, h2]
      _ = (F * F') * C := by ring
  · subst hB
    have h1 : A * He = -F := by
      calc A * He = F * (-1 : ℝ) := h
        _ = -F := by ring
    have h2 : Hf = -(F' * C) := by
      calc Hf = -((-1 : ℝ) * Hf) := by ring
        _ = -(F' * C) := by rw [h']
    calc A * (Hf * He) = (A * He) * Hf := by ring
      _ = (-F) * (-(F' * C)) := by rw [h1, h2]
      _ = (F * F') * C := by ring

/-! ### Structural laws of branch transport -/

/-- The identity automorphism fixes every distinguished center. -/
theorem centerPerm_one_apply (m : MultiCenterMolecule V) (c : m.Center) :
    m.centerPerm (1 : m.Aut) c = c := by
  apply Subtype.ext
  simp [MultiCenterMolecule.centerPerm]

/-- Every ligand index has the identity proper transport. -/
theorem properTransport_refl (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (c : m.Center) (i : Fin 4) :
    ProperTransport m cfg c i i := by
  refine ⟨1, centerPerm_one_apply m c, ?_, ?_⟩
  · simpa using congrArg (fun p : Equiv.Perm (Fin 4) => p i) (m.ligandPermAt_one c)
  · intro d hd
    rw [centerPerm_one_apply, m.ligandPermAt_one]
    simp

/-- Branch transport is reversible with the same mirror flag. -/
theorem branchTransport_inverse (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (c : m.Center) {i j : Fin 4} {b : Bool}
    (h : BranchTransport m cfg c i j b) :
    BranchTransport m cfg c j i b := by
  classical
  rcases h with ⟨e, hc, hi, hsign⟩
  have hc' : m.centerPerm e⁻¹ c = c := centerPerm_inv_eq m e c hc
  have hi' : m.ligandPermAt e⁻¹ c j = i := ligandPermAt_inv_apply m e c i j hc hi
  refine ⟨e⁻¹, hc', hi', ?_⟩
  intro d hd
  have hd' : LigandBranchReaches m c i (((e : Equiv.Perm V)⁻¹) d.1) :=
    ligandBranchReaches_map (m := m) (c := c) (i := j) (j := i) (e := e⁻¹) hc' hi' hd
  let dc : m.Center := m.centerPerm e⁻¹ d
  have hdcval : dc.1 = ((e : Equiv.Perm V)⁻¹) d.1 := rfl
  have hd'' : LigandBranchReaches m c i dc.1 := by
    simpa [hdcval] using hd'
  have hS := hsign dc hd''
  have hcenter : m.centerPerm e dc = d := by
    have hdc : dc = (m.centerPerm e)⁻¹ d := by
      dsimp only [dc]
      exact centerPerm_inv_apply m e d
    rw [hdc]
    exact Equiv.apply_symm_apply (m.centerPerm e) d
  have hlig : m.ligandPermAt e dc = (m.ligandPermAt e⁻¹ d)⁻¹ := by
    have hmul := m.ligandPermAt_mul (e := e) (f := e⁻¹) (c := d)
    have hone : m.ligandPermAt (e * e⁻¹) d = 1 := by
      simp [MultiCenterMolecule.ligandPermAt_one]
    rw [hone] at hmul
    have hprod : m.ligandPermAt e dc * m.ligandPermAt e⁻¹ d = 1 := by
      simpa [dc] using hmul.symm
    exact eq_inv_of_mul_eq_one_left hprod
  have hH : permHandedness (m.ligandPermAt e dc) =
      permHandedness (m.ligandPermAt e⁻¹ d) := by
    rw [hlig, permHandedness_inv]
  -- Rewrite the forward sign equation at `dc`.
  have hS' : m.configurationSign cfg dc * permHandedness (m.ligandPermAt e⁻¹ d) =
      (if b then -1 else 1) * m.configurationSign cfg d := by
    rw [← hH, ← hcenter]
    exact hS
  have halg := sign_transport_algebra
    (A := m.configurationSign cfg d) (B := m.configurationSign cfg dc)
    (H := permHandedness (m.ligandPermAt e⁻¹ d))
    (F := (if b then -1 else 1))
    (permHandedness_eq_one_or_eq_neg_one (cfg d))
    (permHandedness_eq_one_or_eq_neg_one (cfg dc)) hS'
  simpa [dc] using halg

/-- Branch transports compose, and the mirror flags add by XOR. -/
theorem branchTransport_comp (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (c : m.Center) {i j k : Fin 4} {b b' : Bool}
    (h1 : BranchTransport m cfg c i j b)
    (h2 : BranchTransport m cfg c j k b') :
    BranchTransport m cfg c i k (b ^^ b') := by
  classical
  rcases h1 with ⟨e, hce, hie, hse⟩
  rcases h2 with ⟨f, hcf, hjf, hsf⟩
  refine ⟨f * e, ?_, ?_, ?_⟩
  · rw [centerPerm_mul_apply m f e c, hce, hcf]
  · have hmul := m.ligandPermAt_mul (e := f) (f := e) (c := c)
    rw [hmul]
    simp [hce, hie, hjf]
  · intro d hd
    have hd_e : LigandBranchReaches m c j (m.centerPerm e d).1 := by
      have hmap :=
        ligandBranchReaches_map (m := m) (c := c) (i := i) (j := j) (e := e) hce hie hd
      simpa [MultiCenterMolecule.centerPerm] using hmap
    have h1' := hse d hd
    have h2' := hsf (m.centerPerm e d) hd_e
    have hlig := m.ligandPermAt_mul (e := f) (f := e) (c := d)
    rw [hlig, permHandedness_mul]
    rw [centerPerm_mul_apply m f e d]
    have halg := sign_compose_algebra
      (A := m.configurationSign cfg d)
      (B := m.configurationSign cfg (m.centerPerm e d))
      (C := m.configurationSign cfg (m.centerPerm f (m.centerPerm e d)))
      (He := permHandedness (m.ligandPermAt e d))
      (Hf := permHandedness (m.ligandPermAt f (m.centerPerm e d)))
      (F := (if b then -1 else 1)) (F' := (if b' then -1 else 1))
      (permHandedness_eq_one_or_eq_neg_one (cfg (m.centerPerm e d))) h1' h2'
    calc m.configurationSign cfg d *
          (permHandedness (m.ligandPermAt f (m.centerPerm e d)) *
            permHandedness (m.ligandPermAt e d))
        = ((if b then -1 else 1) * (if b' then -1 else 1)) *
            m.configurationSign cfg (m.centerPerm f (m.centerPerm e d)) := halg
      _ = (if b ^^ b' then -1 else 1) *
            m.configurationSign cfg (m.centerPerm f (m.centerPerm e d)) := by
            rw [mirrorFactor_mul]

/-! ### Enantiomorphy -/

/-- Enantiomorphy is irreflexive. -/
theorem enantiomorphic_irrefl (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (c : m.Center) (i : Fin 4) :
    ¬ Enantiomorphic m cfg c i i :=
  fun h => h.1 rfl

/-- Enantiomorphy is symmetric. -/
theorem enantiomorphic_symm (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (c : m.Center) {i j : Fin 4} (h : Enantiomorphic m cfg c i j) :
    Enantiomorphic m cfg c j i := by
  rcases h with ⟨hij, hm, hp⟩
  refine ⟨hij.symm, branchTransport_inverse m cfg c hm, ?_⟩
  intro hproper
  exact hp (branchTransport_inverse m cfg c hproper)

/-- Branch transport is unchanged by mirroring the whole configuration. -/
theorem branchTransport_mirrorConfiguration (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (c : m.Center) (i j : Fin 4) (b : Bool) :
    BranchTransport m cfg c i j b ↔
      BranchTransport m (m.mirrorConfiguration cfg) c i j b := by
  constructor
  · rintro ⟨e, hc, hi, hsign⟩
    refine ⟨e, hc, hi, fun d hd => ?_⟩
    have h := hsign d hd
    have hm : (-(m.configurationSign cfg d)) *
        permHandedness (m.ligandPermAt e d) =
          (if b then -1 else 1) *
            (-(m.configurationSign cfg (m.centerPerm e d))) := by
      calc (-(m.configurationSign cfg d)) * permHandedness (m.ligandPermAt e d)
          = -(m.configurationSign cfg d * permHandedness (m.ligandPermAt e d)) := by ring
        _ = -((if b then -1 else 1) *
              m.configurationSign cfg (m.centerPerm e d)) := by rw [h]
        _ = (if b then -1 else 1) *
              (-(m.configurationSign cfg (m.centerPerm e d))) := by ring
    simpa [MultiCenterMolecule.configurationSign_mirrorConfiguration] using hm
  · rintro ⟨e, hc, hi, hsign⟩
    refine ⟨e, hc, hi, fun d hd => ?_⟩
    have h := hsign d hd
    have h' : (-(m.configurationSign cfg d)) * permHandedness (m.ligandPermAt e d) =
        (if b then -1 else 1) *
          (-(m.configurationSign cfg (m.centerPerm e d))) := by
      simpa [MultiCenterMolecule.configurationSign_mirrorConfiguration] using h
    have hm : m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) =
        (if b then -1 else 1) * m.configurationSign cfg (m.centerPerm e d) := by
      calc m.configurationSign cfg d * permHandedness (m.ligandPermAt e d)
          = -((-(m.configurationSign cfg d)) *
              permHandedness (m.ligandPermAt e d)) := by ring
        _ = -((if b then -1 else 1) *
              (-(m.configurationSign cfg (m.centerPerm e d)))) := by rw [h']
        _ = (if b then -1 else 1) *
              m.configurationSign cfg (m.centerPerm e d) := by ring
    simpa [MultiCenterMolecule.configurationSign_mirrorConfiguration] using hm

/-- Enantiomorphy is invariant under mirroring the whole configuration. -/
theorem enantiomorphic_mirrorConfiguration (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (c : m.Center) (i j : Fin 4) :
    Enantiomorphic m cfg c i j ↔
      Enantiomorphic m (m.mirrorConfiguration cfg) c i j := by
  constructor
  · rintro ⟨hij, hm, hp⟩
    refine ⟨hij, (branchTransport_mirrorConfiguration m cfg c i j true).1 hm, ?_⟩
    intro hproper
    exact hp ((branchTransport_mirrorConfiguration m cfg c i j false).2 hproper)
  · rintro ⟨hij, hm, hp⟩
    refine ⟨hij, (branchTransport_mirrorConfiguration m cfg c i j true).2 hm, ?_⟩
    intro hproper
    exact hp ((branchTransport_mirrorConfiguration m cfg c i j false).1 hproper)

/-! ### Uniqueness of the enantiomorphic partner (matching) -/

/-- Two mirror transports from the same branch compose to a proper transport between their
targets. -/
theorem mirror_targets_properTransport (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (c : m.Center) {i j k : Fin 4}
    (hj : MirrorTransport m cfg c i j) (hk : MirrorTransport m cfg c i k) :
    ProperTransport m cfg c j k := by
  have hinv : MirrorTransport m cfg c j i := branchTransport_inverse m cfg c hj
  have hcomp : BranchTransport m cfg c j k (true ^^ true) :=
    branchTransport_comp m cfg c hinv hk
  simpa using hcomp

/-- Pairwise proper-distinguishability of the four ligand indices prevents an enantiomorphic
branch from having two distinct partners.  The two mirror witnesses, one reversed, compose to a
proper transport between the two partner branches, contradicting distinguishability.

This is the independent source-symmetry derivation of the matching uniqueness needed by a rule-5
sort step; the matching itself is not assumed. -/
theorem enantiomorphic_partner_unique (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (c : m.Center)
    (hdistinct : ∀ i j : Fin 4, i ≠ j → ¬ ProperTransport m cfg c i j)
    {i j k : Fin 4}
    (hj : Enantiomorphic m cfg c i j) (hk : Enantiomorphic m cfg c i k) :
    j = k := by
  by_contra hne
  have hproper : ProperTransport m cfg c j k :=
    mirror_targets_properTransport m cfg c hj.2.1 hk.2.1
  exact hdistinct j k hne hproper

/-- The subtype of enantiomorphic partners of a fixed branch is a subsingleton. -/
theorem enantiomorphicPartner_subsingleton (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (c : m.Center) (i : Fin 4)
    (hdistinct : ∀ i j : Fin 4, i ≠ j → ¬ ProperTransport m cfg c i j) :
    Subsingleton { j : Fin 4 // Enantiomorphic m cfg c i j } := by
  refine ⟨fun a b => ?_⟩
  apply Subtype.ext
  exact enantiomorphic_partner_unique m cfg c hdistinct a.2 b.2

/-- If an enantiomorphic partner exists, it is unique.  Existence is not asserted: it depends on
the molecule and configuration. -/
theorem existsUnique_enantiomorphicPartner (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (c : m.Center) (i : Fin 4)
    (hdistinct : ∀ i j : Fin 4, i ≠ j → ¬ ProperTransport m cfg c i j)
    (hex : ∃ j : Fin 4, Enantiomorphic m cfg c i j) :
    ∃! j : Fin 4, Enantiomorphic m cfg c i j := by
  rcases hex with ⟨j, hj⟩
  exact ⟨j, hj, fun k hk => enantiomorphic_partner_unique m cfg c hdistinct hk hj⟩

/-! ### Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.configurationSign_mul_ligandPermAt
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.branchTransport_iff_transportedSign
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.pairwiseDisjointLigandBranches_elim
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.ligandAtomAt_ne_center
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.ligandBranchReaches_self
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.centerPerm_eq_iff
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.centerPerm_inv_eq
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.centerPerm_inv_apply
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.centerPerm_mul_apply
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.ligandPermAt_inv_apply
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.ligandBranchReaches_map
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.mirrorFactor_mul
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.centerPerm_one_apply
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.properTransport_refl
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.branchTransport_inverse
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.branchTransport_comp
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.enantiomorphic_irrefl
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.enantiomorphic_symm
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.branchTransport_mirrorConfiguration
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.enantiomorphic_mirrorConfiguration
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.mirror_targets_properTransport
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.enantiomorphic_partner_unique
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.enantiomorphicPartner_subsingleton
assert_kernel_only TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry.existsUnique_enantiomorphicPartner

end

end RootedTetrahedralBranchSymmetry
end OneCenter
end TetraStereo
