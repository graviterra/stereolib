import TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry
import TetraStereo.OneCenter.MultiCenterConfiguration

set_option autoImplicit false

/-!
# Invariance of rooted branch symmetry under per-center ligand-frame reindexing

`TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry` defines the rooted branch relations
`BranchTransport`, `ProperTransport`, `MirrorTransport`, `Enantiomorphic` and the structural
predicates `PairwiseDisjointLigandBranches` directly on a `MultiCenterMolecule` and its
`Configuration`.  `TetraStereo.OneCenter.Reindex` treats a single-center molecule, so the
multi-center case was previously open.

This module supplies the multi-center reindexing.  Given a molecule `m` and an arbitrary
per-center family of ligand-index permutations

`τ : m.Center → Equiv.Perm (Fin 4)`,

we build the molecule `m.reindexFrames τ` with the *same* underlying molecular graph and the same
distinguished center set, but with the ligand enumeration at `c` post-composed with `τ c`
(`ligandAtomAt c i = m.ligandAtomAt c (τ c i)`).  A configuration `cfg` is transported to the
configuration `m.reindexConfiguration τ cfg` whose local frame at `c` is
`cfg c * (τ c)⁻¹`; this is exactly the frame convention already used by
`MultiCenterMolecule.smulConfiguration` (right multiplication by the inverse of the reindexing).

The main results are:

* `reindexFrames_ligandPermAt`: the actual ligand permutation induced by an automorphism at a
  center conjugates across the reindexing:
  `ligandPermAt e' c = (τ (centerPerm e' c))⁻¹ * ligandPermAt e c * τ c`.
* `ligandBranchReaches_reindexFrames_iff`: deleted-root reachability is unchanged under the index
  map `i ↦ τ c i` (it is the same walk in the same underlying graph).
* `branchTransport_reindexFrames_iff`: the frame-aware transport relation at *every* branch center
  is exactly transported:
  `BranchTransport (reindexFrames τ) newcfg c i j b ↔
     BranchTransport m cfg c (τ c i) (τ c j) b`.
  No root parity condition is imposed, and no sign relation is assumed: the equivalence is proved
  at each branch center from the old equations and the sign factor of the transported frame.
* `properTransport_reindexFrames_iff`, `mirrorTransport_reindexFrames_iff`,
  `enantiomorphic_reindexFrames_iff`, `pairwiseDisjointLigandBranches_reindexFrames_iff`, and
  `pairwiseProperDistinguishable_reindexFrames_iff`: the public source-symmetry relations do not
  depend on the arbitrary initial ligand numbering.

The statements concern the sign of an all-real orientation (`Perm.sign`), not a physical global
conformation and not the faithfulness of an external CIP reader.
-/

namespace TetraStereo
namespace OneCenter

noncomputable section

open RootedTetrahedralBranchSymmetry

namespace MultiCenterMolecule

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Reindexing the ligand frames at every center -/

/-- Reindex the ligand enumeration at every distinguished center.

The underlying molecular graph and the distinguished center set are kept verbatim; only the
labelling of the four ligand atoms at each center changes:
`ligandAtomAt c i = m.ligandAtomAt c (τ c i)`. -/
def reindexFrames (m : MultiCenterMolecule V) (τ : m.Center → Equiv.Perm (Fin 4)) :
    MultiCenterMolecule V where
  mol := m.mol
  centers := m.centers
  ligandAtom := fun c hc i => m.ligandAtom c hc (τ ⟨c, hc⟩ i)
  ligandAtom_adj := fun c hc i => m.ligandAtom_adj c hc (τ ⟨c, hc⟩ i)
  ligandAtom_injective := by
    intro c hc i j hij
    exact (τ ⟨c, hc⟩).injective (m.ligandAtom_injective c hc hij)
  ligandAtom_surjective := by
    intro c hc v hv
    obtain ⟨i, hi⟩ := m.ligandAtom_surjective c hc v hv
    exact ⟨(τ ⟨c, hc⟩)⁻¹ i, by simpa using hi⟩

@[simp] theorem reindexFrames_mol (m : MultiCenterMolecule V)
    (τ : m.Center → Equiv.Perm (Fin 4)) :
    (m.reindexFrames τ).mol = m.mol := rfl

@[simp] theorem reindexFrames_centers (m : MultiCenterMolecule V)
    (τ : m.Center → Equiv.Perm (Fin 4)) :
    (m.reindexFrames τ).centers = m.centers := rfl

@[simp] theorem reindexFrames_ligandAtomAt (m : MultiCenterMolecule V)
    (τ : m.Center → Equiv.Perm (Fin 4)) (c : m.Center) (i : Fin 4) :
    (m.reindexFrames τ).ligandAtomAt c i = m.ligandAtomAt c (τ c i) := rfl

/-- The same automorphism, regarded as an automorphism of the reindexed molecule. -/
def autReindex (m : MultiCenterMolecule V) (τ : m.Center → Equiv.Perm (Fin 4))
    (e : m.Aut) : (m.reindexFrames τ).Aut :=
  ⟨(e : Equiv.Perm V), by
    refine ⟨?_, ?_⟩
    · simp
    · simp [MultiCenterMolecule.PreservesCenters]⟩

/-- Forget the reindexed frame labelling and regard an automorphism of the reindexed molecule as
an automorphism of the original molecule. -/
def autUnreindex (m : MultiCenterMolecule V) (τ : m.Center → Equiv.Perm (Fin 4))
    (e : (m.reindexFrames τ).Aut) : m.Aut :=
  ⟨(e : Equiv.Perm V), by
    refine ⟨?_, ?_⟩
    · simp
    · simp [MultiCenterMolecule.PreservesCenters]⟩

@[simp] theorem autUnreindex_autReindex (m : MultiCenterMolecule V)
    (τ : m.Center → Equiv.Perm (Fin 4)) (e : m.Aut) :
    m.autUnreindex τ (m.autReindex τ e) = e := by
  apply Subtype.ext
  rfl

@[simp] theorem autReindex_autUnreindex (m : MultiCenterMolecule V)
    (τ : m.Center → Equiv.Perm (Fin 4)) (e : (m.reindexFrames τ).Aut) :
    m.autReindex τ (m.autUnreindex τ e) = e := by
  apply Subtype.ext
  rfl

/-- The permutation of the distinguished centers is unchanged by ligand reindexing. -/
theorem reindexFrames_centerPerm (m : MultiCenterMolecule V)
    (τ : m.Center → Equiv.Perm (Fin 4)) (e : m.Aut) (c : m.Center) :
    (m.reindexFrames τ).centerPerm (m.autReindex τ e) c = m.centerPerm e c := by
  apply Subtype.ext
  rfl

/-- The actual ligand permutation induced at a center conjugates across the reindexing:
the reindexing acts by `τ` on the source indices and by `τ` at the image center on the target
indices.  This is the multi-center analogue of `OneCenterMolecule.ligandPerm_reindex`. -/
theorem reindexFrames_ligandPermAt (m : MultiCenterMolecule V)
    (τ : m.Center → Equiv.Perm (Fin 4)) (e : m.Aut) (c : m.Center) :
    (m.reindexFrames τ).ligandPermAt (m.autReindex τ e) c =
      (τ ((m.reindexFrames τ).centerPerm (m.autReindex τ e) c))⁻¹ *
        m.ligandPermAt e c * τ c := by
  classical
  have hcenter : (m.reindexFrames τ).centerPerm (m.autReindex τ e) c = m.centerPerm e c :=
    reindexFrames_centerPerm m τ e c
  apply Equiv.ext
  intro i
  -- Compare the actual ligand atoms at the image center.  The transported automorphism carries
  -- the ligand atom with old index `τ c i` at `c` to the same atom in both descriptions.
  have hL : (m.reindexFrames τ).ligandAtomAt
        ((m.reindexFrames τ).centerPerm (m.autReindex τ e) c)
        ((m.reindexFrames τ).ligandPermAt (m.autReindex τ e) c i)
      = (e : Equiv.Perm V) (m.ligandAtomAt c (τ c i)) := by
    rw [MultiCenterMolecule.ligandAtomAt_ligandPermAt]
    simp
    rfl
  have hR : m.ligandAtomAt (m.centerPerm e c) (m.ligandPermAt e c (τ c i)) =
      (e : Equiv.Perm V) (m.ligandAtomAt c (τ c i)) :=
    m.ligandAtomAt_ligandPermAt (e := e) (c := c) (i := τ c i)
  have hL' : m.ligandAtomAt (m.centerPerm e c)
        (τ (m.centerPerm e c)
          ((m.reindexFrames τ).ligandPermAt (m.autReindex τ e) c i))
      = (e : Equiv.Perm V) (m.ligandAtomAt c (τ c i)) := by
    have h := hL
    rw [hcenter] at h
    rw [reindexFrames_ligandAtomAt] at h
    exact h
  have hAtom : m.ligandAtomAt (m.centerPerm e c)
        (τ (m.centerPerm e c)
          ((m.reindexFrames τ).ligandPermAt (m.autReindex τ e) c i)) =
      m.ligandAtomAt (m.centerPerm e c) (m.ligandPermAt e c (τ c i)) :=
    hL'.trans hR.symm
  have hinj := m.ligandAtomAt_injective (m.centerPerm e c) hAtom
  have hfin : (m.reindexFrames τ).ligandPermAt (m.autReindex τ e) c i =
      (τ (m.centerPerm e c))⁻¹ (m.ligandPermAt e c (τ c i)) := by
    have := congrArg (fun x => (τ (m.centerPerm e c))⁻¹ x) hinj
    simpa using this
  simpa [Equiv.Perm.mul_apply, hcenter] using hfin

/-- Index-level form of the conjugation formula: at a center `c`, a new index `i` corresponds to
the old index `τ c i`, and its image under the automorphism is `τ` of the old image index. -/
theorem reindexFrames_ligandPermAt_apply_iff (m : MultiCenterMolecule V)
    (τ : m.Center → Equiv.Perm (Fin 4)) (e : m.Aut) (c : m.Center) (i j : Fin 4) :
    (m.reindexFrames τ).ligandPermAt (m.autReindex τ e) c i = j ↔
      m.ligandPermAt e c (τ c i) =
        τ ((m.reindexFrames τ).centerPerm (m.autReindex τ e) c) j := by
  rw [reindexFrames_ligandPermAt]
  constructor
  · intro h
    have := congrArg
      (fun x => τ ((m.reindexFrames τ).centerPerm (m.autReindex τ e) c) x) h
    simpa [Equiv.Perm.mul_apply] using this
  · intro h
    have := congrArg
      (fun x => (τ ((m.reindexFrames τ).centerPerm (m.autReindex τ e) c))⁻¹ x) h
    simpa [Equiv.Perm.mul_apply] using this

/-! ### Transport of configuration frames and of deleted-root reachability -/

/-- Transport a configuration to the reindexed molecule.

The local frame at `c` is post-multiplied by `(τ c)⁻¹`, matching the inverse-right-multiplication
convention of `MultiCenterMolecule.smulConfiguration`. -/
def reindexConfiguration (m : MultiCenterMolecule V) (τ : m.Center → Equiv.Perm (Fin 4))
    (cfg : m.Configuration) : (m.reindexFrames τ).Configuration :=
  fun c => cfg c * (τ c)⁻¹

@[simp] theorem reindexConfiguration_apply (m : MultiCenterMolecule V)
    (τ : m.Center → Equiv.Perm (Fin 4)) (cfg : m.Configuration) (c : m.Center) :
    m.reindexConfiguration τ cfg c = cfg c * (τ c)⁻¹ := rfl

/-- The local handedness sign of the transported configuration picks up the parity of the
per-center reindexing. -/
theorem configurationSign_reindexConfiguration (m : MultiCenterMolecule V)
    (τ : m.Center → Equiv.Perm (Fin 4)) (cfg : m.Configuration) (c : m.Center) :
    (m.reindexFrames τ).configurationSign (m.reindexConfiguration τ cfg) c =
      m.configurationSign cfg c * permHandedness (τ c) := by
  simp [MultiCenterMolecule.configurationSign, reindexConfiguration, permHandedness_mul]

/-- Inverting a factor that is `1` or `-1` is harmless. -/
private theorem mul_factor_iff {A B : ℝ} {t : ℝ} (ht : t = 1 ∨ t = -1) :
    A * t = B * t ↔ A = B := by
  rcases ht with h | h <;> simp [h]

/-- The pointwise sign equation used by `BranchTransport` is transported exactly.

At a branch center `d` the new frame sign contributes `permHandedness (τ d)` to both sides, while
the transported configuration at the image center contributes `permHandedness (τ (centerPerm e d))`
to both sides; cancelling the nonzero `±1` factor gives the original equation.  This is the
frame-aware, all-branch-centers content of the reindexing; no root parity is consulted. -/
theorem branchTransportSign_reindexFrames_iff (m : MultiCenterMolecule V)
    (τ : m.Center → Equiv.Perm (Fin 4)) (cfg : m.Configuration) (e : m.Aut)
    (d : m.Center) (b : Bool) :
    (m.reindexFrames τ).configurationSign (m.reindexConfiguration τ cfg) d *
        permHandedness ((m.reindexFrames τ).ligandPermAt (m.autReindex τ e) d) =
      (if b then -1 else 1) *
        (m.reindexFrames τ).configurationSign (m.reindexConfiguration τ cfg)
          ((m.reindexFrames τ).centerPerm (m.autReindex τ e) d) ↔
    m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) =
      (if b then -1 else 1) * m.configurationSign cfg (m.centerPerm e d) := by
  have hcenter : (m.reindexFrames τ).centerPerm (m.autReindex τ e) d = m.centerPerm e d :=
    reindexFrames_centerPerm m τ e d
  have hlig : permHandedness ((m.reindexFrames τ).ligandPermAt (m.autReindex τ e) d) =
      permHandedness (τ (m.centerPerm e d)) * permHandedness (m.ligandPermAt e d) *
        permHandedness (τ d) := by
    have h := congrArg permHandedness (reindexFrames_ligandPermAt m τ e d)
    rw [hcenter] at h
    rw [h]
    simp [permHandedness_mul]
  have hnewL :
      (m.reindexFrames τ).configurationSign (m.reindexConfiguration τ cfg) d *
          permHandedness ((m.reindexFrames τ).ligandPermAt (m.autReindex τ e) d)
        = (m.configurationSign cfg d * permHandedness (m.ligandPermAt e d)) *
            permHandedness (τ (m.centerPerm e d)) := by
    rw [configurationSign_reindexConfiguration m τ cfg d, hlig]
    calc
      (m.configurationSign cfg d * permHandedness (τ d)) *
          (permHandedness (τ (m.centerPerm e d)) * permHandedness (m.ligandPermAt e d) *
            permHandedness (τ d))
          = ((m.configurationSign cfg d * permHandedness (m.ligandPermAt e d)) *
              permHandedness (τ (m.centerPerm e d))) *
              (permHandedness (τ d) * permHandedness (τ d)) := by ring
      _ = (m.configurationSign cfg d * permHandedness (m.ligandPermAt e d)) *
              permHandedness (τ (m.centerPerm e d)) := by
            rw [permHandedness_mul_self]
            ring
  have hnewR :
      (if b then -1 else 1) *
          (m.reindexFrames τ).configurationSign (m.reindexConfiguration τ cfg)
            ((m.reindexFrames τ).centerPerm (m.autReindex τ e) d)
        = ((if b then -1 else 1) * m.configurationSign cfg (m.centerPerm e d)) *
            permHandedness (τ (m.centerPerm e d)) := by
    rw [hcenter, configurationSign_reindexConfiguration m τ cfg (m.centerPerm e d)]
    ring
  rw [hnewL, hnewR]
  exact mul_factor_iff (permHandedness_eq_one_or_eq_neg_one (τ (m.centerPerm e d)))

/-- Deleted-root ligand-branch reachability is literally the same walk; only the ligand index is
changed by `τ c`. -/
theorem ligandBranchReaches_reindexFrames_iff (m : MultiCenterMolecule V)
    (τ : m.Center → Equiv.Perm (Fin 4)) (c : m.Center) (i : Fin 4) (v : V) :
    LigandBranchReaches (m.reindexFrames τ) c i v ↔
      LigandBranchReaches m c (τ c i) v :=
  Iff.rfl

/-! ### Exact transport of the rooted branch relations -/

/-- Rooted branch transport is exactly invariant under per-center ligand-frame reindexing.

The displayed equivalence holds at *every* branch center: the sign equation in the reindexed
molecule for the branch labelled `i` is, pointwise at each center `d` of that branch, the original
sign equation for the branch labelled `τ c i`.  The mirror flag `b` is unchanged.  No hypothesis
on root-attachment parity is used, and the sign relation is not assumed: it follows from the old
branch equation and the transported frame convention `cfg c * (τ c)⁻¹`. -/
theorem branchTransport_reindexFrames_iff (m : MultiCenterMolecule V)
    (τ : m.Center → Equiv.Perm (Fin 4)) (cfg : m.Configuration) (c : m.Center)
    (i j : Fin 4) (b : Bool) :
    BranchTransport (m.reindexFrames τ) (m.reindexConfiguration τ cfg) c i j b ↔
      BranchTransport m cfg c (τ c i) (τ c j) b := by
  classical
  constructor
  · rintro ⟨e', hc', hi', hsign'⟩
    let e : m.Aut := m.autUnreindex τ e'
    have heq : m.autReindex τ e = e' := m.autReindex_autUnreindex τ e'
    have hc'2 : (m.reindexFrames τ).centerPerm (m.autReindex τ e) c = c := by
      rw [heq]
      exact hc'
    have hi'2 : (m.reindexFrames τ).ligandPermAt (m.autReindex τ e) c i = j := by
      rw [heq]
      exact hi'
    have hc : m.centerPerm e c = c := by
      rw [← reindexFrames_centerPerm m τ e c]
      exact hc'2
    refine ⟨e, hc, ?_, ?_⟩
    · have h := (reindexFrames_ligandPermAt_apply_iff m τ e c i j).1 hi'2
      have himg : τ ((m.reindexFrames τ).centerPerm (m.autReindex τ e) c) = τ c := by
        rw [hc'2]
      rwa [himg] at h
    · intro d hd
      have hd' : LigandBranchReaches (m.reindexFrames τ) c i d.1 :=
        (ligandBranchReaches_reindexFrames_iff m τ c i d.1).2 hd
      have hs := hsign' d hd'
      rw [← heq] at hs
      exact (branchTransportSign_reindexFrames_iff m τ cfg e d b).1 hs
  · rintro ⟨e, hc, hi, hsign⟩
    refine ⟨m.autReindex τ e, ?_, ?_, ?_⟩
    · rw [reindexFrames_centerPerm m τ e c]
      exact hc
    · apply (reindexFrames_ligandPermAt_apply_iff m τ e c i j).2
      have himg : τ ((m.reindexFrames τ).centerPerm (m.autReindex τ e) c) = τ c := by
        rw [reindexFrames_centerPerm m τ e c, hc]
      rw [himg]
      exact hi
    · intro d hd'
      have hd : LigandBranchReaches m c (τ c i) d.1 :=
        (ligandBranchReaches_reindexFrames_iff m τ c i d.1).1 hd'
      exact (branchTransportSign_reindexFrames_iff m τ cfg e d b).2 (hsign d hd)

/-- Proper (non-mirror) branch transport is invariant under per-center ligand-frame reindexing. -/
theorem properTransport_reindexFrames_iff (m : MultiCenterMolecule V)
    (τ : m.Center → Equiv.Perm (Fin 4)) (cfg : m.Configuration) (c : m.Center)
    (i j : Fin 4) :
    ProperTransport (m.reindexFrames τ) (m.reindexConfiguration τ cfg) c i j ↔
      ProperTransport m cfg c (τ c i) (τ c j) :=
  branchTransport_reindexFrames_iff m τ cfg c i j false

/-- Mirror branch transport is invariant under per-center ligand-frame reindexing. -/
theorem mirrorTransport_reindexFrames_iff (m : MultiCenterMolecule V)
    (τ : m.Center → Equiv.Perm (Fin 4)) (cfg : m.Configuration) (c : m.Center)
    (i j : Fin 4) :
    MirrorTransport (m.reindexFrames τ) (m.reindexConfiguration τ cfg) c i j ↔
      MirrorTransport m cfg c (τ c i) (τ c j) :=
  branchTransport_reindexFrames_iff m τ cfg c i j true

/-- Enantiomorphy of two ligand branches is invariant under per-center ligand-frame reindexing. -/
theorem enantiomorphic_reindexFrames_iff (m : MultiCenterMolecule V)
    (τ : m.Center → Equiv.Perm (Fin 4)) (cfg : m.Configuration) (c : m.Center)
    (i j : Fin 4) :
    Enantiomorphic (m.reindexFrames τ) (m.reindexConfiguration τ cfg) c i j ↔
      Enantiomorphic m cfg c (τ c i) (τ c j) := by
  simp only [Enantiomorphic, mirrorTransport_reindexFrames_iff, properTransport_reindexFrames_iff]
  constructor
  · rintro ⟨hij, hm, hp⟩
    exact ⟨fun h => hij ((τ c).injective h), hm, hp⟩
  · rintro ⟨hij, hm, hp⟩
    exact ⟨fun h => hij (congrArg (τ c) h), hm, hp⟩

/-- Pairwise disjointness of the deleted-root ligand branches is invariant under per-center
ligand-frame reindexing. -/
theorem pairwiseDisjointLigandBranches_reindexFrames_iff (m : MultiCenterMolecule V)
    (τ : m.Center → Equiv.Perm (Fin 4)) (c : m.Center) :
    PairwiseDisjointLigandBranches (m.reindexFrames τ) c ↔
      PairwiseDisjointLigandBranches m c := by
  unfold PairwiseDisjointLigandBranches
  constructor
  · intro h i j hij v hi hj
    have hne : (τ c)⁻¹ i ≠ (τ c)⁻¹ j := by
      intro hEq
      apply hij
      have := congrArg (τ c) hEq
      simpa using this
    exact h ((τ c)⁻¹ i) ((τ c)⁻¹ j) hne v
      ((ligandBranchReaches_reindexFrames_iff m τ c ((τ c)⁻¹ i) v).2 (by simpa using hi))
      ((ligandBranchReaches_reindexFrames_iff m τ c ((τ c)⁻¹ j) v).2 (by simpa using hj))
  · intro h i j hij v hi hj
    exact h (τ c i) (τ c j) (fun hEq => hij ((τ c).injective hEq)) v
      ((ligandBranchReaches_reindexFrames_iff m τ c i v).1 hi)
      ((ligandBranchReaches_reindexFrames_iff m τ c j v).1 hj)

/-- No two distinct ligand branches at `c` are related by a proper transport.  This is the explicit
distinguishability hypothesis consumed by `RootedTetrahedralBranchSymmetry`'s uniqueness results. -/
def PairwiseProperDistinguishable (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (c : m.Center) : Prop :=
  ∀ i j : Fin 4, i ≠ j → ¬ ProperTransport m cfg c i j

/-- Pairwise proper distinguishability of the ligand branches is invariant under per-center
ligand-frame reindexing. -/
theorem pairwiseProperDistinguishable_reindexFrames_iff (m : MultiCenterMolecule V)
    (τ : m.Center → Equiv.Perm (Fin 4)) (cfg : m.Configuration) (c : m.Center) :
    PairwiseProperDistinguishable (m.reindexFrames τ) (m.reindexConfiguration τ cfg) c ↔
      PairwiseProperDistinguishable m cfg c := by
  unfold PairwiseProperDistinguishable
  constructor
  · intro h i j hij hp
    have hne : (τ c)⁻¹ i ≠ (τ c)⁻¹ j := by
      intro hEq
      apply hij
      have := congrArg (τ c) hEq
      simpa using this
    exact h ((τ c)⁻¹ i) ((τ c)⁻¹ j) hne
      ((properTransport_reindexFrames_iff m τ cfg c ((τ c)⁻¹ i) ((τ c)⁻¹ j)).2
        (by simpa using hp))
  · intro h i j hij hp
    exact h (τ c i) (τ c j) (fun hEq => hij ((τ c).injective hEq))
      ((properTransport_reindexFrames_iff m τ cfg c i j).1 hp)

/-! ### Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.MultiCenterMolecule.reindexFrames
assert_kernel_only TetraStereo.OneCenter.MultiCenterMolecule.autReindex
assert_kernel_only TetraStereo.OneCenter.MultiCenterMolecule.autUnreindex
assert_kernel_only TetraStereo.OneCenter.MultiCenterMolecule.reindexConfiguration
assert_kernel_only TetraStereo.OneCenter.MultiCenterMolecule.PairwiseProperDistinguishable
assert_kernel_only TetraStereo.OneCenter.MultiCenterMolecule.reindexFrames_mol
assert_kernel_only TetraStereo.OneCenter.MultiCenterMolecule.reindexFrames_centers
assert_kernel_only TetraStereo.OneCenter.MultiCenterMolecule.reindexFrames_ligandAtomAt
assert_kernel_only TetraStereo.OneCenter.MultiCenterMolecule.autUnreindex_autReindex
assert_kernel_only TetraStereo.OneCenter.MultiCenterMolecule.autReindex_autUnreindex
assert_kernel_only TetraStereo.OneCenter.MultiCenterMolecule.reindexFrames_centerPerm
assert_kernel_only TetraStereo.OneCenter.MultiCenterMolecule.reindexFrames_ligandPermAt
assert_kernel_only TetraStereo.OneCenter.MultiCenterMolecule.reindexFrames_ligandPermAt_apply_iff
assert_kernel_only TetraStereo.OneCenter.MultiCenterMolecule.reindexConfiguration_apply
assert_kernel_only TetraStereo.OneCenter.MultiCenterMolecule.configurationSign_reindexConfiguration
assert_kernel_only TetraStereo.OneCenter.MultiCenterMolecule.branchTransportSign_reindexFrames_iff
assert_kernel_only TetraStereo.OneCenter.MultiCenterMolecule.ligandBranchReaches_reindexFrames_iff
assert_kernel_only TetraStereo.OneCenter.MultiCenterMolecule.branchTransport_reindexFrames_iff
assert_kernel_only TetraStereo.OneCenter.MultiCenterMolecule.properTransport_reindexFrames_iff
assert_kernel_only TetraStereo.OneCenter.MultiCenterMolecule.mirrorTransport_reindexFrames_iff
assert_kernel_only TetraStereo.OneCenter.MultiCenterMolecule.enantiomorphic_reindexFrames_iff
assert_kernel_only TetraStereo.OneCenter.MultiCenterMolecule.pairwiseDisjointLigandBranches_reindexFrames_iff
assert_kernel_only TetraStereo.OneCenter.MultiCenterMolecule.pairwiseProperDistinguishable_reindexFrames_iff

end MultiCenterMolecule

end
end OneCenter
end TetraStereo
