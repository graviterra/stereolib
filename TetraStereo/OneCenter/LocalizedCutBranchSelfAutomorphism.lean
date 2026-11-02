import TetraStereo.OneCenter.AcyclicCutBranchAutomorphism
import TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
















































namespace TetraStereo
namespace OneCenter
namespace LocalizedCutBranchSelfAutomorphism

open AcyclicCutBranchAutomorphism

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## The raw self-extension and its inverse -/

/-- The raw self-extension of a rooted cut-branch self-isomorphism: `φ` inside the cut branch and
the identity outside it. -/
noncomputable def cutBranchSelfFun (m : MoleculeGraph V) (c u : V)
    (φ : RootedCutBranchIso m c u u) (x : V) : V := by
  classical
  exact if hx : x ∈ CutBranch m c u then (φ.toEquiv ⟨x, hx⟩ : V) else x

/-- On branch vertices the raw self-extension is `φ`. -/
theorem cutBranchSelfFun_of_mem (m : MoleculeGraph V) (c u : V)
    (φ : RootedCutBranchIso m c u u) {x : V} (hx : x ∈ CutBranch m c u) :
    cutBranchSelfFun m c u φ x = (φ.toEquiv ⟨x, hx⟩ : V) := by
  classical
  rw [cutBranchSelfFun, dif_pos hx]

/-- Outside the branch the raw self-extension is the identity. -/
theorem cutBranchSelfFun_of_not_mem (m : MoleculeGraph V) (c u : V)
    (φ : RootedCutBranchIso m c u u) {x : V} (hx : x ∉ CutBranch m c u) :
    cutBranchSelfFun m c u φ x = x := by
  classical
  rw [cutBranchSelfFun, dif_neg hx]

/-- The inverse raw map: `φ.toEquiv.symm` inside the branch and the identity outside. -/
noncomputable def cutBranchSelfInvFun (m : MoleculeGraph V) (c u : V)
    (φ : RootedCutBranchIso m c u u) (x : V) : V := by
  classical
  exact if hx : x ∈ CutBranch m c u then (φ.toEquiv.symm ⟨x, hx⟩ : V) else x

/-- On branch vertices the inverse raw map is `φ.symm`. -/
theorem cutBranchSelfInvFun_of_mem (m : MoleculeGraph V) (c u : V)
    (φ : RootedCutBranchIso m c u u) {x : V} (hx : x ∈ CutBranch m c u) :
    cutBranchSelfInvFun m c u φ x = (φ.toEquiv.symm ⟨x, hx⟩ : V) := by
  classical
  rw [cutBranchSelfInvFun, dif_pos hx]

/-- Outside the branch the inverse raw map is the identity. -/
theorem cutBranchSelfInvFun_of_not_mem (m : MoleculeGraph V) (c u : V)
    (φ : RootedCutBranchIso m c u u) {x : V} (hx : x ∉ CutBranch m c u) :
    cutBranchSelfInvFun m c u φ x = x := by
  classical
  rw [cutBranchSelfInvFun, dif_neg hx]

/-! ## The self-isomorphism as a permutation

The branch is mapped onto itself, so the membership test of the raw map and of the inverse raw map
agree on every image; no disjointness or acyclicity is needed for the permutation structure. -/

theorem cutBranchSelfInvFun_apply_selfFun (m : MoleculeGraph V) (c u : V)
    (φ : RootedCutBranchIso m c u u) (x : V) :
    cutBranchSelfInvFun m c u φ (cutBranchSelfFun m c u φ x) = x := by
  classical
  by_cases hx : x ∈ CutBranch m c u
  · rw [cutBranchSelfFun_of_mem m c u φ hx]
    have hmem : ((φ.toEquiv ⟨x, hx⟩ : CutBranch m c u) : V) ∈ CutBranch m c u :=
      (φ.toEquiv ⟨x, hx⟩).2
    rw [cutBranchSelfInvFun_of_mem m c u φ hmem]
    have hsub : (⟨((φ.toEquiv ⟨x, hx⟩ : CutBranch m c u) : V), hmem⟩ :
        CutBranch m c u) = φ.toEquiv ⟨x, hx⟩ := Subtype.ext rfl
    rw [hsub, Equiv.symm_apply_apply]
  · rw [cutBranchSelfFun_of_not_mem m c u φ hx,
      cutBranchSelfInvFun_of_not_mem m c u φ hx]

theorem cutBranchSelfFun_apply_invFun (m : MoleculeGraph V) (c u : V)
    (φ : RootedCutBranchIso m c u u) (x : V) :
    cutBranchSelfFun m c u φ (cutBranchSelfInvFun m c u φ x) = x := by
  classical
  by_cases hx : x ∈ CutBranch m c u
  · rw [cutBranchSelfInvFun_of_mem m c u φ hx]
    have hmem : ((φ.toEquiv.symm ⟨x, hx⟩ : CutBranch m c u) : V) ∈ CutBranch m c u :=
      (φ.toEquiv.symm ⟨x, hx⟩).2
    rw [cutBranchSelfFun_of_mem m c u φ hmem]
    have hsub : (⟨((φ.toEquiv.symm ⟨x, hx⟩ : CutBranch m c u) : V), hmem⟩ :
        CutBranch m c u) = φ.toEquiv.symm ⟨x, hx⟩ := Subtype.ext rfl
    rw [hsub, Equiv.apply_symm_apply]
  · rw [cutBranchSelfInvFun_of_not_mem m c u φ hx,
      cutBranchSelfFun_of_not_mem m c u φ hx]

/-- The global permutation induced by a rooted cut-branch self-isomorphism: `φ` on the branch,
identity outside. -/
noncomputable def cutBranchSelfPerm (m : MoleculeGraph V) (c u : V)
    (φ : RootedCutBranchIso m c u u) : Equiv.Perm V where
  toFun := cutBranchSelfFun m c u φ
  invFun := cutBranchSelfInvFun m c u φ
  left_inv := cutBranchSelfInvFun_apply_selfFun m c u φ
  right_inv := cutBranchSelfFun_apply_invFun m c u φ

/-! ## The inverse is the extension of the inverse branch isomorphism -/

/-- The inverse self-isomorphism of a rooted cut-branch self-isomorphism.  It preserves atomic
number, mass and adjacency by reading `φ` backwards, and fixes the attachment because `φ` does. -/
noncomputable def rootedCutBranchIsoSymm {m : MoleculeGraph V} {c u : V}
    (φ : RootedCutBranchIso m c u u) : RootedCutBranchIso m c u u where
  toEquiv := φ.toEquiv.symm
  map_attach := by
    intro hu hu'
    have h := congrArg φ.toEquiv.symm (φ.map_attach hu' hu)
    rw [Equiv.symm_apply_apply] at h
    exact h.symm
  atomZ_eq := by
    intro x
    have h := φ.atomZ_eq (φ.toEquiv.symm x)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  atomMass_eq := by
    intro x
    have h := φ.atomMass_eq (φ.toEquiv.symm x)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  adj_iff := by
    intro x y
    exact RootedCutBranchIso.adj_iff_symm φ x y

/-- The inverse raw map is literally the raw map of the inverse branch isomorphism. -/
theorem cutBranchSelfInvFun_eq_cutBranchSelfFun_symm (m : MoleculeGraph V) (c u : V)
    (φ : RootedCutBranchIso m c u u) (x : V) :
    cutBranchSelfInvFun m c u φ x = cutBranchSelfFun m c u (rootedCutBranchIsoSymm φ) x := rfl

/-! ## Behaviour of the permutation -/

@[simp] theorem cutBranchSelfPerm_apply (m : MoleculeGraph V) (c u : V)
    (φ : RootedCutBranchIso m c u u) (x : V) :
    cutBranchSelfPerm m c u φ x = cutBranchSelfFun m c u φ x := rfl

theorem cutBranchSelfPerm_apply_of_mem (m : MoleculeGraph V) (c u : V)
    (φ : RootedCutBranchIso m c u u) {x : V} (hx : x ∈ CutBranch m c u) :
    cutBranchSelfPerm m c u φ x = (φ.toEquiv ⟨x, hx⟩ : V) := by
  rw [cutBranchSelfPerm_apply, cutBranchSelfFun_of_mem m c u φ hx]

theorem cutBranchSelfPerm_apply_of_not_mem (m : MoleculeGraph V) (c u : V)
    (φ : RootedCutBranchIso m c u u) {x : V} (hx : x ∉ CutBranch m c u) :
    cutBranchSelfPerm m c u φ x = x := by
  rw [cutBranchSelfPerm_apply, cutBranchSelfFun_of_not_mem m c u φ hx]

/-- The permutation carries the branch into itself. -/
theorem cutBranchSelfPerm_apply_mem (m : MoleculeGraph V) (c u : V)
    (φ : RootedCutBranchIso m c u u) {x : V} (hx : x ∈ CutBranch m c u) :
    cutBranchSelfPerm m c u φ x ∈ CutBranch m c u := by
  rw [cutBranchSelfPerm_apply_of_mem m c u φ hx]
  exact (φ.toEquiv ⟨x, hx⟩).2

/-- On the branch subtype the permutation is exactly `φ.toEquiv`. -/
theorem cutBranchSelfPerm_map_branch (m : MoleculeGraph V) (c u : V)
    (φ : RootedCutBranchIso m c u u) (x : CutBranch m c u) :
    (⟨cutBranchSelfPerm m c u φ x.1, cutBranchSelfPerm_apply_mem m c u φ x.2⟩ :
        CutBranch m c u) = φ.toEquiv x := by
  apply Subtype.ext
  exact cutBranchSelfPerm_apply_of_mem m c u φ x.2

/-- The permutation fixes the deleted root. -/
theorem cutBranchSelfPerm_apply_center (m : MoleculeGraph V) (c u : V)
    (φ : RootedCutBranchIso m c u u) :
    cutBranchSelfPerm m c u φ c = c := by
  rw [cutBranchSelfPerm_apply_of_not_mem m c u φ (center_not_mem_cutBranch m c u)]

/-- The permutation fixes the attachment vertex. -/
theorem cutBranchSelfPerm_apply_attach (m : MoleculeGraph V) (c u : V)
    (φ : RootedCutBranchIso m c u u) (hcu : m.Adj c u) :
    cutBranchSelfPerm m c u φ u = u := by
  rw [cutBranchSelfPerm_apply_of_mem m c u φ (cutBranch_mem_self m hcu)]
  exact congrArg Subtype.val (φ.map_attach (cutBranch_mem_self m hcu)
    (cutBranch_mem_self m hcu))

/-! ## Adjacency preservation

The only cross-boundary adjacency is the attachment edge `u-c`, and `φ` fixes `u`.  Everything else
either stays inside the branch (where `φ` preserves adjacency) or is fixed by the identity outside
the branch. -/

/-- Adjacency preservation when `x` lies in the branch and `y` does not. -/
theorem cutBranchSelfFun_adj_iff_of_mem_of_not_mem (m : MoleculeGraph V) (c u : V)
    (hacyc : m.Acyclic) (hcu : m.Adj c u) (φ : RootedCutBranchIso m c u u)
    {x y : V} (hx : x ∈ CutBranch m c u) (hy : y ∉ CutBranch m c u) :
    m.Adj (cutBranchSelfFun m c u φ x) y ↔ m.Adj x y := by
  classical
  rw [cutBranchSelfFun_of_mem m c u φ hx]
  have hφmem : ((φ.toEquiv ⟨x, hx⟩ : CutBranch m c u) : V) ∈ CutBranch m c u :=
    (φ.toEquiv ⟨x, hx⟩).2
  have hleft : m.Adj ((φ.toEquiv ⟨x, hx⟩ : CutBranch m c u) : V) y ↔ x = u ∧ y = c := by
    constructor
    · intro h
      rcases cutBranch_incidence m hacyc hcu hφmem y h with hmem | ⟨hφu, hyc⟩
      · exact absurd hmem hy
      · refine ⟨?_, hyc⟩
        have hsub : φ.toEquiv ⟨x, hx⟩ = (⟨u, cutBranch_mem_self m hcu⟩ : CutBranch m c u) :=
          Subtype.ext hφu
        have hinj : (⟨x, hx⟩ : CutBranch m c u) = ⟨u, cutBranch_mem_self m hcu⟩ := by
          apply φ.toEquiv.injective
          rw [hsub, φ.map_attach (cutBranch_mem_self m hcu) (cutBranch_mem_self m hcu)]
        exact congrArg Subtype.val hinj
    · rintro ⟨hx_eq, hy_eq⟩
      rw [hy_eq, cutBranch_adj_center_iff m hacyc hcu hφmem]
      have hxsub : (⟨x, hx⟩ : CutBranch m c u) = ⟨u, cutBranch_mem_self m hcu⟩ :=
        Subtype.ext hx_eq
      rw [hxsub, φ.map_attach (cutBranch_mem_self m hcu) (cutBranch_mem_self m hcu)]
  have hright : m.Adj x y ↔ x = u ∧ y = c := by
    constructor
    · intro h
      rcases cutBranch_incidence m hacyc hcu hx y h with hmem | hpair
      · exact absurd hmem hy
      · exact hpair
    · rintro ⟨hx_eq, hy_eq⟩
      rw [hx_eq, hy_eq]
      exact m.adj_symm.mpr hcu
  exact hleft.trans hright.symm

/-- Adjacency preservation when `x` does not lie in the branch and `y` does. -/
theorem cutBranchSelfFun_adj_iff_of_not_mem_of_mem (m : MoleculeGraph V) (c u : V)
    (hacyc : m.Acyclic) (hcu : m.Adj c u) (φ : RootedCutBranchIso m c u u)
    {x y : V} (hx : x ∉ CutBranch m c u) (hy : y ∈ CutBranch m c u) :
    m.Adj x (cutBranchSelfFun m c u φ y) ↔ m.Adj x y := by
  classical
  have h := cutBranchSelfFun_adj_iff_of_mem_of_not_mem m c u hacyc hcu φ hy hx
  rw [cutBranchSelfFun_of_mem m c u φ hy] at h
  rw [cutBranchSelfFun_of_mem m c u φ hy]
  exact m.adj_symm.trans (h.trans m.adj_symm)

/-- **The self-extension preserves adjacency everywhere.** -/
theorem cutBranchSelfFun_adj_iff (m : MoleculeGraph V) (c u : V)
    (hacyc : m.Acyclic) (hcu : m.Adj c u) (φ : RootedCutBranchIso m c u u) (x y : V) :
    m.Adj (cutBranchSelfFun m c u φ x) (cutBranchSelfFun m c u φ y) ↔ m.Adj x y := by
  classical
  by_cases hx : x ∈ CutBranch m c u
  · by_cases hy : y ∈ CutBranch m c u
    · rw [cutBranchSelfFun_of_mem m c u φ hx, cutBranchSelfFun_of_mem m c u φ hy]
      exact φ.adj_iff ⟨x, hx⟩ ⟨y, hy⟩
    · rw [cutBranchSelfFun_of_not_mem m c u φ hy]
      exact cutBranchSelfFun_adj_iff_of_mem_of_not_mem m c u hacyc hcu φ hx hy
  · by_cases hy : y ∈ CutBranch m c u
    · rw [cutBranchSelfFun_of_not_mem m c u φ hx]
      exact cutBranchSelfFun_adj_iff_of_not_mem_of_mem m c u hacyc hcu φ hx hy
    · rw [cutBranchSelfFun_of_not_mem m c u φ hx, cutBranchSelfFun_of_not_mem m c u φ hy]

/-- Adjacency preservation for the permutation form. -/
theorem cutBranchSelfPerm_adj_iff (m : MoleculeGraph V) (c u : V)
    (hacyc : m.Acyclic) (hcu : m.Adj c u) (φ : RootedCutBranchIso m c u u) (x y : V) :
    m.Adj (cutBranchSelfPerm m c u φ x) (cutBranchSelfPerm m c u φ y) ↔ m.Adj x y :=
  cutBranchSelfFun_adj_iff m c u hacyc hcu φ x y

/-! ## The global automorphism -/

/-- **The self-extension is a molecular-graph automorphism.**  It preserves `atomZ`, `atomMass`,
constant formal charge, and every bond order. -/
theorem cutBranchSelf_isAutomorphism (m : MoleculeGraph V) (c u : V)
    (hacyc : m.Acyclic) (hcu : m.Adj c u) (hsimple : m.SimpleBonded)
    (hcharge : ConstantFormalCharge m) (φ : RootedCutBranchIso m c u u) :
    m.IsAutomorphism (cutBranchSelfPerm m c u φ) := by
  obtain ⟨q, hq⟩ := hcharge
  have hAdj : ∀ x y, m.Adj (cutBranchSelfPerm m c u φ x)
      (cutBranchSelfPerm m c u φ y) ↔ m.Adj x y :=
    fun x y => cutBranchSelfPerm_adj_iff m c u hacyc hcu φ x y
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ CutBranch m c u
    · rw [cutBranchSelfPerm_apply_of_mem m c u φ hx]
      exact φ.atomZ_eq ⟨x, hx⟩
    · rw [cutBranchSelfPerm_apply_of_not_mem m c u φ hx]
  · intro x
    by_cases hx : x ∈ CutBranch m c u
    · rw [cutBranchSelfPerm_apply_of_mem m c u φ hx]
      exact φ.atomMass_eq ⟨x, hx⟩
    · rw [cutBranchSelfPerm_apply_of_not_mem m c u φ hx]
  · intro x
    exact (hq (cutBranchSelfPerm m c u φ x)).trans (hq x).symm
  · intro x y
    exact bond_eq_of_adj_iff m hsimple (cutBranchSelfPerm m c u φ) hAdj x y

/-- The global self-extension packaged as an automorphism of the molecular graph. -/
noncomputable def cutBranchSelfAut (m : MoleculeGraph V) (c u : V)
    (hacyc : m.Acyclic) (hcu : m.Adj c u) (hsimple : m.SimpleBonded)
    (hcharge : ConstantFormalCharge m) (φ : RootedCutBranchIso m c u u) : m.Aut :=
  ⟨cutBranchSelfPerm m c u φ,
    cutBranchSelf_isAutomorphism m c u hacyc hcu hsimple hcharge φ⟩

@[simp] theorem cutBranchSelfAut_apply (m : MoleculeGraph V) (c u : V)
    (hacyc : m.Acyclic) (hcu : m.Adj c u) (hsimple : m.SimpleBonded)
    (hcharge : ConstantFormalCharge m) (φ : RootedCutBranchIso m c u u) (x : V) :
    (cutBranchSelfAut m c u hacyc hcu hsimple hcharge φ : Equiv.Perm V) x =
      cutBranchSelfFun m c u φ x := rfl

theorem cutBranchSelfAut_apply_of_mem (m : MoleculeGraph V) (c u : V)
    (hacyc : m.Acyclic) (hcu : m.Adj c u) (hsimple : m.SimpleBonded)
    (hcharge : ConstantFormalCharge m) (φ : RootedCutBranchIso m c u u) {x : V}
    (hx : x ∈ CutBranch m c u) :
    (cutBranchSelfAut m c u hacyc hcu hsimple hcharge φ : Equiv.Perm V) x =
      (φ.toEquiv ⟨x, hx⟩ : V) := by
  rw [cutBranchSelfAut_apply, cutBranchSelfFun_of_mem m c u φ hx]

theorem cutBranchSelfAut_apply_of_not_mem (m : MoleculeGraph V) (c u : V)
    (hacyc : m.Acyclic) (hcu : m.Adj c u) (hsimple : m.SimpleBonded)
    (hcharge : ConstantFormalCharge m) (φ : RootedCutBranchIso m c u u) {x : V}
    (hx : x ∉ CutBranch m c u) :
    (cutBranchSelfAut m c u hacyc hcu hsimple hcharge φ : Equiv.Perm V) x = x := by
  rw [cutBranchSelfAut_apply, cutBranchSelfFun_of_not_mem m c u φ hx]

/-- The self-automorphism fixes the root. -/
theorem cutBranchSelfAut_apply_center (m : MoleculeGraph V) (c u : V)
    (hacyc : m.Acyclic) (hcu : m.Adj c u) (hsimple : m.SimpleBonded)
    (hcharge : ConstantFormalCharge m) (φ : RootedCutBranchIso m c u u) :
    (cutBranchSelfAut m c u hacyc hcu hsimple hcharge φ : Equiv.Perm V) c = c :=
  cutBranchSelfPerm_apply_center m c u φ

/-- The self-automorphism fixes the attachment vertex. -/
theorem cutBranchSelfAut_apply_attach (m : MoleculeGraph V) (c u : V)
    (hacyc : m.Acyclic) (hcu : m.Adj c u) (hsimple : m.SimpleBonded)
    (hcharge : ConstantFormalCharge m) (φ : RootedCutBranchIso m c u u) :
    (cutBranchSelfAut m c u hacyc hcu hsimple hcharge φ : Equiv.Perm V) u = u :=
  cutBranchSelfPerm_apply_attach m c u φ hcu

/-! ## Lift to the automatically detected multi-center molecule -/

/-- The self-extension regarded as an automorphism of the automatically detected multi-center
molecule.  Degree-four detection is automatic; no additional inventory is needed. -/
noncomputable def detectedCutBranchSelfAut (m : MoleculeGraph V) (c u : V)
    (hacyc : m.Acyclic) (hcu : m.Adj c u) (hsimple : m.SimpleBonded)
    (hcharge : ConstantFormalCharge m) (φ : RootedCutBranchIso m c u u) :
    m.detectedMultiCenterMolecule.Aut :=
  m.detectedMultiCenterAutOfGraphAut
    (cutBranchSelfAut m c u hacyc hcu hsimple hcharge φ)

@[simp] theorem detectedCutBranchSelfAut_apply (m : MoleculeGraph V) (c u : V)
    (hacyc : m.Acyclic) (hcu : m.Adj c u) (hsimple : m.SimpleBonded)
    (hcharge : ConstantFormalCharge m) (φ : RootedCutBranchIso m c u u) (x : V) :
    ((detectedCutBranchSelfAut m c u hacyc hcu hsimple hcharge φ :
        m.detectedMultiCenterMolecule.Aut) : Equiv.Perm V) x =
      cutBranchSelfFun m c u φ x := rfl

theorem detectedCutBranchSelfAut_apply_of_mem (m : MoleculeGraph V) (c u : V)
    (hacyc : m.Acyclic) (hcu : m.Adj c u) (hsimple : m.SimpleBonded)
    (hcharge : ConstantFormalCharge m) (φ : RootedCutBranchIso m c u u) {x : V}
    (hx : x ∈ CutBranch m c u) :
    ((detectedCutBranchSelfAut m c u hacyc hcu hsimple hcharge φ :
        m.detectedMultiCenterMolecule.Aut) : Equiv.Perm V) x =
      (φ.toEquiv ⟨x, hx⟩ : V) := by
  rw [detectedCutBranchSelfAut_apply, cutBranchSelfFun_of_mem m c u φ hx]

theorem detectedCutBranchSelfAut_apply_of_not_mem (m : MoleculeGraph V) (c u : V)
    (hacyc : m.Acyclic) (hcu : m.Adj c u) (hsimple : m.SimpleBonded)
    (hcharge : ConstantFormalCharge m) (φ : RootedCutBranchIso m c u u) {x : V}
    (hx : x ∉ CutBranch m c u) :
    ((detectedCutBranchSelfAut m c u hacyc hcu hsimple hcharge φ :
        m.detectedMultiCenterMolecule.Aut) : Equiv.Perm V) x = x := by
  rw [detectedCutBranchSelfAut_apply, cutBranchSelfFun_of_not_mem m c u φ hx]

/-- The lifted self-automorphism fixes the root. -/
theorem detectedCutBranchSelfAut_apply_center (m : MoleculeGraph V) (c u : V)
    (hacyc : m.Acyclic) (hcu : m.Adj c u) (hsimple : m.SimpleBonded)
    (hcharge : ConstantFormalCharge m) (φ : RootedCutBranchIso m c u u) :
    ((detectedCutBranchSelfAut m c u hacyc hcu hsimple hcharge φ :
        m.detectedMultiCenterMolecule.Aut) : Equiv.Perm V) c = c :=
  cutBranchSelfPerm_apply_center m c u φ

/-- The lifted self-automorphism fixes the attachment vertex. -/
theorem detectedCutBranchSelfAut_apply_attach (m : MoleculeGraph V) (c u : V)
    (hacyc : m.Acyclic) (hcu : m.Adj c u) (hsimple : m.SimpleBonded)
    (hcharge : ConstantFormalCharge m) (φ : RootedCutBranchIso m c u u) :
    ((detectedCutBranchSelfAut m c u hacyc hcu hsimple hcharge φ :
        m.detectedMultiCenterMolecule.Aut) : Equiv.Perm V) u = u :=
  cutBranchSelfPerm_apply_attach m c u φ hcu

/-- At a detected tetrahedral center `c` fixed by the self-extension, the induced permutation of
the center type fixes the corresponding center. -/
theorem detectedCutBranchSelfAut_centerPerm_eq_self (m : MoleculeGraph V) (c u : V)
    (hacyc : m.Acyclic) (hcu : m.Adj c u) (hsimple : m.SimpleBonded)
    (hcharge : ConstantFormalCharge m) (φ : RootedCutBranchIso m c u u)
    (hc : c ∈ m.tetrahedralCenterSet) :
    m.detectedMultiCenterMolecule.centerPerm
        (detectedCutBranchSelfAut m c u hacyc hcu hsimple hcharge φ) ⟨c, hc⟩ =
      ⟨c, hc⟩ := by
  apply Subtype.ext
  change ((detectedCutBranchSelfAut m c u hacyc hcu hsimple hcharge φ :
      m.detectedMultiCenterMolecule.Aut) : Equiv.Perm V) c = c
  exact detectedCutBranchSelfAut_apply_center m c u hacyc hcu hsimple hcharge φ

/-! ## Generic fixed-point helpers for `centerPerm` and `ligandPermAt` -/

/-- A multi-center automorphism that fixes the underlying atom of a center fixes that center under
`centerPerm`. -/
theorem centerPerm_eq_self_of_apply_eq (m : MultiCenterMolecule V) (e : m.Aut) (c : m.Center)
    (h : (e : Equiv.Perm V) c.1 = c.1) : m.centerPerm e c = c :=
  Subtype.ext h

/-- If a multi-center automorphism fixes a center and the ligand atom of slot `i`, then the induced
ligand permutation fixes slot `i`. -/
theorem ligandPermAt_eq_self_of_ligandAtomAt_eq_self (m : MultiCenterMolecule V) (e : m.Aut)
    (c : m.Center) (i : Fin 4) (hc : m.centerPerm e c = c)
    (hu : (e : Equiv.Perm V) (m.ligandAtomAt c i) = m.ligandAtomAt c i) :
    m.ligandPermAt e c i = i := by
  apply m.ligandAtomAt_injective c
  have h := m.ligandAtomAt_ligandPermAt (e := e) (c := c) i
  rw [hc, hu] at h
  exact h

/-! ## The detected self-extension fixes the ligand slot -/

/-- The detected self-automorphism induced by a self-isomorphism of the branch at slot `i` fixes
slot `i` of the ligand permutation at the center. -/
theorem detectedCutBranchSelfAut_ligandPermAt_eq_self
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : ConstantFormalCharge input.certified.moleculeGraph)
    (c : input.certified.detectedMultiCenterMolecule.Center) (i : Fin 4)
    (φ : RootedCutBranchIso input.certified.moleculeGraph c.1
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt c i)
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt c i)) :
    input.certified.detectedMultiCenterMolecule.ligandPermAt
        (detectedCutBranchSelfAut input.certified.moleculeGraph c.1
          (input.certified.detectedMultiCenterMolecule.ligandAtomAt c i) acyclic
          (input.certified.detectedMultiCenterMolecule.ligandAtomAt_adj c i)
          singleBonded hcharge φ) c i = i := by
  apply ligandPermAt_eq_self_of_ligandAtomAt_eq_self
  · exact detectedCutBranchSelfAut_centerPerm_eq_self input.certified.moleculeGraph c.1
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt c i) acyclic
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt_adj c i)
      singleBonded hcharge φ c.2
  · exact detectedCutBranchSelfAut_apply_attach input.certified.moleculeGraph c.1
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt c i) acyclic
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt_adj c i)
      singleBonded hcharge φ

/-! ## The physical nearest centre is fixed

The physical unique-nearest predicate is graph-theoretic: cut-branch membership, the pure physical
mark, physical simple-walk spheres and path distances.  All of these are transported along the
self-extension, and physical uniqueness identifies the transported nearest centre with the original
one.  No configuration, reader, build, mirror, properness or non-native-label hypothesis occurs. -/

/-- **The detected self-extension fixes the physical nearest centre (slot form).**  For a detected
input, a root center `c`, a ligand slot `i` and reader-free physical unique-nearest data on the cut
branch at that slot, the atom map of the self-extension fixes the physical nearest centre. -/
theorem detectedCutBranchSelfAut_fixes_physicalBranchUniqueNearest_center
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : ConstantFormalCharge input.certified.moleculeGraph)
    (c : input.certified.detectedMultiCenterMolecule.Center) (i : Fin 4)
    (φ : RootedCutBranchIso input.certified.moleculeGraph c.1
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt c i)
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt c i))
    {center : input.certified.Atom} {distance : Nat}
    (nearest : TetraStereo.OneCenter.PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt c i) center distance) :
    ((detectedCutBranchSelfAut input.certified.moleculeGraph c.1
        (input.certified.detectedMultiCenterMolecule.ligandAtomAt c i) acyclic
        (input.certified.detectedMultiCenterMolecule.ligandAtomAt_adj c i)
        singleBonded hcharge φ :
        input.certified.detectedMultiCenterMolecule.Aut) :
      Equiv.Perm input.certified.Atom) center = center := by
  let m : MultiCenterMolecule input.certified.Atom :=
    input.certified.detectedMultiCenterMolecule
  let e : m.Aut := detectedCutBranchSelfAut input.certified.moleculeGraph c.1
    (m.ligandAtomAt c i) acyclic (m.ligandAtomAt_adj c i) singleBonded hcharge φ
  change (e : Equiv.Perm input.certified.Atom) center = center
  have hc : m.centerPerm e c = c :=
    detectedCutBranchSelfAut_centerPerm_eq_self input.certified.moleculeGraph c.1
      (m.ligandAtomAt c i) acyclic (m.ligandAtomAt_adj c i) singleBonded hcharge φ c.2
  have hu : (e : Equiv.Perm input.certified.Atom) (m.ligandAtomAt c i) = m.ligandAtomAt c i :=
    detectedCutBranchSelfAut_apply_attach input.certified.moleculeGraph c.1
      (m.ligandAtomAt c i) acyclic (m.ligandAtomAt_adj c i) singleBonded hcharge φ
  have hi : m.ligandPermAt e c i = i :=
    ligandPermAt_eq_self_of_ligandAtomAt_eq_self m e c i hc hu
  have transported : TetraStereo.OneCenter.PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩
      (m.ligandAtomAt c i) ((e : Equiv.Perm input.certified.Atom) center) distance :=
    LocalizedPhysicalReferenceCovariance.physicalBranchUniqueNearest_transport_detected
      (input := input) (c := c) (i := i) (j := i) (e := e) hc hi nearest
  exact (LocalizedPhysicalReferenceCovariance.physicalBranchUniqueNearest_center_unique_detected
    (input := input) (data₁ := nearest) (data₂ := transported)).1.symm

/-- **The detected self-extension fixes the physical nearest centre (ligand form).**  The root and
the attachment are given as an actual root center and an actual adjacent ligand atom; the ligand
slot is recovered from the detected enumeration, so no slot is part of the statement. -/
theorem detectedCutBranchSelfAut_fixes_physicalBranchUniqueNearest_center_of_adj
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : ConstantFormalCharge input.certified.moleculeGraph)
    (c : input.certified.detectedMultiCenterMolecule.Center) (u : input.certified.Atom)
    (hcu : input.certified.moleculeGraph.Adj c.1 u)
    (φ : RootedCutBranchIso input.certified.moleculeGraph c.1 u u)
    {center : input.certified.Atom} {distance : Nat}
    (nearest : TetraStereo.OneCenter.PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩ u center
      distance) :
    ((detectedCutBranchSelfAut input.certified.moleculeGraph c.1 u acyclic hcu singleBonded
        hcharge φ : input.certified.detectedMultiCenterMolecule.Aut) :
      Equiv.Perm input.certified.Atom) center = center := by
  obtain ⟨i, hi⟩ :=
    input.certified.detectedMultiCenterMolecule.ligandAtomAt_surjective c u hcu
  cases hi
  exact detectedCutBranchSelfAut_fixes_physicalBranchUniqueNearest_center (input := input)
    (singleBonded := singleBonded) (acyclic := acyclic) (hcharge := hcharge) (c := c) (i := i)
    (φ := φ) (nearest := nearest)

/-- **The branch self-isomorphism fixes the physical nearest centre.**  The nearest centre, as a
point of the cut branch, is fixed by `φ.toEquiv` itself.  This is the direct form consumed by the
actual-tree stage analysis: the actual shape self-isomorphism does not move the physically unique
nearest eligible centre. -/
theorem rootedCutBranchIso_fixes_physicalBranchUniqueNearest_center
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : ConstantFormalCharge input.certified.moleculeGraph)
    (c : input.certified.detectedMultiCenterMolecule.Center) (u : input.certified.Atom)
    (hcu : input.certified.moleculeGraph.Adj c.1 u)
    (φ : RootedCutBranchIso input.certified.moleculeGraph c.1 u u)
    {center : input.certified.Atom} {distance : Nat}
    (nearest : TetraStereo.OneCenter.PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩ u center
      distance) :
    (φ.toEquiv ⟨center, nearest.1⟩ : input.certified.Atom) = center := by
  have hfix := detectedCutBranchSelfAut_fixes_physicalBranchUniqueNearest_center_of_adj
    (input := input) (singleBonded := singleBonded) (acyclic := acyclic)
    (hcharge := hcharge) (c := c) (u := u) (hcu := hcu) (φ := φ) (nearest := nearest)
  have hmem : center ∈ CutBranch input.certified.moleculeGraph c.1 u := nearest.1
  have hval : ((detectedCutBranchSelfAut input.certified.moleculeGraph c.1 u acyclic hcu
      singleBonded hcharge φ : input.certified.detectedMultiCenterMolecule.Aut) :
      Equiv.Perm input.certified.Atom) center =
      (φ.toEquiv ⟨center, hmem⟩ : input.certified.Atom) :=
    detectedCutBranchSelfAut_apply_of_mem input.certified.moleculeGraph c.1 u acyclic hcu
      singleBonded hcharge φ hmem
  rw [hval] at hfix
  exact hfix

end

end LocalizedCutBranchSelfAutomorphism
end OneCenter
end TetraStereo

assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.cutBranchSelfFun
assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.cutBranchSelfFun_of_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.cutBranchSelfFun_of_not_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.cutBranchSelfInvFun
assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.cutBranchSelfInvFun_of_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.cutBranchSelfInvFun_of_not_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.cutBranchSelfInvFun_apply_selfFun
assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.cutBranchSelfFun_apply_invFun
assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.cutBranchSelfPerm
assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.rootedCutBranchIsoSymm
assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.cutBranchSelfInvFun_eq_cutBranchSelfFun_symm
assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.cutBranchSelfPerm_apply
assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.cutBranchSelfPerm_apply_of_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.cutBranchSelfPerm_apply_of_not_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.cutBranchSelfPerm_apply_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.cutBranchSelfPerm_map_branch
assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.cutBranchSelfPerm_apply_center
assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.cutBranchSelfPerm_apply_attach
assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.cutBranchSelfFun_adj_iff_of_mem_of_not_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.cutBranchSelfFun_adj_iff_of_not_mem_of_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.cutBranchSelfFun_adj_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.cutBranchSelfPerm_adj_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.cutBranchSelf_isAutomorphism
assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.cutBranchSelfAut
assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.cutBranchSelfAut_apply
assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.cutBranchSelfAut_apply_of_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.cutBranchSelfAut_apply_of_not_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.cutBranchSelfAut_apply_center
assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.cutBranchSelfAut_apply_attach
assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.detectedCutBranchSelfAut
assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.detectedCutBranchSelfAut_apply
assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.detectedCutBranchSelfAut_apply_of_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.detectedCutBranchSelfAut_apply_of_not_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.detectedCutBranchSelfAut_apply_center
assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.detectedCutBranchSelfAut_apply_attach
assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.detectedCutBranchSelfAut_centerPerm_eq_self
assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.centerPerm_eq_self_of_apply_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.ligandPermAt_eq_self_of_ligandAtomAt_eq_self
assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.detectedCutBranchSelfAut_ligandPermAt_eq_self
assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.detectedCutBranchSelfAut_fixes_physicalBranchUniqueNearest_center
assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.detectedCutBranchSelfAut_fixes_physicalBranchUniqueNearest_center_of_adj
assert_kernel_only TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism.rootedCutBranchIso_fixes_physicalBranchUniqueNearest_center
