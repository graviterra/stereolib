import TetraStereo.OneCenter.MultiCenterSymmetry

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

namespace MultiCenterMolecule

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A (toy) multi-center stereochemical configuration: a choice of local frame at each distinguished
center. -/
abbrev Configuration (m : MultiCenterMolecule V) : Type _ :=
  m.Center → Equiv.Perm (Fin 4)

/-- The local ligand-index permutation induced by a multi-center automorphism at a specific center.

This is defined relative to the (chosen) `Fin 4 ≃ Neighbor` equivalences bundled in
`MultiCenterMolecule.ligandEquiv`. -/
noncomputable def ligandPermAt (m : MultiCenterMolecule V) (e : m.Aut) (c : m.Center) :
    Equiv.Perm (Fin 4) := by
  classical
  let eMol : m.mol.Aut := ⟨(e : Equiv.Perm V), MultiCenterMolecule.Aut.mem_molAut (m := m) e⟩
  exact
    (m.ligandEquiv c).trans (MoleculeGraph.neighborEquiv (m := m.mol) eMol c.1) |>.trans
      (m.ligandEquiv (m.centerPerm e c)).symm

@[simp] theorem ligandAtomAt_ligandPermAt (m : MultiCenterMolecule V) (e : m.Aut) (c : m.Center)
    (i : Fin 4) :
    m.ligandAtomAt (m.centerPerm e c) (m.ligandPermAt e c i) =
      (e : Equiv.Perm V) (m.ligandAtomAt c i) := by
  classical
  have h :
      m.ligandEquiv (m.centerPerm e c) (m.ligandPermAt e c i) =
        MoleculeGraph.neighborEquiv (m := m.mol)
          (⟨(e : Equiv.Perm V), MultiCenterMolecule.Aut.mem_molAut (m := m) e⟩) c.1
            (m.ligandEquiv c i) := by
    -- Unfold `ligandPermAt`; the goal reduces to `apply_symm_apply` for `ligandEquiv`.
    simp [ligandPermAt, Equiv.trans_apply]
    exact (m.ligandEquiv (m.centerPerm e c)).apply_symm_apply _
  simpa [MultiCenterMolecule.ligandEquiv, MoleculeGraph.neighborEquiv, MultiCenterMolecule.ligandAtomAt] using
    congrArg Subtype.val h

theorem ligandPermAt_one (m : MultiCenterMolecule V) (c : m.Center) :
    m.ligandPermAt (1 : m.Aut) c = 1 := by
  classical
  ext i
  have hi : m.ligandPermAt (1 : m.Aut) c i = i := by
    -- Compare images via `ligandAtomAt`.
    have hcenter : m.centerPerm (1 : m.Aut) c = c := by
      simpa [MultiCenterMolecule.centerPermHom] using congrArg (fun p => p c) (m.centerPermHom.map_one)
    apply m.ligandAtomAt_injective c
    -- Transport through the identity automorphism.
    have hAtom := m.ligandAtomAt_ligandPermAt (e := (1 : m.Aut)) (c := c) i
    simpa [hcenter] using hAtom
  simpa using congrArg Fin.val hi

theorem ligandPermAt_mul (m : MultiCenterMolecule V) (e f : m.Aut) (c : m.Center) :
    m.ligandPermAt (e * f) c = m.ligandPermAt e (m.centerPerm f c) * m.ligandPermAt f c := by
  classical
  ext i
  have hcenter :
      m.centerPerm (e * f) c = m.centerPerm e (m.centerPerm f c) := by
    -- `centerPerm` is a hom.
    simpa [MultiCenterMolecule.centerPermHom] using congrArg (fun p => p c) (m.centerPermHom.map_mul e f)
  -- Compare indices via injectivity of the target center's ligand enumeration.
  have hi :
      m.ligandPermAt (e * f) c i =
        m.ligandPermAt e (m.centerPerm f c) (m.ligandPermAt f c i) := by
    apply m.ligandAtomAt_injective (m.centerPerm (e * f) c)
    -- LHS transports directly by `e * f`.
    have hL := m.ligandAtomAt_ligandPermAt (e := (e * f)) (c := c) i
    -- RHS transports by `f`, then by `e`.
    have hF := m.ligandAtomAt_ligandPermAt (e := f) (c := c) i
    have hE :=
      m.ligandAtomAt_ligandPermAt (e := e) (c := m.centerPerm f c) (i := m.ligandPermAt f c i)
    -- Rewrite the center on the RHS using `hcenter`.
    have hE' :
        m.ligandAtomAt (m.centerPerm (e * f) c)
            (m.ligandPermAt e (m.centerPerm f c) (m.ligandPermAt f c i)) =
          (e : Equiv.Perm V)
            (m.ligandAtomAt (m.centerPerm f c) (m.ligandPermAt f c i)) := by
      simp [hcenter]
    -- Now both sides are `e (f (ligandAtomAt c i))`.
    calc
      m.ligandAtomAt (m.centerPerm (e * f) c) (m.ligandPermAt (e * f) c i)
          = (e * f : Equiv.Perm V) (m.ligandAtomAt c i) := hL
      _ = (e : Equiv.Perm V) ((f : Equiv.Perm V) (m.ligandAtomAt c i)) := rfl
      _ = (e : Equiv.Perm V) (m.ligandAtomAt (m.centerPerm f c) (m.ligandPermAt f c i)) := by
            simp [hF]
      _ = m.ligandAtomAt (m.centerPerm (e * f) c)
            (m.ligandPermAt e (m.centerPerm f c) (m.ligandPermAt f c i)) := by
            simp [hE']
  -- Unpack multiplication in `Equiv.Perm`: `(σ * τ) i = σ (τ i)`.
  have hi' :
      (m.ligandPermAt (e * f) c) i = (m.ligandPermAt e (m.centerPerm f c) * m.ligandPermAt f c) i := by
    simpa using hi
  simpa using congrArg Fin.val hi'

/-- The action of a multi-center automorphism on configurations:
permute the centers, and reindex each local frame by the induced ligand permutation. -/
noncomputable def smulConfiguration (m : MultiCenterMolecule V) (e : m.Aut)
    (cfg : m.Configuration) : m.Configuration :=
  fun c => cfg ((m.centerPerm e)⁻¹ c) * (m.ligandPermAt e ((m.centerPerm e)⁻¹ c))⁻¹

instance (m : MultiCenterMolecule V) : MulAction m.Aut m.Configuration where
  smul := m.smulConfiguration
  one_smul := by
    classical
    intro cfg
    funext c
    change m.smulConfiguration (1 : m.Aut) cfg c = cfg c
    have hcenter : m.centerPerm (1 : m.Aut) = 1 := by
      simpa [MultiCenterMolecule.centerPermHom] using (m.centerPermHom.map_one)
    simp [MultiCenterMolecule.smulConfiguration, hcenter, ligandPermAt_one]
  mul_smul := by
    classical
    intro e f cfg
    funext c
    change m.smulConfiguration (e * f) cfg c = m.smulConfiguration e (m.smulConfiguration f cfg) c
    have hcenterMul : m.centerPerm (e * f) = m.centerPerm e * m.centerPerm f := by
      simpa [MultiCenterMolecule.centerPermHom] using (m.centerPermHom.map_mul e f)
    let preE : m.Center := ((m.centerPerm e)⁻¹ c)
    let pre0 : m.Center := ((m.centerPerm f)⁻¹ preE)
    have hpre : ((m.centerPerm (e * f))⁻¹ c) = pre0 := by
      have hinv : (m.centerPerm (e * f))⁻¹ = (m.centerPerm f)⁻¹ * (m.centerPerm e)⁻¹ := by
        simp [hcenterMul, mul_inv_rev]
      have := congrArg (fun p => p c) hinv
      simpa [preE, pre0] using this
    have hpreE : m.centerPerm f pre0 = preE := by
      simp [pre0, preE]
    simp [MultiCenterMolecule.smulConfiguration, hpre, preE, pre0, mul_assoc, ligandPermAt_mul, mul_inv_rev]

theorem smulConfiguration_apply (m : MultiCenterMolecule V) (e : m.Aut) (cfg : m.Configuration)
    (c : m.Center) :
    (e • cfg) c =
      cfg ((m.centerPerm e)⁻¹ c) * (m.ligandPermAt e ((m.centerPerm e)⁻¹ c))⁻¹ := rfl

/-- A sign pattern on the distinguished centers of `m`. -/
abbrev SignPattern (m : MultiCenterMolecule V) : Type _ :=
  m.Center → ℝ

/-- The handedness-sign of a multi-center configuration at each center. -/
abbrev configurationSign (m : MultiCenterMolecule V) (cfg : m.Configuration) : m.SignPattern :=
  fun c => permHandedness (cfg c)

theorem configurationSign_smul (m : MultiCenterMolecule V) (e : m.Aut) (cfg : m.Configuration)
    (c : m.Center) :
    m.configurationSign (e • cfg) c =
      m.configurationSign cfg ((m.centerPerm e)⁻¹ c) *
        permHandedness (m.ligandPermAt e ((m.centerPerm e)⁻¹ c)) := by
  dsimp [configurationSign]
  have h := congrArg permHandedness (m.smulConfiguration_apply (e := e) (cfg := cfg) (c := c))
  -- `permHandedness` ignores inversion.
  simpa [permHandedness_mul] using h

/-- The induced action of a multi-center automorphism on sign patterns:
permute centers and multiply by the local ligand-permutation handedness. -/
noncomputable def smulSignPattern (m : MultiCenterMolecule V) (e : m.Aut) (s : m.SignPattern) :
    m.SignPattern :=
  fun c => s ((m.centerPerm e)⁻¹ c) * permHandedness (m.ligandPermAt e ((m.centerPerm e)⁻¹ c))

instance (m : MultiCenterMolecule V) : MulAction m.Aut m.SignPattern where
  smul := m.smulSignPattern
  one_smul := by
    classical
    intro s
    funext c
    change m.smulSignPattern (1 : m.Aut) s c = s c
    have hcenter : m.centerPerm (1 : m.Aut) = 1 := by
      simpa [MultiCenterMolecule.centerPermHom] using (m.centerPermHom.map_one)
    simp [MultiCenterMolecule.smulSignPattern, hcenter, ligandPermAt_one]
  mul_smul := by
    classical
    intro e f s
    funext c
    change m.smulSignPattern (e * f) s c = m.smulSignPattern e (m.smulSignPattern f s) c
    have hcenterMul : m.centerPerm (e * f) = m.centerPerm e * m.centerPerm f := by
      simpa [MultiCenterMolecule.centerPermHom] using (m.centerPermHom.map_mul e f)
    let preE : m.Center := ((m.centerPerm e)⁻¹ c)
    let pre0 : m.Center := ((m.centerPerm f)⁻¹ preE)
    have hpre : ((m.centerPerm (e * f))⁻¹ c) = pre0 := by
      have hinv : (m.centerPerm (e * f))⁻¹ = (m.centerPerm f)⁻¹ * (m.centerPerm e)⁻¹ := by
        simp [hcenterMul, mul_inv_rev]
      have := congrArg (fun p => p c) hinv
      simpa [preE, pre0] using this
    have hpreE : m.centerPerm f pre0 = preE := by
      simp [pre0, preE]
    -- Unfold and reduce to a commutative rearrangement in `ℝ`.
    simp [MultiCenterMolecule.smulSignPattern, hpre, preE, pre0, ligandPermAt_mul, permHandedness_mul, mul_assoc]
    refine Or.inl ?_
    ac_rfl

theorem configurationSign_smul_eq (m : MultiCenterMolecule V) (e : m.Aut) (cfg : m.Configuration) :
    m.configurationSign (e • cfg) = e • m.configurationSign cfg := by
  funext c
  simpa [MultiCenterMolecule.smulSignPattern] using (m.configurationSign_smul (e := e) (cfg := cfg) (c := c))

/-- A fixed odd permutation of the four ligand indices, used to model mirror inversion at a single
center. -/
def mirrorFrame : Equiv.Perm (Fin 4) :=
  Equiv.swap (0 : Fin 4) 1

/-- Mirror (invert) every local frame by composing with a fixed odd permutation. -/
def mirrorConfiguration (m : MultiCenterMolecule V) (cfg : m.Configuration) : m.Configuration :=
  fun c => cfg c * mirrorFrame

theorem configurationSign_mirrorConfiguration (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (c : m.Center) :
    m.configurationSign (m.mirrorConfiguration cfg) c = -m.configurationSign cfg c := by
  simp [configurationSign, mirrorConfiguration, mirrorFrame, permHandedness_mul]

theorem configurationSign_mirrorConfiguration_eq_neg (m : MultiCenterMolecule V) (cfg : m.Configuration) :
    m.configurationSign (m.mirrorConfiguration cfg) = -m.configurationSign cfg := by
  funext c
  simpa using (m.configurationSign_mirrorConfiguration (cfg := cfg) (c := c))

/-- A configuration is *achiral by symmetry* when it is symmetry-equivalent (via a molecular
automorphism) to its mirror. -/
def AchiralConfigurationBySymmetry (m : MultiCenterMolecule V) (cfg : m.Configuration) : Prop :=
  ∃ e : m.Aut, m.configurationSign (e • cfg) = m.configurationSign (m.mirrorConfiguration cfg)

/-- A configuration is *chiral by symmetry* when no molecular automorphism carries it to its mirror. -/
def ChiralConfigurationBySymmetry (m : MultiCenterMolecule V) (cfg : m.Configuration) : Prop :=
  ∀ e : m.Aut, m.configurationSign (e • cfg) ≠ m.configurationSign (m.mirrorConfiguration cfg)

theorem achiralConfigurationBySymmetry_iff_exists_smul_eq_neg (m : MultiCenterMolecule V)
    (cfg : m.Configuration) :
    m.AchiralConfigurationBySymmetry cfg ↔ ∃ e : m.Aut, e • m.configurationSign cfg = -m.configurationSign cfg := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    simpa [m.configurationSign_smul_eq (e := e) (cfg := cfg),
      m.configurationSign_mirrorConfiguration_eq_neg (cfg := cfg)] using he
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    simpa [m.configurationSign_smul_eq (e := e) (cfg := cfg),
      m.configurationSign_mirrorConfiguration_eq_neg (cfg := cfg)] using he

theorem chiralConfigurationBySymmetry_iff_forall_smul_ne_neg (m : MultiCenterMolecule V)
    (cfg : m.Configuration) :
    m.ChiralConfigurationBySymmetry cfg ↔
      ∀ e : m.Aut, e • m.configurationSign cfg ≠ -m.configurationSign cfg := by
  constructor
  · intro h e
    have : m.configurationSign (e • cfg) ≠ m.configurationSign (m.mirrorConfiguration cfg) := h e
    simpa [m.configurationSign_smul_eq (e := e) (cfg := cfg),
      m.configurationSign_mirrorConfiguration_eq_neg (cfg := cfg)] using this
  · intro h e
    have : e • m.configurationSign cfg ≠ -m.configurationSign cfg := h e
    simpa [m.configurationSign_smul_eq (e := e) (cfg := cfg),
      m.configurationSign_mirrorConfiguration_eq_neg (cfg := cfg)] using this

end MultiCenterMolecule

end
end OneCenter
end TetraStereo
