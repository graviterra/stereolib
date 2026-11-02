import TetraStereo.OneCenter.MultiCenterCIP
import TetraStereo.OneCenter.MultiCenterSignPatternQuotient

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

namespace MultiCenterMolecule

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A sign pattern with the `m.Aut`-action that only permutes the distinguished centers.

This is the action naturally satisfied by CIP-normalized sign patterns. -/
structure CipSignPattern (m : MultiCenterMolecule V) : Type _ where
  val : m.SignPattern

namespace CipSignPattern

variable {m : MultiCenterMolecule V}

instance : Coe m.CipSignPattern m.SignPattern :=
  ⟨CipSignPattern.val⟩

instance : CoeFun m.CipSignPattern (fun _ => m.Center → ℝ) where
  coe s := s.val

@[simp] theorem coe_val (s : m.CipSignPattern) : (s : m.SignPattern) = s.val := rfl

@[ext] theorem ext (s t : m.CipSignPattern) (h : ∀ c, s c = t c) : s = t := by
  cases s with
  | mk sv =>
      cases t with
      | mk tv =>
          have : sv = tv := funext h
          simp [this]

instance : Neg m.CipSignPattern where
  neg s := ⟨-s.val⟩

@[simp] theorem val_neg (s : m.CipSignPattern) : (-s).val = -s.val := rfl

end CipSignPattern

/-- The center-permutation action of a multi-center automorphism on CIP sign patterns. -/
noncomputable def smulCipSignPattern (m : MultiCenterMolecule V) (e : m.Aut) (s : m.CipSignPattern) :
    m.CipSignPattern :=
  ⟨fun c => s ((m.centerPerm e)⁻¹ c)⟩

instance (m : MultiCenterMolecule V) : MulAction m.Aut m.CipSignPattern where
  smul := m.smulCipSignPattern
  one_smul := by
    classical
    intro s
    ext c
    change m.smulCipSignPattern (1 : m.Aut) s c = s c
    have hcenter : m.centerPerm (1 : m.Aut) = 1 := by
      simpa [MultiCenterMolecule.centerPermHom] using (m.centerPermHom.map_one)
    simp [MultiCenterMolecule.smulCipSignPattern, hcenter]
  mul_smul := by
    classical
    intro e f s
    ext c
    change m.smulCipSignPattern (e * f) s c = m.smulCipSignPattern e (m.smulCipSignPattern f s) c
    have hcenterMul : m.centerPerm (e * f) = m.centerPerm e * m.centerPerm f := by
      simpa [MultiCenterMolecule.centerPermHom] using (m.centerPermHom.map_mul e f)
    simp [MultiCenterMolecule.smulCipSignPattern, hcenterMul, mul_inv_rev]

/-- Orbit quotient of CIP sign patterns by the center-permutation action. -/
abbrev CipSignPatternQ (m : MultiCenterMolecule V) : Type _ :=
  MulAction.orbitRel.Quotient m.Aut m.CipSignPattern

/-- `cipConfigurationSign` descends to the configuration orbit quotient, assuming every distinguished
center is CIP-stereogenic. -/
noncomputable def cipConfigurationSignQ (m : MultiCenterMolecule V)
    (hst : ∀ c : m.Center, m.StereogenicByCIPAt c) :
    m.ConfigurationQ → m.CipSignPatternQ :=
  Quotient.map' (fun cfg => (⟨m.cipConfigurationSign cfg⟩ : m.CipSignPattern)) (by
    classical
    intro cfg₁ cfg₂ h
    rcases (MulAction.mem_orbit_iff).1 ((MulAction.orbitRel_apply).1 h) with ⟨e, rfl⟩
    refine (MulAction.orbitRel_apply).2 ?_
    refine (MulAction.mem_orbit_iff).2 ?_
    refine ⟨e, ?_⟩
    ext c
    change m.cipConfigurationSign cfg₂ ((m.centerPerm e)⁻¹ c) = m.cipConfigurationSign (e • cfg₂) c
    simpa using
      (m.cipConfigurationSign_smul_of_stereogenicByCIPAt (hst := hst) (e := e) (cfg := cfg₂) (c := c)).symm)

/-- A CIP sign pattern is *achiral by symmetry* when a molecular automorphism carries it to its
negation (under center permutation only). -/
def AchiralCipSignPatternBySymmetry (m : MultiCenterMolecule V) (s : m.CipSignPattern) : Prop :=
  ∃ e : m.Aut, e • s = -s

/-- A CIP sign pattern is *chiral by symmetry* when no molecular automorphism carries it to its
negation (under center permutation only). -/
def ChiralCipSignPatternBySymmetry (m : MultiCenterMolecule V) (s : m.CipSignPattern) : Prop :=
  ∀ e : m.Aut, e • s ≠ -s

theorem achiralCipSignPatternBySymmetry_iff_quotient_eq (m : MultiCenterMolecule V) (s : m.CipSignPattern) :
    m.AchiralCipSignPatternBySymmetry s ↔ (Quotient.mk'' s : m.CipSignPatternQ) = Quotient.mk'' (-s) := by
  classical
  constructor
  · rintro ⟨e, he⟩
    refine Quotient.sound ?_
    refine (MulAction.orbitRel_apply).2 ?_
    refine ⟨e⁻¹, ?_⟩
    have hneg : -s = e • s := by simpa using he.symm
    calc
      (e⁻¹ : m.Aut) • (-s) = (e⁻¹ : m.Aut) • (e • s) := by simp [hneg]
      _ = s := by simp [smul_smul]
  · intro h
    have hs : MulAction.orbitRel m.Aut m.CipSignPattern s (-s) := Quotient.exact h
    rcases (MulAction.mem_orbit_iff).1 ((MulAction.orbitRel_apply).1 hs) with ⟨e, he⟩
    refine ⟨e⁻¹, ?_⟩
    have h' := congrArg (fun t => (e⁻¹ : m.Aut) • t) he
    have : (-s) = (e⁻¹ : m.Aut) • s := by
      simpa [smul_smul] using h'
    simpa using this.symm

theorem chiralCipSignPatternBySymmetry_iff_quotient_ne (m : MultiCenterMolecule V) (s : m.CipSignPattern) :
    m.ChiralCipSignPatternBySymmetry s ↔ (Quotient.mk'' s : m.CipSignPatternQ) ≠ Quotient.mk'' (-s) := by
  constructor
  · intro h hs
    have : m.AchiralCipSignPatternBySymmetry s :=
      (m.achiralCipSignPatternBySymmetry_iff_quotient_eq (s := s)).2 hs
    rcases this with ⟨e, he⟩
    exact h e he
  · intro h e he
    have hs : (Quotient.mk'' s : m.CipSignPatternQ) = Quotient.mk'' (-s) :=
      (m.achiralCipSignPatternBySymmetry_iff_quotient_eq (s := s)).1 ⟨e, he⟩
    exact h hs

/-- A configuration is *CIP-achiral by symmetry* when some molecular automorphism carries its
`cipConfigurationSign` to the mirror `cipConfigurationSign`. -/
def AchiralCipConfigurationBySymmetry (m : MultiCenterMolecule V) (cfg : m.Configuration) : Prop :=
  ∃ e : m.Aut, m.cipConfigurationSign (e • cfg) = m.cipConfigurationSign (m.mirrorConfiguration cfg)

/-- A configuration is *CIP-chiral by symmetry* when no molecular automorphism carries its
`cipConfigurationSign` to the mirror `cipConfigurationSign`. -/
def ChiralCipConfigurationBySymmetry (m : MultiCenterMolecule V) (cfg : m.Configuration) : Prop :=
  ∀ e : m.Aut, m.cipConfigurationSign (e • cfg) ≠ m.cipConfigurationSign (m.mirrorConfiguration cfg)

theorem cipConfigurationSign_smul_eq_of_stereogenicByCIPAt (m : MultiCenterMolecule V)
    (hst : ∀ c : m.Center, m.StereogenicByCIPAt c) (e : m.Aut) (cfg : m.Configuration) :
    e • (⟨m.cipConfigurationSign cfg⟩ : m.CipSignPattern) =
      (⟨m.cipConfigurationSign (e • cfg)⟩ : m.CipSignPattern) := by
  ext c
  change m.cipConfigurationSign cfg ((m.centerPerm e)⁻¹ c) = m.cipConfigurationSign (e • cfg) c
  simpa using
    (m.cipConfigurationSign_smul_of_stereogenicByCIPAt (hst := hst) (e := e) (cfg := cfg) (c := c)).symm

theorem achiralCipConfigurationBySymmetry_iff_achiralCipSignPattern (m : MultiCenterMolecule V)
    (hst : ∀ c : m.Center, m.StereogenicByCIPAt c) (cfg : m.Configuration) :
    m.AchiralCipConfigurationBySymmetry cfg ↔
      m.AchiralCipSignPatternBySymmetry (⟨m.cipConfigurationSign cfg⟩ : m.CipSignPattern) := by
  classical
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    have hmirror : m.cipConfigurationSign (m.mirrorConfiguration cfg) = -m.cipConfigurationSign cfg := by
      simpa using (m.cipConfigurationSign_mirrorConfiguration_eq_neg (cfg := cfg))
    have hneg : m.cipConfigurationSign (e • cfg) = -m.cipConfigurationSign cfg := by
      simpa [hmirror] using he
    -- Transport `cipConfigurationSign (e • cfg)` back to the `CipSignPattern` action.
    have hsmul :
        e • (⟨m.cipConfigurationSign cfg⟩ : m.CipSignPattern) =
          (⟨m.cipConfigurationSign (e • cfg)⟩ : m.CipSignPattern) :=
      m.cipConfigurationSign_smul_eq_of_stereogenicByCIPAt (hst := hst) (e := e) (cfg := cfg)
    have hCip :
        (⟨m.cipConfigurationSign (e • cfg)⟩ : m.CipSignPattern) =
          -(⟨m.cipConfigurationSign cfg⟩ : m.CipSignPattern) := by
      ext c
      have hc := congrArg (fun s : m.SignPattern => s c) hneg
      simpa using hc
    simpa [hsmul] using hCip
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    have hsmul :
        e • (⟨m.cipConfigurationSign cfg⟩ : m.CipSignPattern) =
          (⟨m.cipConfigurationSign (e • cfg)⟩ : m.CipSignPattern) :=
      m.cipConfigurationSign_smul_eq_of_stereogenicByCIPAt (hst := hst) (e := e) (cfg := cfg)
    have hneg :
        (⟨m.cipConfigurationSign (e • cfg)⟩ : m.CipSignPattern) =
          -(⟨m.cipConfigurationSign cfg⟩ : m.CipSignPattern) := by
      simpa [hsmul] using he
    -- Unwrap back to `SignPattern` and use the mirror lemma.
    have hneg' : m.cipConfigurationSign (e • cfg) = -m.cipConfigurationSign cfg := by
      funext c
      have hc := congrArg (fun s : m.CipSignPattern => s c) hneg
      simpa using hc
    have hmirror : m.cipConfigurationSign (m.mirrorConfiguration cfg) = -m.cipConfigurationSign cfg := by
      simpa using (m.cipConfigurationSign_mirrorConfiguration_eq_neg (cfg := cfg))
    simpa [hmirror] using hneg'

theorem chiralCipConfigurationBySymmetry_iff_chiralCipSignPattern (m : MultiCenterMolecule V)
    (hst : ∀ c : m.Center, m.StereogenicByCIPAt c) (cfg : m.Configuration) :
    m.ChiralCipConfigurationBySymmetry cfg ↔
      m.ChiralCipSignPatternBySymmetry (⟨m.cipConfigurationSign cfg⟩ : m.CipSignPattern) := by
  classical
  constructor
  · intro h e he
    have hAchSign :
        m.AchiralCipSignPatternBySymmetry (⟨m.cipConfigurationSign cfg⟩ : m.CipSignPattern) :=
      ⟨e, he⟩
    have hAchCfg : m.AchiralCipConfigurationBySymmetry cfg :=
      (m.achiralCipConfigurationBySymmetry_iff_achiralCipSignPattern (hst := hst) (cfg := cfg)).2 hAchSign
    rcases hAchCfg with ⟨eCfg, heCfg⟩
    exact (h eCfg) heCfg
  · intro h e heCfg
    have hAchCfg : m.AchiralCipConfigurationBySymmetry cfg := ⟨e, heCfg⟩
    have hAchSign : m.AchiralCipSignPatternBySymmetry (⟨m.cipConfigurationSign cfg⟩ : m.CipSignPattern) :=
      (m.achiralCipConfigurationBySymmetry_iff_achiralCipSignPattern (hst := hst) (cfg := cfg)).1 hAchCfg
    rcases hAchSign with ⟨e', he'⟩
    exact h e' he'

theorem achiralCipConfigurationBySymmetry_iff_quotient_eq (m : MultiCenterMolecule V)
    (hst : ∀ c : m.Center, m.StereogenicByCIPAt c) (cfg : m.Configuration) :
    m.AchiralCipConfigurationBySymmetry cfg ↔
      (Quotient.mk'' (⟨m.cipConfigurationSign cfg⟩ : m.CipSignPattern) : m.CipSignPatternQ) =
        Quotient.mk'' (-(⟨m.cipConfigurationSign cfg⟩ : m.CipSignPattern)) := by
  have :
      m.AchiralCipSignPatternBySymmetry (⟨m.cipConfigurationSign cfg⟩ : m.CipSignPattern) ↔
        (Quotient.mk'' (⟨m.cipConfigurationSign cfg⟩ : m.CipSignPattern) : m.CipSignPatternQ) =
          Quotient.mk'' (-(⟨m.cipConfigurationSign cfg⟩ : m.CipSignPattern)) :=
    m.achiralCipSignPatternBySymmetry_iff_quotient_eq (s := (⟨m.cipConfigurationSign cfg⟩ : m.CipSignPattern))
  exact
    (m.achiralCipConfigurationBySymmetry_iff_achiralCipSignPattern (hst := hst) (cfg := cfg)).trans this

theorem chiralCipConfigurationBySymmetry_iff_quotient_ne (m : MultiCenterMolecule V)
    (hst : ∀ c : m.Center, m.StereogenicByCIPAt c) (cfg : m.Configuration) :
    m.ChiralCipConfigurationBySymmetry cfg ↔
      (Quotient.mk'' (⟨m.cipConfigurationSign cfg⟩ : m.CipSignPattern) : m.CipSignPatternQ) ≠
        Quotient.mk'' (-(⟨m.cipConfigurationSign cfg⟩ : m.CipSignPattern)) := by
  have :
      m.ChiralCipSignPatternBySymmetry (⟨m.cipConfigurationSign cfg⟩ : m.CipSignPattern) ↔
        (Quotient.mk'' (⟨m.cipConfigurationSign cfg⟩ : m.CipSignPattern) : m.CipSignPatternQ) ≠
          Quotient.mk'' (-(⟨m.cipConfigurationSign cfg⟩ : m.CipSignPattern)) :=
    m.chiralCipSignPatternBySymmetry_iff_quotient_ne (s := (⟨m.cipConfigurationSign cfg⟩ : m.CipSignPattern))
  exact
    (m.chiralCipConfigurationBySymmetry_iff_chiralCipSignPattern (hst := hst) (cfg := cfg)).trans this

end MultiCenterMolecule

end
end OneCenter
end TetraStereo
