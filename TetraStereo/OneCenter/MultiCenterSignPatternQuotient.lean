import TetraStereo.OneCenter.MultiCenterConfiguration
import Mathlib.GroupTheory.GroupAction.Defs

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

namespace MultiCenterMolecule

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The orbit quotient of configurations by the multi-center automorphism action. -/
abbrev ConfigurationQ (m : MultiCenterMolecule V) : Type _ :=
  MulAction.orbitRel.Quotient m.Aut m.Configuration

/-- The orbit quotient of sign patterns by the multi-center automorphism action. -/
abbrev SignPatternQ (m : MultiCenterMolecule V) : Type _ :=
  MulAction.orbitRel.Quotient m.Aut m.SignPattern

/-- The induced map from configuration orbits to sign-pattern orbits. -/
noncomputable def configurationSignQ (m : MultiCenterMolecule V) :
    m.ConfigurationQ → m.SignPatternQ :=
  Quotient.map' m.configurationSign (by
    classical
    intro cfg₁ cfg₂ h
    -- Unpack orbit-relations as existence of a symmetry taking `cfg₂` to `cfg₁`.
    rcases (MulAction.mem_orbit_iff).1 ((MulAction.orbitRel_apply).1 h) with ⟨e, rfl⟩
    -- The sign pattern transports equivariantly under the symmetry action.
    refine (MulAction.orbitRel_apply).2 ?_
    have hs : m.configurationSign (e • cfg₂) = e • m.configurationSign cfg₂ :=
      m.configurationSign_smul_eq (e := e) (cfg := cfg₂)
    simp [hs])

/-- A sign pattern is *achiral by symmetry* when a molecular automorphism carries it to its
negation. -/
def AchiralSignPatternBySymmetry (m : MultiCenterMolecule V) (s : m.SignPattern) : Prop :=
  ∃ e : m.Aut, e • s = -s

/-- A sign pattern is *chiral by symmetry* when no molecular automorphism carries it to its
negation. -/
def ChiralSignPatternBySymmetry (m : MultiCenterMolecule V) (s : m.SignPattern) : Prop :=
  ∀ e : m.Aut, e • s ≠ -s

theorem achiralSignPatternBySymmetry_iff_quotient_eq (m : MultiCenterMolecule V) (s : m.SignPattern) :
    m.AchiralSignPatternBySymmetry s ↔ (Quotient.mk'' s : m.SignPatternQ) = Quotient.mk'' (-s) := by
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
    have hs : MulAction.orbitRel m.Aut m.SignPattern s (-s) := Quotient.exact h
    rcases (MulAction.mem_orbit_iff).1 ((MulAction.orbitRel_apply).1 hs) with ⟨e, he⟩
    refine ⟨e⁻¹, ?_⟩
    have h' := congrArg (fun t => (e⁻¹ : m.Aut) • t) he
    have : (-s) = (e⁻¹ : m.Aut) • s := by
      simpa [smul_smul] using h'
    simpa using this.symm

theorem chiralSignPatternBySymmetry_iff_quotient_ne (m : MultiCenterMolecule V) (s : m.SignPattern) :
    m.ChiralSignPatternBySymmetry s ↔ (Quotient.mk'' s : m.SignPatternQ) ≠ Quotient.mk'' (-s) := by
  constructor
  · intro h hs
    have : m.AchiralSignPatternBySymmetry s :=
      (m.achiralSignPatternBySymmetry_iff_quotient_eq (s := s)).2 hs
    rcases this with ⟨e, he⟩
    exact h e he
  · intro h e he
    have hs : (Quotient.mk'' s : m.SignPatternQ) = Quotient.mk'' (-s) :=
      (m.achiralSignPatternBySymmetry_iff_quotient_eq (s := s)).1 ⟨e, he⟩
    exact h hs

theorem achiralConfigurationBySymmetry_iff_achiralSignPattern (m : MultiCenterMolecule V)
    (cfg : m.Configuration) :
    m.AchiralConfigurationBySymmetry cfg ↔ m.AchiralSignPatternBySymmetry (m.configurationSign cfg) := by
  simpa [AchiralSignPatternBySymmetry] using
    (m.achiralConfigurationBySymmetry_iff_exists_smul_eq_neg (cfg := cfg))

theorem chiralConfigurationBySymmetry_iff_chiralSignPattern (m : MultiCenterMolecule V)
    (cfg : m.Configuration) :
    m.ChiralConfigurationBySymmetry cfg ↔ m.ChiralSignPatternBySymmetry (m.configurationSign cfg) := by
  simpa [ChiralSignPatternBySymmetry] using
    (m.chiralConfigurationBySymmetry_iff_forall_smul_ne_neg (cfg := cfg))

theorem achiralConfigurationBySymmetry_iff_quotient_eq (m : MultiCenterMolecule V)
    (cfg : m.Configuration) :
    m.AchiralConfigurationBySymmetry cfg ↔
      (Quotient.mk'' (m.configurationSign cfg) : m.SignPatternQ) = Quotient.mk'' (-m.configurationSign cfg) := by
  constructor
  · intro h
    have h' : m.AchiralSignPatternBySymmetry (m.configurationSign cfg) := by
      simpa [m.achiralConfigurationBySymmetry_iff_achiralSignPattern (cfg := cfg)] using h
    simpa [m.achiralSignPatternBySymmetry_iff_quotient_eq] using h'
  · intro h
    have h' : m.AchiralSignPatternBySymmetry (m.configurationSign cfg) := by
      simpa [m.achiralSignPatternBySymmetry_iff_quotient_eq] using h
    simpa [m.achiralConfigurationBySymmetry_iff_achiralSignPattern (cfg := cfg)] using h'

theorem chiralConfigurationBySymmetry_iff_quotient_ne (m : MultiCenterMolecule V) (cfg : m.Configuration) :
    m.ChiralConfigurationBySymmetry cfg ↔
      (Quotient.mk'' (m.configurationSign cfg) : m.SignPatternQ) ≠ Quotient.mk'' (-m.configurationSign cfg) := by
  exact
    (m.chiralConfigurationBySymmetry_iff_chiralSignPattern (cfg := cfg)).trans
      (m.chiralSignPatternBySymmetry_iff_quotient_ne (s := m.configurationSign cfg))

end MultiCenterMolecule

end
end OneCenter
end TetraStereo
