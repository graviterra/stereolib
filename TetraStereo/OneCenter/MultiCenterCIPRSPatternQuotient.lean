import TetraStereo.OneCenter.MultiCenterRS
import TetraStereo.OneCenter.MultiCenterSignPatternQuotient

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

namespace MultiCenterMolecule

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A multi-center `R/S` pattern with the `m.Aut`-action that only permutes the distinguished
centers.

This is the action naturally satisfied by CIP-normalized `R/S` patterns under CIP-stereogenicity. -/
structure CipRSPattern (m : MultiCenterMolecule V) : Type _ where
  val : m.RSPattern

namespace CipRSPattern

variable {m : MultiCenterMolecule V}

instance : Coe m.CipRSPattern m.RSPattern :=
  ⟨CipRSPattern.val⟩

instance : CoeFun m.CipRSPattern (fun _ => m.Center → RS) where
  coe s := s.val

@[simp] theorem coe_val (s : m.CipRSPattern) : (s : m.RSPattern) = s.val := rfl

@[ext] theorem ext (s t : m.CipRSPattern) (h : ∀ c, s c = t c) : s = t := by
  cases s with
  | mk sv =>
      cases t with
      | mk tv =>
          have : sv = tv := funext h
          simp [this]

instance : Neg m.CipRSPattern where
  neg s := ⟨m.mirrorRSPattern s.val⟩

@[simp] theorem val_neg (s : m.CipRSPattern) : (-s).val = m.mirrorRSPattern s.val := rfl

end CipRSPattern

/-- The center-permutation action of a multi-center automorphism on CIP `R/S` patterns. -/
noncomputable def smulCipRSPattern (m : MultiCenterMolecule V) (e : m.Aut) (s : m.CipRSPattern) :
    m.CipRSPattern :=
  ⟨fun c => s ((m.centerPerm e)⁻¹ c)⟩

instance (m : MultiCenterMolecule V) : MulAction m.Aut m.CipRSPattern where
  smul := m.smulCipRSPattern
  one_smul := by
    classical
    intro s
    ext c
    change m.smulCipRSPattern (1 : m.Aut) s c = s c
    have hcenter : m.centerPerm (1 : m.Aut) = 1 := by
      simpa [MultiCenterMolecule.centerPermHom] using (m.centerPermHom.map_one)
    simp [MultiCenterMolecule.smulCipRSPattern, hcenter]
  mul_smul := by
    classical
    intro e f s
    ext c
    change m.smulCipRSPattern (e * f) s c = m.smulCipRSPattern e (m.smulCipRSPattern f s) c
    have hcenterMul : m.centerPerm (e * f) = m.centerPerm e * m.centerPerm f := by
      simpa [MultiCenterMolecule.centerPermHom] using (m.centerPermHom.map_mul e f)
    simp [MultiCenterMolecule.smulCipRSPattern, hcenterMul, mul_inv_rev]

/-- Orbit quotient of CIP `R/S` patterns by the center-permutation action. -/
abbrev CipRSPatternQ (m : MultiCenterMolecule V) : Type _ :=
  MulAction.orbitRel.Quotient m.Aut m.CipRSPattern

/-- `cipConfigurationRS` descends to the configuration orbit quotient, assuming every distinguished
center is CIP-stereogenic. -/
noncomputable def cipConfigurationRSQ (m : MultiCenterMolecule V)
    (hst : ∀ c : m.Center, m.StereogenicByCIPAt c) :
    m.ConfigurationQ → m.CipRSPatternQ :=
  Quotient.map' (fun cfg => (⟨m.cipConfigurationRS cfg⟩ : m.CipRSPattern)) (by
    classical
    intro cfg₁ cfg₂ h
    rcases (MulAction.mem_orbit_iff).1 ((MulAction.orbitRel_apply).1 h) with ⟨e, rfl⟩
    refine (MulAction.orbitRel_apply).2 ?_
    refine (MulAction.mem_orbit_iff).2 ?_
    refine ⟨e, ?_⟩
    ext c
    change m.smulCipRSPattern e (⟨m.cipConfigurationRS cfg₂⟩ : m.CipRSPattern) c =
      (⟨m.cipConfigurationRS (e • cfg₂)⟩ : m.CipRSPattern) c
    have hsign :
        m.cipConfigurationSign (e • cfg₂) c = m.cipConfigurationSign cfg₂ ((m.centerPerm e)⁻¹ c) :=
      m.cipConfigurationSign_smul_of_stereogenicByCIPAt (hst := hst) (e := e) (cfg := cfg₂) (c := c)
    simp [MultiCenterMolecule.smulCipRSPattern, MultiCenterMolecule.cipConfigurationRS,
      MultiCenterMolecule.rsPatternOfSignPattern, hsign])

/-- `cipConfigurationRSCycleCut` descends to the configuration orbit quotient, assuming every
distinguished center is cycle-cut CIP-stereogenic. -/
noncomputable def cipConfigurationRSCycleCutQ (m : MultiCenterMolecule V)
    (hst : ∀ c : m.Center, m.StereogenicByCIPCycleCutAt c) :
    m.ConfigurationQ → m.CipRSPatternQ :=
  Quotient.map' (fun cfg => (⟨m.cipConfigurationRSCycleCut cfg⟩ : m.CipRSPattern)) (by
    classical
    intro cfg₁ cfg₂ h
    rcases (MulAction.mem_orbit_iff).1 ((MulAction.orbitRel_apply).1 h) with ⟨e, rfl⟩
    refine (MulAction.orbitRel_apply).2 ?_
    refine (MulAction.mem_orbit_iff).2 ?_
    refine ⟨e, ?_⟩
    ext c
    change m.smulCipRSPattern e (⟨m.cipConfigurationRSCycleCut cfg₂⟩ : m.CipRSPattern) c =
      (⟨m.cipConfigurationRSCycleCut (e • cfg₂)⟩ : m.CipRSPattern) c
    have hsign :
        m.cipConfigurationSignCycleCut (e • cfg₂) c =
          m.cipConfigurationSignCycleCut cfg₂ ((m.centerPerm e)⁻¹ c) :=
      m.cipConfigurationSignCycleCut_smul_of_stereogenicByCIPCycleCutAt
        (hst := hst) (e := e) (cfg := cfg₂) (c := c)
    simp [MultiCenterMolecule.smulCipRSPattern, MultiCenterMolecule.cipConfigurationRSCycleCut,
      MultiCenterMolecule.rsPatternOfSignPattern, hsign])

/-- Descriptor-facing quotient classifier, currently backed by cycle-cut CIP. -/
abbrev cipConfigurationRSDescriptorQ (m : MultiCenterMolecule V)
    (hst : ∀ c : m.Center, m.StereogenicByCIPDescriptorAt c) :
    m.ConfigurationQ → m.CipRSPatternQ :=
  m.cipConfigurationRSCycleCutQ hst

theorem cipConfigurationRSQ_eq_cipConfigurationRSCycleCutQ_of_allCentersRawCycleCutKeyAgreement
    (m : MultiCenterMolecule V) (h : m.AllCentersRawCycleCutKeyAgreement)
    (hst : ∀ c : m.Center, m.StereogenicByCIPAt c) :
    m.cipConfigurationRSQ hst =
      m.cipConfigurationRSCycleCutQ
        (fun c =>
          (m.stereogenicByCIPAt_iff_stereogenicByCIPCycleCutAt_of_rawCycleCutKeyAgreementAt
            c (h c)).1 (hst c)) := by
  funext q
  refine Quotient.inductionOn q ?_
  intro cfg
  change
    (Quotient.mk'' (⟨m.cipConfigurationRS cfg⟩ : m.CipRSPattern) : m.CipRSPatternQ) =
      Quotient.mk'' (⟨m.cipConfigurationRSCycleCut cfg⟩ : m.CipRSPattern)
  rw [m.cipConfigurationRS_eq_cipConfigurationRSCycleCut_of_allCentersRawCycleCutKeyAgreement h cfg]

theorem cipConfigurationRSQ_eq_cipConfigurationRSCycleCutQ_of_treeLike
    (m : MultiCenterMolecule V) (htree : m.mol.TreeLike)
    (hst : ∀ c : m.Center, m.StereogenicByCIPAt c) :
    m.cipConfigurationRSQ hst =
      m.cipConfigurationRSCycleCutQ
        (fun c => (m.stereogenicByCIPAt_iff_stereogenicByCIPCycleCutAt_of_treeLike htree c).1
          (hst c)) :=
  m.cipConfigurationRSQ_eq_cipConfigurationRSCycleCutQ_of_allCentersRawCycleCutKeyAgreement
    (m.allCentersRawCycleCutKeyAgreement_of_treeLike htree) hst

theorem cipConfigurationRSQ_eq_cipConfigurationRSDescriptorQ_of_treeLike
    (m : MultiCenterMolecule V) (htree : m.mol.TreeLike)
    (hst : ∀ c : m.Center, m.StereogenicByCIPAt c) :
    m.cipConfigurationRSQ hst =
      m.cipConfigurationRSDescriptorQ
        (fun c => (m.stereogenicByCIPAt_iff_stereogenicByCIPCycleCutAt_of_treeLike htree c).1
          (hst c)) :=
  m.cipConfigurationRSQ_eq_cipConfigurationRSCycleCutQ_of_treeLike htree hst

/-! ### Achiral/chiral criteria (CIP `R/S` patterns) -/

/-- A CIP `R/S` pattern is *achiral by symmetry* when some molecular automorphism carries it to its
mirror (swap every `R` and `S`). -/
def AchiralCipRSPatternBySymmetry (m : MultiCenterMolecule V) (s : m.CipRSPattern) : Prop :=
  ∃ e : m.Aut, e • s = -s

/-- A CIP `R/S` pattern is *chiral by symmetry* when no molecular automorphism carries it to its
mirror. -/
def ChiralCipRSPatternBySymmetry (m : MultiCenterMolecule V) (s : m.CipRSPattern) : Prop :=
  ∀ e : m.Aut, e • s ≠ -s

theorem achiralCipRSPatternBySymmetry_iff_quotient_eq (m : MultiCenterMolecule V) (s : m.CipRSPattern) :
    m.AchiralCipRSPatternBySymmetry s ↔ (Quotient.mk'' s : m.CipRSPatternQ) = Quotient.mk'' (-s) := by
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
    have hs : MulAction.orbitRel m.Aut m.CipRSPattern s (-s) := Quotient.exact h
    rcases (MulAction.mem_orbit_iff).1 ((MulAction.orbitRel_apply).1 hs) with ⟨e, he⟩
    refine ⟨e⁻¹, ?_⟩
    have h' := congrArg (fun t => (e⁻¹ : m.Aut) • t) he
    have : (-s) = (e⁻¹ : m.Aut) • s := by
      simpa [smul_smul] using h'
    simpa using this.symm

theorem chiralCipRSPatternBySymmetry_iff_quotient_ne (m : MultiCenterMolecule V) (s : m.CipRSPattern) :
    m.ChiralCipRSPatternBySymmetry s ↔ (Quotient.mk'' s : m.CipRSPatternQ) ≠ Quotient.mk'' (-s) := by
  constructor
  · intro h hs
    have : m.AchiralCipRSPatternBySymmetry s :=
      (m.achiralCipRSPatternBySymmetry_iff_quotient_eq (s := s)).2 hs
    rcases this with ⟨e, he⟩
    exact h e he
  · intro h e he
    have hs : (Quotient.mk'' s : m.CipRSPatternQ) = Quotient.mk'' (-s) :=
      (m.achiralCipRSPatternBySymmetry_iff_quotient_eq (s := s)).1 ⟨e, he⟩
    exact h hs

end MultiCenterMolecule

end
end OneCenter
end TetraStereo
