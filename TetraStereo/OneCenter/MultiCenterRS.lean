import TetraStereo.OneCenter.MultiCenterCIP
import TetraStereo.OneCenter.RS

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

namespace MultiCenterMolecule

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- An `R/S` assignment on the distinguished centers of a multi-center molecule. -/
abbrev RSPattern (m : MultiCenterMolecule V) : Type _ :=
  m.Center → RS

/-- Convert a sign pattern to an `R/S` pattern by applying `RS.ofHandedness` at each center. -/
abbrev rsPatternOfSignPattern (m : MultiCenterMolecule V) (s : m.SignPattern) : m.RSPattern :=
  fun c => RS.ofHandedness (s c)

/-- The `R/S` pattern of a configuration, obtained from its local handedness sign at each center. -/
abbrev configurationRS (m : MultiCenterMolecule V) (cfg : m.Configuration) : m.RSPattern :=
  m.rsPatternOfSignPattern (m.configurationSign cfg)

/-- The raw `R/S` pattern of a configuration after CIP normalization.

This is deterministic even if a distinguished center has tied CIP keys.  Prefer
`cipConfigurationRSOfResolved` or `cipConfigurationRS?` for descriptor-level statements. -/
abbrev cipConfigurationRS (m : MultiCenterMolecule V) (cfg : m.Configuration) : m.RSPattern :=
  m.rsPatternOfSignPattern (m.cipConfigurationSign cfg)

/-- The raw `R/S` pattern of a configuration after cycle-cut CIP normalization. -/
abbrev cipConfigurationRSCycleCut (m : MultiCenterMolecule V)
    (cfg : m.Configuration) : m.RSPattern :=
  m.rsPatternOfSignPattern (m.cipConfigurationSignCycleCut cfg)

/-- The CIP-normalized `R/S` pattern with explicit evidence that every center is CIP-resolved. -/
abbrev cipConfigurationRSOfResolved (m : MultiCenterMolecule V) (_ : m.ResolvedAllCIP)
    (cfg : m.Configuration) : m.RSPattern :=
  m.cipConfigurationRS cfg

/-- The cycle-cut CIP-normalized `R/S` pattern with explicit evidence that every center is
cycle-cut CIP-resolved. -/
abbrev cipConfigurationRSCycleCutOfResolved
    (m : MultiCenterMolecule V) (_ : m.ResolvedAllCIPCycleCut)
    (cfg : m.Configuration) : m.RSPattern :=
  m.cipConfigurationRSCycleCut cfg

/-- Safe CIP-normalized `R/S`: returns `none` unless every distinguished center is CIP-resolved. -/
noncomputable def cipConfigurationRS? (m : MultiCenterMolecule V) (cfg : m.Configuration) :
    Option m.RSPattern :=
  by
    classical
    exact
      if h : m.AllCentersResolvedByCIP then
        some (m.cipConfigurationRSOfResolved ⟨h⟩ cfg)
      else
        none

/-- Safe cycle-cut CIP-normalized `R/S`: returns `none` unless every distinguished center is
cycle-cut CIP-resolved. -/
noncomputable def cipConfigurationRSCycleCut? (m : MultiCenterMolecule V)
    (cfg : m.Configuration) : Option m.RSPattern :=
  by
    classical
    exact
      if h : m.AllCentersResolvedByCIPCycleCut then
        some (m.cipConfigurationRSCycleCutOfResolved ⟨h⟩ cfg)
      else
        none

theorem cipConfigurationRS?_eq_some_of_allCentersResolvedByCIP
    (m : MultiCenterMolecule V) (h : m.AllCentersResolvedByCIP) (cfg : m.Configuration) :
    m.cipConfigurationRS? cfg = some (m.cipConfigurationRS cfg) := by
  classical
  simp [cipConfigurationRS?, h]

theorem cipConfigurationRSCycleCut?_eq_some_of_allCentersResolvedByCIPCycleCut
    (m : MultiCenterMolecule V) (h : m.AllCentersResolvedByCIPCycleCut)
    (cfg : m.Configuration) :
    m.cipConfigurationRSCycleCut? cfg = some (m.cipConfigurationRSCycleCut cfg) := by
  classical
  simp [cipConfigurationRSCycleCut?, h]

theorem cipConfigurationRS?_eq_none_of_not_allCentersResolvedByCIP
    (m : MultiCenterMolecule V) (h : ¬ m.AllCentersResolvedByCIP) (cfg : m.Configuration) :
    m.cipConfigurationRS? cfg = none := by
  classical
  change
    (if h' : m.AllCentersResolvedByCIP then
      some (m.cipConfigurationRSOfResolved ⟨h'⟩ cfg)
    else
      none) = none
  rw [dif_neg h]

theorem cipConfigurationRSCycleCut?_eq_none_of_not_allCentersResolvedByCIPCycleCut
    (m : MultiCenterMolecule V) (h : ¬ m.AllCentersResolvedByCIPCycleCut)
    (cfg : m.Configuration) :
    m.cipConfigurationRSCycleCut? cfg = none := by
  classical
  change
    (if h' : m.AllCentersResolvedByCIPCycleCut then
      some (m.cipConfigurationRSCycleCutOfResolved ⟨h'⟩ cfg)
    else
      none) = none
  rw [dif_neg h]

/-! ### Preferred descriptor-facing aliases -/

/-- Descriptor-facing CIP-normalized `R/S` pattern. -/
abbrev cipConfigurationRSDescriptor (m : MultiCenterMolecule V)
    (cfg : m.Configuration) : m.RSPattern :=
  m.cipConfigurationRSCycleCut cfg

/-- Descriptor-facing CIP-normalized `R/S` pattern with an all-centers-resolved certificate. -/
abbrev cipConfigurationRSDescriptorOfResolved
    (m : MultiCenterMolecule V) (h : m.ResolvedAllCIPDescriptor)
    (cfg : m.Configuration) : m.RSPattern :=
  m.cipConfigurationRSCycleCutOfResolved h cfg

/-- Safe descriptor-facing CIP-normalized `R/S` pattern. -/
abbrev cipConfigurationRSDescriptor? (m : MultiCenterMolecule V)
    (cfg : m.Configuration) : Option m.RSPattern :=
  m.cipConfigurationRSCycleCut? cfg

theorem cipConfigurationRSDescriptor?_eq_some_of_allCentersResolvedByCIPDescriptor
    (m : MultiCenterMolecule V) (h : m.AllCentersResolvedByCIPDescriptor)
    (cfg : m.Configuration) :
    m.cipConfigurationRSDescriptor? cfg = some (m.cipConfigurationRSDescriptor cfg) := by
  exact m.cipConfigurationRSCycleCut?_eq_some_of_allCentersResolvedByCIPCycleCut h cfg

theorem cipConfigurationRS_eq_cipConfigurationRSCycleCut_of_allCentersRawCycleCutKeyAgreement
    (m : MultiCenterMolecule V) (h : m.AllCentersRawCycleCutKeyAgreement)
    (cfg : m.Configuration) :
    m.cipConfigurationRS cfg = m.cipConfigurationRSCycleCut cfg := by
  funext c
  simp [cipConfigurationRS, cipConfigurationRSCycleCut,
    m.cipConfigurationSign_eq_cipConfigurationSignCycleCut_of_allCentersRawCycleCutKeyAgreement h cfg]

theorem cipConfigurationRS_eq_cipConfigurationRSCycleCut_of_treeLike
    (m : MultiCenterMolecule V) (htree : m.mol.TreeLike)
    (cfg : m.Configuration) :
    m.cipConfigurationRS cfg = m.cipConfigurationRSCycleCut cfg :=
  m.cipConfigurationRS_eq_cipConfigurationRSCycleCut_of_allCentersRawCycleCutKeyAgreement
    (m.allCentersRawCycleCutKeyAgreement_of_treeLike htree) cfg

theorem cipConfigurationRS?_eq_cipConfigurationRSCycleCut?_of_allCentersRawCycleCutKeyAgreement
    (m : MultiCenterMolecule V) (h : m.AllCentersRawCycleCutKeyAgreement)
    (cfg : m.Configuration) :
    m.cipConfigurationRS? cfg = m.cipConfigurationRSCycleCut? cfg := by
  classical
  have hresolved :=
    m.allCentersResolvedByCIP_iff_allCentersResolvedByCIPCycleCut_of_allCentersRawCycleCutKeyAgreement h
  by_cases hr : m.AllCentersResolvedByCIP
  · have hrc : m.AllCentersResolvedByCIPCycleCut := hresolved.1 hr
    rw [m.cipConfigurationRS?_eq_some_of_allCentersResolvedByCIP hr cfg]
    rw [m.cipConfigurationRSCycleCut?_eq_some_of_allCentersResolvedByCIPCycleCut hrc cfg]
    rw [m.cipConfigurationRS_eq_cipConfigurationRSCycleCut_of_allCentersRawCycleCutKeyAgreement
      h cfg]
  · have hrc : ¬ m.AllCentersResolvedByCIPCycleCut := by
      intro hrc
      exact hr (hresolved.2 hrc)
    rw [m.cipConfigurationRS?_eq_none_of_not_allCentersResolvedByCIP hr cfg]
    rw [m.cipConfigurationRSCycleCut?_eq_none_of_not_allCentersResolvedByCIPCycleCut hrc cfg]

theorem cipConfigurationRS?_eq_cipConfigurationRSCycleCut?_of_treeLike
    (m : MultiCenterMolecule V) (htree : m.mol.TreeLike)
    (cfg : m.Configuration) :
    m.cipConfigurationRS? cfg = m.cipConfigurationRSCycleCut? cfg :=
  m.cipConfigurationRS?_eq_cipConfigurationRSCycleCut?_of_allCentersRawCycleCutKeyAgreement
    (m.allCentersRawCycleCutKeyAgreement_of_treeLike htree) cfg

theorem cipConfigurationRS?_eq_cipConfigurationRSDescriptor?_of_treeLike
    (m : MultiCenterMolecule V) (htree : m.mol.TreeLike)
    (cfg : m.Configuration) :
    m.cipConfigurationRS? cfg = m.cipConfigurationRSDescriptor? cfg :=
  m.cipConfigurationRS?_eq_cipConfigurationRSCycleCut?_of_treeLike htree cfg

/-- Mirror (swap `R` and `S`) in an `R/S` pattern. -/
def mirrorRSPattern (m : MultiCenterMolecule V) (rs : m.RSPattern) : m.RSPattern :=
  fun c => RS.swap (rs c)

theorem configurationRS_mirrorConfiguration (m : MultiCenterMolecule V) (cfg : m.Configuration) :
    m.configurationRS (m.mirrorConfiguration cfg) = m.mirrorRSPattern (m.configurationRS cfg) := by
  funext c
  have hh : m.configurationSign cfg c = 1 ∨ m.configurationSign cfg c = -1 := by
    simpa [MultiCenterMolecule.configurationSign] using permHandedness_eq_one_or_eq_neg_one (cfg c)
  have hmirror : m.configurationSign (m.mirrorConfiguration cfg) c = -m.configurationSign cfg c := by
    simpa using (m.configurationSign_mirrorConfiguration (cfg := cfg) (c := c))
  calc
    m.configurationRS (m.mirrorConfiguration cfg) c
        = RS.ofHandedness (m.configurationSign (m.mirrorConfiguration cfg) c) := rfl
    _ = RS.ofHandedness (-m.configurationSign cfg c) := by simp [hmirror]
    _ = RS.swap (RS.ofHandedness (m.configurationSign cfg c)) := by
          simpa using RS.ofHandedness_neg (m.configurationSign cfg c) hh
    _ = m.mirrorRSPattern (m.configurationRS cfg) c := rfl

theorem cipConfigurationRS_mirrorConfiguration (m : MultiCenterMolecule V) (cfg : m.Configuration) :
    m.cipConfigurationRS (m.mirrorConfiguration cfg) = m.mirrorRSPattern (m.cipConfigurationRS cfg) := by
  funext c
  have hh : m.cipConfigurationSign cfg c = 1 ∨ m.cipConfigurationSign cfg c = -1 := by
    simpa [MultiCenterMolecule.cipConfigurationSign, MultiCenterMolecule.cipNormalizeConfiguration,
      MultiCenterMolecule.configurationSign] using
        permHandedness_eq_one_or_eq_neg_one (cfg c * m.cipPermutationAt c)
  have hmirror : m.cipConfigurationSign (m.mirrorConfiguration cfg) c = -m.cipConfigurationSign cfg c := by
    simpa using (m.cipConfigurationSign_mirrorConfiguration (cfg := cfg) (c := c))
  calc
    m.cipConfigurationRS (m.mirrorConfiguration cfg) c
        = RS.ofHandedness (m.cipConfigurationSign (m.mirrorConfiguration cfg) c) := rfl
    _ = RS.ofHandedness (-m.cipConfigurationSign cfg c) := by simp [hmirror]
    _ = RS.swap (RS.ofHandedness (m.cipConfigurationSign cfg c)) := by
          simpa using RS.ofHandedness_neg (m.cipConfigurationSign cfg c) hh
    _ = m.mirrorRSPattern (m.cipConfigurationRS cfg) c := rfl

theorem cipConfigurationRSCycleCut_mirrorConfiguration
    (m : MultiCenterMolecule V) (cfg : m.Configuration) :
    m.cipConfigurationRSCycleCut (m.mirrorConfiguration cfg) =
      m.mirrorRSPattern (m.cipConfigurationRSCycleCut cfg) := by
  funext c
  have hh :
      m.cipConfigurationSignCycleCut cfg c = 1 ∨
        m.cipConfigurationSignCycleCut cfg c = -1 := by
    simpa [MultiCenterMolecule.cipConfigurationSignCycleCut,
      MultiCenterMolecule.cipNormalizeConfigurationCycleCut,
      MultiCenterMolecule.configurationSign] using
        permHandedness_eq_one_or_eq_neg_one (cfg c * m.cipPermutationCycleCutAt c)
  have hmirror :
      m.cipConfigurationSignCycleCut (m.mirrorConfiguration cfg) c =
        -m.cipConfigurationSignCycleCut cfg c := by
    simpa using (m.cipConfigurationSignCycleCut_mirrorConfiguration (cfg := cfg) (c := c))
  calc
    m.cipConfigurationRSCycleCut (m.mirrorConfiguration cfg) c
        = RS.ofHandedness (m.cipConfigurationSignCycleCut (m.mirrorConfiguration cfg) c) := rfl
    _ = RS.ofHandedness (-m.cipConfigurationSignCycleCut cfg c) := by simp [hmirror]
    _ = RS.swap (RS.ofHandedness (m.cipConfigurationSignCycleCut cfg c)) := by
          simpa using RS.ofHandedness_neg (m.cipConfigurationSignCycleCut cfg c) hh
    _ = m.mirrorRSPattern (m.cipConfigurationRSCycleCut cfg) c := rfl

theorem cipConfigurationRS?_mirrorConfiguration (m : MultiCenterMolecule V)
    (cfg : m.Configuration) :
    m.cipConfigurationRS? (m.mirrorConfiguration cfg) =
      (m.cipConfigurationRS? cfg).map m.mirrorRSPattern := by
  classical
  by_cases h : m.AllCentersResolvedByCIP
  · simp [cipConfigurationRS?, h, m.cipConfigurationRS_mirrorConfiguration (cfg := cfg)]
  · rw [m.cipConfigurationRS?_eq_none_of_not_allCentersResolvedByCIP h (m.mirrorConfiguration cfg)]
    rw [m.cipConfigurationRS?_eq_none_of_not_allCentersResolvedByCIP h cfg]
    rfl

theorem cipConfigurationRSCycleCut?_mirrorConfiguration
    (m : MultiCenterMolecule V) (cfg : m.Configuration) :
    m.cipConfigurationRSCycleCut? (m.mirrorConfiguration cfg) =
      (m.cipConfigurationRSCycleCut? cfg).map m.mirrorRSPattern := by
  classical
  by_cases h : m.AllCentersResolvedByCIPCycleCut
  · simp [cipConfigurationRSCycleCut?, h,
      m.cipConfigurationRSCycleCut_mirrorConfiguration (cfg := cfg)]
  · rw [m.cipConfigurationRSCycleCut?_eq_none_of_not_allCentersResolvedByCIPCycleCut h
      (m.mirrorConfiguration cfg)]
    rw [m.cipConfigurationRSCycleCut?_eq_none_of_not_allCentersResolvedByCIPCycleCut h cfg]
    rfl

end MultiCenterMolecule

end
end OneCenter
end TetraStereo
