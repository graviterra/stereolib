import TetraStereo.OneCenter.MultiCenterCIPRSPatternQuotient

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

/-- The three chemistry-facing outcomes for comparing two CIP `R/S` classes. -/
inductive CipRSClassRelation : Type where
  | same
  | enantiomeric
  | diastereomeric
  deriving DecidableEq, Repr

/-- The two descriptor-level chirality outcomes for one CIP `R/S` configuration. -/
inductive CipRSChirality : Type where
  | meso
  | chiral
  deriving DecidableEq, Repr

namespace MultiCenterMolecule

variable {V : Type*} [Fintype V] [DecidableEq V]

/-!
  Chemistry-facing relations for CIP-normalized multi-center `R/S` patterns.

  These definitions sit one layer above the orbit quotient: two patterns are compared after
  quotienting by molecular automorphisms, and mirror images are represented by pointwise `R/S`
  swap.
-/

/-- Two CIP `R/S` patterns represent the same symmetry class. -/
def SameCipRSPatternClass (m : MultiCenterMolecule V) (s t : m.CipRSPattern) : Prop :=
  (Quotient.mk'' s : m.CipRSPatternQ) = Quotient.mk'' t

/-- Two CIP `R/S` patterns are mirror-related after quotienting by molecular symmetries. -/
def MirrorCipRSPatternClass (m : MultiCenterMolecule V) (s t : m.CipRSPattern) : Prop :=
  m.SameCipRSPatternClass (-s) t

/-- Two CIP `R/S` patterns are enantiomeric when they are distinct symmetry classes but
mirror-related. -/
def EnantiomericCipRSPatternsBySymmetry (m : MultiCenterMolecule V) (s t : m.CipRSPattern) :
    Prop :=
  m.MirrorCipRSPatternClass s t ∧ ¬ m.SameCipRSPatternClass s t

/-- Two CIP `R/S` patterns are diastereomeric when they are neither the same class nor
mirror-related. -/
def DiastereomericCipRSPatternsBySymmetry (m : MultiCenterMolecule V) (s t : m.CipRSPattern) :
    Prop :=
  ¬ m.SameCipRSPatternClass s t ∧ ¬ m.MirrorCipRSPatternClass s t

/-- Interpret a concrete relation outcome as a proposition about two CIP `R/S` pattern classes. -/
def CipRSPatternClassificationHolds (m : MultiCenterMolecule V)
    (s t : m.CipRSPattern) : CipRSClassRelation → Prop
  | .same => m.SameCipRSPatternClass s t
  | .enantiomeric => m.EnantiomericCipRSPatternsBySymmetry s t
  | .diastereomeric => m.DiastereomericCipRSPatternsBySymmetry s t

/-- A concrete, proof-audited classifier for two CIP `R/S` pattern classes. -/
noncomputable def classifyCipRSPatternClass
    (m : MultiCenterMolecule V) (s t : m.CipRSPattern) : CipRSClassRelation :=
  by
    classical
    exact
      if m.SameCipRSPatternClass s t then
        .same
      else if m.MirrorCipRSPatternClass s t then
        .enantiomeric
      else
        .diastereomeric

theorem classifyCipRSPatternClass_sound
    (m : MultiCenterMolecule V) (s t : m.CipRSPattern) :
    m.CipRSPatternClassificationHolds s t (m.classifyCipRSPatternClass s t) := by
  classical
  unfold classifyCipRSPatternClass CipRSPatternClassificationHolds
  by_cases hsame : m.SameCipRSPatternClass s t
  · simp [hsame]
  · by_cases hmirror : m.MirrorCipRSPatternClass s t
    · simp [hsame, hmirror, EnantiomericCipRSPatternsBySymmetry]
    · simp [hsame, hmirror, DiastereomericCipRSPatternsBySymmetry]

theorem classifyCipRSPatternClass_self_same
    (m : MultiCenterMolecule V) (s : m.CipRSPattern) :
    m.classifyCipRSPatternClass s s = CipRSClassRelation.same := by
  classical
  simp [classifyCipRSPatternClass, SameCipRSPatternClass]

/-- A meso CIP `R/S` pattern is an achiral pattern witnessed by a molecular symmetry. -/
abbrev MesoCipRSPatternBySymmetry (m : MultiCenterMolecule V) (s : m.CipRSPattern) : Prop :=
  m.AchiralCipRSPatternBySymmetry s

theorem mesoCipRSPatternBySymmetry_iff_same_mirror (m : MultiCenterMolecule V)
    (s : m.CipRSPattern) :
    m.MesoCipRSPatternBySymmetry s ↔ m.SameCipRSPatternClass s (-s) := by
  exact m.achiralCipRSPatternBySymmetry_iff_quotient_eq (s := s)

theorem enantiomeric_self_mirror_iff_chiral (m : MultiCenterMolecule V) (s : m.CipRSPattern) :
    m.EnantiomericCipRSPatternsBySymmetry s (-s) ↔ m.ChiralCipRSPatternBySymmetry s := by
  constructor
  · intro h
    exact (m.chiralCipRSPatternBySymmetry_iff_quotient_ne (s := s)).2 h.2
  · intro h
    constructor
    · rfl
    · exact (m.chiralCipRSPatternBySymmetry_iff_quotient_ne (s := s)).1 h

theorem mesoCipRSPatternBySymmetry_iff_not_chiral
    (m : MultiCenterMolecule V) (s : m.CipRSPattern) :
    m.MesoCipRSPatternBySymmetry s ↔ ¬ m.ChiralCipRSPatternBySymmetry s := by
  classical
  constructor
  · rintro ⟨e, he⟩ hchiral
    exact hchiral e he
  · intro hnotChiral
    by_contra hnotMeso
    apply hnotChiral
    intro e he
    exact hnotMeso ⟨e, he⟩

theorem chiralCipRSPatternBySymmetry_iff_not_meso
    (m : MultiCenterMolecule V) (s : m.CipRSPattern) :
    m.ChiralCipRSPatternBySymmetry s ↔ ¬ m.MesoCipRSPatternBySymmetry s := by
  classical
  rw [m.mesoCipRSPatternBySymmetry_iff_not_chiral (s := s), not_not]

theorem classifyCipRSPatternClass_self_mirror_same_of_meso
    (m : MultiCenterMolecule V) {s : m.CipRSPattern}
    (h : m.MesoCipRSPatternBySymmetry s) :
    m.classifyCipRSPatternClass s (-s) = CipRSClassRelation.same := by
  classical
  have hsame : m.SameCipRSPatternClass s (-s) :=
    (m.mesoCipRSPatternBySymmetry_iff_same_mirror (s := s)).1 h
  simp [classifyCipRSPatternClass, hsame]

theorem classifyCipRSPatternClass_self_mirror_enantiomeric_of_chiral
    (m : MultiCenterMolecule V) {s : m.CipRSPattern}
    (h : m.ChiralCipRSPatternBySymmetry s) :
    m.classifyCipRSPatternClass s (-s) = CipRSClassRelation.enantiomeric := by
  classical
  have hsame : ¬ m.SameCipRSPatternClass s (-s) :=
    (m.chiralCipRSPatternBySymmetry_iff_quotient_ne (s := s)).1 h
  have hmirror : m.MirrorCipRSPatternClass s (-s) := by
    rfl
  simp [classifyCipRSPatternClass, hsame, hmirror]

theorem cipRSPattern_not_enantiomeric_of_same
    (m : MultiCenterMolecule V) {s t : m.CipRSPattern}
    (h : m.SameCipRSPatternClass s t) :
    ¬ m.EnantiomericCipRSPatternsBySymmetry s t := by
  intro henant
  exact henant.2 h

theorem cipRSPattern_not_diastereomeric_of_same
    (m : MultiCenterMolecule V) {s t : m.CipRSPattern}
    (h : m.SameCipRSPatternClass s t) :
    ¬ m.DiastereomericCipRSPatternsBySymmetry s t := by
  intro hdias
  exact hdias.1 h

theorem cipRSPattern_not_diastereomeric_of_enantiomeric
    (m : MultiCenterMolecule V) {s t : m.CipRSPattern}
    (h : m.EnantiomericCipRSPatternsBySymmetry s t) :
    ¬ m.DiastereomericCipRSPatternsBySymmetry s t := by
  intro hdias
  exact hdias.2 h.1

theorem cipRSPattern_enantiomeric_or_diastereomeric_iff_not_same
    (m : MultiCenterMolecule V) (s t : m.CipRSPattern) :
    m.EnantiomericCipRSPatternsBySymmetry s t ∨
        m.DiastereomericCipRSPatternsBySymmetry s t ↔
      ¬ m.SameCipRSPatternClass s t := by
  classical
  constructor
  · intro h hsame
    rcases h with henant | hdias
    · exact henant.2 hsame
    · exact hdias.1 hsame
  · intro hnotSame
    by_cases hmirror : m.MirrorCipRSPatternClass s t
    · exact Or.inl ⟨hmirror, hnotSame⟩
    · exact Or.inr ⟨hnotSame, hmirror⟩

theorem cipRSPattern_classification_exhaustive
    (m : MultiCenterMolecule V) (s t : m.CipRSPattern) :
    m.SameCipRSPatternClass s t ∨
      m.EnantiomericCipRSPatternsBySymmetry s t ∨
        m.DiastereomericCipRSPatternsBySymmetry s t := by
  classical
  by_cases hsame : m.SameCipRSPatternClass s t
  · exact Or.inl hsame
  · exact Or.inr ((m.cipRSPattern_enantiomeric_or_diastereomeric_iff_not_same s t).2 hsame)

/-- Exactly one of same-class, enantiomeric, or diastereomeric holds for a pair of CIP `R/S`
patterns. -/
def CipRSPatternClassificationExactlyOne (m : MultiCenterMolecule V)
    (s t : m.CipRSPattern) : Prop :=
  (m.SameCipRSPatternClass s t ∧
      ¬ m.EnantiomericCipRSPatternsBySymmetry s t ∧
      ¬ m.DiastereomericCipRSPatternsBySymmetry s t) ∨
    (m.EnantiomericCipRSPatternsBySymmetry s t ∧
      ¬ m.SameCipRSPatternClass s t ∧
      ¬ m.DiastereomericCipRSPatternsBySymmetry s t) ∨
    (m.DiastereomericCipRSPatternsBySymmetry s t ∧
      ¬ m.SameCipRSPatternClass s t ∧
      ¬ m.EnantiomericCipRSPatternsBySymmetry s t)

theorem cipRSPattern_classification_exactly_one
    (m : MultiCenterMolecule V) (s t : m.CipRSPattern) :
    m.CipRSPatternClassificationExactlyOne s t := by
  classical
  by_cases hsame : m.SameCipRSPatternClass s t
  · exact Or.inl
      ⟨hsame, m.cipRSPattern_not_enantiomeric_of_same hsame,
        m.cipRSPattern_not_diastereomeric_of_same hsame⟩
  · by_cases hmirror : m.MirrorCipRSPatternClass s t
    · have henant : m.EnantiomericCipRSPatternsBySymmetry s t := ⟨hmirror, hsame⟩
      exact Or.inr (Or.inl
        ⟨henant, hsame, m.cipRSPattern_not_diastereomeric_of_enantiomeric henant⟩)
    · have hdias : m.DiastereomericCipRSPatternsBySymmetry s t := ⟨hsame, hmirror⟩
      have hnotEnant : ¬ m.EnantiomericCipRSPatternsBySymmetry s t := by
        intro henant
        exact hmirror henant.1
      exact Or.inr (Or.inr ⟨hdias, hsame, hnotEnant⟩)

/-! ### Configuration-level CIP `R/S` relations -/

/-- The raw CIP-normalized `R/S` pattern associated to a multi-center configuration.

This inherits deterministic CIP tie-breakers.  Prefer `cipRSPatternOfConfigurationOfResolved` or
`cipRSPatternOfConfiguration?` when using the pattern as a stereochemical descriptor. -/
abbrev cipRSPatternOfConfiguration (m : MultiCenterMolecule V) (cfg : m.Configuration) :
    m.CipRSPattern :=
  ⟨m.cipConfigurationRS cfg⟩

/-- The CIP-normalized `R/S` pattern with explicit evidence that every center is CIP-resolved. -/
abbrev cipRSPatternOfConfigurationOfResolved (m : MultiCenterMolecule V)
    (h : m.ResolvedAllCIP) (cfg : m.Configuration) : m.CipRSPattern :=
  ⟨m.cipConfigurationRSOfResolved h cfg⟩

/-- The raw cycle-cut CIP-normalized `R/S` pattern associated to a multi-center configuration.

This is deterministic even if descriptor CIP priorities tie. Prefer
`cipRSPatternOfConfigurationCycleCutOfResolved`,
`cipRSPatternOfConfigurationCycleCut?`, or the descriptor-facing aliases below for
chemistry-facing statements. -/
abbrev cipRSPatternOfConfigurationCycleCut (m : MultiCenterMolecule V)
    (cfg : m.Configuration) : m.CipRSPattern :=
  ⟨m.cipConfigurationRSCycleCut cfg⟩

/-- The cycle-cut CIP-normalized `R/S` pattern with explicit evidence that every center is
cycle-cut CIP-resolved. -/
abbrev cipRSPatternOfConfigurationCycleCutOfResolved
    (m : MultiCenterMolecule V) (h : m.ResolvedAllCIPCycleCut)
    (cfg : m.Configuration) : m.CipRSPattern :=
  ⟨m.cipConfigurationRSCycleCutOfResolved h cfg⟩

/-- Safe CIP-normalized `R/S` pattern: returns `none` unless every distinguished center is
CIP-resolved. -/
noncomputable def cipRSPatternOfConfiguration? (m : MultiCenterMolecule V)
    (cfg : m.Configuration) : Option m.CipRSPattern :=
  (m.cipConfigurationRS? cfg).map fun rs => (⟨rs⟩ : m.CipRSPattern)

/-- Safe cycle-cut CIP-normalized `R/S` pattern: returns `none` unless every distinguished center
is cycle-cut CIP-resolved. -/
noncomputable def cipRSPatternOfConfigurationCycleCut? (m : MultiCenterMolecule V)
    (cfg : m.Configuration) : Option m.CipRSPattern :=
  (m.cipConfigurationRSCycleCut? cfg).map fun rs => (⟨rs⟩ : m.CipRSPattern)

theorem cipRSPatternOfConfiguration?_eq_some_of_allCentersResolvedByCIP
    (m : MultiCenterMolecule V) (h : m.AllCentersResolvedByCIP) (cfg : m.Configuration) :
    m.cipRSPatternOfConfiguration? cfg = some (m.cipRSPatternOfConfiguration cfg) := by
  classical
  simp [cipRSPatternOfConfiguration?, m.cipConfigurationRS?_eq_some_of_allCentersResolvedByCIP h cfg,
    cipRSPatternOfConfiguration]

theorem cipRSPatternOfConfigurationCycleCut?_eq_some_of_allCentersResolvedByCIPCycleCut
    (m : MultiCenterMolecule V) (h : m.AllCentersResolvedByCIPCycleCut)
    (cfg : m.Configuration) :
    m.cipRSPatternOfConfigurationCycleCut? cfg =
      some (m.cipRSPatternOfConfigurationCycleCut cfg) := by
  classical
  simp [cipRSPatternOfConfigurationCycleCut?,
    m.cipConfigurationRSCycleCut?_eq_some_of_allCentersResolvedByCIPCycleCut h cfg]

/-! ### Preferred descriptor-facing aliases -/

/-- Descriptor-facing CIP-normalized `R/S` pattern for a configuration. -/
abbrev cipRSPatternOfConfigurationDescriptor (m : MultiCenterMolecule V)
    (cfg : m.Configuration) : m.CipRSPattern :=
  m.cipRSPatternOfConfigurationCycleCut cfg

/-- Descriptor-facing CIP-normalized `R/S` pattern with an all-centers-resolved certificate. -/
abbrev cipRSPatternOfConfigurationDescriptorOfResolved
    (m : MultiCenterMolecule V) (h : m.ResolvedAllCIPDescriptor)
    (cfg : m.Configuration) : m.CipRSPattern :=
  m.cipRSPatternOfConfigurationCycleCutOfResolved h cfg

/-- Safe descriptor-facing CIP-normalized `R/S` pattern. -/
abbrev cipRSPatternOfConfigurationDescriptor? (m : MultiCenterMolecule V)
    (cfg : m.Configuration) : Option m.CipRSPattern :=
  m.cipRSPatternOfConfigurationCycleCut? cfg

theorem cipRSPatternOfConfigurationDescriptor?_eq_some_of_allCentersResolvedByCIPDescriptor
    (m : MultiCenterMolecule V) (h : m.AllCentersResolvedByCIPDescriptor)
    (cfg : m.Configuration) :
    m.cipRSPatternOfConfigurationDescriptor? cfg =
      some (m.cipRSPatternOfConfigurationDescriptor cfg) := by
  exact m.cipRSPatternOfConfigurationCycleCut?_eq_some_of_allCentersResolvedByCIPCycleCut h cfg

theorem cipRSPatternOfConfiguration_eq_cipRSPatternOfConfigurationCycleCut_of_allCentersRawCycleCutKeyAgreement
    (m : MultiCenterMolecule V) (h : m.AllCentersRawCycleCutKeyAgreement)
    (cfg : m.Configuration) :
    m.cipRSPatternOfConfiguration cfg = m.cipRSPatternOfConfigurationCycleCut cfg := by
  ext c
  simpa [cipRSPatternOfConfiguration, cipRSPatternOfConfigurationCycleCut] using
    congrFun
      (m.cipConfigurationRS_eq_cipConfigurationRSCycleCut_of_allCentersRawCycleCutKeyAgreement h cfg) c

theorem cipRSPatternOfConfiguration_eq_cipRSPatternOfConfigurationCycleCut_of_treeLike
    (m : MultiCenterMolecule V) (htree : m.mol.TreeLike)
    (cfg : m.Configuration) :
    m.cipRSPatternOfConfiguration cfg = m.cipRSPatternOfConfigurationCycleCut cfg :=
  m.cipRSPatternOfConfiguration_eq_cipRSPatternOfConfigurationCycleCut_of_allCentersRawCycleCutKeyAgreement
    (m.allCentersRawCycleCutKeyAgreement_of_treeLike htree) cfg

theorem cipRSPatternOfConfiguration?_eq_cipRSPatternOfConfigurationCycleCut?_of_allCentersRawCycleCutKeyAgreement
    (m : MultiCenterMolecule V) (h : m.AllCentersRawCycleCutKeyAgreement)
    (cfg : m.Configuration) :
    m.cipRSPatternOfConfiguration? cfg = m.cipRSPatternOfConfigurationCycleCut? cfg := by
  simp [cipRSPatternOfConfiguration?, cipRSPatternOfConfigurationCycleCut?,
    m.cipConfigurationRS?_eq_cipConfigurationRSCycleCut?_of_allCentersRawCycleCutKeyAgreement h cfg]

theorem cipRSPatternOfConfiguration?_eq_cipRSPatternOfConfigurationCycleCut?_of_treeLike
    (m : MultiCenterMolecule V) (htree : m.mol.TreeLike)
    (cfg : m.Configuration) :
    m.cipRSPatternOfConfiguration? cfg = m.cipRSPatternOfConfigurationCycleCut? cfg :=
  m.cipRSPatternOfConfiguration?_eq_cipRSPatternOfConfigurationCycleCut?_of_allCentersRawCycleCutKeyAgreement
    (m.allCentersRawCycleCutKeyAgreement_of_treeLike htree) cfg

theorem cipRSPatternOfConfiguration?_eq_cipRSPatternOfConfigurationDescriptor?_of_treeLike
    (m : MultiCenterMolecule V) (htree : m.mol.TreeLike)
    (cfg : m.Configuration) :
    m.cipRSPatternOfConfiguration? cfg = m.cipRSPatternOfConfigurationDescriptor? cfg :=
  m.cipRSPatternOfConfiguration?_eq_cipRSPatternOfConfigurationCycleCut?_of_treeLike htree cfg

/-- Same CIP `R/S` class, with explicit resolved-CIP evidence. -/
def SameCipRSConfigurationClassOfResolved (m : MultiCenterMolecule V) (_ : m.ResolvedAllCIP)
    (cfg₁ cfg₂ : m.Configuration) : Prop :=
  m.SameCipRSPatternClass (m.cipRSPatternOfConfiguration cfg₁) (m.cipRSPatternOfConfiguration cfg₂)

/-- Mirror-related CIP `R/S` classes, with explicit resolved-CIP evidence. -/
def MirrorCipRSConfigurationClassOfResolved (m : MultiCenterMolecule V)
    (_ : m.ResolvedAllCIP) (cfg₁ cfg₂ : m.Configuration) : Prop :=
  m.MirrorCipRSPatternClass (m.cipRSPatternOfConfiguration cfg₁) (m.cipRSPatternOfConfiguration cfg₂)

/-- Two configurations have the same CIP `R/S` class when their CIP `R/S` patterns agree modulo
molecular symmetry. -/
def SameCipRSConfigurationClass (m : MultiCenterMolecule V) (cfg₁ cfg₂ : m.Configuration) :
    Prop :=
  m.SameCipRSPatternClass (m.cipRSPatternOfConfiguration cfg₁) (m.cipRSPatternOfConfiguration cfg₂)

/-- Two configurations are mirror-related at the CIP `R/S` class level. -/
def MirrorCipRSConfigurationClass (m : MultiCenterMolecule V) (cfg₁ cfg₂ : m.Configuration) :
    Prop :=
  m.MirrorCipRSPatternClass (m.cipRSPatternOfConfiguration cfg₁) (m.cipRSPatternOfConfiguration cfg₂)

/-- Two configurations have the same descriptor-facing cycle-cut CIP `R/S` class. -/
def SameCipRSConfigurationCycleCutClass
    (m : MultiCenterMolecule V) (cfg₁ cfg₂ : m.Configuration) : Prop :=
  m.SameCipRSPatternClass (m.cipRSPatternOfConfigurationCycleCut cfg₁)
    (m.cipRSPatternOfConfigurationCycleCut cfg₂)

/-- Two configurations are mirror-related at the descriptor-facing cycle-cut CIP `R/S` class
level. -/
def MirrorCipRSConfigurationCycleCutClass
    (m : MultiCenterMolecule V) (cfg₁ cfg₂ : m.Configuration) : Prop :=
  m.MirrorCipRSPatternClass (m.cipRSPatternOfConfigurationCycleCut cfg₁)
    (m.cipRSPatternOfConfigurationCycleCut cfg₂)

theorem sameCipRSConfigurationClass_iff_cycleCut_of_treeLike
    (m : MultiCenterMolecule V) (htree : m.mol.TreeLike)
    (cfg₁ cfg₂ : m.Configuration) :
    m.SameCipRSConfigurationClass cfg₁ cfg₂ ↔
      m.SameCipRSConfigurationCycleCutClass cfg₁ cfg₂ := by
  rw [SameCipRSConfigurationClass, SameCipRSConfigurationCycleCutClass,
    m.cipRSPatternOfConfiguration_eq_cipRSPatternOfConfigurationCycleCut_of_treeLike htree cfg₁,
    m.cipRSPatternOfConfiguration_eq_cipRSPatternOfConfigurationCycleCut_of_treeLike htree cfg₂]

theorem mirrorCipRSConfigurationClass_iff_cycleCut_of_treeLike
    (m : MultiCenterMolecule V) (htree : m.mol.TreeLike)
    (cfg₁ cfg₂ : m.Configuration) :
    m.MirrorCipRSConfigurationClass cfg₁ cfg₂ ↔
      m.MirrorCipRSConfigurationCycleCutClass cfg₁ cfg₂ := by
  rw [MirrorCipRSConfigurationClass, MirrorCipRSConfigurationCycleCutClass,
    m.cipRSPatternOfConfiguration_eq_cipRSPatternOfConfigurationCycleCut_of_treeLike htree cfg₁,
    m.cipRSPatternOfConfiguration_eq_cipRSPatternOfConfigurationCycleCut_of_treeLike htree cfg₂]

/-- Two configurations are enantiomeric by their CIP `R/S` classes: mirror-related but not the same
symmetry class. -/
def EnantiomericCipRSConfigurationsBySymmetry (m : MultiCenterMolecule V)
    (cfg₁ cfg₂ : m.Configuration) : Prop :=
  m.EnantiomericCipRSPatternsBySymmetry (m.cipRSPatternOfConfiguration cfg₁)
    (m.cipRSPatternOfConfiguration cfg₂)

/-- Two configurations are enantiomeric by descriptor-facing cycle-cut CIP `R/S` classes. -/
def EnantiomericCipRSConfigurationsCycleCutBySymmetry
    (m : MultiCenterMolecule V) (cfg₁ cfg₂ : m.Configuration) : Prop :=
  m.EnantiomericCipRSPatternsBySymmetry (m.cipRSPatternOfConfigurationCycleCut cfg₁)
    (m.cipRSPatternOfConfigurationCycleCut cfg₂)

/-- Two configurations are diastereomeric by their CIP `R/S` classes: neither same-class nor
mirror-related. -/
def DiastereomericCipRSConfigurationsBySymmetry (m : MultiCenterMolecule V)
    (cfg₁ cfg₂ : m.Configuration) : Prop :=
  m.DiastereomericCipRSPatternsBySymmetry (m.cipRSPatternOfConfiguration cfg₁)
    (m.cipRSPatternOfConfiguration cfg₂)

/-- Two configurations are diastereomeric by descriptor-facing cycle-cut CIP `R/S` classes. -/
def DiastereomericCipRSConfigurationsCycleCutBySymmetry
    (m : MultiCenterMolecule V) (cfg₁ cfg₂ : m.Configuration) : Prop :=
  m.DiastereomericCipRSPatternsBySymmetry (m.cipRSPatternOfConfigurationCycleCut cfg₁)
    (m.cipRSPatternOfConfigurationCycleCut cfg₂)

theorem enantiomericCipRSConfigurationsBySymmetry_iff_cycleCut_of_treeLike
    (m : MultiCenterMolecule V) (htree : m.mol.TreeLike)
    (cfg₁ cfg₂ : m.Configuration) :
    m.EnantiomericCipRSConfigurationsBySymmetry cfg₁ cfg₂ ↔
      m.EnantiomericCipRSConfigurationsCycleCutBySymmetry cfg₁ cfg₂ := by
  rw [EnantiomericCipRSConfigurationsBySymmetry,
    EnantiomericCipRSConfigurationsCycleCutBySymmetry,
    m.cipRSPatternOfConfiguration_eq_cipRSPatternOfConfigurationCycleCut_of_treeLike htree cfg₁,
    m.cipRSPatternOfConfiguration_eq_cipRSPatternOfConfigurationCycleCut_of_treeLike htree cfg₂]

theorem diastereomericCipRSConfigurationsBySymmetry_iff_cycleCut_of_treeLike
    (m : MultiCenterMolecule V) (htree : m.mol.TreeLike)
    (cfg₁ cfg₂ : m.Configuration) :
    m.DiastereomericCipRSConfigurationsBySymmetry cfg₁ cfg₂ ↔
      m.DiastereomericCipRSConfigurationsCycleCutBySymmetry cfg₁ cfg₂ := by
  rw [DiastereomericCipRSConfigurationsBySymmetry,
    DiastereomericCipRSConfigurationsCycleCutBySymmetry,
    m.cipRSPatternOfConfiguration_eq_cipRSPatternOfConfigurationCycleCut_of_treeLike htree cfg₁,
    m.cipRSPatternOfConfiguration_eq_cipRSPatternOfConfigurationCycleCut_of_treeLike htree cfg₂]

theorem cipRSConfiguration_classification_exhaustive
    (m : MultiCenterMolecule V) (cfg₁ cfg₂ : m.Configuration) :
    m.SameCipRSConfigurationClass cfg₁ cfg₂ ∨
      m.EnantiomericCipRSConfigurationsBySymmetry cfg₁ cfg₂ ∨
        m.DiastereomericCipRSConfigurationsBySymmetry cfg₁ cfg₂ := by
  simpa [SameCipRSConfigurationClass, EnantiomericCipRSConfigurationsBySymmetry,
    DiastereomericCipRSConfigurationsBySymmetry] using
    m.cipRSPattern_classification_exhaustive
      (m.cipRSPatternOfConfiguration cfg₁) (m.cipRSPatternOfConfiguration cfg₂)

theorem cipRSConfigurationCycleCut_classification_exhaustive
    (m : MultiCenterMolecule V) (cfg₁ cfg₂ : m.Configuration) :
    m.SameCipRSConfigurationCycleCutClass cfg₁ cfg₂ ∨
      m.EnantiomericCipRSConfigurationsCycleCutBySymmetry cfg₁ cfg₂ ∨
        m.DiastereomericCipRSConfigurationsCycleCutBySymmetry cfg₁ cfg₂ := by
  simpa [SameCipRSConfigurationCycleCutClass,
    EnantiomericCipRSConfigurationsCycleCutBySymmetry,
    DiastereomericCipRSConfigurationsCycleCutBySymmetry] using
    m.cipRSPattern_classification_exhaustive
      (m.cipRSPatternOfConfigurationCycleCut cfg₁)
      (m.cipRSPatternOfConfigurationCycleCut cfg₂)

theorem cipRSConfiguration_enantiomeric_or_diastereomeric_iff_not_same
    (m : MultiCenterMolecule V) (cfg₁ cfg₂ : m.Configuration) :
    m.EnantiomericCipRSConfigurationsBySymmetry cfg₁ cfg₂ ∨
        m.DiastereomericCipRSConfigurationsBySymmetry cfg₁ cfg₂ ↔
      ¬ m.SameCipRSConfigurationClass cfg₁ cfg₂ := by
  simpa [SameCipRSConfigurationClass, EnantiomericCipRSConfigurationsBySymmetry,
    DiastereomericCipRSConfigurationsBySymmetry] using
    m.cipRSPattern_enantiomeric_or_diastereomeric_iff_not_same
      (m.cipRSPatternOfConfiguration cfg₁) (m.cipRSPatternOfConfiguration cfg₂)

theorem cipRSConfigurationCycleCut_enantiomeric_or_diastereomeric_iff_not_same
    (m : MultiCenterMolecule V) (cfg₁ cfg₂ : m.Configuration) :
    m.EnantiomericCipRSConfigurationsCycleCutBySymmetry cfg₁ cfg₂ ∨
        m.DiastereomericCipRSConfigurationsCycleCutBySymmetry cfg₁ cfg₂ ↔
      ¬ m.SameCipRSConfigurationCycleCutClass cfg₁ cfg₂ := by
  simpa [SameCipRSConfigurationCycleCutClass,
    EnantiomericCipRSConfigurationsCycleCutBySymmetry,
    DiastereomericCipRSConfigurationsCycleCutBySymmetry] using
    m.cipRSPattern_enantiomeric_or_diastereomeric_iff_not_same
      (m.cipRSPatternOfConfigurationCycleCut cfg₁)
      (m.cipRSPatternOfConfigurationCycleCut cfg₂)

/-- Interpret a concrete relation outcome as a proposition about two raw CIP `R/S`
configuration classes. -/
def CipRSConfigurationClassificationHolds
    (m : MultiCenterMolecule V) (cfg₁ cfg₂ : m.Configuration) : CipRSClassRelation → Prop
  | .same => m.SameCipRSConfigurationClass cfg₁ cfg₂
  | .enantiomeric => m.EnantiomericCipRSConfigurationsBySymmetry cfg₁ cfg₂
  | .diastereomeric => m.DiastereomericCipRSConfigurationsBySymmetry cfg₁ cfg₂

/-- Interpret a concrete relation outcome as a proposition about two descriptor-facing cycle-cut
CIP `R/S` configuration classes. -/
def CipRSConfigurationCycleCutClassificationHolds
    (m : MultiCenterMolecule V) (cfg₁ cfg₂ : m.Configuration) : CipRSClassRelation → Prop
  | .same => m.SameCipRSConfigurationCycleCutClass cfg₁ cfg₂
  | .enantiomeric => m.EnantiomericCipRSConfigurationsCycleCutBySymmetry cfg₁ cfg₂
  | .diastereomeric => m.DiastereomericCipRSConfigurationsCycleCutBySymmetry cfg₁ cfg₂

/-- Concrete classifier for raw CIP `R/S` configuration classes. -/
noncomputable def classifyCipRSConfiguration
    (m : MultiCenterMolecule V) (cfg₁ cfg₂ : m.Configuration) : CipRSClassRelation :=
  m.classifyCipRSPatternClass (m.cipRSPatternOfConfiguration cfg₁)
    (m.cipRSPatternOfConfiguration cfg₂)

/-- Concrete classifier for descriptor-facing cycle-cut CIP `R/S` configuration classes. -/
noncomputable def classifyCipRSConfigurationCycleCut
    (m : MultiCenterMolecule V) (cfg₁ cfg₂ : m.Configuration) : CipRSClassRelation :=
  m.classifyCipRSPatternClass (m.cipRSPatternOfConfigurationCycleCut cfg₁)
    (m.cipRSPatternOfConfigurationCycleCut cfg₂)

theorem classifyCipRSConfiguration_sound
    (m : MultiCenterMolecule V) (cfg₁ cfg₂ : m.Configuration) :
    m.CipRSConfigurationClassificationHolds cfg₁ cfg₂
      (m.classifyCipRSConfiguration cfg₁ cfg₂) := by
  simpa [classifyCipRSConfiguration, CipRSConfigurationClassificationHolds,
    SameCipRSConfigurationClass, EnantiomericCipRSConfigurationsBySymmetry,
    DiastereomericCipRSConfigurationsBySymmetry] using
    m.classifyCipRSPatternClass_sound
      (m.cipRSPatternOfConfiguration cfg₁) (m.cipRSPatternOfConfiguration cfg₂)

theorem classifyCipRSConfigurationCycleCut_sound
    (m : MultiCenterMolecule V) (cfg₁ cfg₂ : m.Configuration) :
    m.CipRSConfigurationCycleCutClassificationHolds cfg₁ cfg₂
      (m.classifyCipRSConfigurationCycleCut cfg₁ cfg₂) := by
  simpa [classifyCipRSConfigurationCycleCut, CipRSConfigurationCycleCutClassificationHolds,
    SameCipRSConfigurationCycleCutClass,
    EnantiomericCipRSConfigurationsCycleCutBySymmetry,
    DiastereomericCipRSConfigurationsCycleCutBySymmetry] using
    m.classifyCipRSPatternClass_sound
      (m.cipRSPatternOfConfigurationCycleCut cfg₁)
      (m.cipRSPatternOfConfigurationCycleCut cfg₂)

theorem classifyCipRSConfiguration_self_same
    (m : MultiCenterMolecule V) (cfg : m.Configuration) :
    m.classifyCipRSConfiguration cfg cfg = CipRSClassRelation.same := by
  classical
  simp [classifyCipRSConfiguration, classifyCipRSPatternClass_self_same]

theorem classifyCipRSConfiguration_self_same_sound
    (m : MultiCenterMolecule V) (cfg : m.Configuration) :
    m.CipRSConfigurationClassificationHolds cfg cfg CipRSClassRelation.same := by
  have hsound := m.classifyCipRSConfiguration_sound cfg cfg
  simpa [m.classifyCipRSConfiguration_self_same cfg] using hsound

theorem classifyCipRSConfigurationCycleCut_self_same
    (m : MultiCenterMolecule V) (cfg : m.Configuration) :
    m.classifyCipRSConfigurationCycleCut cfg cfg = CipRSClassRelation.same := by
  classical
  simp [classifyCipRSConfigurationCycleCut, classifyCipRSPatternClass_self_same]

theorem classifyCipRSConfigurationCycleCut_self_same_sound
    (m : MultiCenterMolecule V) (cfg : m.Configuration) :
    m.CipRSConfigurationCycleCutClassificationHolds cfg cfg CipRSClassRelation.same := by
  have hsound := m.classifyCipRSConfigurationCycleCut_sound cfg cfg
  simpa [m.classifyCipRSConfigurationCycleCut_self_same cfg] using hsound

/-- Exactly one of same-class, enantiomeric, or diastereomeric holds for a pair of configurations
under raw CIP `R/S` classes. -/
def CipRSConfigurationClassificationExactlyOne
    (m : MultiCenterMolecule V) (cfg₁ cfg₂ : m.Configuration) : Prop :=
  (m.SameCipRSConfigurationClass cfg₁ cfg₂ ∧
      ¬ m.EnantiomericCipRSConfigurationsBySymmetry cfg₁ cfg₂ ∧
      ¬ m.DiastereomericCipRSConfigurationsBySymmetry cfg₁ cfg₂) ∨
    (m.EnantiomericCipRSConfigurationsBySymmetry cfg₁ cfg₂ ∧
      ¬ m.SameCipRSConfigurationClass cfg₁ cfg₂ ∧
      ¬ m.DiastereomericCipRSConfigurationsBySymmetry cfg₁ cfg₂) ∨
    (m.DiastereomericCipRSConfigurationsBySymmetry cfg₁ cfg₂ ∧
      ¬ m.SameCipRSConfigurationClass cfg₁ cfg₂ ∧
      ¬ m.EnantiomericCipRSConfigurationsBySymmetry cfg₁ cfg₂)

/-- Exactly one of same-class, enantiomeric, or diastereomeric holds for a pair of configurations
under descriptor-facing cycle-cut CIP `R/S` classes. -/
def CipRSConfigurationCycleCutClassificationExactlyOne
    (m : MultiCenterMolecule V) (cfg₁ cfg₂ : m.Configuration) : Prop :=
  (m.SameCipRSConfigurationCycleCutClass cfg₁ cfg₂ ∧
      ¬ m.EnantiomericCipRSConfigurationsCycleCutBySymmetry cfg₁ cfg₂ ∧
      ¬ m.DiastereomericCipRSConfigurationsCycleCutBySymmetry cfg₁ cfg₂) ∨
    (m.EnantiomericCipRSConfigurationsCycleCutBySymmetry cfg₁ cfg₂ ∧
      ¬ m.SameCipRSConfigurationCycleCutClass cfg₁ cfg₂ ∧
      ¬ m.DiastereomericCipRSConfigurationsCycleCutBySymmetry cfg₁ cfg₂) ∨
    (m.DiastereomericCipRSConfigurationsCycleCutBySymmetry cfg₁ cfg₂ ∧
      ¬ m.SameCipRSConfigurationCycleCutClass cfg₁ cfg₂ ∧
      ¬ m.EnantiomericCipRSConfigurationsCycleCutBySymmetry cfg₁ cfg₂)

theorem cipRSConfiguration_classification_exactly_one
    (m : MultiCenterMolecule V) (cfg₁ cfg₂ : m.Configuration) :
    m.CipRSConfigurationClassificationExactlyOne cfg₁ cfg₂ := by
  simpa [CipRSConfigurationClassificationExactlyOne,
    SameCipRSConfigurationClass, EnantiomericCipRSConfigurationsBySymmetry,
    DiastereomericCipRSConfigurationsBySymmetry] using
    m.cipRSPattern_classification_exactly_one
      (m.cipRSPatternOfConfiguration cfg₁) (m.cipRSPatternOfConfiguration cfg₂)

theorem cipRSConfigurationCycleCut_classification_exactly_one
    (m : MultiCenterMolecule V) (cfg₁ cfg₂ : m.Configuration) :
    m.CipRSConfigurationCycleCutClassificationExactlyOne cfg₁ cfg₂ := by
  simpa [CipRSConfigurationCycleCutClassificationExactlyOne,
    SameCipRSConfigurationCycleCutClass,
    EnantiomericCipRSConfigurationsCycleCutBySymmetry,
    DiastereomericCipRSConfigurationsCycleCutBySymmetry] using
    m.cipRSPattern_classification_exactly_one
      (m.cipRSPatternOfConfigurationCycleCut cfg₁)
      (m.cipRSPatternOfConfigurationCycleCut cfg₂)

/-- A configuration is meso at the CIP `R/S` class level when its CIP `R/S` pattern is achiral by
molecular symmetry. -/
abbrev MesoCipRSConfigurationBySymmetry (m : MultiCenterMolecule V) (cfg : m.Configuration) :
    Prop :=
  m.MesoCipRSPatternBySymmetry (m.cipRSPatternOfConfiguration cfg)

/-- A configuration is meso at the descriptor-facing cycle-cut CIP `R/S` class level. -/
abbrev MesoCipRSConfigurationCycleCutBySymmetry
    (m : MultiCenterMolecule V) (cfg : m.Configuration) : Prop :=
  m.MesoCipRSPatternBySymmetry (m.cipRSPatternOfConfigurationCycleCut cfg)

/-- A configuration is chiral at the CIP `R/S` class level when its CIP `R/S` pattern is chiral by
molecular symmetry. -/
abbrev ChiralCipRSConfigurationBySymmetry (m : MultiCenterMolecule V) (cfg : m.Configuration) :
    Prop :=
  m.ChiralCipRSPatternBySymmetry (m.cipRSPatternOfConfiguration cfg)

/-- A configuration is chiral at the descriptor-facing cycle-cut CIP `R/S` class level. -/
abbrev ChiralCipRSConfigurationCycleCutBySymmetry
    (m : MultiCenterMolecule V) (cfg : m.Configuration) : Prop :=
  m.ChiralCipRSPatternBySymmetry (m.cipRSPatternOfConfigurationCycleCut cfg)

theorem mesoCipRSConfigurationBySymmetry_iff_cycleCut_of_treeLike
    (m : MultiCenterMolecule V) (htree : m.mol.TreeLike)
    (cfg : m.Configuration) :
    m.MesoCipRSConfigurationBySymmetry cfg ↔
      m.MesoCipRSConfigurationCycleCutBySymmetry cfg := by
  rw [MesoCipRSConfigurationBySymmetry, MesoCipRSConfigurationCycleCutBySymmetry,
    m.cipRSPatternOfConfiguration_eq_cipRSPatternOfConfigurationCycleCut_of_treeLike htree cfg]

theorem chiralCipRSConfigurationBySymmetry_iff_cycleCut_of_treeLike
    (m : MultiCenterMolecule V) (htree : m.mol.TreeLike)
    (cfg : m.Configuration) :
    m.ChiralCipRSConfigurationBySymmetry cfg ↔
      m.ChiralCipRSConfigurationCycleCutBySymmetry cfg := by
  rw [ChiralCipRSConfigurationBySymmetry, ChiralCipRSConfigurationCycleCutBySymmetry,
    m.cipRSPatternOfConfiguration_eq_cipRSPatternOfConfigurationCycleCut_of_treeLike htree cfg]

theorem mesoCipRSConfigurationBySymmetry_iff_not_chiral
    (m : MultiCenterMolecule V) (cfg : m.Configuration) :
    m.MesoCipRSConfigurationBySymmetry cfg ↔
      ¬ m.ChiralCipRSConfigurationBySymmetry cfg := by
  simpa [MesoCipRSConfigurationBySymmetry, ChiralCipRSConfigurationBySymmetry] using
    m.mesoCipRSPatternBySymmetry_iff_not_chiral
      (s := m.cipRSPatternOfConfiguration cfg)

theorem chiralCipRSConfigurationBySymmetry_iff_not_meso
    (m : MultiCenterMolecule V) (cfg : m.Configuration) :
    m.ChiralCipRSConfigurationBySymmetry cfg ↔
      ¬ m.MesoCipRSConfigurationBySymmetry cfg := by
  simpa [MesoCipRSConfigurationBySymmetry, ChiralCipRSConfigurationBySymmetry] using
    m.chiralCipRSPatternBySymmetry_iff_not_meso
      (s := m.cipRSPatternOfConfiguration cfg)

theorem mesoCipRSConfigurationCycleCutBySymmetry_iff_not_chiral
    (m : MultiCenterMolecule V) (cfg : m.Configuration) :
    m.MesoCipRSConfigurationCycleCutBySymmetry cfg ↔
      ¬ m.ChiralCipRSConfigurationCycleCutBySymmetry cfg := by
  simpa [MesoCipRSConfigurationCycleCutBySymmetry,
    ChiralCipRSConfigurationCycleCutBySymmetry] using
    m.mesoCipRSPatternBySymmetry_iff_not_chiral
      (s := m.cipRSPatternOfConfigurationCycleCut cfg)

theorem chiralCipRSConfigurationCycleCutBySymmetry_iff_not_meso
    (m : MultiCenterMolecule V) (cfg : m.Configuration) :
    m.ChiralCipRSConfigurationCycleCutBySymmetry cfg ↔
      ¬ m.MesoCipRSConfigurationCycleCutBySymmetry cfg := by
  simpa [MesoCipRSConfigurationCycleCutBySymmetry,
    ChiralCipRSConfigurationCycleCutBySymmetry] using
    m.chiralCipRSPatternBySymmetry_iff_not_meso
      (s := m.cipRSPatternOfConfigurationCycleCut cfg)

theorem cipRSPatternOfConfiguration_mirrorConfiguration (m : MultiCenterMolecule V)
    (cfg : m.Configuration) :
    m.cipRSPatternOfConfiguration (m.mirrorConfiguration cfg) = -m.cipRSPatternOfConfiguration cfg := by
  ext c
  simpa [cipRSPatternOfConfiguration] using
    congrFun (m.cipConfigurationRS_mirrorConfiguration (cfg := cfg)) c

theorem cipRSPatternOfConfigurationCycleCut_mirrorConfiguration
    (m : MultiCenterMolecule V) (cfg : m.Configuration) :
    m.cipRSPatternOfConfigurationCycleCut (m.mirrorConfiguration cfg) =
      -m.cipRSPatternOfConfigurationCycleCut cfg := by
  ext c
  simpa [cipRSPatternOfConfigurationCycleCut] using
    congrFun (m.cipConfigurationRSCycleCut_mirrorConfiguration (cfg := cfg)) c

theorem cipRSPatternOfConfiguration?_mirrorConfiguration (m : MultiCenterMolecule V)
    (cfg : m.Configuration) :
    m.cipRSPatternOfConfiguration? (m.mirrorConfiguration cfg) =
      (m.cipRSPatternOfConfiguration? cfg).map Neg.neg := by
  classical
  by_cases h : m.AllCentersResolvedByCIP
  · simp [cipRSPatternOfConfiguration?,
      m.cipConfigurationRS?_eq_some_of_allCentersResolvedByCIP h cfg,
      m.cipConfigurationRS?_eq_some_of_allCentersResolvedByCIP h (m.mirrorConfiguration cfg),
      cipRSPatternOfConfiguration_mirrorConfiguration]
  · simp [cipRSPatternOfConfiguration?, m.cipConfigurationRS?_eq_none_of_not_allCentersResolvedByCIP h]

theorem cipRSPatternOfConfigurationCycleCut?_mirrorConfiguration
    (m : MultiCenterMolecule V) (cfg : m.Configuration) :
    m.cipRSPatternOfConfigurationCycleCut? (m.mirrorConfiguration cfg) =
      (m.cipRSPatternOfConfigurationCycleCut? cfg).map Neg.neg := by
  classical
  by_cases h : m.AllCentersResolvedByCIPCycleCut
  · have hneg :
        (⟨m.mirrorRSPattern (m.cipConfigurationRSCycleCut cfg)⟩ : m.CipRSPattern) =
          -(⟨m.cipConfigurationRSCycleCut cfg⟩ : m.CipRSPattern) := rfl
    simp [cipRSPatternOfConfigurationCycleCut?,
      m.cipConfigurationRSCycleCut?_eq_some_of_allCentersResolvedByCIPCycleCut h cfg,
      m.cipConfigurationRSCycleCut?_eq_some_of_allCentersResolvedByCIPCycleCut h
        (m.mirrorConfiguration cfg),
      m.cipConfigurationRSCycleCut_mirrorConfiguration (cfg := cfg), hneg]
  · simp [cipRSPatternOfConfigurationCycleCut?,
      m.cipConfigurationRSCycleCut?_eq_none_of_not_allCentersResolvedByCIPCycleCut h]

theorem cipRSPatternOfConfiguration_smul_eq_of_stereogenicByCIPAt (m : MultiCenterMolecule V)
    (hst : ∀ c : m.Center, m.StereogenicByCIPAt c) (e : m.Aut) (cfg : m.Configuration) :
    e • m.cipRSPatternOfConfiguration cfg = m.cipRSPatternOfConfiguration (e • cfg) := by
  ext c
  have hsign :
      m.cipConfigurationSign (e • cfg) c = m.cipConfigurationSign cfg ((m.centerPerm e)⁻¹ c) :=
    m.cipConfigurationSign_smul_of_stereogenicByCIPAt (hst := hst) (e := e) (cfg := cfg) (c := c)
  change m.smulCipRSPattern e (m.cipRSPatternOfConfiguration cfg) c =
    m.cipRSPatternOfConfiguration (e • cfg) c
  simp [smulCipRSPattern, cipConfigurationRS, rsPatternOfSignPattern, hsign]

theorem cipRSPatternOfConfigurationCycleCut_smul_eq_of_stereogenicByCIPCycleCutAt
    (m : MultiCenterMolecule V) (hst : ∀ c : m.Center, m.StereogenicByCIPCycleCutAt c)
    (e : m.Aut) (cfg : m.Configuration) :
    e • m.cipRSPatternOfConfigurationCycleCut cfg =
      m.cipRSPatternOfConfigurationCycleCut (e • cfg) := by
  ext c
  have hsign :
      m.cipConfigurationSignCycleCut (e • cfg) c =
        m.cipConfigurationSignCycleCut cfg ((m.centerPerm e)⁻¹ c) :=
    m.cipConfigurationSignCycleCut_smul_of_stereogenicByCIPCycleCutAt
      (hst := hst) (e := e) (cfg := cfg) (c := c)
  change m.smulCipRSPattern e (m.cipRSPatternOfConfigurationCycleCut cfg) c =
    m.cipRSPatternOfConfigurationCycleCut (e • cfg) c
  simp [smulCipRSPattern, cipConfigurationRSCycleCut, rsPatternOfSignPattern, hsign]

theorem mesoCipRSConfigurationBySymmetry_iff_exists_smul_eq_mirror
    (m : MultiCenterMolecule V) (hst : ∀ c : m.Center, m.StereogenicByCIPAt c)
    (cfg : m.Configuration) :
    m.MesoCipRSConfigurationBySymmetry cfg ↔
      ∃ e : m.Aut,
        m.cipRSPatternOfConfiguration (e • cfg) =
          m.cipRSPatternOfConfiguration (m.mirrorConfiguration cfg) := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    calc
      m.cipRSPatternOfConfiguration (e • cfg)
          = e • m.cipRSPatternOfConfiguration cfg := by
              exact (m.cipRSPatternOfConfiguration_smul_eq_of_stereogenicByCIPAt
                (hst := hst) (e := e) (cfg := cfg)).symm
      _ = -m.cipRSPatternOfConfiguration cfg := he
      _ = m.cipRSPatternOfConfiguration (m.mirrorConfiguration cfg) := by
            exact (m.cipRSPatternOfConfiguration_mirrorConfiguration (cfg := cfg)).symm
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    calc
      e • m.cipRSPatternOfConfiguration cfg
          = m.cipRSPatternOfConfiguration (e • cfg) := by
              exact m.cipRSPatternOfConfiguration_smul_eq_of_stereogenicByCIPAt
                (hst := hst) (e := e) (cfg := cfg)
      _ = m.cipRSPatternOfConfiguration (m.mirrorConfiguration cfg) := he
      _ = -m.cipRSPatternOfConfiguration cfg := by
            exact m.cipRSPatternOfConfiguration_mirrorConfiguration (cfg := cfg)

theorem chiralCipRSConfigurationBySymmetry_iff_forall_smul_ne_mirror
    (m : MultiCenterMolecule V) (hst : ∀ c : m.Center, m.StereogenicByCIPAt c)
    (cfg : m.Configuration) :
    m.ChiralCipRSConfigurationBySymmetry cfg ↔
      ∀ e : m.Aut,
        m.cipRSPatternOfConfiguration (e • cfg) ≠
          m.cipRSPatternOfConfiguration (m.mirrorConfiguration cfg) := by
  constructor
  · intro h e he
    have hsmul :
        e • m.cipRSPatternOfConfiguration cfg =
          m.cipRSPatternOfConfiguration (m.mirrorConfiguration cfg) := by
      simpa [m.cipRSPatternOfConfiguration_smul_eq_of_stereogenicByCIPAt
        (hst := hst) (e := e) (cfg := cfg)] using he
    have hneg :
        e • m.cipRSPatternOfConfiguration cfg = -m.cipRSPatternOfConfiguration cfg := by
      simpa [m.cipRSPatternOfConfiguration_mirrorConfiguration (cfg := cfg)] using hsmul
    exact h e hneg
  · intro h e he
    have hmirror :
        m.cipRSPatternOfConfiguration (e • cfg) =
          m.cipRSPatternOfConfiguration (m.mirrorConfiguration cfg) := by
      calc
        m.cipRSPatternOfConfiguration (e • cfg)
            = e • m.cipRSPatternOfConfiguration cfg := by
                exact (m.cipRSPatternOfConfiguration_smul_eq_of_stereogenicByCIPAt
                  (hst := hst) (e := e) (cfg := cfg)).symm
        _ = -m.cipRSPatternOfConfiguration cfg := he
        _ = m.cipRSPatternOfConfiguration (m.mirrorConfiguration cfg) := by
              exact (m.cipRSPatternOfConfiguration_mirrorConfiguration (cfg := cfg)).symm
    exact h e hmirror

theorem mesoCipRSConfigurationCycleCutBySymmetry_iff_exists_smul_eq_mirror
    (m : MultiCenterMolecule V) (hst : ∀ c : m.Center, m.StereogenicByCIPCycleCutAt c)
    (cfg : m.Configuration) :
    m.MesoCipRSConfigurationCycleCutBySymmetry cfg ↔
      ∃ e : m.Aut,
        m.cipRSPatternOfConfigurationCycleCut (e • cfg) =
          m.cipRSPatternOfConfigurationCycleCut (m.mirrorConfiguration cfg) := by
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    calc
      m.cipRSPatternOfConfigurationCycleCut (e • cfg)
          = e • m.cipRSPatternOfConfigurationCycleCut cfg := by
              exact (m.cipRSPatternOfConfigurationCycleCut_smul_eq_of_stereogenicByCIPCycleCutAt
                (hst := hst) (e := e) (cfg := cfg)).symm
      _ = -m.cipRSPatternOfConfigurationCycleCut cfg := he
      _ = m.cipRSPatternOfConfigurationCycleCut (m.mirrorConfiguration cfg) := by
            exact (m.cipRSPatternOfConfigurationCycleCut_mirrorConfiguration (cfg := cfg)).symm
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    calc
      e • m.cipRSPatternOfConfigurationCycleCut cfg
          = m.cipRSPatternOfConfigurationCycleCut (e • cfg) := by
              exact m.cipRSPatternOfConfigurationCycleCut_smul_eq_of_stereogenicByCIPCycleCutAt
                (hst := hst) (e := e) (cfg := cfg)
      _ = m.cipRSPatternOfConfigurationCycleCut (m.mirrorConfiguration cfg) := he
      _ = -m.cipRSPatternOfConfigurationCycleCut cfg := by
            exact m.cipRSPatternOfConfigurationCycleCut_mirrorConfiguration (cfg := cfg)

theorem mesoCipRSConfigurationBySymmetry_iff_same_mirror (m : MultiCenterMolecule V)
    (cfg : m.Configuration) :
    m.MesoCipRSConfigurationBySymmetry cfg ↔
      m.SameCipRSConfigurationClass cfg (m.mirrorConfiguration cfg) := by
  simpa [MesoCipRSConfigurationBySymmetry, SameCipRSConfigurationClass,
    cipRSPatternOfConfiguration_mirrorConfiguration] using
    (m.mesoCipRSPatternBySymmetry_iff_same_mirror (s := m.cipRSPatternOfConfiguration cfg))

theorem chiralCipRSConfigurationBySymmetry_iff_not_same_mirror (m : MultiCenterMolecule V)
    (cfg : m.Configuration) :
    m.ChiralCipRSConfigurationBySymmetry cfg ↔
      ¬ m.SameCipRSConfigurationClass cfg (m.mirrorConfiguration cfg) := by
  simpa [ChiralCipRSConfigurationBySymmetry, SameCipRSConfigurationClass,
    cipRSPatternOfConfiguration_mirrorConfiguration] using
    (m.chiralCipRSPatternBySymmetry_iff_quotient_ne (s := m.cipRSPatternOfConfiguration cfg))

theorem chiralCipRSConfigurationCycleCutBySymmetry_iff_forall_smul_ne_mirror
    (m : MultiCenterMolecule V) (hst : ∀ c : m.Center, m.StereogenicByCIPCycleCutAt c)
    (cfg : m.Configuration) :
    m.ChiralCipRSConfigurationCycleCutBySymmetry cfg ↔
      ∀ e : m.Aut,
        m.cipRSPatternOfConfigurationCycleCut (e • cfg) ≠
          m.cipRSPatternOfConfigurationCycleCut (m.mirrorConfiguration cfg) := by
  constructor
  · intro h e he
    have hsmul :
        e • m.cipRSPatternOfConfigurationCycleCut cfg =
          m.cipRSPatternOfConfigurationCycleCut (m.mirrorConfiguration cfg) := by
      simpa [m.cipRSPatternOfConfigurationCycleCut_smul_eq_of_stereogenicByCIPCycleCutAt
        (hst := hst) (e := e) (cfg := cfg)] using he
    have hneg :
        e • m.cipRSPatternOfConfigurationCycleCut cfg =
          -m.cipRSPatternOfConfigurationCycleCut cfg := by
      simpa [m.cipRSPatternOfConfigurationCycleCut_mirrorConfiguration (cfg := cfg)] using hsmul
    exact h e hneg
  · intro h e he
    have hmirror :
        m.cipRSPatternOfConfigurationCycleCut (e • cfg) =
          m.cipRSPatternOfConfigurationCycleCut (m.mirrorConfiguration cfg) := by
      calc
        m.cipRSPatternOfConfigurationCycleCut (e • cfg)
            = e • m.cipRSPatternOfConfigurationCycleCut cfg := by
                exact (m.cipRSPatternOfConfigurationCycleCut_smul_eq_of_stereogenicByCIPCycleCutAt
                  (hst := hst) (e := e) (cfg := cfg)).symm
        _ = -m.cipRSPatternOfConfigurationCycleCut cfg := he
        _ = m.cipRSPatternOfConfigurationCycleCut (m.mirrorConfiguration cfg) := by
              exact (m.cipRSPatternOfConfigurationCycleCut_mirrorConfiguration (cfg := cfg)).symm
    exact h e hmirror

theorem mesoCipRSConfigurationCycleCutBySymmetry_iff_same_mirror
    (m : MultiCenterMolecule V) (cfg : m.Configuration) :
    m.MesoCipRSConfigurationCycleCutBySymmetry cfg ↔
      m.SameCipRSConfigurationCycleCutClass cfg (m.mirrorConfiguration cfg) := by
  simpa [MesoCipRSConfigurationCycleCutBySymmetry, SameCipRSConfigurationCycleCutClass,
    cipRSPatternOfConfigurationCycleCut_mirrorConfiguration] using
    (m.mesoCipRSPatternBySymmetry_iff_same_mirror
      (s := m.cipRSPatternOfConfigurationCycleCut cfg))

theorem chiralCipRSConfigurationCycleCutBySymmetry_iff_not_same_mirror
    (m : MultiCenterMolecule V) (cfg : m.Configuration) :
    m.ChiralCipRSConfigurationCycleCutBySymmetry cfg ↔
      ¬ m.SameCipRSConfigurationCycleCutClass cfg (m.mirrorConfiguration cfg) := by
  simpa [ChiralCipRSConfigurationCycleCutBySymmetry, SameCipRSConfigurationCycleCutClass,
    cipRSPatternOfConfigurationCycleCut_mirrorConfiguration] using
    (m.chiralCipRSPatternBySymmetry_iff_quotient_ne
      (s := m.cipRSPatternOfConfigurationCycleCut cfg))

theorem enantiomeric_cipRSConfigurations_self_mirror_iff_chiral (m : MultiCenterMolecule V)
    (cfg : m.Configuration) :
    m.EnantiomericCipRSConfigurationsBySymmetry cfg (m.mirrorConfiguration cfg) ↔
      m.ChiralCipRSConfigurationBySymmetry cfg := by
  rw [EnantiomericCipRSConfigurationsBySymmetry, cipRSPatternOfConfiguration_mirrorConfiguration]
  exact m.enantiomeric_self_mirror_iff_chiral (s := m.cipRSPatternOfConfiguration cfg)

theorem enantiomeric_cipRSConfigurationsCycleCut_self_mirror_iff_chiral
    (m : MultiCenterMolecule V) (cfg : m.Configuration) :
    m.EnantiomericCipRSConfigurationsCycleCutBySymmetry cfg (m.mirrorConfiguration cfg) ↔
      m.ChiralCipRSConfigurationCycleCutBySymmetry cfg := by
  rw [EnantiomericCipRSConfigurationsCycleCutBySymmetry,
    cipRSPatternOfConfigurationCycleCut_mirrorConfiguration]
  exact m.enantiomeric_self_mirror_iff_chiral
    (s := m.cipRSPatternOfConfigurationCycleCut cfg)

theorem classifyCipRSConfiguration_self_mirror_same_of_meso
    (m : MultiCenterMolecule V) {cfg : m.Configuration}
    (h : m.MesoCipRSConfigurationBySymmetry cfg) :
    m.classifyCipRSConfiguration cfg (m.mirrorConfiguration cfg) =
      CipRSClassRelation.same := by
  classical
  simpa [classifyCipRSConfiguration,
    m.cipRSPatternOfConfiguration_mirrorConfiguration (cfg := cfg)] using
    (m.classifyCipRSPatternClass_self_mirror_same_of_meso
      (s := m.cipRSPatternOfConfiguration cfg) h)

theorem classifyCipRSConfiguration_self_mirror_same_sound_of_meso
    (m : MultiCenterMolecule V) {cfg : m.Configuration}
    (h : m.MesoCipRSConfigurationBySymmetry cfg) :
    m.CipRSConfigurationClassificationHolds cfg (m.mirrorConfiguration cfg)
      CipRSClassRelation.same := by
  have hsound := m.classifyCipRSConfiguration_sound cfg (m.mirrorConfiguration cfg)
  simpa [m.classifyCipRSConfiguration_self_mirror_same_of_meso h] using hsound

theorem classifyCipRSConfiguration_self_mirror_enantiomeric_of_chiral
    (m : MultiCenterMolecule V) {cfg : m.Configuration}
    (h : m.ChiralCipRSConfigurationBySymmetry cfg) :
    m.classifyCipRSConfiguration cfg (m.mirrorConfiguration cfg) =
      CipRSClassRelation.enantiomeric := by
  classical
  simpa [classifyCipRSConfiguration,
    m.cipRSPatternOfConfiguration_mirrorConfiguration (cfg := cfg)] using
    (m.classifyCipRSPatternClass_self_mirror_enantiomeric_of_chiral
      (s := m.cipRSPatternOfConfiguration cfg) h)

theorem classifyCipRSConfiguration_self_mirror_enantiomeric_sound_of_chiral
    (m : MultiCenterMolecule V) {cfg : m.Configuration}
    (h : m.ChiralCipRSConfigurationBySymmetry cfg) :
    m.CipRSConfigurationClassificationHolds cfg (m.mirrorConfiguration cfg)
      CipRSClassRelation.enantiomeric := by
  have hsound := m.classifyCipRSConfiguration_sound cfg (m.mirrorConfiguration cfg)
  simpa [m.classifyCipRSConfiguration_self_mirror_enantiomeric_of_chiral h] using hsound

theorem classifyCipRSConfigurationCycleCut_self_mirror_same_of_meso
    (m : MultiCenterMolecule V) {cfg : m.Configuration}
    (h : m.MesoCipRSConfigurationCycleCutBySymmetry cfg) :
    m.classifyCipRSConfigurationCycleCut cfg (m.mirrorConfiguration cfg) =
      CipRSClassRelation.same := by
  classical
  simpa [classifyCipRSConfigurationCycleCut,
    m.cipRSPatternOfConfigurationCycleCut_mirrorConfiguration (cfg := cfg)] using
    (m.classifyCipRSPatternClass_self_mirror_same_of_meso
      (s := m.cipRSPatternOfConfigurationCycleCut cfg) h)

theorem classifyCipRSConfigurationCycleCut_self_mirror_same_sound_of_meso
    (m : MultiCenterMolecule V) {cfg : m.Configuration}
    (h : m.MesoCipRSConfigurationCycleCutBySymmetry cfg) :
    m.CipRSConfigurationCycleCutClassificationHolds cfg (m.mirrorConfiguration cfg)
      CipRSClassRelation.same := by
  have hsound := m.classifyCipRSConfigurationCycleCut_sound cfg (m.mirrorConfiguration cfg)
  simpa [m.classifyCipRSConfigurationCycleCut_self_mirror_same_of_meso h] using hsound

theorem classifyCipRSConfigurationCycleCut_self_mirror_enantiomeric_of_chiral
    (m : MultiCenterMolecule V) {cfg : m.Configuration}
    (h : m.ChiralCipRSConfigurationCycleCutBySymmetry cfg) :
    m.classifyCipRSConfigurationCycleCut cfg (m.mirrorConfiguration cfg) =
      CipRSClassRelation.enantiomeric := by
  classical
  simpa [classifyCipRSConfigurationCycleCut,
    m.cipRSPatternOfConfigurationCycleCut_mirrorConfiguration (cfg := cfg)] using
    (m.classifyCipRSPatternClass_self_mirror_enantiomeric_of_chiral
      (s := m.cipRSPatternOfConfigurationCycleCut cfg) h)

theorem classifyCipRSConfigurationCycleCut_self_mirror_enantiomeric_sound_of_chiral
    (m : MultiCenterMolecule V) {cfg : m.Configuration}
    (h : m.ChiralCipRSConfigurationCycleCutBySymmetry cfg) :
    m.CipRSConfigurationCycleCutClassificationHolds cfg (m.mirrorConfiguration cfg)
      CipRSClassRelation.enantiomeric := by
  have hsound := m.classifyCipRSConfigurationCycleCut_sound cfg (m.mirrorConfiguration cfg)
  simpa [m.classifyCipRSConfigurationCycleCut_self_mirror_enantiomeric_of_chiral h] using hsound

/-! ### Canonical two-center patterns -/

/-- A constant CIP `R/S` pattern on all distinguished centers. -/
def constantCipRSPattern (m : MultiCenterMolecule V) (r : RS) : m.CipRSPattern :=
  ⟨fun _ => r⟩

/-- A two-center CIP `R/S` pattern, with `r₀` at `c₀` and `r₁` away from `c₀`.

For actual two-center use, pair this with a hypothesis that every center is `c₀` or `c₁`. -/
def twoCenterCipRSPattern (m : MultiCenterMolecule V) (c₀ c₁ : m.Center) (r₀ r₁ : RS) :
    m.CipRSPattern :=
  ⟨fun c => if c = c₀ then r₀ else if c = c₁ then r₁ else r₁⟩

@[simp] theorem neg_constantCipRSPattern (m : MultiCenterMolecule V) (r : RS) :
    (-m.constantCipRSPattern r : m.CipRSPattern) = m.constantCipRSPattern (RS.swap r) := by
  ext c
  cases r <;> simp [constantCipRSPattern, mirrorRSPattern, RS.swap]

@[simp] theorem neg_twoCenterCipRSPattern (m : MultiCenterMolecule V) (c₀ c₁ : m.Center)
    (r₀ r₁ : RS) :
    (-m.twoCenterCipRSPattern c₀ c₁ r₀ r₁ : m.CipRSPattern) =
      m.twoCenterCipRSPattern c₀ c₁ (RS.swap r₀) (RS.swap r₁) := by
  ext c
  by_cases h0 : c = c₀ <;> by_cases h1 : c = c₁ <;>
    by_cases h10 : c₁ = c₀ <;>
      simp [twoCenterCipRSPattern, mirrorRSPattern, h0, h1, h10]

theorem constantR_chiralBySymmetry_of_center (m : MultiCenterMolecule V) (c : m.Center) :
    m.ChiralCipRSPatternBySymmetry (m.constantCipRSPattern RS.R) := by
  intro e he
  have hval := congrArg (fun s => s c) he
  change m.smulCipRSPattern e (m.constantCipRSPattern RS.R) c =
    (-m.constantCipRSPattern RS.R : m.CipRSPattern) c at hval
  simp [smulCipRSPattern, constantCipRSPattern, mirrorRSPattern, RS.swap] at hval

theorem constantS_chiralBySymmetry_of_center (m : MultiCenterMolecule V) (c : m.Center) :
    m.ChiralCipRSPatternBySymmetry (m.constantCipRSPattern RS.S) := by
  intro e he
  have hval := congrArg (fun s => s c) he
  change m.smulCipRSPattern e (m.constantCipRSPattern RS.S) c =
    (-m.constantCipRSPattern RS.S : m.CipRSPattern) c at hval
  simp [smulCipRSPattern, constantCipRSPattern, mirrorRSPattern, RS.swap] at hval

theorem constantR_constantS_enantiomericBySymmetry_of_center (m : MultiCenterMolecule V)
    (c : m.Center) :
    m.EnantiomericCipRSPatternsBySymmetry (m.constantCipRSPattern RS.R)
      (m.constantCipRSPattern RS.S) := by
  constructor
  · rfl
  · have hchiral :=
      (m.chiralCipRSPatternBySymmetry_iff_quotient_ne
        (s := m.constantCipRSPattern RS.R)).1
        (m.constantR_chiralBySymmetry_of_center c)
    simpa [SameCipRSPatternClass] using hchiral

theorem twoCenter_mixed_mesoBySwap (m : MultiCenterMolecule V) {cR cS : m.Center}
    (hne : cR ≠ cS) (hcenters : ∀ c : m.Center, c = cR ∨ c = cS) (e : m.Aut)
    (hR : m.centerPerm e cR = cS) (hS : m.centerPerm e cS = cR) :
    m.MesoCipRSPatternBySymmetry (m.twoCenterCipRSPattern cR cS RS.R RS.S) := by
  refine ⟨e, ?_⟩
  ext c
  rcases hcenters c with hc | hc
  · subst c
    have hpre : (Equiv.symm (m.centerPerm e)) cR = cS := by
      apply (m.centerPerm e).injective
      simp [hS]
    change m.smulCipRSPattern e (m.twoCenterCipRSPattern cR cS RS.R RS.S) cR =
      (-m.twoCenterCipRSPattern cR cS RS.R RS.S : m.CipRSPattern) cR
    simp [smulCipRSPattern, twoCenterCipRSPattern, mirrorRSPattern, RS.swap, hpre, hne.symm]
  · subst c
    have hpre : (Equiv.symm (m.centerPerm e)) cS = cR := by
      apply (m.centerPerm e).injective
      simp [hR]
    change m.smulCipRSPattern e (m.twoCenterCipRSPattern cR cS RS.R RS.S) cS =
      (-m.twoCenterCipRSPattern cR cS RS.R RS.S : m.CipRSPattern) cS
    simp [smulCipRSPattern, twoCenterCipRSPattern, mirrorRSPattern, RS.swap, hpre, hne.symm]

theorem constantR_diastereomeric_twoCenterMixed (m : MultiCenterMolecule V) {cR cS : m.Center}
    (hne : cR ≠ cS) :
    m.DiastereomericCipRSPatternsBySymmetry (m.constantCipRSPattern RS.R)
      (m.twoCenterCipRSPattern cR cS RS.R RS.S) := by
  constructor
  · intro hsame
    have hrel :
        MulAction.orbitRel m.Aut m.CipRSPattern (m.constantCipRSPattern RS.R)
          (m.twoCenterCipRSPattern cR cS RS.R RS.S) :=
      Quotient.exact hsame
    rcases (MulAction.mem_orbit_iff).1 ((MulAction.orbitRel_apply).1 hrel) with ⟨e, he⟩
    let cImage : m.Center := m.centerPerm e cS
    have hval := congrArg (fun s => s cImage) he
    change m.smulCipRSPattern e (m.twoCenterCipRSPattern cR cS RS.R RS.S) cImage =
      m.constantCipRSPattern RS.R cImage at hval
    have hpre : (Equiv.symm (m.centerPerm e)) cImage = cS := by
      simp [cImage]
    simp [smulCipRSPattern, twoCenterCipRSPattern, constantCipRSPattern, hpre, hne.symm] at hval
  · intro hmirror
    have hrel :
        MulAction.orbitRel m.Aut m.CipRSPattern (-(m.constantCipRSPattern RS.R : m.CipRSPattern))
          (m.twoCenterCipRSPattern cR cS RS.R RS.S) :=
      Quotient.exact hmirror
    rcases (MulAction.mem_orbit_iff).1 ((MulAction.orbitRel_apply).1 hrel) with ⟨e, he⟩
    let cImage : m.Center := m.centerPerm e cR
    have hval := congrArg (fun s => s cImage) he
    change m.smulCipRSPattern e (m.twoCenterCipRSPattern cR cS RS.R RS.S) cImage =
      (-(m.constantCipRSPattern RS.R : m.CipRSPattern)) cImage at hval
    have hpre : (Equiv.symm (m.centerPerm e)) cImage = cR := by
      simp [cImage]
    simp [smulCipRSPattern, twoCenterCipRSPattern, constantCipRSPattern, mirrorRSPattern, RS.swap,
      hpre] at hval

theorem constantS_diastereomeric_twoCenterMixed (m : MultiCenterMolecule V) {cR cS : m.Center}
    (hne : cR ≠ cS) :
    m.DiastereomericCipRSPatternsBySymmetry (m.constantCipRSPattern RS.S)
      (m.twoCenterCipRSPattern cR cS RS.R RS.S) := by
  constructor
  · intro hsame
    have hrel :
        MulAction.orbitRel m.Aut m.CipRSPattern (m.constantCipRSPattern RS.S)
          (m.twoCenterCipRSPattern cR cS RS.R RS.S) :=
      Quotient.exact hsame
    rcases (MulAction.mem_orbit_iff).1 ((MulAction.orbitRel_apply).1 hrel) with ⟨e, he⟩
    let cImage : m.Center := m.centerPerm e cR
    have hval := congrArg (fun s => s cImage) he
    change m.smulCipRSPattern e (m.twoCenterCipRSPattern cR cS RS.R RS.S) cImage =
      m.constantCipRSPattern RS.S cImage at hval
    have hpre : (Equiv.symm (m.centerPerm e)) cImage = cR := by
      simp [cImage]
    simp [smulCipRSPattern, twoCenterCipRSPattern, constantCipRSPattern, hpre] at hval
  · intro hmirror
    have hrel :
        MulAction.orbitRel m.Aut m.CipRSPattern (-(m.constantCipRSPattern RS.S : m.CipRSPattern))
          (m.twoCenterCipRSPattern cR cS RS.R RS.S) :=
      Quotient.exact hmirror
    rcases (MulAction.mem_orbit_iff).1 ((MulAction.orbitRel_apply).1 hrel) with ⟨e, he⟩
    let cImage : m.Center := m.centerPerm e cS
    have hval := congrArg (fun s => s cImage) he
    change m.smulCipRSPattern e (m.twoCenterCipRSPattern cR cS RS.R RS.S) cImage =
      (-(m.constantCipRSPattern RS.S : m.CipRSPattern)) cImage at hval
    have hpre : (Equiv.symm (m.centerPerm e)) cImage = cS := by
      simp [cImage]
    simp [smulCipRSPattern, twoCenterCipRSPattern, constantCipRSPattern, mirrorRSPattern, RS.swap,
      hpre, hne.symm] at hval

end MultiCenterMolecule

end
end OneCenter
end TetraStereo
