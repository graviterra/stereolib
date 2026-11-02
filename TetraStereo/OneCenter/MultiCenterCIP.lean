import TetraStereo.OneCenter.CIPCycleCut
import TetraStereo.OneCenter.MultiCenterConfiguration
import TetraStereo.OneCenter.Reindex

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

namespace MultiCenterMolecule

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The CIP key of a ligand at a distinguished center, computed from the underlying molecular graph. -/
def cipKeyAt (m : MultiCenterMolecule V) (c : m.Center) (i : Fin 4) :
    List MoleculeGraph.AtomLabel :=
  (m.toOneCenterMolecule c).cipKey i

/-- The four ligand indices at a distinguished center, sorted in descending CIP order.

This raw order is deterministic even when CIP keys tie.  Use `cipOrderAtOfResolved` or
`cipOrderAt?` for descriptor-level use. -/
def cipOrderAt (m : MultiCenterMolecule V) (c : m.Center) : List (Fin 4) :=
  (m.toOneCenterMolecule c).cipOrder

/-- The raw CIP permutation at a distinguished center.

This permutation uses the deterministic tie-breaker inherited from `OneCenterMolecule`.
Use `cipPermutationAtOfResolved` or `cipPermutationAt?` when assigning stereochemical
descriptors. -/
def cipPermutationAt (m : MultiCenterMolecule V) (c : m.Center) : Equiv.Perm (Fin 4) :=
  (m.toOneCenterMolecule c).cipPermutation

/-- The cycle-cut CIP key of a ligand at a distinguished center. -/
def cipKeyCycleCutAt (m : MultiCenterMolecule V) (c : m.Center) (i : Fin 4) :
    List MoleculeGraph.AtomLabel :=
  (m.toOneCenterMolecule c).cipKeyCycleCut i

/-- The raw cycle-cut CIP order at a distinguished center. -/
def cipOrderCycleCutAt (m : MultiCenterMolecule V) (c : m.Center) : List (Fin 4) :=
  (m.toOneCenterMolecule c).cipOrderCycleCut

/-- The raw cycle-cut CIP permutation at a distinguished center. -/
def cipPermutationCycleCutAt (m : MultiCenterMolecule V) (c : m.Center) :
    Equiv.Perm (Fin 4) :=
  (m.toOneCenterMolecule c).cipPermutationCycleCut

/-- CIP-normalize a multi-center configuration by composing each local frame with the local CIP
permutation. -/
def cipNormalizeConfiguration (m : MultiCenterMolecule V) (cfg : m.Configuration) : m.Configuration :=
  fun c => cfg c * m.cipPermutationAt c

/-- Cycle-cut CIP-normalize a multi-center configuration by composing each local frame with the
local cycle-cut CIP permutation. -/
def cipNormalizeConfigurationCycleCut (m : MultiCenterMolecule V)
    (cfg : m.Configuration) : m.Configuration :=
  fun c => cfg c * m.cipPermutationCycleCutAt c

@[simp] theorem cipNormalizeConfiguration_apply (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (c : m.Center) :
    m.cipNormalizeConfiguration cfg c = cfg c * m.cipPermutationAt c := rfl

@[simp] theorem cipNormalizeConfigurationCycleCut_apply
    (m : MultiCenterMolecule V) (cfg : m.Configuration) (c : m.Center) :
    m.cipNormalizeConfigurationCycleCut cfg c = cfg c * m.cipPermutationCycleCutAt c := rfl

/-- The handedness-sign after CIP normalization. -/
abbrev cipConfigurationSign (m : MultiCenterMolecule V) (cfg : m.Configuration) : m.SignPattern :=
  m.configurationSign (m.cipNormalizeConfiguration cfg)

/-- The handedness-sign after cycle-cut CIP normalization. -/
abbrev cipConfigurationSignCycleCut (m : MultiCenterMolecule V)
    (cfg : m.Configuration) : m.SignPattern :=
  m.configurationSign (m.cipNormalizeConfigurationCycleCut cfg)

@[simp] theorem cipConfigurationSign_apply (m : MultiCenterMolecule V) (cfg : m.Configuration) (c : m.Center) :
    m.cipConfigurationSign cfg c = permHandedness (cfg c * m.cipPermutationAt c) := by
  rfl

@[simp] theorem cipConfigurationSignCycleCut_apply
    (m : MultiCenterMolecule V) (cfg : m.Configuration) (c : m.Center) :
    m.cipConfigurationSignCycleCut cfg c =
      permHandedness (cfg c * m.cipPermutationCycleCutAt c) := by
  rfl

theorem cipConfigurationSign_eq (m : MultiCenterMolecule V) (cfg : m.Configuration) (c : m.Center) :
    m.cipConfigurationSign cfg c =
      m.configurationSign cfg c * permHandedness (m.cipPermutationAt c) := by
  simp [MultiCenterMolecule.cipConfigurationSign, MultiCenterMolecule.cipNormalizeConfiguration,
    MultiCenterMolecule.configurationSign, permHandedness_mul]

theorem cipConfigurationSignCycleCut_eq
    (m : MultiCenterMolecule V) (cfg : m.Configuration) (c : m.Center) :
    m.cipConfigurationSignCycleCut cfg c =
      m.configurationSign cfg c * permHandedness (m.cipPermutationCycleCutAt c) := by
  simp [MultiCenterMolecule.cipConfigurationSignCycleCut,
    MultiCenterMolecule.cipNormalizeConfigurationCycleCut,
    MultiCenterMolecule.configurationSign, permHandedness_mul]

theorem cipConfigurationSign_mirrorConfiguration (m : MultiCenterMolecule V) (cfg : m.Configuration) (c : m.Center) :
    m.cipConfigurationSign (m.mirrorConfiguration cfg) c = -m.cipConfigurationSign cfg c := by
  simp [MultiCenterMolecule.cipConfigurationSign, MultiCenterMolecule.cipNormalizeConfiguration,
    MultiCenterMolecule.mirrorConfiguration, MultiCenterMolecule.configurationSign, permHandedness_mul,
    mul_assoc, mirrorFrame]

theorem cipConfigurationSignCycleCut_mirrorConfiguration
    (m : MultiCenterMolecule V) (cfg : m.Configuration) (c : m.Center) :
    m.cipConfigurationSignCycleCut (m.mirrorConfiguration cfg) c =
      -m.cipConfigurationSignCycleCut cfg c := by
  simp [MultiCenterMolecule.cipConfigurationSignCycleCut,
    MultiCenterMolecule.cipNormalizeConfigurationCycleCut,
    MultiCenterMolecule.mirrorConfiguration, MultiCenterMolecule.configurationSign, permHandedness_mul,
    mul_assoc, mirrorFrame]

theorem cipConfigurationSign_mirrorConfiguration_eq_neg (m : MultiCenterMolecule V) (cfg : m.Configuration) :
    m.cipConfigurationSign (m.mirrorConfiguration cfg) = -m.cipConfigurationSign cfg := by
  funext c
  simpa using (m.cipConfigurationSign_mirrorConfiguration (cfg := cfg) (c := c))

/-- Cycle-cut CIP-normalized signs change sign under mirror. -/
theorem cipConfigurationSignCycleCut_mirrorConfiguration_eq_neg
    (m : MultiCenterMolecule V) (cfg : m.Configuration) :
    m.cipConfigurationSignCycleCut (m.mirrorConfiguration cfg) =
      -m.cipConfigurationSignCycleCut cfg := by
  funext c
  simpa using (m.cipConfigurationSignCycleCut_mirrorConfiguration (cfg := cfg) (c := c))

/-- A distinguished center is *CIP-stereogenic* when its four ligand keys are pairwise distinct. -/
def StereogenicByCIPAt (m : MultiCenterMolecule V) (c : m.Center) : Prop :=
  (m.toOneCenterMolecule c).StereogenicByCIP

/-- A distinguished center is cycle-cut CIP-stereogenic when its cycle-cut ligand keys are pairwise
distinct. -/
def StereogenicByCIPCycleCutAt (m : MultiCenterMolecule V) (c : m.Center) : Prop :=
  (m.toOneCenterMolecule c).StereogenicByCIPCycleCut

/-- Resolved CIP priorities at a distinguished center. -/
abbrev ResolvedCIPAt (m : MultiCenterMolecule V) (c : m.Center) : Prop :=
  m.StereogenicByCIPAt c

/-- Resolved cycle-cut CIP priorities at a distinguished center. -/
abbrev ResolvedCIPCycleCutAt (m : MultiCenterMolecule V) (c : m.Center) : Prop :=
  m.StereogenicByCIPCycleCutAt c

/-- All distinguished centers have resolved CIP priorities. -/
abbrev AllCentersResolvedByCIP (m : MultiCenterMolecule V) : Prop :=
  ∀ c : m.Center, m.ResolvedCIPAt c

/-- All distinguished centers have resolved cycle-cut CIP priorities. -/
abbrev AllCentersResolvedByCIPCycleCut (m : MultiCenterMolecule V) : Prop :=
  ∀ c : m.Center, m.ResolvedCIPCycleCutAt c

/-- A bundled certificate that all distinguished centers are CIP-resolved. -/
structure ResolvedAllCIP (m : MultiCenterMolecule V) : Type _ where
  resolved : m.AllCentersResolvedByCIP

/-- A bundled certificate that all distinguished centers are cycle-cut CIP-resolved. -/
structure ResolvedAllCIPCycleCut (m : MultiCenterMolecule V) : Type _ where
  resolved : m.AllCentersResolvedByCIPCycleCut

/-- The local CIP order at a resolved distinguished center. -/
def cipOrderAtOfResolved (m : MultiCenterMolecule V) (c : m.Center)
    (_ : m.ResolvedCIPAt c) : List (Fin 4) :=
  m.cipOrderAt c

/-- The local CIP permutation at a resolved distinguished center. -/
def cipPermutationAtOfResolved (m : MultiCenterMolecule V) (c : m.Center)
    (_ : m.ResolvedCIPAt c) : Equiv.Perm (Fin 4) :=
  m.cipPermutationAt c

/-- The local cycle-cut CIP order at a resolved distinguished center. -/
def cipOrderCycleCutAtOfResolved (m : MultiCenterMolecule V) (c : m.Center)
    (_ : m.ResolvedCIPCycleCutAt c) : List (Fin 4) :=
  m.cipOrderCycleCutAt c

/-- The local cycle-cut CIP permutation at a resolved distinguished center. -/
def cipPermutationCycleCutAtOfResolved (m : MultiCenterMolecule V) (c : m.Center)
    (_ : m.ResolvedCIPCycleCutAt c) : Equiv.Perm (Fin 4) :=
  m.cipPermutationCycleCutAt c

@[simp] theorem cipOrderAtOfResolved_eq (m : MultiCenterMolecule V) (c : m.Center)
    (h : m.ResolvedCIPAt c) :
    m.cipOrderAtOfResolved c h = m.cipOrderAt c := rfl

@[simp] theorem cipPermutationAtOfResolved_eq (m : MultiCenterMolecule V) (c : m.Center)
    (h : m.ResolvedCIPAt c) :
    m.cipPermutationAtOfResolved c h = m.cipPermutationAt c := rfl

@[simp] theorem cipOrderCycleCutAtOfResolved_eq
    (m : MultiCenterMolecule V) (c : m.Center) (h : m.ResolvedCIPCycleCutAt c) :
    m.cipOrderCycleCutAtOfResolved c h = m.cipOrderCycleCutAt c := rfl

@[simp] theorem cipPermutationCycleCutAtOfResolved_eq
    (m : MultiCenterMolecule V) (c : m.Center) (h : m.ResolvedCIPCycleCutAt c) :
    m.cipPermutationCycleCutAtOfResolved c h = m.cipPermutationCycleCutAt c := rfl


noncomputable def cipOrderAt? (m : MultiCenterMolecule V) (c : m.Center) :
    Option (List (Fin 4)) :=
  by
    classical
    exact if h : m.ResolvedCIPAt c then some (m.cipOrderAtOfResolved c h) else none


noncomputable def cipPermutationAt? (m : MultiCenterMolecule V) (c : m.Center) :
    Option (Equiv.Perm (Fin 4)) :=
  by
    classical
    exact if h : m.ResolvedCIPAt c then some (m.cipPermutationAtOfResolved c h) else none


noncomputable def cipOrderCycleCutAt? (m : MultiCenterMolecule V) (c : m.Center) :
    Option (List (Fin 4)) :=
  by
    classical
    exact
      if h : m.ResolvedCIPCycleCutAt c then
        some (m.cipOrderCycleCutAtOfResolved c h)
      else
        none


noncomputable def cipPermutationCycleCutAt? (m : MultiCenterMolecule V) (c : m.Center) :
    Option (Equiv.Perm (Fin 4)) :=
  by
    classical
    exact
      if h : m.ResolvedCIPCycleCutAt c then
        some (m.cipPermutationCycleCutAtOfResolved c h)
      else
        none

theorem cipOrderAt?_eq_some_of_resolvedCIPAt (m : MultiCenterMolecule V)
    (c : m.Center) (h : m.ResolvedCIPAt c) :
    m.cipOrderAt? c = some (m.cipOrderAt c) := by
  classical
  simp [cipOrderAt?, h]

theorem cipOrderAt?_eq_none_of_not_resolvedCIPAt (m : MultiCenterMolecule V)
    (c : m.Center) (h : ¬ m.ResolvedCIPAt c) :
    m.cipOrderAt? c = none := by
  classical
  simp [cipOrderAt?, h]

theorem cipPermutationAt?_eq_some_of_resolvedCIPAt (m : MultiCenterMolecule V)
    (c : m.Center) (h : m.ResolvedCIPAt c) :
    m.cipPermutationAt? c = some (m.cipPermutationAt c) := by
  classical
  simp [cipPermutationAt?, h]

theorem cipPermutationAt?_eq_none_of_not_resolvedCIPAt (m : MultiCenterMolecule V)
    (c : m.Center) (h : ¬ m.ResolvedCIPAt c) :
    m.cipPermutationAt? c = none := by
  classical
  simp [cipPermutationAt?, h]

theorem cipOrderCycleCutAt?_eq_some_of_resolvedCIPCycleCutAt
    (m : MultiCenterMolecule V) (c : m.Center) (h : m.ResolvedCIPCycleCutAt c) :
    m.cipOrderCycleCutAt? c = some (m.cipOrderCycleCutAt c) := by
  classical
  simp [cipOrderCycleCutAt?, h]

theorem cipOrderCycleCutAt?_eq_none_of_not_resolvedCIPCycleCutAt
    (m : MultiCenterMolecule V) (c : m.Center) (h : ¬ m.ResolvedCIPCycleCutAt c) :
    m.cipOrderCycleCutAt? c = none := by
  classical
  simp [cipOrderCycleCutAt?, h]

theorem cipPermutationCycleCutAt?_eq_some_of_resolvedCIPCycleCutAt
    (m : MultiCenterMolecule V) (c : m.Center) (h : m.ResolvedCIPCycleCutAt c) :
    m.cipPermutationCycleCutAt? c = some (m.cipPermutationCycleCutAt c) := by
  classical
  simp [cipPermutationCycleCutAt?, h]

theorem cipPermutationCycleCutAt?_eq_none_of_not_resolvedCIPCycleCutAt
    (m : MultiCenterMolecule V) (c : m.Center) (h : ¬ m.ResolvedCIPCycleCutAt c) :
    m.cipPermutationCycleCutAt? c = none := by
  classical
  simp [cipPermutationCycleCutAt?, h]

/-- CIP-normalize a configuration with an explicit all-centers-resolved certificate. -/
def cipNormalizeConfigurationOfResolved (m : MultiCenterMolecule V) (_ : m.ResolvedAllCIP)
    (cfg : m.Configuration) : m.Configuration :=
  m.cipNormalizeConfiguration cfg

/-- Cycle-cut CIP-normalize a configuration with an explicit all-centers-resolved certificate. -/
def cipNormalizeConfigurationCycleCutOfResolved
    (m : MultiCenterMolecule V) (_ : m.ResolvedAllCIPCycleCut)
    (cfg : m.Configuration) : m.Configuration :=
  m.cipNormalizeConfigurationCycleCut cfg

/-- CIP-normalized handedness signs with an explicit all-centers-resolved certificate. -/
abbrev cipConfigurationSignOfResolved (m : MultiCenterMolecule V) (_ : m.ResolvedAllCIP)
    (cfg : m.Configuration) : m.SignPattern :=
  m.cipConfigurationSign cfg

/-- Cycle-cut CIP-normalized handedness signs with an explicit all-centers-resolved certificate. -/
abbrev cipConfigurationSignCycleCutOfResolved
    (m : MultiCenterMolecule V) (_ : m.ResolvedAllCIPCycleCut)
    (cfg : m.Configuration) : m.SignPattern :=
  m.cipConfigurationSignCycleCut cfg

/-- Safe CIP normalization: returns `none` unless every distinguished center has resolved CIP
priorities. -/
noncomputable def cipNormalizeConfiguration? (m : MultiCenterMolecule V)
    (cfg : m.Configuration) : Option m.Configuration :=
  by
    classical
    exact
      if h : m.AllCentersResolvedByCIP then
        some (m.cipNormalizeConfigurationOfResolved ⟨h⟩ cfg)
      else
        none

/-- Safe cycle-cut CIP normalization: returns `none` unless every distinguished center has
resolved cycle-cut CIP priorities. -/
noncomputable def cipNormalizeConfigurationCycleCut? (m : MultiCenterMolecule V)
    (cfg : m.Configuration) : Option m.Configuration :=
  by
    classical
    exact
      if h : m.AllCentersResolvedByCIPCycleCut then
        some (m.cipNormalizeConfigurationCycleCutOfResolved ⟨h⟩ cfg)
      else
        none

/-- Safe CIP-normalized handedness signs: returns `none` unless every distinguished center has
resolved CIP priorities. -/
noncomputable def cipConfigurationSign? (m : MultiCenterMolecule V)
    (cfg : m.Configuration) : Option m.SignPattern :=
  by
    classical
    exact
      if h : m.AllCentersResolvedByCIP then
        some (m.cipConfigurationSignOfResolved ⟨h⟩ cfg)
      else
        none

/-- Safe cycle-cut CIP-normalized handedness signs: returns `none` unless every distinguished
center has resolved cycle-cut CIP priorities. -/
noncomputable def cipConfigurationSignCycleCut? (m : MultiCenterMolecule V)
    (cfg : m.Configuration) : Option m.SignPattern :=
  by
    classical
    exact
      if h : m.AllCentersResolvedByCIPCycleCut then
        some (m.cipConfigurationSignCycleCutOfResolved ⟨h⟩ cfg)
      else
        none

theorem cipNormalizeConfiguration?_eq_some_of_allCentersResolvedByCIP
    (m : MultiCenterMolecule V) (h : m.AllCentersResolvedByCIP) (cfg : m.Configuration) :
    m.cipNormalizeConfiguration? cfg = some (m.cipNormalizeConfiguration cfg) := by
  classical
  simp [cipNormalizeConfiguration?, h, cipNormalizeConfigurationOfResolved]

theorem cipNormalizeConfiguration?_eq_none_of_not_allCentersResolvedByCIP
    (m : MultiCenterMolecule V) (h : ¬ m.AllCentersResolvedByCIP) (cfg : m.Configuration) :
    m.cipNormalizeConfiguration? cfg = none := by
  classical
  change
    (if h' : m.AllCentersResolvedByCIP then
      some (m.cipNormalizeConfigurationOfResolved ⟨h'⟩ cfg)
    else
      none) = none
  rw [dif_neg h]

theorem cipNormalizeConfigurationCycleCut?_eq_some_of_allCentersResolvedByCIPCycleCut
    (m : MultiCenterMolecule V) (h : m.AllCentersResolvedByCIPCycleCut)
    (cfg : m.Configuration) :
    m.cipNormalizeConfigurationCycleCut? cfg =
      some (m.cipNormalizeConfigurationCycleCut cfg) := by
  classical
  simp [cipNormalizeConfigurationCycleCut?, h, cipNormalizeConfigurationCycleCutOfResolved]

theorem cipNormalizeConfigurationCycleCut?_eq_none_of_not_allCentersResolvedByCIPCycleCut
    (m : MultiCenterMolecule V) (h : ¬ m.AllCentersResolvedByCIPCycleCut)
    (cfg : m.Configuration) :
    m.cipNormalizeConfigurationCycleCut? cfg = none := by
  classical
  change
    (if h' : m.AllCentersResolvedByCIPCycleCut then
      some (m.cipNormalizeConfigurationCycleCutOfResolved ⟨h'⟩ cfg)
    else
      none) = none
  rw [dif_neg h]

theorem cipConfigurationSign?_eq_some_of_allCentersResolvedByCIP
    (m : MultiCenterMolecule V) (h : m.AllCentersResolvedByCIP) (cfg : m.Configuration) :
    m.cipConfigurationSign? cfg = some (m.cipConfigurationSign cfg) := by
  classical
  simp [cipConfigurationSign?, h]

theorem cipConfigurationSign?_eq_none_of_not_allCentersResolvedByCIP
    (m : MultiCenterMolecule V) (h : ¬ m.AllCentersResolvedByCIP) (cfg : m.Configuration) :
    m.cipConfigurationSign? cfg = none := by
  classical
  change
    (if h' : m.AllCentersResolvedByCIP then
      some (m.cipConfigurationSignOfResolved ⟨h'⟩ cfg)
    else
      none) = none
  rw [dif_neg h]

theorem cipConfigurationSignCycleCut?_eq_some_of_allCentersResolvedByCIPCycleCut
    (m : MultiCenterMolecule V) (h : m.AllCentersResolvedByCIPCycleCut)
    (cfg : m.Configuration) :
    m.cipConfigurationSignCycleCut? cfg = some (m.cipConfigurationSignCycleCut cfg) := by
  classical
  simp [cipConfigurationSignCycleCut?, h]

theorem cipConfigurationSignCycleCut?_eq_none_of_not_allCentersResolvedByCIPCycleCut
    (m : MultiCenterMolecule V) (h : ¬ m.AllCentersResolvedByCIPCycleCut)
    (cfg : m.Configuration) :
    m.cipConfigurationSignCycleCut? cfg = none := by
  classical
  change
    (if h' : m.AllCentersResolvedByCIPCycleCut then
      some (m.cipConfigurationSignCycleCutOfResolved ⟨h'⟩ cfg)
    else
      none) = none
  rw [dif_neg h]

/-! ### Preferred descriptor-facing aliases -/

/-- Descriptor-facing local CIP key at a distinguished center. -/
abbrev cipKeyDescriptorAt (m : MultiCenterMolecule V) (c : m.Center) (i : Fin 4) :
    List MoleculeGraph.AtomLabel :=
  m.cipKeyCycleCutAt c i

/-- Descriptor-facing local CIP-stereogenicity at a distinguished center. -/
abbrev StereogenicByCIPDescriptorAt (m : MultiCenterMolecule V) (c : m.Center) : Prop :=
  m.StereogenicByCIPCycleCutAt c

/-- Descriptor-facing resolved local CIP priorities at a distinguished center. -/
abbrev ResolvedCIPDescriptorAt (m : MultiCenterMolecule V) (c : m.Center) : Prop :=
  m.ResolvedCIPCycleCutAt c

/-- Descriptor-facing all-centers resolved CIP priorities. -/
abbrev AllCentersResolvedByCIPDescriptor (m : MultiCenterMolecule V) : Prop :=
  m.AllCentersResolvedByCIPCycleCut

/-- Descriptor-facing bundled all-centers-resolved certificate. -/
abbrev ResolvedAllCIPDescriptor (m : MultiCenterMolecule V) : Type _ :=
  m.ResolvedAllCIPCycleCut

/-- Descriptor-facing local CIP order at a distinguished center. -/
abbrev cipOrderDescriptorAt (m : MultiCenterMolecule V) (c : m.Center) : List (Fin 4) :=
  m.cipOrderCycleCutAt c

/-- Descriptor-facing local CIP permutation at a distinguished center. -/
abbrev cipPermutationDescriptorAt (m : MultiCenterMolecule V) (c : m.Center) :
    Equiv.Perm (Fin 4) :=
  m.cipPermutationCycleCutAt c

/-- Descriptor-facing local CIP order with tie refusal. -/
abbrev cipOrderDescriptorAt? (m : MultiCenterMolecule V) (c : m.Center) :
    Option (List (Fin 4)) :=
  m.cipOrderCycleCutAt? c

/-- Descriptor-facing local CIP permutation with tie refusal. -/
abbrev cipPermutationDescriptorAt? (m : MultiCenterMolecule V) (c : m.Center) :
    Option (Equiv.Perm (Fin 4)) :=
  m.cipPermutationCycleCutAt? c

/-- Descriptor-facing CIP-normalized configuration. -/
abbrev cipNormalizeConfigurationDescriptor (m : MultiCenterMolecule V)
    (cfg : m.Configuration) : m.Configuration :=
  m.cipNormalizeConfigurationCycleCut cfg

/-- Descriptor-facing CIP-normalized handedness signs. -/
abbrev cipConfigurationSignDescriptor (m : MultiCenterMolecule V)
    (cfg : m.Configuration) : m.SignPattern :=
  m.cipConfigurationSignCycleCut cfg

/-- Safe descriptor-facing CIP-normalized configuration. -/
abbrev cipNormalizeConfigurationDescriptor? (m : MultiCenterMolecule V)
    (cfg : m.Configuration) : Option m.Configuration :=
  m.cipNormalizeConfigurationCycleCut? cfg

/-- Safe descriptor-facing CIP-normalized handedness signs. -/
abbrev cipConfigurationSignDescriptor? (m : MultiCenterMolecule V)
    (cfg : m.Configuration) : Option m.SignPattern :=
  m.cipConfigurationSignCycleCut? cfg

/-! ### Raw/cycle-cut agreement bridge -/

/-- Raw and cycle-cut local CIP keys agree at a distinguished center. -/
def RawCycleCutKeyAgreementAt (m : MultiCenterMolecule V) (c : m.Center) : Prop :=
  (m.toOneCenterMolecule c).RawCycleCutKeyAgreement

/-- Raw and cycle-cut local CIP keys agree at every distinguished center. -/
abbrev AllCentersRawCycleCutKeyAgreement (m : MultiCenterMolecule V) : Prop :=
  ∀ c : m.Center, m.RawCycleCutKeyAgreementAt c

theorem rawCycleCutKeyAgreementAt_of_treeLike
    (m : MultiCenterMolecule V) (htree : m.mol.TreeLike) (c : m.Center) :
    m.RawCycleCutKeyAgreementAt c := by
  simpa [RawCycleCutKeyAgreementAt, MultiCenterMolecule.toOneCenterMolecule] using
    (m.toOneCenterMolecule c).rawCycleCutKeyAgreement_of_treeLike htree

theorem allCentersRawCycleCutKeyAgreement_of_treeLike
    (m : MultiCenterMolecule V) (htree : m.mol.TreeLike) :
    m.AllCentersRawCycleCutKeyAgreement := by
  intro c
  exact m.rawCycleCutKeyAgreementAt_of_treeLike htree c

theorem cipKeyAt_eq_cipKeyCycleCutAt_of_rawCycleCutKeyAgreementAt
    (m : MultiCenterMolecule V) (c : m.Center) (h : m.RawCycleCutKeyAgreementAt c)
    (i : Fin 4) :
    m.cipKeyAt c i = m.cipKeyCycleCutAt c i := by
  simpa [RawCycleCutKeyAgreementAt, cipKeyAt, cipKeyCycleCutAt] using h i

theorem stereogenicByCIPAt_iff_stereogenicByCIPCycleCutAt_of_rawCycleCutKeyAgreementAt
    (m : MultiCenterMolecule V) (c : m.Center) (h : m.RawCycleCutKeyAgreementAt c) :
    m.StereogenicByCIPAt c ↔ m.StereogenicByCIPCycleCutAt c := by
  simpa [RawCycleCutKeyAgreementAt, StereogenicByCIPAt, StereogenicByCIPCycleCutAt] using
    (m.toOneCenterMolecule c).stereogenicByCIP_iff_stereogenicByCIPCycleCut_of_rawCycleCutKeyAgreement h

theorem resolvedCIPAt_iff_resolvedCIPCycleCutAt_of_rawCycleCutKeyAgreementAt
    (m : MultiCenterMolecule V) (c : m.Center) (h : m.RawCycleCutKeyAgreementAt c) :
    m.ResolvedCIPAt c ↔ m.ResolvedCIPCycleCutAt c :=
  m.stereogenicByCIPAt_iff_stereogenicByCIPCycleCutAt_of_rawCycleCutKeyAgreementAt c h

theorem allCentersResolvedByCIP_iff_allCentersResolvedByCIPCycleCut_of_allCentersRawCycleCutKeyAgreement
    (m : MultiCenterMolecule V) (h : m.AllCentersRawCycleCutKeyAgreement) :
    m.AllCentersResolvedByCIP ↔ m.AllCentersResolvedByCIPCycleCut := by
  constructor
  · intro hres c
    exact
      (m.resolvedCIPAt_iff_resolvedCIPCycleCutAt_of_rawCycleCutKeyAgreementAt c (h c)).1
        (hres c)
  · intro hres c
    exact
      (m.resolvedCIPAt_iff_resolvedCIPCycleCutAt_of_rawCycleCutKeyAgreementAt c (h c)).2
        (hres c)

theorem cipOrderAt_eq_cipOrderCycleCutAt_of_rawCycleCutKeyAgreementAt
    (m : MultiCenterMolecule V) (c : m.Center) (h : m.RawCycleCutKeyAgreementAt c) :
    m.cipOrderAt c = m.cipOrderCycleCutAt c := by
  simpa [RawCycleCutKeyAgreementAt, cipOrderAt, cipOrderCycleCutAt] using
    (m.toOneCenterMolecule c).cipOrder_eq_cipOrderCycleCut_of_rawCycleCutKeyAgreement h

theorem cipPermutationAt_eq_cipPermutationCycleCutAt_of_rawCycleCutKeyAgreementAt
    (m : MultiCenterMolecule V) (c : m.Center) (h : m.RawCycleCutKeyAgreementAt c) :
    m.cipPermutationAt c = m.cipPermutationCycleCutAt c := by
  simpa [RawCycleCutKeyAgreementAt, cipPermutationAt, cipPermutationCycleCutAt] using
    (m.toOneCenterMolecule c).cipPermutation_eq_cipPermutationCycleCut_of_rawCycleCutKeyAgreement h

theorem cipNormalizeConfiguration_eq_cipNormalizeConfigurationCycleCut_of_allCentersRawCycleCutKeyAgreement
    (m : MultiCenterMolecule V) (h : m.AllCentersRawCycleCutKeyAgreement)
    (cfg : m.Configuration) :
    m.cipNormalizeConfiguration cfg = m.cipNormalizeConfigurationCycleCut cfg := by
  funext c
  simp [cipNormalizeConfiguration, cipNormalizeConfigurationCycleCut,
    m.cipPermutationAt_eq_cipPermutationCycleCutAt_of_rawCycleCutKeyAgreementAt c (h c)]

theorem cipConfigurationSign_eq_cipConfigurationSignCycleCut_of_allCentersRawCycleCutKeyAgreement
    (m : MultiCenterMolecule V) (h : m.AllCentersRawCycleCutKeyAgreement)
    (cfg : m.Configuration) :
    m.cipConfigurationSign cfg = m.cipConfigurationSignCycleCut cfg := by
  funext c
  simp [m.cipPermutationAt_eq_cipPermutationCycleCutAt_of_rawCycleCutKeyAgreementAt c (h c)]

theorem cipKeyAt_eq_cipKeyCycleCutAt_of_treeLike
    (m : MultiCenterMolecule V) (htree : m.mol.TreeLike) (c : m.Center) (i : Fin 4) :
    m.cipKeyAt c i = m.cipKeyCycleCutAt c i :=
  m.cipKeyAt_eq_cipKeyCycleCutAt_of_rawCycleCutKeyAgreementAt c
    (m.rawCycleCutKeyAgreementAt_of_treeLike htree c) i

theorem stereogenicByCIPAt_iff_stereogenicByCIPCycleCutAt_of_treeLike
    (m : MultiCenterMolecule V) (htree : m.mol.TreeLike) (c : m.Center) :
    m.StereogenicByCIPAt c ↔ m.StereogenicByCIPCycleCutAt c :=
  m.stereogenicByCIPAt_iff_stereogenicByCIPCycleCutAt_of_rawCycleCutKeyAgreementAt c
    (m.rawCycleCutKeyAgreementAt_of_treeLike htree c)

theorem allCentersResolvedByCIP_iff_allCentersResolvedByCIPCycleCut_of_treeLike
    (m : MultiCenterMolecule V) (htree : m.mol.TreeLike) :
    m.AllCentersResolvedByCIP ↔ m.AllCentersResolvedByCIPCycleCut :=
  m.allCentersResolvedByCIP_iff_allCentersResolvedByCIPCycleCut_of_allCentersRawCycleCutKeyAgreement
    (m.allCentersRawCycleCutKeyAgreement_of_treeLike htree)

theorem cipOrderAt_eq_cipOrderCycleCutAt_of_treeLike
    (m : MultiCenterMolecule V) (htree : m.mol.TreeLike) (c : m.Center) :
    m.cipOrderAt c = m.cipOrderCycleCutAt c :=
  m.cipOrderAt_eq_cipOrderCycleCutAt_of_rawCycleCutKeyAgreementAt c
    (m.rawCycleCutKeyAgreementAt_of_treeLike htree c)

theorem cipPermutationAt_eq_cipPermutationCycleCutAt_of_treeLike
    (m : MultiCenterMolecule V) (htree : m.mol.TreeLike) (c : m.Center) :
    m.cipPermutationAt c = m.cipPermutationCycleCutAt c :=
  m.cipPermutationAt_eq_cipPermutationCycleCutAt_of_rawCycleCutKeyAgreementAt c
    (m.rawCycleCutKeyAgreementAt_of_treeLike htree c)

theorem cipNormalizeConfiguration_eq_cipNormalizeConfigurationCycleCut_of_treeLike
    (m : MultiCenterMolecule V) (htree : m.mol.TreeLike)
    (cfg : m.Configuration) :
    m.cipNormalizeConfiguration cfg = m.cipNormalizeConfigurationCycleCut cfg :=
  m.cipNormalizeConfiguration_eq_cipNormalizeConfigurationCycleCut_of_allCentersRawCycleCutKeyAgreement
    (m.allCentersRawCycleCutKeyAgreement_of_treeLike htree) cfg

theorem cipConfigurationSign_eq_cipConfigurationSignCycleCut_of_treeLike
    (m : MultiCenterMolecule V) (htree : m.mol.TreeLike)
    (cfg : m.Configuration) :
    m.cipConfigurationSign cfg = m.cipConfigurationSignCycleCut cfg :=
  m.cipConfigurationSign_eq_cipConfigurationSignCycleCut_of_allCentersRawCycleCutKeyAgreement
    (m.allCentersRawCycleCutKeyAgreement_of_treeLike htree) cfg

theorem cipOrderAt?_eq_cipOrderCycleCutAt?_of_rawCycleCutKeyAgreementAt
    (m : MultiCenterMolecule V) (c : m.Center) (h : m.RawCycleCutKeyAgreementAt c) :
    m.cipOrderAt? c = m.cipOrderCycleCutAt? c := by
  classical
  have hresolved := m.resolvedCIPAt_iff_resolvedCIPCycleCutAt_of_rawCycleCutKeyAgreementAt c h
  by_cases hr : m.ResolvedCIPAt c
  · have hrc : m.ResolvedCIPCycleCutAt c := hresolved.1 hr
    simp [cipOrderAt?, cipOrderCycleCutAt?, hr, hrc,
      m.cipOrderAt_eq_cipOrderCycleCutAt_of_rawCycleCutKeyAgreementAt c h]
  · have hrc : ¬ m.ResolvedCIPCycleCutAt c := by
      intro hrc
      exact hr (hresolved.2 hrc)
    simp [cipOrderAt?, cipOrderCycleCutAt?, hr, hrc]

theorem cipPermutationAt?_eq_cipPermutationCycleCutAt?_of_rawCycleCutKeyAgreementAt
    (m : MultiCenterMolecule V) (c : m.Center) (h : m.RawCycleCutKeyAgreementAt c) :
    m.cipPermutationAt? c = m.cipPermutationCycleCutAt? c := by
  classical
  have hresolved := m.resolvedCIPAt_iff_resolvedCIPCycleCutAt_of_rawCycleCutKeyAgreementAt c h
  by_cases hr : m.ResolvedCIPAt c
  · have hrc : m.ResolvedCIPCycleCutAt c := hresolved.1 hr
    simp [cipPermutationAt?, cipPermutationCycleCutAt?, hr, hrc,
      m.cipPermutationAt_eq_cipPermutationCycleCutAt_of_rawCycleCutKeyAgreementAt c h]
  · have hrc : ¬ m.ResolvedCIPCycleCutAt c := by
      intro hrc
      exact hr (hresolved.2 hrc)
    simp [cipPermutationAt?, cipPermutationCycleCutAt?, hr, hrc]

theorem cipOrderAt?_eq_cipOrderCycleCutAt?_of_treeLike
    (m : MultiCenterMolecule V) (htree : m.mol.TreeLike) (c : m.Center) :
    m.cipOrderAt? c = m.cipOrderCycleCutAt? c :=
  m.cipOrderAt?_eq_cipOrderCycleCutAt?_of_rawCycleCutKeyAgreementAt c
    (m.rawCycleCutKeyAgreementAt_of_treeLike htree c)

theorem cipPermutationAt?_eq_cipPermutationCycleCutAt?_of_treeLike
    (m : MultiCenterMolecule V) (htree : m.mol.TreeLike) (c : m.Center) :
    m.cipPermutationAt? c = m.cipPermutationCycleCutAt? c :=
  m.cipPermutationAt?_eq_cipPermutationCycleCutAt?_of_rawCycleCutKeyAgreementAt c
    (m.rawCycleCutKeyAgreementAt_of_treeLike htree c)

theorem cipNormalizeConfiguration?_eq_cipNormalizeConfigurationCycleCut?_of_allCentersRawCycleCutKeyAgreement
    (m : MultiCenterMolecule V) (h : m.AllCentersRawCycleCutKeyAgreement)
    (cfg : m.Configuration) :
    m.cipNormalizeConfiguration? cfg = m.cipNormalizeConfigurationCycleCut? cfg := by
  classical
  have hresolved :=
    m.allCentersResolvedByCIP_iff_allCentersResolvedByCIPCycleCut_of_allCentersRawCycleCutKeyAgreement h
  by_cases hr : m.AllCentersResolvedByCIP
  · have hrc : m.AllCentersResolvedByCIPCycleCut := hresolved.1 hr
    simp [cipNormalizeConfiguration?, cipNormalizeConfigurationCycleCut?, hr, hrc,
      cipNormalizeConfigurationOfResolved, cipNormalizeConfigurationCycleCutOfResolved,
      m.cipNormalizeConfiguration_eq_cipNormalizeConfigurationCycleCut_of_allCentersRawCycleCutKeyAgreement
        h cfg]
  · have hrc : ¬ m.AllCentersResolvedByCIPCycleCut := by
      intro hrc
      exact hr (hresolved.2 hrc)
    rw [m.cipNormalizeConfiguration?_eq_none_of_not_allCentersResolvedByCIP hr cfg]
    rw [m.cipNormalizeConfigurationCycleCut?_eq_none_of_not_allCentersResolvedByCIPCycleCut hrc cfg]

theorem cipConfigurationSign?_eq_cipConfigurationSignCycleCut?_of_allCentersRawCycleCutKeyAgreement
    (m : MultiCenterMolecule V) (h : m.AllCentersRawCycleCutKeyAgreement)
    (cfg : m.Configuration) :
    m.cipConfigurationSign? cfg = m.cipConfigurationSignCycleCut? cfg := by
  classical
  have hresolved :=
    m.allCentersResolvedByCIP_iff_allCentersResolvedByCIPCycleCut_of_allCentersRawCycleCutKeyAgreement h
  by_cases hr : m.AllCentersResolvedByCIP
  · have hrc : m.AllCentersResolvedByCIPCycleCut := hresolved.1 hr
    simp [cipConfigurationSign?, cipConfigurationSignCycleCut?, hr, hrc,
      m.cipConfigurationSign_eq_cipConfigurationSignCycleCut_of_allCentersRawCycleCutKeyAgreement
        h cfg]
  · have hrc : ¬ m.AllCentersResolvedByCIPCycleCut := by
      intro hrc
      exact hr (hresolved.2 hrc)
    rw [m.cipConfigurationSign?_eq_none_of_not_allCentersResolvedByCIP hr cfg]
    rw [m.cipConfigurationSignCycleCut?_eq_none_of_not_allCentersResolvedByCIPCycleCut hrc cfg]

theorem cipNormalizeConfiguration?_eq_cipNormalizeConfigurationCycleCut?_of_treeLike
    (m : MultiCenterMolecule V) (htree : m.mol.TreeLike)
    (cfg : m.Configuration) :
    m.cipNormalizeConfiguration? cfg = m.cipNormalizeConfigurationCycleCut? cfg :=
  m.cipNormalizeConfiguration?_eq_cipNormalizeConfigurationCycleCut?_of_allCentersRawCycleCutKeyAgreement
    (m.allCentersRawCycleCutKeyAgreement_of_treeLike htree) cfg

theorem cipConfigurationSign?_eq_cipConfigurationSignCycleCut?_of_treeLike
    (m : MultiCenterMolecule V) (htree : m.mol.TreeLike)
    (cfg : m.Configuration) :
    m.cipConfigurationSign? cfg = m.cipConfigurationSignCycleCut? cfg :=
  m.cipConfigurationSign?_eq_cipConfigurationSignCycleCut?_of_allCentersRawCycleCutKeyAgreement
    (m.allCentersRawCycleCutKeyAgreement_of_treeLike htree) cfg

theorem cipNormalizeConfiguration?_eq_cipNormalizeConfigurationDescriptor?_of_treeLike
    (m : MultiCenterMolecule V) (htree : m.mol.TreeLike)
    (cfg : m.Configuration) :
    m.cipNormalizeConfiguration? cfg = m.cipNormalizeConfigurationDescriptor? cfg :=
  m.cipNormalizeConfiguration?_eq_cipNormalizeConfigurationCycleCut?_of_treeLike htree cfg

theorem cipConfigurationSign?_eq_cipConfigurationSignDescriptor?_of_treeLike
    (m : MultiCenterMolecule V) (htree : m.mol.TreeLike)
    (cfg : m.Configuration) :
    m.cipConfigurationSign? cfg = m.cipConfigurationSignDescriptor? cfg :=
  m.cipConfigurationSign?_eq_cipConfigurationSignCycleCut?_of_treeLike htree cfg

/-- The CIP key of a ligand is invariant under a multi-center automorphism, after transporting the
center and ligand index appropriately. -/
theorem cipKeyAt_eq_cipKeyAt_ligandPermAt (m : MultiCenterMolecule V) (e : m.Aut) (c : m.Center) (i : Fin 4) :
    m.cipKeyAt (m.centerPerm e c) (m.ligandPermAt e c i) = m.cipKeyAt c i := by
  classical
  -- Package `e` as a graph automorphism.
  let eMol : m.mol.Aut := ⟨(e : Equiv.Perm V), MultiCenterMolecule.Aut.mem_molAut (m := m) e⟩
  have hZ : ∀ v, m.mol.atomZ ((e : Equiv.Perm V) v) = m.mol.atomZ v := by
    intro v
    exact MoleculeGraph.Aut.atomZ_eq (m := m.mol) eMol v
  have hMass : ∀ v, m.mol.atomMass ((e : Equiv.Perm V) v) = m.mol.atomMass v := by
    intro v
    exact MoleculeGraph.Aut.atomMass_eq (m := m.mol) eMol v
  have hBond : ∀ u v, m.mol.bond ((e : Equiv.Perm V) u) ((e : Equiv.Perm V) v) = m.mol.bond u v := by
    intro u v
    exact MoleculeGraph.Aut.bond_eq (m := m.mol) eMol u v

  have hlig :
      m.ligandAtomAt (m.centerPerm e c) (m.ligandPermAt e c i) =
        (e : Equiv.Perm V) (m.ligandAtomAt c i) := by
    simp

  have hkey :
      MoleculeGraph.cipKeyFrom m.mol ((e : Equiv.Perm V) c.1) ((e : Equiv.Perm V) (m.ligandAtomAt c i)) =
        MoleculeGraph.cipKeyFrom m.mol c.1 (m.ligandAtomAt c i) := by
    simpa using
      (MoleculeGraph.cipKeyFrom_eq_of_preserves (m := m.mol) (e := (e : Equiv.Perm V))
        (hZ := hZ) (hMass := hMass) (hBond := hBond) (center := c.1) (start := m.ligandAtomAt c i))

  -- Unfold `cipKeyAt` and rewrite by the transported ligand and center.
  dsimp [MultiCenterMolecule.cipKeyAt, OneCenterMolecule.cipKey, MultiCenterMolecule.toOneCenterMolecule]
  simpa [hlig] using hkey

/-- The cycle-cut CIP key of a ligand is invariant under a multi-center automorphism, after
transporting the center and ligand index appropriately. -/
theorem cipKeyCycleCutAt_eq_cipKeyCycleCutAt_ligandPermAt
    (m : MultiCenterMolecule V) (e : m.Aut) (c : m.Center) (i : Fin 4) :
    m.cipKeyCycleCutAt (m.centerPerm e c) (m.ligandPermAt e c i) =
      m.cipKeyCycleCutAt c i := by
  classical
  let eMol : m.mol.Aut := ⟨(e : Equiv.Perm V), MultiCenterMolecule.Aut.mem_molAut (m := m) e⟩
  have hZ : ∀ v, m.mol.atomZ ((e : Equiv.Perm V) v) = m.mol.atomZ v := by
    intro v
    exact MoleculeGraph.Aut.atomZ_eq (m := m.mol) eMol v
  have hMass : ∀ v, m.mol.atomMass ((e : Equiv.Perm V) v) = m.mol.atomMass v := by
    intro v
    exact MoleculeGraph.Aut.atomMass_eq (m := m.mol) eMol v
  have hBond : ∀ u v, m.mol.bond ((e : Equiv.Perm V) u) ((e : Equiv.Perm V) v) = m.mol.bond u v := by
    intro u v
    exact MoleculeGraph.Aut.bond_eq (m := m.mol) eMol u v

  have hlig :
      m.ligandAtomAt (m.centerPerm e c) (m.ligandPermAt e c i) =
        (e : Equiv.Perm V) (m.ligandAtomAt c i) := by
    simp

  have hkey :
      MoleculeGraph.cipKeyFromCycleCut m.mol ((e : Equiv.Perm V) c.1)
          ((e : Equiv.Perm V) (m.ligandAtomAt c i)) =
        MoleculeGraph.cipKeyFromCycleCut m.mol c.1 (m.ligandAtomAt c i) := by
    simpa using
      (MoleculeGraph.cipKeyFromCycleCut_eq_of_preserves (m := m.mol)
        (e := (e : Equiv.Perm V)) (hZ := hZ) (hMass := hMass) (hBond := hBond)
        (center := c.1) (start := m.ligandAtomAt c i))

  dsimp [MultiCenterMolecule.cipKeyCycleCutAt, OneCenterMolecule.cipKeyCycleCut,
    MultiCenterMolecule.toOneCenterMolecule]
  simpa [hlig] using hkey

theorem stereogenicByCIPAt_centerPerm (m : MultiCenterMolecule V) (e : m.Aut) (c : m.Center) :
    m.StereogenicByCIPAt c → m.StereogenicByCIPAt (m.centerPerm e c) := by
  intro hst i j hij
  -- Pull the key equality back along the induced ligand permutation.
  have hi :
      m.cipKeyAt c ((m.ligandPermAt e c)⁻¹ i) = m.cipKeyAt (m.centerPerm e c) i := by
    have h :=
      (m.cipKeyAt_eq_cipKeyAt_ligandPermAt (e := e) (c := c) (i := ((m.ligandPermAt e c)⁻¹ i)))
    simpa using h.symm
  have hj :
      m.cipKeyAt c ((m.ligandPermAt e c)⁻¹ j) = m.cipKeyAt (m.centerPerm e c) j := by
    have h :=
      (m.cipKeyAt_eq_cipKeyAt_ligandPermAt (e := e) (c := c) (i := ((m.ligandPermAt e c)⁻¹ j)))
    simpa using h.symm
  have hij0 : m.cipKeyAt (m.centerPerm e c) i = m.cipKeyAt (m.centerPerm e c) j := by
    simpa [MultiCenterMolecule.cipKeyAt] using hij
  have hij' : m.cipKeyAt c ((m.ligandPermAt e c)⁻¹ i) = m.cipKeyAt c ((m.ligandPermAt e c)⁻¹ j) := by
    simpa [hi.symm, hj.symm] using hij0
  have : (m.ligandPermAt e c)⁻¹ i = (m.ligandPermAt e c)⁻¹ j := hst hij'
  have := congrArg (m.ligandPermAt e c) this
  simpa using this

theorem stereogenicByCIPCycleCutAt_centerPerm
    (m : MultiCenterMolecule V) (e : m.Aut) (c : m.Center) :
    m.StereogenicByCIPCycleCutAt c → m.StereogenicByCIPCycleCutAt (m.centerPerm e c) := by
  intro hst i j hij
  have hi :
      m.cipKeyCycleCutAt c ((m.ligandPermAt e c)⁻¹ i) =
        m.cipKeyCycleCutAt (m.centerPerm e c) i := by
    have h :=
      (m.cipKeyCycleCutAt_eq_cipKeyCycleCutAt_ligandPermAt
        (e := e) (c := c) (i := ((m.ligandPermAt e c)⁻¹ i)))
    simpa using h.symm
  have hj :
      m.cipKeyCycleCutAt c ((m.ligandPermAt e c)⁻¹ j) =
        m.cipKeyCycleCutAt (m.centerPerm e c) j := by
    have h :=
      (m.cipKeyCycleCutAt_eq_cipKeyCycleCutAt_ligandPermAt
        (e := e) (c := c) (i := ((m.ligandPermAt e c)⁻¹ j)))
    simpa using h.symm
  have hij0 :
      m.cipKeyCycleCutAt (m.centerPerm e c) i =
        m.cipKeyCycleCutAt (m.centerPerm e c) j := by
    simpa [MultiCenterMolecule.cipKeyCycleCutAt] using hij
  have hij' :
      m.cipKeyCycleCutAt c ((m.ligandPermAt e c)⁻¹ i) =
        m.cipKeyCycleCutAt c ((m.ligandPermAt e c)⁻¹ j) := by
    simpa [hi.symm, hj.symm] using hij0
  have : (m.ligandPermAt e c)⁻¹ i = (m.ligandPermAt e c)⁻¹ j := hst hij'
  have := congrArg (m.ligandPermAt e c) this
  simpa using this

/-- The CIP permutation transports naturally across a multi-center automorphism, assuming the
source center is CIP-stereogenic. -/
theorem cipPermutationAt_centerPerm_of_stereogenicByCIPAt (m : MultiCenterMolecule V) (e : m.Aut)
    (c : m.Center) (hst : m.StereogenicByCIPAt c) :
    m.cipPermutationAt (m.centerPerm e c) = m.ligandPermAt e c * m.cipPermutationAt c := by
  classical
  let c' : m.Center := m.centerPerm e c
  let π : Equiv.Perm (Fin 4) := m.ligandPermAt e c
  let m₀ : OneCenterMolecule V := m.toOneCenterMolecule c
  let m₁ : OneCenterMolecule V := m.toOneCenterMolecule c'

  have hkey : ∀ i : Fin 4, (m₁.reindex π).cipKey i = m₀.cipKey i := by
    intro i
    have h :=
      m.cipKeyAt_eq_cipKeyAt_ligandPermAt (e := e) (c := c) (i := i)
    -- `cipKey_reindex` turns the LHS into `cipKey` at index `π i`.
    simpa [m₀, m₁, c', π, MultiCenterMolecule.cipKeyAt] using
      (show (m₁.reindex π).cipKey i = m₁.cipKey (π i) from by simp [OneCenterMolecule.cipKey_reindex]).trans h

  have hcmp :
      (fun i j => decide ((m₁.reindex π).cipKeyWithTie j ≤ (m₁.reindex π).cipKeyWithTie i)) =
        fun i j => decide (m₀.cipKeyWithTie j ≤ m₀.cipKeyWithTie i) := by
    funext i j
    have hi : (m₁.reindex π).cipKeyWithTie i = m₀.cipKeyWithTie i := by
      simp [OneCenterMolecule.cipKeyWithTie, hkey i]
    have hj : (m₁.reindex π).cipKeyWithTie j = m₀.cipKeyWithTie j := by
      simp [OneCenterMolecule.cipKeyWithTie, hkey j]
    simp [hi, hj]

  have horder : (m₁.reindex π).cipOrder = m₀.cipOrder := by
    simp [OneCenterMolecule.cipOrder, hcmp]

  have hpermTransport : (m₁.reindex π).cipPermutation = m₀.cipPermutation := by
    ext i
    simp [OneCenterMolecule.cipPermutation, horder, List.get_eq_getElem]

  have hst₁ : m₁.StereogenicByCIP := m.stereogenicByCIPAt_centerPerm (e := e) (c := c) hst

  have hreindex : (m₁.reindex π).cipPermutation = π⁻¹ * m₁.cipPermutation :=
    m₁.cipPermutation_reindex_of_stereogenicByCIP (hst := hst₁) π

  have hEq : m₀.cipPermutation = π⁻¹ * m₁.cipPermutation := by
    simpa [hpermTransport] using hreindex
  have hfinal : π * m₀.cipPermutation = m₁.cipPermutation := by
    have := congrArg (fun x => π * x) hEq
    simpa [mul_assoc] using this

  -- Unfold back to the multi-center definitions.
  dsimp [MultiCenterMolecule.cipPermutationAt, MultiCenterMolecule.toOneCenterMolecule, c', π, m₀, m₁] at hfinal ⊢
  simpa using hfinal.symm

/-- The cycle-cut CIP permutation transports naturally across a multi-center automorphism,
assuming the source center is cycle-cut CIP-stereogenic. -/
theorem cipPermutationCycleCutAt_centerPerm_of_stereogenicByCIPCycleCutAt
    (m : MultiCenterMolecule V) (e : m.Aut) (c : m.Center)
    (hst : m.StereogenicByCIPCycleCutAt c) :
    m.cipPermutationCycleCutAt (m.centerPerm e c) =
      m.ligandPermAt e c * m.cipPermutationCycleCutAt c := by
  classical
  let c' : m.Center := m.centerPerm e c
  let π : Equiv.Perm (Fin 4) := m.ligandPermAt e c
  let m₀ : OneCenterMolecule V := m.toOneCenterMolecule c
  let m₁ : OneCenterMolecule V := m.toOneCenterMolecule c'

  have hkey : ∀ i : Fin 4, (m₁.reindex π).cipKeyCycleCut i = m₀.cipKeyCycleCut i := by
    intro i
    have h :=
      m.cipKeyCycleCutAt_eq_cipKeyCycleCutAt_ligandPermAt (e := e) (c := c) (i := i)
    simpa [m₀, m₁, c', π, MultiCenterMolecule.cipKeyCycleCutAt] using
      (show (m₁.reindex π).cipKeyCycleCut i = m₁.cipKeyCycleCut (π i) from by
        simp [OneCenterMolecule.cipKeyCycleCut_reindex]).trans h

  have hcmp :
      (fun i j =>
          decide ((m₁.reindex π).cipKeyWithTieCycleCut j ≤
            (m₁.reindex π).cipKeyWithTieCycleCut i)) =
        fun i j => decide (m₀.cipKeyWithTieCycleCut j ≤ m₀.cipKeyWithTieCycleCut i) := by
    funext i j
    have hi : (m₁.reindex π).cipKeyWithTieCycleCut i = m₀.cipKeyWithTieCycleCut i := by
      simp [OneCenterMolecule.cipKeyWithTieCycleCut, hkey i]
    have hj : (m₁.reindex π).cipKeyWithTieCycleCut j = m₀.cipKeyWithTieCycleCut j := by
      simp [OneCenterMolecule.cipKeyWithTieCycleCut, hkey j]
    simp [hi, hj]

  have horder : (m₁.reindex π).cipOrderCycleCut = m₀.cipOrderCycleCut := by
    simp [OneCenterMolecule.cipOrderCycleCut, hcmp]

  have hpermTransport : (m₁.reindex π).cipPermutationCycleCut = m₀.cipPermutationCycleCut := by
    ext i
    simp [OneCenterMolecule.cipPermutationCycleCut, horder, List.get_eq_getElem]

  have hst₁ : m₁.StereogenicByCIPCycleCut :=
    m.stereogenicByCIPCycleCutAt_centerPerm (e := e) (c := c) hst

  have hreindex :
      (m₁.reindex π).cipPermutationCycleCut = π⁻¹ * m₁.cipPermutationCycleCut :=
    m₁.cipPermutationCycleCut_reindex_of_stereogenicByCIPCycleCut (hst := hst₁) π

  have hEq : m₀.cipPermutationCycleCut = π⁻¹ * m₁.cipPermutationCycleCut := by
    simpa [hpermTransport] using hreindex
  have hfinal : π * m₀.cipPermutationCycleCut = m₁.cipPermutationCycleCut := by
    have := congrArg (fun x => π * x) hEq
    simpa [mul_assoc] using this

  dsimp [MultiCenterMolecule.cipPermutationCycleCutAt, MultiCenterMolecule.toOneCenterMolecule,
    c', π, m₀, m₁] at hfinal ⊢
  simpa using hfinal.symm

theorem cipNormalizeConfiguration_smul_of_stereogenicByCIPAt (m : MultiCenterMolecule V)
    (hst : ∀ c : m.Center, m.StereogenicByCIPAt c) (e : m.Aut) (cfg : m.Configuration) (c : m.Center) :
    m.cipNormalizeConfiguration (e • cfg) c =
      m.cipNormalizeConfiguration cfg ((m.centerPerm e)⁻¹ c) := by
  classical
  let pre : m.Center := ((m.centerPerm e)⁻¹ c)
  have hpre : m.centerPerm e pre = c := by
    simp [pre]
  have hperm :
      m.cipPermutationAt c = m.ligandPermAt e pre * m.cipPermutationAt pre := by
    -- Apply the center-transport lemma at `pre`, then rewrite the transported center.
    simpa [hpre, pre] using
      (m.cipPermutationAt_centerPerm_of_stereogenicByCIPAt (e := e) (c := pre) (hst := hst pre))
  -- Unfold the action on configurations and cancel the induced ligand permutation against the transported CIP permutation.
  simp [MultiCenterMolecule.cipNormalizeConfiguration, MultiCenterMolecule.smulConfiguration_apply, pre, hperm, mul_assoc]

theorem cipConfigurationSign_smul_of_stereogenicByCIPAt (m : MultiCenterMolecule V)
    (hst : ∀ c : m.Center, m.StereogenicByCIPAt c) (e : m.Aut) (cfg : m.Configuration) (c : m.Center) :
    m.cipConfigurationSign (e • cfg) c = m.cipConfigurationSign cfg ((m.centerPerm e)⁻¹ c) := by
  -- Reduce to the configuration-level equivariance lemma.
  simpa [MultiCenterMolecule.cipConfigurationSign, MultiCenterMolecule.configurationSign] using
    congrArg permHandedness
      (m.cipNormalizeConfiguration_smul_of_stereogenicByCIPAt (hst := hst) (e := e) (cfg := cfg) c)

theorem cipNormalizeConfigurationCycleCut_smul_of_stereogenicByCIPCycleCutAt
    (m : MultiCenterMolecule V) (hst : ∀ c : m.Center, m.StereogenicByCIPCycleCutAt c)
    (e : m.Aut) (cfg : m.Configuration) (c : m.Center) :
    m.cipNormalizeConfigurationCycleCut (e • cfg) c =
      m.cipNormalizeConfigurationCycleCut cfg ((m.centerPerm e)⁻¹ c) := by
  classical
  let pre : m.Center := ((m.centerPerm e)⁻¹ c)
  have hpre : m.centerPerm e pre = c := by
    simp [pre]
  have hperm :
      m.cipPermutationCycleCutAt c = m.ligandPermAt e pre * m.cipPermutationCycleCutAt pre := by
    simpa [hpre, pre] using
      (m.cipPermutationCycleCutAt_centerPerm_of_stereogenicByCIPCycleCutAt
        (e := e) (c := pre) (hst := hst pre))
  simp [MultiCenterMolecule.cipNormalizeConfigurationCycleCut,
    MultiCenterMolecule.smulConfiguration_apply, pre, hperm, mul_assoc]

theorem cipConfigurationSignCycleCut_smul_of_stereogenicByCIPCycleCutAt
    (m : MultiCenterMolecule V) (hst : ∀ c : m.Center, m.StereogenicByCIPCycleCutAt c)
    (e : m.Aut) (cfg : m.Configuration) (c : m.Center) :
    m.cipConfigurationSignCycleCut (e • cfg) c =
      m.cipConfigurationSignCycleCut cfg ((m.centerPerm e)⁻¹ c) := by
  simpa [MultiCenterMolecule.cipConfigurationSignCycleCut,
    MultiCenterMolecule.configurationSign] using
    congrArg permHandedness
      (m.cipNormalizeConfigurationCycleCut_smul_of_stereogenicByCIPCycleCutAt
        (hst := hst) (e := e) (cfg := cfg) c)

end MultiCenterMolecule

end
end OneCenter
end TetraStereo
