/-
Copyright (c) 2026 TetraStereo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.UnitInterval
import TetraStereo.OneCenter.OrganicStereoRealConfiguration














































set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace OrganicStereoEmbeddedBands

noncomputable section

/-- Euclidean three-space, the ambient space of molecular geometry. -/
abbrev real3 : Type := EuclideanSpace ℝ (Fin 3)

/-- The closed parameter square of a ribbon band.  The first coordinate runs along the
length, the second across the width. -/
abbrev RibbonDomain : Type := unitInterval × unitInterval

/-! ## Explicit seam gluing modes -/

/-- The two possible seam identifications of a ribbon band.  This is gluing data, not a
stereochemical descriptor. -/
inductive SeamMode where
  | untwisted
  | twisted
  deriving DecidableEq, Repr

namespace SeamMode

/-- The explicit width-coordinate identifications used at the seam. -/
def glue : SeamMode → unitInterval → unitInterval
  | untwisted => id
  | twisted => unitInterval.symm

@[simp] theorem glue_untwisted (s : unitInterval) : glue untwisted s = s := rfl

@[simp] theorem glue_twisted (s : unitInterval) :
    glue twisted s = unitInterval.symm s := rfl

theorem glue_involutive (m : SeamMode) : Function.Involutive (glue m) := by
  cases m <;> intro s
  · rfl
  · exact unitInterval.symm_symm s

theorem glue_injective (m : SeamMode) : Function.Injective (glue m) :=
  (glue_involutive m).injective

theorem continuous_glue (m : SeamMode) : Continuous (glue m) := by
  cases m
  · exact continuous_id
  · exact unitInterval.continuous_symm

end SeamMode

/-! ## The exact seam equivalence on the parameter square -/

/-- Exact seam equivalence on the parameter square.  It is the identity relation together
with the two oriented boundary identifications.  In the untwisted mode the last edge point
`(1, s)` is equivalent to the first edge point `(0, s)`; in the twisted mode it is
equivalent to `(0, 1 - s)`.  The third disjunct is the symmetric copy of the second, so the
relation is symmetric by construction. -/
def SeamRel (m : SeamMode) (x y : RibbonDomain) : Prop :=
  x = y ∨
    (x.1 = (1 : unitInterval) ∧ y.1 = (0 : unitInterval) ∧
      y.2 = SeamMode.glue m x.2) ∨
    (y.1 = (1 : unitInterval) ∧ x.1 = (0 : unitInterval) ∧
      x.2 = SeamMode.glue m y.2)

/-- The unit interval has distinct endpoints; used to keep the seam orientation disjoint. -/
theorem one_ne_zero_unitInterval : (1 : unitInterval) ≠ 0 := by
  intro h
  have h' : ((1 : unitInterval) : ℝ) = ((0 : unitInterval) : ℝ) :=
    congrArg Subtype.val h
  norm_num at h'

/-- The unit interval has distinct endpoints; used to keep the seam orientation disjoint. -/
theorem zero_ne_one_unitInterval : (0 : unitInterval) ≠ 1 :=
  fun h => one_ne_zero_unitInterval h.symm

@[simp] theorem seamRel_self (m : SeamMode) (x : RibbonDomain) : SeamRel m x x :=
  Or.inl rfl

/-- The exact seam relation is symmetric. -/
theorem seamRel_symm (m : SeamMode) : Symmetric (SeamRel m) := by
  intro x y h
  rcases h with h | ⟨hx1, hy1, hy2⟩ | ⟨hy1, hx1, hx2⟩
  · exact Or.inl h.symm
  · exact Or.inr (Or.inr ⟨hx1, hy1, hy2⟩)
  · exact Or.inr (Or.inl ⟨hy1, hx1, hx2⟩)

/-- The exact seam relation is transitive.  The only a priori dangerous chains would
identify a first-edge point with the last edge and back while flipping the width twice; the
explicit involution `SeamMode.glue` makes such a chain collapse to equality. -/
theorem seamRel_trans (m : SeamMode) : Transitive (SeamRel m) := by
  intro x y z hxy hyz
  rcases hxy with rfl | ⟨hx1, hy1, hy2⟩ | ⟨hy1, hx1, hx2⟩
  · exact hyz
  · rcases hyz with rfl | ⟨hy1', hz1, hz2⟩ | ⟨hz1, hy1', hy2'⟩
    · exact Or.inr (Or.inl ⟨hx1, hy1, hy2⟩)
    · exact absurd (hy1.symm.trans hy1') zero_ne_one_unitInterval
    · have hxz : x.2 = z.2 :=
        SeamMode.glue_injective m (hy2.symm.trans hy2')
      exact Or.inl (Prod.ext (hx1.trans hz1.symm) hxz)
  · rcases hyz with rfl | ⟨hy1', hz1, hz2⟩ | ⟨hz1, hy1', hy2'⟩
    · exact Or.inr (Or.inr ⟨hy1, hx1, hx2⟩)
    · exact Or.inl (Prod.ext (hx1.trans hz1.symm) (hx2.trans hz2.symm))
    · exact absurd (hy1.symm.trans hy1') one_ne_zero_unitInterval

/-- The exact seam relation is an equivalence relation. -/
theorem seamRel_equivalence (m : SeamMode) : Equivalence (SeamRel m) where
  refl := seamRel_self m
  symm := fun {_ _} h => seamRel_symm m h
  trans := fun {_ _ _} h₁ h₂ => seamRel_trans m h₁ h₂

/-- A strip map is embedded *modulo the exact seam equivalence* when equal strip images force
seam-related parameters.  This is the correct embeddedness predicate for a band: full
injectivity on the parameter square is impossible because the seam identifies distinct
endpoint points (`Band.not_injective_strip`). -/
def InjectiveModuloSeam (m : SeamMode) (strip : RibbonDomain → real3) : Prop :=
  ∀ x y : RibbonDomain, strip x = strip y → SeamRel m x y

/-- The requested untwisted gluing: the last edge point `(1, s)` is the first edge point
`(0, s)`. -/
theorem seamRel_untwisted_edges (s : unitInterval) :
    SeamRel SeamMode.untwisted
      ((1 : unitInterval), s) ((0 : unitInterval), s) :=
  Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)

/-- The requested twisted gluing: the last edge point `(1, s)` is the first edge point
`(0, 1 - s)`. -/
theorem seamRel_twisted_edges (s : unitInterval) :
    SeamRel SeamMode.twisted
      ((1 : unitInterval), s) ((0 : unitInterval), unitInterval.symm s) :=
  Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)

/-! ## Embedded bands as typed surface data -/

/-- An embedded ribbon band.  It retains the full continuous strip map, its exact seam
gluing, and the proof that the only identifications it makes are the seam identifications.
-/
structure Band where
  /-- Explicit seam gluing mode (untwisted or twisted). -/
  mode : SeamMode
  /-- The continuous strip map on the parameter square. -/
  strip : RibbonDomain → real3
  /-- Continuity of the strip map. -/
  continuous_strip : Continuous strip
  /-- Exact seam gluing of the two length edges. -/
  seam : ∀ s : unitInterval,
    strip ((1 : unitInterval), s) = strip ((0 : unitInterval), SeamMode.glue mode s)
  /-- The strip is injective modulo the exact seam equivalence. -/
  injective_mod_seam : ∀ x y : RibbonDomain, strip x = strip y → SeamRel mode x y

namespace Band

@[ext] theorem ext {G H : Band} (hmode : G.mode = H.mode) (hstrip : G.strip = H.strip) :
    G = H := by
  cases G
  cases H
  simp_all

/-- The structural modulo-seam injectivity field, restated as the standalone predicate. -/
theorem injectiveModuloSeam (G : Band) : InjectiveModuloSeam G.mode G.strip :=
  G.injective_mod_seam

/-- The image of the strip map: every surface point of the band. -/
def surface (G : Band) : Set real3 := Set.range G.strip

@[simp] theorem mem_surface_iff (G : Band) (p : real3) :
    p ∈ G.surface ↔ ∃ x : RibbonDomain, G.strip x = p := Iff.rfl

/-- Seam-related parameter points have the same strip image.  This is the direction that
uses the explicit gluing and the involution property, not injectivity. -/
theorem strip_seamRel (G : Band) {x y : RibbonDomain} (h : SeamRel G.mode x y) :
    G.strip x = G.strip y := by
  rcases h with h | ⟨hx1, hy1, hy2⟩ | ⟨hy1, hx1, hx2⟩
  · rw [h]
  · have hx : x = ((1 : unitInterval), x.2) := Prod.ext hx1 rfl
    have hy : ((0 : unitInterval), SeamMode.glue G.mode x.2) = y :=
      Prod.ext hy1.symm hy2.symm
    rw [hx, G.seam x.2, hy]
  · have hx : x = ((0 : unitInterval), SeamMode.glue G.mode y.2) := Prod.ext hx1 hx2
    have hy : y = ((1 : unitInterval), y.2) := Prod.ext hy1 rfl
    rw [hx, hy, G.seam y.2]

/-- Modulo the exact seam equivalence, strip images determine seam classes precisely.  This
is the exact embeddedness statement used for bands; it is not full injectivity. -/
theorem strip_eq_iff_seamRel (G : Band) (x y : RibbonDomain) :
    G.strip x = G.strip y ↔ SeamRel G.mode x y :=
  ⟨G.injective_mod_seam x y, G.strip_seamRel⟩

/-- No ribbon band can have an injective strip map on the whole parameter square: the seam
identifies distinct endpoint points.  This is why `InjectiveModuloSeam` is the correct
notion and why full injectivity is never claimed. -/
theorem not_injective_strip (G : Band) : ¬ Function.Injective G.strip := by
  intro hinj
  have hEq : G.strip ((1 : unitInterval), (0 : unitInterval)) =
      G.strip ((0 : unitInterval), SeamMode.glue G.mode 0) := G.seam 0
  have hDom : ((1 : unitInterval), (0 : unitInterval)) =
      ((0 : unitInterval), SeamMode.glue G.mode 0) := hinj hEq
  exact one_ne_zero_unitInterval (congrArg Prod.fst hDom)

/-- The width-`e` curve running along the band (the boundary curve when `e = 0` or `e = 1`). -/
def edgeCurve (G : Band) (e : unitInterval) : unitInterval → real3 :=
  fun x => G.strip (x, e)

/-- In the untwisted mode each width curve closes up across the seam. -/
theorem edgeCurve_untwisted_closed (G : Band) (hmode : G.mode = SeamMode.untwisted)
    (e : unitInterval) : G.edgeCurve e 1 = G.edgeCurve e 0 := by
  have h := G.seam e
  simpa [edgeCurve, hmode] using h

/-- In the twisted mode the edge curve at width `e` continues as the edge curve at width
`1 - e`; this is the half-twist of the boundary, expressed purely as gluing data. -/
theorem edgeCurve_twisted_crosses (G : Band) (hmode : G.mode = SeamMode.twisted)
    (e : unitInterval) :
    G.edgeCurve e 1 = G.edgeCurve (unitInterval.symm e) 0 := by
  have h := G.seam e
  simpa [edgeCurve, hmode] using h

/-- Ambient homeomorphism transport of a band.  It keeps every parameter point and the
explicit seam mode, and reindexes strip images by the ambient homeomorphism. -/
def transport (G : Band) (h : real3 ≃ₜ real3) : Band where
  mode := G.mode
  strip := h ∘ G.strip
  continuous_strip := h.continuous.comp G.continuous_strip
  seam := by
    intro s
    simpa only [Function.comp_apply] using congrArg h (G.seam s)
  injective_mod_seam := by
    intro x y hxy
    exact G.injective_mod_seam x y (h.injective hxy)

@[simp] theorem transport_mode (G : Band) (h : real3 ≃ₜ real3) :
    (G.transport h).mode = G.mode := rfl

@[simp] theorem transport_strip_apply (G : Band) (h : real3 ≃ₜ real3)
    (x : RibbonDomain) : (G.transport h).strip x = h (G.strip x) := rfl

/-- Seam classes are unchanged by ambient transport; this is a definitional identity. -/
theorem transport_seamRel_iff (G : Band) (h : real3 ≃ₜ real3) (x y : RibbonDomain) :
    SeamRel (G.transport h).mode x y ↔ SeamRel G.mode x y :=
  Iff.rfl

/-- Ambient transport keeps the whole band surface, transported as a set. -/
theorem surface_transport (G : Band) (h : real3 ≃ₜ real3) :
    (G.transport h).surface = h '' G.surface := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨G.strip x, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨q, ⟨x, rfl⟩, hq⟩
    exact ⟨x, by rw [transport_strip_apply]; exact hq⟩

/-- Two ambient homeomorphisms compose under transport. -/
theorem transport_transport (G : Band) (h k : real3 ≃ₜ real3) :
    (G.transport h).transport k = G.transport (h.trans k) := by
  apply Band.ext
  · rfl
  · funext x
    rfl

/-- Transport by the identity homeomorphism is the identity on bands. -/
theorem transport_refl (G : Band) :
    G.transport (Homeomorph.refl real3) = G := by
  apply Band.ext
  · rfl
  · funext x
    rfl

end Band

/-! ## Source-indexed attachment with exact positions -/

/-- A source-indexed attachment of a band to real atom / interaction positions.  The
agreement field is what prevents decorative payloads: the parameter point attached to a
source index maps to exactly the supplied position of that source. -/
structure SourceAttachingCore (G : Band) (ι : Type*) [Fintype ι] where
  /-- Supplied real position for each source index. -/
  sourcePosition : ι → real3
  /-- Parameter point on the band attached to each source index. -/
  attachment : ι → RibbonDomain
  /-- Positional agreement between the surface and the source. -/
  agreement : ∀ i : ι, G.strip (attachment i) = sourcePosition i

namespace SourceAttachingCore

variable {G : Band} {ι : Type*} [Fintype ι]

/-- Every attached source position really lies on the band surface. -/
theorem sourcePosition_mem_surface (src : SourceAttachingCore G ι) (i : ι) :
    src.sourcePosition i ∈ G.surface :=
  ⟨src.attachment i, src.agreement i⟩

/-- Distinct source positions correspond exactly to non-seam-related attachment points. -/
theorem source_eq_iff (src : SourceAttachingCore G ι) (i j : ι) :
    src.sourcePosition i = src.sourcePosition j ↔
      SeamRel G.mode (src.attachment i) (src.attachment j) := by
  rw [← src.agreement i, ← src.agreement j]
  exact Band.strip_eq_iff_seamRel G (src.attachment i) (src.attachment j)

/-- Transport an attachment along an ambient homeomorphism; the parameter points stay the
same and the source positions are moved by the homeomorphism. -/
def transport (h : real3 ≃ₜ real3) (src : SourceAttachingCore G ι) :
    SourceAttachingCore (G.transport h) ι where
  sourcePosition := h ∘ src.sourcePosition
  attachment := src.attachment
  agreement := by
    intro i
    simp only [Function.comp_apply, Band.transport_strip_apply, src.agreement i]

@[simp] theorem transport_sourcePosition (h : real3 ≃ₜ real3)
    (src : SourceAttachingCore G ι) (i : ι) :
    (src.transport h).sourcePosition i = h (src.sourcePosition i) := rfl

@[simp] theorem transport_attachment (h : real3 ≃ₜ real3)
    (src : SourceAttachingCore G ι) (i : ι) :
    (src.transport h).attachment i = src.attachment i := rfl

end SourceAttachingCore

/-! ## The complete encoding of a supplied band, with left inverse -/

/-- A complete representation of a supplied band together with a finite source attachment.
It retains every surface point, the exact seam gluing, and all source positions. -/
structure BandRecord (ι : Type*) [Fintype ι] where
  /-- Explicit seam gluing mode. -/
  mode : SeamMode
  /-- Every surface point, retained as a genuine function on the parameter square. -/
  surfacePoint : RibbonDomain → real3
  /-- Continuity of the retained surface map. -/
  continuous_surfacePoint : Continuous surfacePoint
  /-- Retained exact seam gluing. -/
  seam_gluing : ∀ s : unitInterval,
    surfacePoint ((1 : unitInterval), s) =
      surfacePoint ((0 : unitInterval), SeamMode.glue mode s)
  /-- Retained modulo-seam injectivity. -/
  exact_seam_injectivity : ∀ x y : RibbonDomain,
    surfacePoint x = surfacePoint y → SeamRel mode x y
  /-- Retained source positions. -/
  sourcePosition : ι → real3
  /-- Retained attachment parameter points. -/
  attachment : ι → RibbonDomain
  /-- Retained positional agreement. -/
  agreement : ∀ i : ι, surfacePoint (attachment i) = sourcePosition i

namespace BandRecord

variable {ι : Type*} [Fintype ι]

/-- Decode a complete record back to its band. -/
def toBand (R : BandRecord ι) : Band where
  mode := R.mode
  strip := R.surfacePoint
  continuous_strip := R.continuous_surfacePoint
  seam := R.seam_gluing
  injective_mod_seam := R.exact_seam_injectivity

/-- Encode any independently supplied band, together with a source-indexed attachment,
without losing surface points, seam, or source data. -/
def ofBand (G : Band) (src : SourceAttachingCore G ι) : BandRecord ι where
  mode := G.mode
  surfacePoint := G.strip
  continuous_surfacePoint := G.continuous_strip
  seam_gluing := G.seam
  exact_seam_injectivity := G.injective_mod_seam
  sourcePosition := src.sourcePosition
  attachment := src.attachment
  agreement := src.agreement

/-- The decoder is a complete left inverse of the encoder. -/
@[simp] theorem toBand_ofBand (G : Band) (src : SourceAttachingCore G ι) :
    (ofBand G src).toBand = G := rfl

@[simp] theorem toBand_mode (R : BandRecord ι) : R.toBand.mode = R.mode := rfl

@[simp] theorem toBand_strip (R : BandRecord ι) : R.toBand.strip = R.surfacePoint := rfl

/-- Every retained surface point is a surface point of the decoded band. -/
theorem surfacePoint_mem_surface (R : BandRecord ι) (x : RibbonDomain) :
    R.surfacePoint x ∈ R.toBand.surface :=
  ⟨x, rfl⟩

/-- Every retained source position is a surface point of the decoded band. -/
theorem sourcePosition_mem_surface (R : BandRecord ι) (i : ι) :
    R.sourcePosition i ∈ R.toBand.surface :=
  ⟨R.attachment i, R.agreement i⟩

/-- The retained seam gluing is the seam of the decoded band. -/
theorem toBand_seam (R : BandRecord ι) (s : unitInterval) :
    R.toBand.strip ((1 : unitInterval), s) =
      R.toBand.strip ((0 : unitInterval), SeamMode.glue R.mode s) :=
  R.seam_gluing s

/-- The retained source positions satisfy exactly the seam-class criterion. -/
theorem source_eq_iff (R : BandRecord ι) (i j : ι) :
    R.sourcePosition i = R.sourcePosition j ↔
      SeamRel R.mode (R.attachment i) (R.attachment j) := by
  rw [← R.agreement i, ← R.agreement j]
  simpa only [BandRecord.toBand_strip, BandRecord.toBand_mode] using
    Band.strip_eq_iff_seamRel R.toBand (R.attachment i) (R.attachment j)

/-- The encoder is a right inverse of the decoder on every record that was produced by the
encoder. -/
theorem ofBand_toBand (R : BandRecord ι) :
    ofBand R.toBand ⟨R.sourcePosition, R.attachment, R.agreement⟩ = R := rfl

/-- Ambient homeomorphism transport of a complete record, retaining seam and sources. -/
def transport (h : real3 ≃ₜ real3) (R : BandRecord ι) : BandRecord ι where
  mode := R.mode
  surfacePoint := h ∘ R.surfacePoint
  continuous_surfacePoint := h.continuous.comp R.continuous_surfacePoint
  seam_gluing := by
    intro s
    simpa only [Function.comp_apply] using congrArg h (R.seam_gluing s)
  exact_seam_injectivity := by
    intro x y hxy
    exact R.exact_seam_injectivity x y (h.injective hxy)
  sourcePosition := h ∘ R.sourcePosition
  attachment := R.attachment
  agreement := by
    intro i
    simp only [Function.comp_apply, R.agreement i]

/-- Record transport and band transport agree under decoding. -/
theorem toBand_transport (h : real3 ≃ₜ real3) (R : BandRecord ι) :
    (R.transport h).toBand = R.toBand.transport h := rfl

end BandRecord

/-! ## Finite families of bands attached to one source-index type -/

/-- A finite family of bands indexed by `β`, coupled to source indices `ι`.  Each source
index points to one band and one parameter point on it, with exact positional agreement. -/
structure BandAssembly (β ι : Type*) [Fintype β] [Fintype ι] where
  /-- The finite family of bands. -/
  bands : β → Band
  /-- Supplied real position for each source index. -/
  sourcePosition : ι → real3
  /-- The band and parameter point attached to each source index. -/
  attachment : ι → β × RibbonDomain
  /-- Positional agreement: the chosen surface point is the source position. -/
  agreement : ∀ i : ι,
    (bands (attachment i).1).strip (attachment i).2 = sourcePosition i

namespace BandAssembly

variable {β ι : Type*} [Fintype β] [Fintype ι]

/-- Every source position lies on the surface of its assigned band. -/
theorem sourcePosition_mem_surface (A : BandAssembly β ι) (i : ι) :
    A.sourcePosition i ∈ (A.bands (A.attachment i).1).surface :=
  ⟨(A.attachment i).2, A.agreement i⟩

/-- Two source positions attached to the same band at parameters `x` and `y` coincide
exactly when `x` and `y` are seam-related. -/
theorem source_eq_iff_same_band (A : BandAssembly β ι) (b : β) (x y : RibbonDomain)
    (i j : ι) (hi : A.attachment i = (b, x)) (hj : A.attachment j = (b, y)) :
    A.sourcePosition i = A.sourcePosition j ↔
      SeamRel (A.bands b).mode x y := by
  rw [← A.agreement i, ← A.agreement j]
  simpa only [hi, hj] using Band.strip_eq_iff_seamRel (A.bands b) x y

/-- Ambient transport of a whole assembly: every band is transported, source positions are
moved by the homeomorphism, and attachment parameter points are retained. -/
def transport (h : real3 ≃ₜ real3) (A : BandAssembly β ι) : BandAssembly β ι where
  bands := fun b => (A.bands b).transport h
  sourcePosition := h ∘ A.sourcePosition
  attachment := A.attachment
  agreement := by
    intro i
    simp only [Function.comp_apply, Band.transport_strip_apply, A.agreement i]

@[simp] theorem transport_sourcePosition (h : real3 ≃ₜ real3)
    (A : BandAssembly β ι) (i : ι) :
    (A.transport h).sourcePosition i = h (A.sourcePosition i) := rfl

@[simp] theorem transport_attachment (h : real3 ≃ₜ real3)
    (A : BandAssembly β ι) (i : ι) :
    (A.transport h).attachment i = A.attachment i := rfl

@[simp] theorem transport_band_mode (h : real3 ≃ₜ real3)
    (A : BandAssembly β ι) (b : β) :
    ((A.transport h).bands b).mode = (A.bands b).mode := rfl

/-- Typed surface data is not reducible to a list of source positions: if a band carries a
surface point that is not one of the supplied source positions, then the assembly retains a
point strictly beyond the source-position data. -/
theorem exists_surfacePoint_not_sourcePosition (A : BandAssembly β ι) (b : β)
    (x : RibbonDomain)
    (hx : (A.bands b).strip x ∉ Set.range A.sourcePosition) :
    ∃ p : real3, p ∈ (A.bands b).surface ∧ p ∉ Set.range A.sourcePosition :=
  ⟨(A.bands b).strip x, ⟨x, rfl⟩, hx⟩

end BandAssembly

/-! ## Certified authoritative source-indexed attachment -/

/-- The band attachment index type of a certified authoritative chemical source: exactly one
index per source atom.  It is definitionally the source's `Fin atomCount`; no index is
invented and no atom is dropped. -/
abbrev CertifiedSourceIndex (source : CertifiedAuthoritativeChemicalInput) : Type :=
  SourceAtomIndex source

/-- The certified source index is definitionally `Fin source.atomCount`. -/
theorem certifiedSourceIndex_eq_fin (source : CertifiedAuthoritativeChemicalInput) :
    CertifiedSourceIndex source = Fin source.input.molecule.atomCount := rfl

/-- A band attached to a certified authoritative chemical source.  The index type is the
source's own dependent `Fin atomCount` type, and the attached positions are exactly the
supplied real source conformation.  The original certified source is retained as a
parameter and recovered by `sourceOf`. -/
structure CertifiedSourceBand (source : CertifiedAuthoritativeChemicalInput) where
  /-- The embedded ribbon band. -/
  band : Band
  /-- The supplied real source-indexed geometry. -/
  geometry : RealSourceGeometry source
  /-- Attachment of each source atom index to a parameter point of the band. -/
  attachment : CertifiedSourceIndex source → RibbonDomain
  /-- Exact positional agreement with the supplied source conformation. -/
  agreement : ∀ index : CertifiedSourceIndex source,
    band.strip (attachment index) = geometry.conformation index

namespace CertifiedSourceBand

variable {source : CertifiedAuthoritativeChemicalInput}

/-- The original certified source projection is retained unchanged. -/
def sourceOf (_ : CertifiedSourceBand source) : CertifiedAuthoritativeChemicalInput := source

/-- The projection returns exactly the certified source that indexes the band. -/
@[simp] theorem sourceOf_eq (X : CertifiedSourceBand source) : X.sourceOf = source := rfl

/-- The representation does not modify the source input, including all electronic labels. -/
@[simp] theorem sourceOf_input_eq (X : CertifiedSourceBand source) :
    X.sourceOf.input = source.input := rfl

/-- The representation does not change the source atom count. -/
@[simp] theorem sourceOf_atomCount_eq (X : CertifiedSourceBand source) :
    X.sourceOf.input.molecule.atomCount = source.input.molecule.atomCount := rfl

/-- The attachment index type of the represented source is exactly its `Fin atomCount`. -/
theorem index_eq_fin (X : CertifiedSourceBand source) :
    CertifiedSourceIndex X.sourceOf = Fin X.sourceOf.input.molecule.atomCount := rfl

/-- Every attachment index is a genuine source atom index. -/
theorem attachment_index_lt (X : CertifiedSourceBand source)
    (index : CertifiedSourceIndex source) :
    index.val < X.sourceOf.input.molecule.atomCount :=
  index.isLt

/-- The generic source-indexed attaching core whose positions are exactly the supplied
source conformation. -/
def attachingCore (X : CertifiedSourceBand source) :
    SourceAttachingCore X.band (CertifiedSourceIndex source) where
  sourcePosition := X.geometry.conformation
  attachment := X.attachment
  agreement := X.agreement

/-- The complete record over the certified source's own index type.  It retains every
surface point, the seam, and all source positions. -/
def toRecord (X : CertifiedSourceBand source) :
    BandRecord (CertifiedSourceIndex source) :=
  BandRecord.ofBand X.band X.attachingCore

/-- Decoding the complete record recovers exactly the source-indexed band. -/
@[simp] theorem toRecord_toBand (X : CertifiedSourceBand source) :
    X.toRecord.toBand = X.band := rfl

/-- Every position in the supplied source conformation lies on the band surface. -/
theorem conformation_mem_surface (X : CertifiedSourceBand source)
    (index : CertifiedSourceIndex source) :
    X.geometry.conformation index ∈ X.band.surface :=
  ⟨X.attachment index, X.agreement index⟩

/-- Two source conformation positions coincide exactly when their attachment parameters are
related by the exact seam equivalence of the band. -/
theorem conformation_eq_iff_seamRel (X : CertifiedSourceBand source)
    (i j : CertifiedSourceIndex source) :
    X.geometry.conformation i = X.geometry.conformation j ↔
      SeamRel X.band.mode (X.attachment i) (X.attachment j) :=
  SourceAttachingCore.source_eq_iff X.attachingCore i j

/-- Constructor from independently supplied real source geometry: the caller provides the
band, the actual source conformation, and the attachment with positional agreement. -/
def ofGeometry (source : CertifiedAuthoritativeChemicalInput) (G : Band)
    (geometry : RealSourceGeometry source)
    (attachment : CertifiedSourceIndex source → RibbonDomain)
    (agreement : ∀ index : CertifiedSourceIndex source,
      G.strip (attachment index) = geometry.conformation index) :
    CertifiedSourceBand source where
  band := G
  geometry := geometry
  attachment := attachment
  agreement := agreement

@[simp] theorem ofGeometry_band (source : CertifiedAuthoritativeChemicalInput) (G : Band)
    (geometry : RealSourceGeometry source)
    (attachment : CertifiedSourceIndex source → RibbonDomain)
    (agreement : ∀ index : CertifiedSourceIndex source,
      G.strip (attachment index) = geometry.conformation index) :
    (ofGeometry source G geometry attachment agreement).band = G := rfl

@[simp] theorem ofGeometry_geometry (source : CertifiedAuthoritativeChemicalInput) (G : Band)
    (geometry : RealSourceGeometry source)
    (attachment : CertifiedSourceIndex source → RibbonDomain)
    (agreement : ∀ index : CertifiedSourceIndex source,
      G.strip (attachment index) = geometry.conformation index) :
    (ofGeometry source G geometry attachment agreement).geometry = geometry := rfl

/-- Ambient transport of a certified-source band: the band and the supplied conformation are
moved by the same ambient homeomorphism, the attachment parameter points are unchanged, and
the original certified source is still the parameter of the result. -/
def transport (h : real3 ≃ₜ real3) (X : CertifiedSourceBand source) :
    CertifiedSourceBand source where
  band := X.band.transport h
  geometry := RealSourceGeometry.ofConformation source
    (fun index => h (X.geometry.conformation index))
  attachment := X.attachment
  agreement := by
    intro index
    simp only [Band.transport_strip_apply, X.agreement index,
      RealSourceGeometry.ofConformation_conformation]

/-- Transport of a certified-source band keeps the original certified source projection. -/
@[simp] theorem transport_sourceOf (h : real3 ≃ₜ real3) (X : CertifiedSourceBand source) :
    (X.transport h).sourceOf = X.sourceOf := rfl

/-- Transport of a certified-source band keeps every attachment parameter. -/
@[simp] theorem transport_attachment (h : real3 ≃ₜ real3) (X : CertifiedSourceBand source)
    (index : CertifiedSourceIndex source) :
    (X.transport h).attachment index = X.attachment index := rfl

end CertifiedSourceBand

/-! ## Partial source attachment ledgers (off-band atoms retained) -/

/-- A partial source attachment ledger for one band.  Exactly `attachmentCount` ledger entries
are attached to the strip; every other source atom is *not* assumed to lie on the band.  The
whole certified source and the whole supplied `RealSourceGeometry` (one point for every source
atom) are retained unchanged, so organic appendages and other off-band atoms remain
representable.  Entries need not be distinct and no atom need be attached. -/
structure CertifiedPartialBand (source : CertifiedAuthoritativeChemicalInput) where
  /-- The whole supplied real source geometry, covering every source atom. -/
  geometry : RealSourceGeometry source
  /-- The band that carries this partial attachment. -/
  band : Band
  /-- Number of ledger entries attached to the band. -/
  attachmentCount : ℕ
  /-- The source atom attached at each ledger entry. -/
  atom : Fin attachmentCount → CertifiedSourceIndex source
  /-- The parameter point of the band at each ledger entry. -/
  parameter : Fin attachmentCount → RibbonDomain
  /-- Exact positional agreement with the whole supplied source conformation. -/
  agreement : ∀ entry : Fin attachmentCount,
    band.strip (parameter entry) = geometry.conformation (atom entry)

namespace CertifiedPartialBand

variable {source : CertifiedAuthoritativeChemicalInput}

/-- The original certified source projection is retained unchanged. -/
def sourceOf (_ : CertifiedPartialBand source) : CertifiedAuthoritativeChemicalInput := source

/-- The projection returns exactly the certified source that indexes the partial band. -/
@[simp] theorem sourceOf_eq (X : CertifiedPartialBand source) : X.sourceOf = source := rfl

/-- The partial representation does not modify the source input. -/
@[simp] theorem sourceOf_input_eq (X : CertifiedPartialBand source) :
    X.sourceOf.input = source.input := rfl

/-- The partial representation does not change the source atom count. -/
@[simp] theorem sourceOf_atomCount_eq (X : CertifiedPartialBand source) :
    X.sourceOf.input.molecule.atomCount = source.input.molecule.atomCount := rfl

/-- The ledger length is the number of attached entries, not the number of source atoms. -/
def ledgerLength (X : CertifiedPartialBand source) : ℕ := X.attachmentCount

/-- Every ledger atom index is a genuine source atom index. -/
theorem atom_lt (X : CertifiedPartialBand source) (entry : Fin X.attachmentCount) :
    (X.atom entry).val < X.sourceOf.input.molecule.atomCount :=
  (X.atom entry).isLt

/-- Every attached ledger position lies on the band surface. -/
theorem attached_mem_surface (X : CertifiedPartialBand source)
    (entry : Fin X.attachmentCount) :
    X.geometry.conformation (X.atom entry) ∈ X.band.surface :=
  ⟨X.parameter entry, X.agreement entry⟩

/-- Two attached ledger positions agree exactly when their parameters are seam-related.  This
holds whether or not the ledger atoms are distinct. -/
theorem attached_eq_iff_seamRel (X : CertifiedPartialBand source)
    (first second : Fin X.attachmentCount) :
    X.geometry.conformation (X.atom first) = X.geometry.conformation (X.atom second) ↔
      SeamRel X.band.mode (X.parameter first) (X.parameter second) := by
  rw [← X.agreement first, ← X.agreement second]
  exact Band.strip_eq_iff_seamRel X.band (X.parameter first) (X.parameter second)

/-- Every source atom, including an atom with no ledger entry, remains present in the retained
whole source.  No atom is dropped by taking a partial attachment. -/
theorem offband_atom_present (X : CertifiedPartialBand source) {atom : SemanticAtom}
    (member : atom ∈ source.input.molecule.atoms) :
    ∃ index : CertifiedSourceIndex X.sourceOf, sourceAtom X.sourceOf index = atom :=
  sourceAtom_surjective_on_mem X.sourceOf member

/-- The partial ledger as a source attaching core over its own `Fin attachmentCount` index
type.  Works for any `BandRecord` consumer, including the empty ledger. -/
def attachingCore (X : CertifiedPartialBand source) :
    SourceAttachingCore X.band (Fin X.attachmentCount) where
  sourcePosition := fun entry => X.geometry.conformation (X.atom entry)
  attachment := X.parameter
  agreement := X.agreement

/-- The complete record over the partial ledger's own index type. -/
def toRecord (X : CertifiedPartialBand source) : BandRecord (Fin X.attachmentCount) :=
  BandRecord.ofBand X.band X.attachingCore

/-- Decoding the record recovers exactly the band, independently of the ledger length. -/
@[simp] theorem toRecord_toBand (X : CertifiedPartialBand source) :
    X.toRecord.toBand = X.band := rfl

/-- Constructor from a whole source geometry and a partial attachment ledger. -/
def ofGeometry (source : CertifiedAuthoritativeChemicalInput)
    (geometry : RealSourceGeometry source) (band : Band) (attachmentCount : ℕ)
    (atom : Fin attachmentCount → CertifiedSourceIndex source)
    (parameter : Fin attachmentCount → RibbonDomain)
    (agreement : ∀ entry : Fin attachmentCount,
      band.strip (parameter entry) = geometry.conformation (atom entry)) :
    CertifiedPartialBand source where
  geometry := geometry
  band := band
  attachmentCount := attachmentCount
  atom := atom
  parameter := parameter
  agreement := agreement

@[simp] theorem ofGeometry_band (source : CertifiedAuthoritativeChemicalInput)
    (geometry : RealSourceGeometry source) (band : Band) (attachmentCount : ℕ)
    (atom : Fin attachmentCount → CertifiedSourceIndex source)
    (parameter : Fin attachmentCount → RibbonDomain)
    (agreement : ∀ entry : Fin attachmentCount,
      band.strip (parameter entry) = geometry.conformation (atom entry)) :
    (ofGeometry source geometry band attachmentCount atom parameter agreement).band = band := rfl

@[simp] theorem ofGeometry_geometry (source : CertifiedAuthoritativeChemicalInput)
    (geometry : RealSourceGeometry source) (band : Band) (attachmentCount : ℕ)
    (atom : Fin attachmentCount → CertifiedSourceIndex source)
    (parameter : Fin attachmentCount → RibbonDomain)
    (agreement : ∀ entry : Fin attachmentCount,
      band.strip (parameter entry) = geometry.conformation (atom entry)) :
    (ofGeometry source geometry band attachmentCount atom parameter agreement).geometry =
      geometry := rfl

@[simp] theorem ofGeometry_attachmentCount (source : CertifiedAuthoritativeChemicalInput)
    (geometry : RealSourceGeometry source) (band : Band) (attachmentCount : ℕ)
    (atom : Fin attachmentCount → CertifiedSourceIndex source)
    (parameter : Fin attachmentCount → RibbonDomain)
    (agreement : ∀ entry : Fin attachmentCount,
      band.strip (parameter entry) = geometry.conformation (atom entry)) :
    (ofGeometry source geometry band attachmentCount atom parameter agreement).attachmentCount =
      attachmentCount := rfl

/-- Ambient transport of a partial certified-source band.  The band and the *whole* supplied
source conformation (including every off-band atom) are moved by the same ambient
homeomorphism; the ledger atoms and parameter points stay fixed. -/
def transport (h : real3 ≃ₜ real3) (X : CertifiedPartialBand source) :
    CertifiedPartialBand source where
  geometry := RealSourceGeometry.ofConformation source
    (fun index => h (X.geometry.conformation index))
  band := X.band.transport h
  attachmentCount := X.attachmentCount
  atom := X.atom
  parameter := X.parameter
  agreement := by
    intro entry
    simp only [Band.transport_strip_apply, X.agreement entry,
      RealSourceGeometry.ofConformation_conformation]

/-- Transport of a partial band keeps the original certified source projection. -/
@[simp] theorem transport_sourceOf (h : real3 ≃ₜ real3) (X : CertifiedPartialBand source) :
    (X.transport h).sourceOf = X.sourceOf := rfl

/-- Transport of a partial band keeps the ledger length. -/
@[simp] theorem transport_attachmentCount (h : real3 ≃ₜ real3)
    (X : CertifiedPartialBand source) :
    (X.transport h).attachmentCount = X.attachmentCount := rfl

/-- Transport of a partial band keeps every ledger atom. -/
@[simp] theorem transport_atom (h : real3 ≃ₜ real3) (X : CertifiedPartialBand source)
    (entry : Fin X.attachmentCount) :
    (X.transport h).atom entry = X.atom entry := rfl

/-- Transport of a partial band keeps every parameter point. -/
@[simp] theorem transport_parameter (h : real3 ≃ₜ real3) (X : CertifiedPartialBand source)
    (entry : Fin X.attachmentCount) :
    (X.transport h).parameter entry = X.parameter entry := rfl

/-- The *whole* source conformation is transported equivariantly, including every off-band atom;
no atom is dropped or left behind by the ambient homeomorphism. -/
theorem transport_geometry_conformation (h : real3 ≃ₜ real3)
    (X : CertifiedPartialBand source) (index : CertifiedSourceIndex source) :
    (X.transport h).geometry.conformation index = h (X.geometry.conformation index) := rfl

end CertifiedPartialBand

/-! ## Reflection, seam invariance, and handedness signs -/

/-- The ambient origin reflection `x ↦ -x` of Euclidean three-space.  The module only uses
that it is an ambient homeomorphism; the transport theorems below hold for every ambient
homeomorphism. -/
def ambientReflection : real3 ≃ₜ real3 where
  toFun := fun x => -x
  invFun := fun x => -x
  left_inv := by
    intro x
    simp
  right_inv := by
    intro x
    simp
  continuous_toFun := continuous_neg
  continuous_invFun := continuous_neg

@[simp] theorem ambientReflection_apply (x : real3) : ambientReflection x = -x := rfl

theorem ambientReflection_involutive : Function.Involutive ambientReflection := by
  intro x
  simp [ambientReflection]

/-- Reflection never changes the seam type. -/
theorem reflection_preserves_seamMode (G : Band) :
    (G.transport ambientReflection).mode = G.mode := rfl

/-- Reflection never changes the exact seam relation. -/
theorem reflection_preserves_seamRel (G : Band) (x y : RibbonDomain) :
    SeamRel (G.transport ambientReflection).mode x y ↔ SeamRel G.mode x y :=
  Iff.rfl

/-- A proposition is determined by the seam mode when bands with the same gluing mode receive
the same proposition. -/
def DeterminedBySeamMode (P : Band → Prop) : Prop :=
  ∀ G H : Band, G.mode = H.mode → (P G ↔ P H)

/-- A *reflection-antisymmetric sign* at a band: the sign of the reflected band is the
negation of the sign of the band.  This is the behaviour expected of a handedness sign on an
applicable nondegenerate configuration domain.  It is a sign-level notion only: mirror
invariance of a configuration class is a separate property. -/
def ReflectionAntisymmetricSign (P : Band → Prop) (G : Band) : Prop :=
  P (G.transport ambientReflection) ↔ ¬ P G

/-- No proposition is equivalent to its own negation. -/
theorem not_iff_not_self (A : Prop) : ¬(A ↔ ¬A) := by
  intro h
  have hnA : ¬A := fun hA => (h.mp hA) hA
  exact hnA (h.mpr hnA)

/-- A proposition determined only by the seam mode is invariant under ambient transport, in
particular under reflection.  Hence it cannot be a reflection-antisymmetric handedness sign.
This is the precise sense in which twist supplies no handedness-sign information: the twist
contributes only the seam mode, and the seam mode is reflection-stable.  The statement is
confined to signs; it makes no claim about chirality or achirality of bands. -/
theorem determinedBySeamMode_not_reflectionAntisymmetric (P : Band → Prop)
    (hP : DeterminedBySeamMode P) (G : Band) : ¬ ReflectionAntisymmetricSign P G := by
  intro hflip
  have hsame : P (G.transport ambientReflection) ↔ P G :=
    hP _ _ (Band.transport_mode G ambientReflection)
  exact not_iff_not_self (P G) (hsame.symm.trans hflip)

/-- Any mode-determined proposition is invariant under every ambient homeomorphism. -/
theorem determinedBySeamMode_transport (P : Band → Prop)
    (hP : DeterminedBySeamMode P) (G : Band) (h : real3 ≃ₜ real3) :
    P (G.transport h) ↔ P G :=
  hP _ _ (Band.transport_mode G h)

/-- Being twisted is determined by the seam mode, and hence is not a reflection-antisymmetric
handedness sign. -/
theorem twisted_not_reflectionAntisymmetric (G : Band) :
    ¬ ReflectionAntisymmetricSign (fun H : Band => H.mode = SeamMode.twisted) G :=
  determinedBySeamMode_not_reflectionAntisymmetric _
    (by
      intro G' H' h
      dsimp only
      rw [h])
    G

/-- A twisted band and its reflection are both twisted.  The reflection changes the
embedding, never the gluing mode. -/
theorem reflection_of_twisted_is_twisted (G : Band) (h : G.mode = SeamMode.twisted) :
    (G.transport ambientReflection).mode = SeamMode.twisted := by
  rw [Band.transport_mode, h]

end

end OrganicStereoEmbeddedBands
end OneCenter
end TetraStereo
