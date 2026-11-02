/-
Copyright (c) 2026 TetraStereo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TetraStereo.OneCenter.OrganicStereoAmbientMotions
import TetraStereo.OneCenter.OrganicStereoEmbeddedBands
import TetraStereo.OneCenter.OrganicStereoIndependentBandEncoding

/-!
# Ambient transport of embedded-band evidence

`OrganicStereoEmbeddedBands.Band.transport` already *is* the ambient homeomorphism action
requested for a ribbon band: it keeps the seam mode, composes the strip map with the
homeomorphism, derives continuity, seam gluing and modulo-seam injectivity from the supplied
band, and proves identity, composition and the exact surface image.  This module therefore does
not introduce a second name or second implementation for that action; it reuses `transport`.

What was still missing is the transport of the *evidence joined to a band*:

* inverse recovery and cancellation for band transport (the existing module has identity and
  composition but not the inverse laws);
* ambient transport of `SourceAttachingCore`, keeping every attachment parameter and moving every
  supplied source position by the same homeomorphism, with exact positional agreement and the
  seam-class criterion preserved;
* ambient transport of `CertifiedPartialBand`, moving the whole supplied source conformation
  (including every off-band atom) and the band strip by the same homeomorphism while retaining
  the authoritative source, the ledger atoms and the ledger parameters;
* ambient transport of `IndependentBandAttachment`, the independent whole-source input, moving
  every conformation point and every band geometry by the same homeomorphism and retaining the
  source hypergraph, the band index, every attachment type, every atom label and every parameter;
* compatibility of that transport with the existing finite encoding: encoding after transport is
  transport after encoding.

All statements are conditional on independently supplied band geometry and source data.  Nothing
here constructs a band, classifies chirality, or draws a kinetic or linking conclusion.
-/

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

open OrganicStereoEmbeddedBands

noncomputable section

namespace RealSourceGeometry

/-- A source geometry rebuilt from its own conformation is the original geometry.  This is the
eta law used when a transported geometry is identified with the original one. -/
theorem ofConformation_self (source : CertifiedAuthoritativeChemicalInput)
    (geometry : RealSourceGeometry source) :
    ofConformation source (fun index => geometry.conformation index) = geometry := by
  cases geometry
  rfl

end RealSourceGeometry

/-! ## Inverse recovery and cancellation for band transport -/

namespace OrganicStereoEmbeddedBands
namespace Band

/-- Ambient transport by `h` followed by transport by `h.symm` recovers the original band. -/
theorem transport_symm (G : Band) (h : real3 ≃ₜ real3) :
    (G.transport h).transport h.symm = G := by
  apply Band.ext
  · rfl
  · funext x
    simp

/-- Ambient transport by `h.symm` followed by transport by `h` recovers the original band. -/
theorem transport_symm_trans (G : Band) (h : real3 ≃ₜ real3) :
    (G.transport h.symm).transport h = G := by
  apply Band.ext
  · rfl
  · funext x
    simp

/-- Band transport by a fixed ambient homeomorphism is injective: two transported bands are
equal exactly when the original bands are equal. -/
theorem transport_eq_iff {G H : Band} (h : real3 ≃ₜ real3) :
    G.transport h = H.transport h ↔ G = H := by
  constructor
  · intro equal
    have cancelled := congrArg (fun K : Band => K.transport h.symm) equal
    simpa only [transport_symm] using cancelled
  · intro equal
    rw [equal]

/-- Extensional form of the preceding statement: transport is an injective operation. -/
theorem transport_injective (h : real3 ≃ₜ real3) :
    Function.Injective (fun G : Band => G.transport h) :=
  fun _ _ equal => (transport_eq_iff h).mp equal

/-! ### Compatibility with supplied ambient motions -/

/-- At motion time zero the ambient map is the identity, so band transport is the identity. -/
theorem transport_map_zero (G : Band) (motion : AmbientMotion) :
    G.transport (motion.map 0) = G := by
  rw [motion.starts_identity]
  exact transport_refl G

/-- Transport by the endpoint of the identity motion is the identity on bands. -/
theorem transport_endpoint_identity (G : Band) :
    G.transport AmbientMotion.identity.endpoint = G := by
  rw [AmbientMotion.endpoint_identity]
  exact transport_refl G

/-- Transport by two motion endpoints in succession is transport by the endpoint of the
pointwise composition of the motions. -/
theorem transport_endpoint_comp (G : Band) (first second : AmbientMotion) :
    (G.transport first.endpoint).transport second.endpoint =
      G.transport (first.comp second).endpoint := by
  rw [transport_transport]
  rfl

end Band
end OrganicStereoEmbeddedBands

/-! ## Transport of a source-indexed attachment core -/

namespace OrganicStereoEmbeddedBands
namespace SourceAttachingCore

variable {G : Band} {ι : Type*} [Fintype ι]

/-- Reindex an attachment core along an equality of bands.  This is the bookkeeping needed when
the transported band is identified with the original band by inverse recovery. -/
def castBand {G G' : Band} (equal : G = G') (src : SourceAttachingCore G ι) :
    SourceAttachingCore G' ι where
  sourcePosition := src.sourcePosition
  attachment := src.attachment
  agreement := by
    intro i
    rw [← equal]
    exact src.agreement i

@[simp] theorem castBand_sourcePosition {G G' : Band} (equal : G = G')
    (src : SourceAttachingCore G ι) (i : ι) :
    (castBand equal src).sourcePosition i = src.sourcePosition i := rfl

@[simp] theorem castBand_attachment {G G' : Band} (equal : G = G')
    (src : SourceAttachingCore G ι) (i : ι) :
    (castBand equal src).attachment i = src.attachment i := rfl

/-- Attachment cores over a fixed band are determined by their source positions and attachment
parameters; the positional-agreement proof carries no data. -/
theorem ext_of_data {src tgt : SourceAttachingCore G ι}
    (positions : src.sourcePosition = tgt.sourcePosition)
    (attachments : src.attachment = tgt.attachment) : src = tgt := by
  rcases src with ⟨srcPosition, srcAttachment, srcAgreement⟩
  rcases tgt with ⟨tgtPosition, tgtAttachment, tgtAgreement⟩
  simp only at positions attachments
  subst positions
  subst attachments
  rfl

/-- Every transported source position still lies on the transported band surface. -/
theorem transport_sourcePosition_mem_surface (h : real3 ≃ₜ real3)
    (src : SourceAttachingCore G ι) (i : ι) :
    (src.transport h).sourcePosition i ∈ (G.transport h).surface :=
  sourcePosition_mem_surface (src.transport h) i

/-- Two transported source positions agree exactly when the original source positions agree. -/
theorem transport_source_eq_iff (h : real3 ≃ₜ real3)
    (src : SourceAttachingCore G ι) (i j : ι) :
    (src.transport h).sourcePosition i = (src.transport h).sourcePosition j ↔
      src.sourcePosition i = src.sourcePosition j := by
  rw [transport_sourcePosition, transport_sourcePosition]
  exact ⟨fun equal => h.injective equal, fun equal => congrArg h equal⟩

/-- The exact seam-class criterion is preserved by ambient transport: two transported source
positions agree exactly when the unchanged attachment parameters are seam-related under the
unchanged seam mode. -/
theorem transport_source_eq_iff_seamRel (h : real3 ≃ₜ real3)
    (src : SourceAttachingCore G ι) (i j : ι) :
    (src.transport h).sourcePosition i = (src.transport h).sourcePosition j ↔
      SeamRel G.mode (src.attachment i) (src.attachment j) := by
  rw [transport_source_eq_iff, source_eq_iff]

/-- Transport by the identity keeps every source position and every attachment parameter. -/
theorem transport_refl_eq_cast (src : SourceAttachingCore G ι) :
    src.transport (Homeomorph.refl real3) =
      castBand (Band.transport_refl G).symm src := by
  apply ext_of_data
  · funext i
    simp [castBand_sourcePosition]
  · rfl

/-- Transport by `h` and then by `k` is transport by the composite homeomorphism. -/
theorem transport_transport_eq_cast (h k : real3 ≃ₜ real3)
    (src : SourceAttachingCore G ι) :
    (src.transport h).transport k =
      castBand (Band.transport_transport G h k).symm (src.transport (h.trans k)) := by
  apply ext_of_data
  · funext i
    simp [castBand_sourcePosition]
  · rfl

/-- Transport by `h` followed by `h.symm` recovers the original attachment core. -/
theorem transport_symm_eq_cast (h : real3 ≃ₜ real3)
    (src : SourceAttachingCore G ι) :
    (src.transport h).transport h.symm =
      castBand (Band.transport_symm G h).symm src := by
  apply ext_of_data
  · funext i
    simp
  · rfl

/-- Transport by `h.symm` followed by `h` recovers the original attachment core. -/
theorem transport_symm_trans_eq_cast (h : real3 ≃ₜ real3)
    (src : SourceAttachingCore G ι) :
    (src.transport h.symm).transport h =
      castBand (Band.transport_symm_trans G h).symm src := by
  apply ext_of_data
  · funext i
    simp
  · rfl

/-- Transport is injective on attachment cores over a fixed band. -/
theorem transport_injective (h : real3 ≃ₜ real3) :
    Function.Injective
      (fun src : SourceAttachingCore G ι => src.transport h) := by
  intro src tgt equal
  have positions : src.sourcePosition = tgt.sourcePosition := by
    funext i
    exact h.injective (congrArg (fun core => core.sourcePosition i) equal)
  have attachments : src.attachment = tgt.attachment := by
    funext i
    exact congrArg (fun core => core.attachment i) equal
  exact ext_of_data positions attachments

end SourceAttachingCore
end OrganicStereoEmbeddedBands

/-! ## Transport of a partial source-bound band -/

namespace OrganicStereoEmbeddedBands
namespace CertifiedPartialBand

variable {source : CertifiedAuthoritativeChemicalInput}

/-- The transported ledger carries exactly the transported band. -/
@[simp] theorem transport_band (h : real3 ≃ₜ real3)
    (X : CertifiedPartialBand source) :
    (X.transport h).band = X.band.transport h := rfl

/-- The seam classes of the retained band are unchanged by ambient transport. -/
theorem transport_seamRel_iff (h : real3 ≃ₜ real3)
    (X : CertifiedPartialBand source) (x y : RibbonDomain) :
    SeamRel (X.transport h).band.mode x y ↔ SeamRel X.band.mode x y :=
  Iff.rfl

/-- Each ledger entry after transport relates the transported strip value to the transported
whole-source conformation at exactly the original ledger atom. -/
theorem transport_attached_apply (h : real3 ≃ₜ real3)
    (X : CertifiedPartialBand source) (entry : Fin X.attachmentCount) :
    (X.transport h).band.strip ((X.transport h).parameter entry) =
      h (X.geometry.conformation (X.atom entry)) := by
  simpa only [transport_geometry_conformation, transport_atom] using
    (X.transport h).agreement entry

/-- The same homeomorphism is applied to the band strip and to the whole-source conformation:
the original positional agreement is carried to the transported one. -/
theorem transport_agreement_congr (h : real3 ≃ₜ real3)
    (X : CertifiedPartialBand source) (entry : Fin X.attachmentCount) :
    h (X.band.strip (X.parameter entry)) =
      h (X.geometry.conformation (X.atom entry)) :=
  congrArg h (X.agreement entry)

/-- Two transported attached positions agree exactly when the retained ledger parameters are
seam-related under the unchanged seam mode. -/
theorem transport_attached_eq_iff_seamRel (h : real3 ≃ₜ real3)
    (X : CertifiedPartialBand source) (first second : Fin X.attachmentCount) :
    (X.transport h).geometry.conformation ((X.transport h).atom first) =
      (X.transport h).geometry.conformation ((X.transport h).atom second) ↔
      SeamRel X.band.mode (X.parameter first) (X.parameter second) := by
  rw [transport_geometry_conformation, transport_geometry_conformation,
    transport_atom, transport_atom, ← X.attached_eq_iff_seamRel first second]
  exact ⟨fun equal => h.injective equal, fun equal => congrArg h equal⟩

/-- Ambient transport by the identity is the identity on partial source-bound bands. -/
theorem transport_refl (X : CertifiedPartialBand source) :
    X.transport (Homeomorph.refl real3) = X := by
  rcases X with ⟨geometry, band, count, atom, parameter, agreement⟩
  simp [CertifiedPartialBand.transport, Band.transport_refl,
    RealSourceGeometry.ofConformation_self]

/-- Successive ambient transports compose. -/
theorem transport_transport (h k : real3 ≃ₜ real3)
    (X : CertifiedPartialBand source) :
    (X.transport h).transport k = X.transport (h.trans k) := by
  rcases X with ⟨geometry, band, count, atom, parameter, agreement⟩
  simp [CertifiedPartialBand.transport, Band.transport_transport]

/-- Transport by `h` followed by `h.symm` recovers the original partial band, including the
whole source conformation and every ledger entry. -/
theorem transport_symm (h : real3 ≃ₜ real3)
    (X : CertifiedPartialBand source) :
    (X.transport h).transport h.symm = X := by
  rcases X with ⟨geometry, band, count, atom, parameter, agreement⟩
  simp [CertifiedPartialBand.transport, Band.transport_symm,
    RealSourceGeometry.ofConformation_self]

/-- Transport by `h.symm` followed by `h` recovers the original partial band. -/
theorem transport_symm_trans (h : real3 ≃ₜ real3)
    (X : CertifiedPartialBand source) :
    (X.transport h.symm).transport h = X := by
  rcases X with ⟨geometry, band, count, atom, parameter, agreement⟩
  simp [CertifiedPartialBand.transport, Band.transport_symm_trans,
    RealSourceGeometry.ofConformation_self]

/-- Ambient transport is injective on partial source-bound bands. -/
theorem transport_injective (h : real3 ≃ₜ real3) :
    Function.Injective
      (fun X : CertifiedPartialBand source => X.transport h) := by
  intro X Y equal
  have cancelled := congrArg (fun Z : CertifiedPartialBand source => Z.transport h.symm) equal
  simpa [transport_symm] using cancelled

end CertifiedPartialBand
end OrganicStereoEmbeddedBands

/-! ## Transport of the independent whole-source band input -/

namespace OrganicStereoIndependentBandEncoding
namespace IndependentBandAttachment

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Ambient transport of an independent band attachment.  The source hypergraph, the band index
type, every attachment record type, every atom label and every band parameter are retained
verbatim; the whole conformation and every band strip are moved by the same homeomorphism. -/
def transport (h : real3 ≃ₜ real3) (input : IndependentBandAttachment V) :
    IndependentBandAttachment V where
  graph := input.graph
  conformation := fun v => h (input.conformation v)
  bandIndex := input.bandIndex
  fintypeBandIndex := input.fintypeBandIndex
  band := fun b => (input.band b).transport h
  Attachment := input.Attachment
  fintypeAttachment := input.fintypeAttachment
  atom := input.atom
  parameter := input.parameter
  agreement := by
    intro b entry
    simpa only [Band.transport_strip_apply] using
      congrArg h (input.agreement b entry)

/-- The source hypergraph is retained literally. -/
@[simp] theorem transport_graph (h : real3 ≃ₜ real3)
    (input : IndependentBandAttachment V) :
    (input.transport h).graph = input.graph := rfl

/-- Every atom label, attached or not, is moved by the same homeomorphism. -/
@[simp] theorem transport_conformation_apply (h : real3 ≃ₜ real3)
    (input : IndependentBandAttachment V) (v : V) :
    (input.transport h).conformation v = h (input.conformation v) := rfl

/-- The whole transported conformation is the homeomorphic image of the whole input
conformation; no atom is dropped. -/
theorem transport_conformation (h : real3 ≃ₜ real3)
    (input : IndependentBandAttachment V) :
    (input.transport h).conformation = h ∘ input.conformation := rfl

/-- Each band is transported by the same homeomorphism. -/
@[simp] theorem transport_band_apply (h : real3 ≃ₜ real3)
    (input : IndependentBandAttachment V) (b : input.bandIndex) :
    (input.transport h).band b = (input.band b).transport h := rfl

/-- Every band seam mode is retained. -/
@[simp] theorem transport_band_mode (h : real3 ≃ₜ real3)
    (input : IndependentBandAttachment V) (b : input.bandIndex) :
    ((input.transport h).band b).mode = (input.band b).mode := rfl

/-- Every band surface is transported to its exact homeomorphic image. -/
theorem transport_band_surface (h : real3 ≃ₜ real3)
    (input : IndependentBandAttachment V) (b : input.bandIndex) :
    ((input.transport h).band b).surface = h '' (input.band b).surface :=
  Band.surface_transport (input.band b) h

/-- Every atom label and every band parameter is retained. -/
@[simp] theorem transport_atom_apply (h : real3 ≃ₜ real3)
    (input : IndependentBandAttachment V) (b : input.bandIndex)
    (entry : input.Attachment b) :
    (input.transport h).atom b entry = input.atom b entry := rfl

@[simp] theorem transport_parameter_apply (h : real3 ≃ₜ real3)
    (input : IndependentBandAttachment V) (b : input.bandIndex)
    (entry : input.Attachment b) :
    (input.transport h).parameter b entry = input.parameter b entry := rfl

/-- Every per-attachment agreement is preserved: the transported strip value is exactly the
homeomorphic image of the original whole-source position of the same atom label. -/
theorem transport_agreement_apply (h : real3 ≃ₜ real3)
    (input : IndependentBandAttachment V) (b : input.bandIndex)
    (entry : input.Attachment b) :
    ((input.transport h).band b).strip ((input.transport h).parameter b entry) =
      h (input.conformation (input.atom b entry)) := by
  simpa only [transport_conformation_apply, transport_atom_apply,
    transport_parameter_apply] using (input.transport h).agreement b entry

/-- Ambient transport by the identity is the identity on independent band attachments. -/
theorem transport_refl (input : IndependentBandAttachment V) :
    input.transport (Homeomorph.refl real3) = input := by
  simp [IndependentBandAttachment.transport, Band.transport_refl]

/-- Successive ambient transports compose. -/
theorem transport_transport (h k : real3 ≃ₜ real3)
    (input : IndependentBandAttachment V) :
    (input.transport h).transport k = input.transport (h.trans k) := by
  simp [IndependentBandAttachment.transport, Band.transport_transport]

/-- Transport by `h` followed by `h.symm` recovers the whole independent input, including the
hypergraph, every band, every atom label and the entire conformation. -/
theorem transport_symm (h : real3 ≃ₜ real3)
    (input : IndependentBandAttachment V) :
    (input.transport h).transport h.symm = input := by
  simp [IndependentBandAttachment.transport, Band.transport_symm]

/-- Ambient transport is injective on independent band attachments. -/
theorem transport_injective (h : real3 ≃ₜ real3) :
    Function.Injective
      (fun input : IndependentBandAttachment V => input.transport h) := by
  intro X Y equal
  have cancelled :=
    congrArg (fun Z : IndependentBandAttachment V => Z.transport h.symm) equal
  simpa [transport_symm] using cancelled

/-- Transport commutes with the existing finite encoding into a partial source-bound band:
encoding the transported independent input is the transport of the encoded partial band.  This
is the coherent joined-evidence statement: the source, every atom position and the band strip
are moved by one and the same homeomorphism. -/
theorem encodeFamily_transport (input : IndependentBandAttachment V)
    (enumeration : V ≃ Fin (Fintype.card V)) (h : real3 ≃ₜ real3)
    (b : input.bandIndex) :
    encodeFamily (input.transport h) enumeration b =
      (encodeFamily input enumeration b).transport h := by
  rfl

end IndependentBandAttachment
end OrganicStereoIndependentBandEncoding

end
end OneCenter
end TetraStereo
