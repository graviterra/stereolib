/-
Copyright (c) 2026 TetraStereo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TetraStereo.OneCenter.OrganicStereoFiniteClassicalDescription

/-!
# Ingress from independent band attachments into the whole-state description

`OrganicStereoIndependentBandEncoding.IndependentBandAttachment V` is the repository's
independent band input: an arbitrary finite atom-labelled interaction hypergraph, one entire real
conformation, an arbitrary finite band index type, and for every band index a geometric `Band`
together with its own finite attachment type, atom map, parameter map and exact positional
agreement.

`OrganicStereoFiniteClassicalDescription.WholeState V E B` is the repository's single correlated
finite description.  `OrganicStereoFiniteClassicalDescription.toIndependentBandAttachment` already
extracts an `IndependentBandAttachment` from a whole state.  This module supplies the opposite
direction: it builds a whole state *from* an arbitrary independent band input.

* `ofIndependentBandAttachment` constructs `WholeState V (Fin 0) input.bandIndex`; its band-index
  finiteness argument is the one carried by the independent input.  The graph, the entire real
  conformation (including every off-band atom), every band and every per-band attachment
  type/atom/parameter are copied literally.  The bond-path channel is indexed by `Fin 0` and is
  therefore genuinely empty; the electronic, rational-provenance, role, drawing, fragment,
  convention and cage channels take their default absence values (`none` / `[]`), never a
  fabricated payload.
* `toIndependentBandAttachment_ofIndependentBandAttachment` proves that the existing extractor
  returns the original `IndependentBandAttachment` exactly, as a full dependent record equality.
  The data fields are definitionally the input fields; the proposition-valued agreement fields are
  identified by proof irrelevance.  No data is assumed and no inverse is postulated.
* The projection lemmas record the graph, conformation, band, attachment type, atom map and
  parameter map exactly, and expose each absent channel.
* `offBand_conformation_apply` records that an atom label named by no attachment record still
  keeps its exact real position, because the conformation is copied as a whole rather than
  projected onto the band-attached labels.
* `encodeBundled_ofIndependentBandAttachment` lifts the recovery through the existing bundled
  family, so the empty-band case is recovered too.

No totality or injectivity of `atom` is assumed, no band is required to cover `V`, attachment
types may be empty, and several records (of one band or of different bands) may name the same
atom.  The ingress adds no identification of such records.  Nothing here constructs a band,
classifies chirality or claims the physical existence of a band.
-/

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace OrganicStereoBandDescriptionIngress

open OrganicStereoIndependentBandEncoding

noncomputable section

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Off-band atom labels -/

/-- An atom label is off-band for an independent input when no attachment record of any band
names it.  This predicate is used only to state the recovery guarantee; the ingress itself
imposes no coverage condition on the bands. -/
def OffBand (input : IndependentBandAttachment V) (v : V) : Prop :=
  ∀ (band : input.bandIndex) (record : input.Attachment band), input.atom band record ≠ v

/-! ## The ingress -/

/-- Build a `WholeState` from an arbitrary independent band attachment.

The graph and the whole real conformation are copied unchanged.  Every band index keeps its own
geometric `Band`, its own finite attachment type, atom map and parameter map, and the input's
positional agreement is reused literally.  No band must cover `V`, no attachment type must be
nonempty, and there is no totality or injectivity condition on `atom`.  The bond-path family is
`Fin 0` and hence empty; the remaining unspecified channels take their default absence values
(`none` or `[]`).

The band-index finiteness instance is the input's own `fintypeBandIndex`: it is threaded through
the definition type and body with `letI`, so every projection and every existing encoding sees the
canonical stored instance.  No separate finiteness choice is made. -/
def ofIndependentBandAttachment (input : IndependentBandAttachment V) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    WholeState V (Fin 0) input.bandIndex := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  exact
    { graph := input.graph
      electronic? := none
      electronic_unpaired := by
        intro channel present
        cases present
      conformation := input.conformation
      rationalPositions? := none
      rationalPositions_valid := by
        intro positions present
        cases present
      roles := []
      role_valid := by
        intro annotation member
        simp at member
      paths := fun edge => Fin.elim0 edge
      path_valid := by
        intro edge
        exact Fin.elim0 edge
      path_source_endpoint := by
        intro edge
        exact Fin.elim0 edge
      path_target_endpoint := by
        intro edge
        exact Fin.elim0 edge
      bandFamily := fun band =>
        { band := input.band band
          Attachment := input.Attachment band
          fintypeAttachment := input.fintypeAttachment band
          atom := input.atom band
          parameter := input.parameter band }
      band_agreement := fun band record => input.agreement band record
      diagram? := none
      diagramPartial? := none
      diagramIncidence := []
      diagram_valid := by
        intro row member
        simp at member
      fragments := []
      conventions := []
      cages := [] }

/-! ## Source and whole-conformation projections -/

/-- The ingress retains exactly the input hypergraph. -/
@[simp] theorem ofIndependentBandAttachment_graph (input : IndependentBandAttachment V) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (ofIndependentBandAttachment input).graph = input.graph := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- The ingress retains exactly the input whole conformation.  No atom label is dropped. -/
@[simp] theorem ofIndependentBandAttachment_conformation (input : IndependentBandAttachment V) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (ofIndependentBandAttachment input).conformation = input.conformation := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- Pointwise form of whole-conformation preservation, valid at every atom label whether or not
any band attaches it. -/
@[simp] theorem ofIndependentBandAttachment_conformation_apply
    (input : IndependentBandAttachment V) (v : V) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (ofIndependentBandAttachment input).conformation v = input.conformation v := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-! ## Band and attachment projections -/

/-- The band family of the ingress is the input band family, each band equipped with its own
finite attachment type, atom map and parameter map. -/
@[simp] theorem ofIndependentBandAttachment_bandFamily
    (input : IndependentBandAttachment V) (band : input.bandIndex) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (ofIndependentBandAttachment input).bandFamily band =
      { band := input.band band
        Attachment := input.Attachment band
        fintypeAttachment := input.fintypeAttachment band
        atom := input.atom band
        parameter := input.parameter band } := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- Every band geometry is retained literally. -/
@[simp] theorem ofIndependentBandAttachment_bandFamily_band
    (input : IndependentBandAttachment V) (band : input.bandIndex) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    ((ofIndependentBandAttachment input).bandFamily band).band = input.band band := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- Every band keeps its own attachment record type; records of different bands are never merged.
-/
@[simp] theorem ofIndependentBandAttachment_bandFamily_Attachment
    (input : IndependentBandAttachment V) (band : input.bandIndex) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    ((ofIndependentBandAttachment input).bandFamily band).Attachment =
      input.Attachment band := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- Every band keeps its own finiteness evidence for its attachment record type. -/
@[simp] theorem ofIndependentBandAttachment_bandFamily_fintypeAttachment
    (input : IndependentBandAttachment V) (band : input.bandIndex) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    ((ofIndependentBandAttachment input).bandFamily band).fintypeAttachment =
      input.fintypeAttachment band := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- Every attachment record names exactly the input atom label. -/
@[simp] theorem ofIndependentBandAttachment_bandFamily_atom
    (input : IndependentBandAttachment V) (band : input.bandIndex) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    ((ofIndependentBandAttachment input).bandFamily band).atom = input.atom band := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- Every attachment record keeps exactly the input band parameter point. -/
@[simp] theorem ofIndependentBandAttachment_bandFamily_parameter
    (input : IndependentBandAttachment V) (band : input.bandIndex) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    ((ofIndependentBandAttachment input).bandFamily band).parameter =
      input.parameter band := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- Pointwise atom form of attachment preservation. -/
@[simp] theorem ofIndependentBandAttachment_bandFamily_atom_apply
    (input : IndependentBandAttachment V) (band : input.bandIndex)
    (record : input.Attachment band) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    ((ofIndependentBandAttachment input).bandFamily band).atom record =
      input.atom band record := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- Pointwise parameter form of attachment preservation. -/
@[simp] theorem ofIndependentBandAttachment_bandFamily_parameter_apply
    (input : IndependentBandAttachment V) (band : input.bandIndex)
    (record : input.Attachment band) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    ((ofIndependentBandAttachment input).bandFamily band).parameter record =
      input.parameter band record := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- The number of attachment records of a band is the cardinality of that band's own attachment
type. -/
@[simp] theorem ofIndependentBandAttachment_bandFamily_card
    (input : IndependentBandAttachment V) (band : input.bandIndex) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    @Fintype.card ((ofIndependentBandAttachment input).bandFamily band).Attachment
        ((ofIndependentBandAttachment input).bandFamily band).fintypeAttachment =
      @Fintype.card (input.Attachment band) (input.fintypeAttachment band) := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- The positional agreement of every attachment record is the input's agreement.  No further
positional hypothesis is introduced. -/
@[simp] theorem ofIndependentBandAttachment_band_agreement
    (input : IndependentBandAttachment V) (band : input.bandIndex)
    (record : input.Attachment band) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (ofIndependentBandAttachment input).band_agreement band record =
      input.agreement band record := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- The ingress adds no identification of attachment records: two records name the same atom in
the constructed state exactly when they name the same atom in the input.  In particular the atom
map is not assumed injective or total. -/
theorem ofIndependentBandAttachment_atom_eq_iff
    (input : IndependentBandAttachment V) (band : input.bandIndex)
    (first second : input.Attachment band) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    ((ofIndependentBandAttachment input).bandFamily band).atom first =
        ((ofIndependentBandAttachment input).bandFamily band).atom second ↔
      input.atom band first = input.atom band second := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  exact Iff.rfl

/-! ## Genuinely absent channels -/

/-- No electronic inventory is supplied. -/
@[simp] theorem ofIndependentBandAttachment_electronic_none
    (input : IndependentBandAttachment V) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (ofIndependentBandAttachment input).electronic? = none := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- No exact rational provenance is supplied. -/
@[simp] theorem ofIndependentBandAttachment_rationalPositions_none
    (input : IndependentBandAttachment V) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (ofIndependentBandAttachment input).rationalPositions? = none := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- The role ledger is empty; no role annotation is fabricated. -/
@[simp] theorem ofIndependentBandAttachment_roles_nil
    (input : IndependentBandAttachment V) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (ofIndependentBandAttachment input).roles = [] := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- The bond-path family is the empty family over `Fin 0`. -/
@[simp] theorem ofIndependentBandAttachment_paths
    (input : IndependentBandAttachment V) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (ofIndependentBandAttachment input).paths = fun edge => Fin.elim0 edge := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- No drawing data is supplied. -/
@[simp] theorem ofIndependentBandAttachment_diagram_none
    (input : IndependentBandAttachment V) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (ofIndependentBandAttachment input).diagram? = none := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- No sparse drawing coordinates are supplied. -/
@[simp] theorem ofIndependentBandAttachment_diagramPartial_none
    (input : IndependentBandAttachment V) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (ofIndependentBandAttachment input).diagramPartial? = none := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- The raw incidence ledger is empty. -/
@[simp] theorem ofIndependentBandAttachment_diagramIncidence_nil
    (input : IndependentBandAttachment V) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (ofIndependentBandAttachment input).diagramIncidence = [] := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- No fragment annotations are supplied. -/
@[simp] theorem ofIndependentBandAttachment_fragments_nil
    (input : IndependentBandAttachment V) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (ofIndependentBandAttachment input).fragments = [] := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- The drawing-convention channel is empty. -/
@[simp] theorem ofIndependentBandAttachment_conventions_nil
    (input : IndependentBandAttachment V) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (ofIndependentBandAttachment input).conventions = [] := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- No numbered cage annotations are supplied. -/
@[simp] theorem ofIndependentBandAttachment_cages_nil
    (input : IndependentBandAttachment V) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (ofIndependentBandAttachment input).cages = [] := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-! ## Exact recovery of the independent input -/

/-- The existing whole-state extractor applied to the ingress returns the original independent
band attachment exactly, as a full dependent record equality.  The graph, the whole conformation,
the band index type, every band, every attachment type, atom map and parameter map are
definitionally the input data; the agreement fields are proposition-valued and are identified by
proof irrelevance.  No inverse map and no original payload are stored in the state. -/
theorem toIndependentBandAttachment_ofIndependentBandAttachment
    (input : IndependentBandAttachment V) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    toIndependentBandAttachment (ofIndependentBandAttachment input) = input := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- The recovered hypergraph is the input hypergraph. -/
@[simp] theorem toIndependentBandAttachment_ofIndependentBandAttachment_graph
    (input : IndependentBandAttachment V) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (toIndependentBandAttachment (ofIndependentBandAttachment input)).graph = input.graph := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- The recovered whole conformation is the input conformation. -/
@[simp] theorem toIndependentBandAttachment_ofIndependentBandAttachment_conformation
    (input : IndependentBandAttachment V) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (toIndependentBandAttachment (ofIndependentBandAttachment input)).conformation =
      input.conformation := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- Each recovered band is the input band. -/
@[simp] theorem toIndependentBandAttachment_ofIndependentBandAttachment_band
    (input : IndependentBandAttachment V) (band : input.bandIndex) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (toIndependentBandAttachment (ofIndependentBandAttachment input)).band band =
      input.band band := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- Each recovered attachment record type is the input record type. -/
@[simp] theorem toIndependentBandAttachment_ofIndependentBandAttachment_Attachment
    (input : IndependentBandAttachment V) (band : input.bandIndex) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (toIndependentBandAttachment (ofIndependentBandAttachment input)).Attachment band =
      input.Attachment band := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- Each recovered attachment record names the input atom label. -/
@[simp] theorem toIndependentBandAttachment_ofIndependentBandAttachment_atom
    (input : IndependentBandAttachment V) (band : input.bandIndex)
    (record : input.Attachment band) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (toIndependentBandAttachment (ofIndependentBandAttachment input)).atom band record =
      input.atom band record := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- Each recovered attachment record keeps the input band parameter point. -/
@[simp] theorem toIndependentBandAttachment_ofIndependentBandAttachment_parameter
    (input : IndependentBandAttachment V) (band : input.bandIndex)
    (record : input.Attachment band) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (toIndependentBandAttachment (ofIndependentBandAttachment input)).parameter band record =
      input.parameter band record := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-! ## Off-band geometry recovery -/

/-- An atom label that no band attaches still keeps its exact real position.  The ingress copies
the whole conformation, so off-band labels are never collapsed, moved or dropped. -/
theorem offBand_conformation_apply
    (input : IndependentBandAttachment V) (v : V) (_offBand : OffBand input v) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (ofIndependentBandAttachment input).conformation v = input.conformation v := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- Every attached real position agrees exactly with the input's positional agreement: the strip
value of the copy is the same real point as before. -/
theorem ofIndependentBandAttachment_attached_position
    (input : IndependentBandAttachment V) (band : input.bandIndex)
    (record : input.Attachment band) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    ((ofIndependentBandAttachment input).bandFamily band).band.strip
        (((ofIndependentBandAttachment input).bandFamily band).parameter record) =
      (ofIndependentBandAttachment input).conformation
        (((ofIndependentBandAttachment input).bandFamily band).atom record) := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  exact (ofIndependentBandAttachment input).band_agreement band record

/-! ## Empty band families -/

/-- An empty band index type is a legal input for the ingress: the band family is then empty while
the graph and the whole conformation remain present. -/
theorem ofIndependentBandAttachment_bandFamily_eq_empty
    (input : IndependentBandAttachment V) [IsEmpty input.bandIndex] :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (ofIndependentBandAttachment input).bandFamily = fun band => isEmptyElim band := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  funext band
  exact isEmptyElim band

/-- The band index type of an empty independent input has cardinality zero. -/
theorem bandIndex_card_eq_zero
    (input : IndependentBandAttachment V) [IsEmpty input.bandIndex] :
    @Fintype.card input.bandIndex input.fintypeBandIndex = 0 :=
  @Fintype.card_eq_zero input.bandIndex input.fintypeBandIndex ‹IsEmpty input.bandIndex›

/-- The bundled family of an empty independent input has zero bands. -/
theorem encodeBundled_bandCount_eq_zero
    (input : IndependentBandAttachment V) (enumeration : V ≃ Fin (Fintype.card V))
    [IsEmpty input.bandIndex] :
    (encodeBundled input enumeration).bandCount = 0 := by
  rw [encodeBundled_bandCount]
  exact @Fintype.card_eq_zero input.bandIndex input.fintypeBandIndex ‹IsEmpty input.bandIndex›

/-! ## Lifting the recovery through the existing encodings -/

/-- The whole existing bundled family over the ingress is exactly the bundled family of the
original independent input, including the retained certified source, the entire geometry and the
`Fin`-enumerated band family. -/
theorem encodeBundled_ofIndependentBandAttachment
    (input : IndependentBandAttachment V) (enumeration : V ≃ Fin (Fintype.card V)) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    encodeBundled (toIndependentBandAttachment (ofIndependentBandAttachment input))
        enumeration =
      encodeBundled input enumeration := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- The existing bundled family over the ingress has zero bands when the input has no band index,
while still retaining the whole source and every conformation point. -/
theorem encodeBundled_bandCount_eq_zero_of_isEmpty
    (input : IndependentBandAttachment V) (enumeration : V ≃ Fin (Fintype.card V))
    [IsEmpty input.bandIndex] :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (encodeBundled (toIndependentBandAttachment (ofIndependentBandAttachment input))
      enumeration).bandCount = 0 := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rw [encodeBundled_bandCount]
  exact @Fintype.card_eq_zero input.bandIndex input.fintypeBandIndex ‹IsEmpty input.bandIndex›

/-- The existing per-band family encoding over the ingress is exactly the per-band encoding of the
original independent input.  `encodedBandFamily` takes the whole state and calls the extractor
internally, so the state is passed directly. -/
theorem encodedBandFamily_ofIndependentBandAttachment
    (input : IndependentBandAttachment V) (enumeration : V ≃ Fin (Fintype.card V))
    (band : input.bandIndex) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    encodedBandFamily (ofIndependentBandAttachment input) enumeration band =
      encodeFamily input enumeration band := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- The existing `Fin`-enumerated band family over the ingress is exactly the `Fin`-enumerated
family of the original independent input.  As above, the whole state is passed directly. -/
theorem encodedBandAt_ofIndependentBandAttachment
    (input : IndependentBandAttachment V) (enumeration : V ≃ Fin (Fintype.card V))
    (index : Fin (@Fintype.card input.bandIndex input.fintypeBandIndex)) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    encodedBandAt (ofIndependentBandAttachment input) enumeration index =
      encodeAll input enumeration index := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

end

end OrganicStereoBandDescriptionIngress
end OneCenter
end TetraStereo
