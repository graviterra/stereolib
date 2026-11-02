/-
Copyright (c) 2026 TetraStereo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TetraStereo.OneCenter.OrganicStereoFiniteClassicalDescription

/-!
# Attaching an independent band family to an arbitrary whole state

`OrganicStereoIndependentBandEncoding.IndependentBandAttachment V` is the repository's independent
finite band input: an arbitrary finite atom-labelled interaction hypergraph, one whole real
conformation, an arbitrary finite band index type, and for every band index a geometric `Band`
with its own finite attachment type, atom map, parameter map and exact positional agreement.

`OrganicStereoFiniteClassicalDescription.WholeState V E B` is the repository's single correlated
finite description; it carries a graph, an optional electronic inventory, one shared conformation,
rational provenance, a role ledger, a bond-path family over an arbitrary finite `E`, a band family
over an arbitrary finite `B`, drawing data, diagram incidences, fragments, conventions, cages, a
residue ledger and an ordered frame-annotation list.  The existing
`toIndependentBandAttachment` extracts the independent band input from such a state.

This module supplies the general *ingestion* direction.  Instead of building a state from nothing
(as the separate band-description ingress does, with empty drawing/path/electronic channels), it
takes **any existing whole state** and replaces only its band family by the input's bands:

* `attachIndependentBands state input` has type `WholeState V E input.bandIndex`: the band index
  type becomes the input's own finite band index type, and the band family becomes the input's
  band family.  The electronic inventory, rational provenance, role ledger, bond paths, drawing
  data, sparse incidence ledger, fragments, conventions, cages, residue ledger and ordered frame
  list are copied unchanged from the existing state.
* The graph and the single shared conformation are the input's, and the two required hypotheses
  `input.graph = state.graph` and `input.conformation = state.conformation` are *exact*
  equalities, not mere cardinality agreements.  Every state validity field that refers to the
  graph or to the conformation (unpaired-electron agreement, role compatibility, path
  realization, path endpoints, rational-point provenance, diagram backing) is transported along
  those equalities; no validity evidence is assumed or fabricated.
* Every attachment agreement of the constructed state is *derived*: the input's own agreement
  proof, stated at the input's conformation, is reused, and the conformation field of the
  constructed state is definitionally the input's.
* `toIndependentBandAttachment_attachIndependentBands` proves that the existing extractor applied
  to the constructed state returns the original `IndependentBandAttachment` exactly, as a full
  dependent record equality.  The proof is `rfl`: every data field is definitionally an input
  field, and the agreement field is the input's agreement itself.
* The projection lemmas record every unchanged channel, every band projection and the derived
  agreement.  `attachIndependentBands_toIndependentBandAttachment` proves the other round trip:
  attaching the extractor's own family to a state returns that state unchanged.
* `encodedBandFamily_attachIndependentBands` shows that the existing partial-band encoding of the
  attached state is exactly the existing encoding of the independent input.

An empty band index type is allowed: the constructed state then has an empty band family while
every other channel, in particular the whole conformation at every off-band atom, is retained.
Attachment atom maps need not be injective or total: two distinct records that name the same atom
remain two distinct records with the same atom, exactly as in the input.

The old band family of the existing state is intentionally replaced, not merged and not recovered:
nothing here claims that the overwritten bands reappear.  No hidden original input is stored in
the constructed state and no inverse map is postulated.  Nothing here constructs a `Band`, claims
that a band exists, classifies chirality or asserts physical existence.
-/

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace OrganicStereoBandStateAttachment

open OrganicStereoIndependentBandEncoding

noncomputable section

variable {V E B : Type} [DecidableEq V] [Fintype V] [Fintype E] [Fintype B]

/-! ## Off-band atom labels -/

/-- An atom label is off-band for an independent input when no attachment record of any band
names it.  The ingestion imposes no coverage condition; this predicate is used only to state the
off-band retention guarantee. -/
def OffBand (input : IndependentBandAttachment V) (v : V) : Prop :=
  ∀ (band : input.bandIndex) (record : input.Attachment band), input.atom band record ≠ v

/-! ## One band of the independent input as a whole-state band attachment -/

/-- The `BandAttachment` contributed by one independent band index: its geometric band, its own
finite attachment record type, atom map and parameter map are copied literally.  No injectivity,
totality or nonemptiness condition is imposed. -/
def attachedBand (input : IndependentBandAttachment V) (band : input.bandIndex) :
    BandAttachment V where
  band := input.band band
  Attachment := input.Attachment band
  fintypeAttachment := input.fintypeAttachment band
  atom := input.atom band
  parameter := input.parameter band

/-- The constructed attachment carries literally the input band. -/
@[simp] theorem attachedBand_band (input : IndependentBandAttachment V)
    (band : input.bandIndex) :
    (attachedBand input band).band = input.band band := rfl

/-- The constructed attachment carries literally the input attachment record type. -/
@[simp] theorem attachedBand_Attachment (input : IndependentBandAttachment V)
    (band : input.bandIndex) :
    (attachedBand input band).Attachment = input.Attachment band := rfl

/-- The constructed attachment carries literally the input finiteness evidence. -/
@[simp] theorem attachedBand_fintypeAttachment (input : IndependentBandAttachment V)
    (band : input.bandIndex) :
    (attachedBand input band).fintypeAttachment = input.fintypeAttachment band := rfl

/-- The constructed attachment carries literally the input atom map. -/
@[simp] theorem attachedBand_atom (input : IndependentBandAttachment V)
    (band : input.bandIndex) :
    (attachedBand input band).atom = input.atom band := rfl

/-- The constructed attachment carries literally the input parameter map. -/
@[simp] theorem attachedBand_parameter (input : IndependentBandAttachment V)
    (band : input.bandIndex) :
    (attachedBand input band).parameter = input.parameter band := rfl

/-- The positional agreement of one attached band record is exactly the input's agreement.  No
additional positional hypothesis is introduced. -/
theorem attachedBand_agreement (input : IndependentBandAttachment V)
    (band : input.bandIndex) (record : input.Attachment band) :
    (attachedBand input band).band.strip ((attachedBand input band).parameter record) =
      input.conformation ((attachedBand input band).atom record) :=
  input.agreement band record

/-! ## The ingestion -/

/-- Attach an arbitrary independent band family to an arbitrary existing whole state.

The band index type becomes `input.bandIndex`, with the input's stored canonical
`Fintype input.bandIndex` instance threaded through the definition type and body by `letI`.  The
band family is replaced by the input's bands; every other channel is copied from `state`.

The graph and the conformation are taken from the input.  They are tied to the existing state by
the exact equalities `graph_eq` and `conformation_eq`, and all validity fields of the copied
channels that mention the graph or the conformation are transported along those equalities.  The
attachment agreement of the new band family is the input's own agreement proof. -/
def attachIndependentBands (state : WholeState V E B)
    (input : IndependentBandAttachment V)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    WholeState V E input.bandIndex := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  exact
    { graph := input.graph
      electronic? := state.electronic?
      electronic_unpaired := fun channel present owner => by
        rw [graph_eq]
        exact state.electronic_unpaired channel present owner
      conformation := input.conformation
      rationalPositions? := state.rationalPositions?
      rationalPositions_valid := fun positions present atom => by
        rw [conformation_eq]
        exact state.rationalPositions_valid positions present atom
      roles := state.roles
      role_valid := fun annotation member => by
        rw [graph_eq]
        exact state.role_valid annotation member
      paths := state.paths
      path_valid := fun edge => by
        rw [graph_eq]
        exact state.path_valid edge
      path_source_endpoint := fun edge => by
        rw [conformation_eq]
        exact state.path_source_endpoint edge
      path_target_endpoint := fun edge => by
        rw [conformation_eq]
        exact state.path_target_endpoint edge
      bandFamily := fun band => attachedBand input band
      band_agreement := fun band record => input.agreement band record
      diagram? := state.diagram?
      diagramPartial? := state.diagramPartial?
      diagramIncidence := state.diagramIncidence
      diagram_valid := fun row member => by
        rw [graph_eq]
        exact state.diagram_valid row member
      fragments := state.fragments
      conventions := state.conventions
      cages := state.cages
      residueLedger? := state.residueLedger?
      frames := state.frames }

/-! ## The graph and the shared conformation -/

/-- The constructed state's graph is the input graph, hence the existing state's graph through the
supplied exact equality. -/
@[simp] theorem attachIndependentBands_graph (state : WholeState V E B)
    (input : IndependentBandAttachment V)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (attachIndependentBands state input graph_eq conformation_eq).graph = state.graph := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  exact graph_eq

/-- The constructed state's graph is exactly the input graph. -/
@[simp] theorem attachIndependentBands_graph_eq_input (state : WholeState V E B)
    (input : IndependentBandAttachment V)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (attachIndependentBands state input graph_eq conformation_eq).graph = input.graph := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- The constructed state's shared conformation is exactly the existing state's conformation
through the supplied exact equality. -/
@[simp] theorem attachIndependentBands_conformation (state : WholeState V E B)
    (input : IndependentBandAttachment V)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (attachIndependentBands state input graph_eq conformation_eq).conformation =
      state.conformation := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  exact conformation_eq

/-- The constructed state's shared conformation is exactly the input conformation. -/
@[simp] theorem attachIndependentBands_conformation_eq_input (state : WholeState V E B)
    (input : IndependentBandAttachment V)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (attachIndependentBands state input graph_eq conformation_eq).conformation =
      input.conformation := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- Pointwise conformation preservation at every atom label.  The position of an atom is retained
whether or not any band attaches it. -/
@[simp] theorem attachIndependentBands_conformation_apply (state : WholeState V E B)
    (input : IndependentBandAttachment V)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) (v : V) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (attachIndependentBands state input graph_eq conformation_eq).conformation v =
      state.conformation v := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  exact congrFun conformation_eq v

/-- Off-band atom positions are retained.  No band is required to cover `V`, and the hypothesis
records that `v` is named by no attachment record of any band. -/
theorem attachIndependentBands_offband_conformation (state : WholeState V E B)
    (input : IndependentBandAttachment V)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) (v : V)
    (_offBand : OffBand input v) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (attachIndependentBands state input graph_eq conformation_eq).conformation v =
      state.conformation v := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  exact congrFun conformation_eq v

/-! ## Unchanged non-band channels -/

/-- The optional electronic inventory is copied unchanged. -/
@[simp] theorem attachIndependentBands_electronic (state : WholeState V E B)
    (input : IndependentBandAttachment V)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (attachIndependentBands state input graph_eq conformation_eq).electronic? =
      state.electronic? := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- The optional rational provenance is copied unchanged. -/
@[simp] theorem attachIndependentBands_rationalPositions (state : WholeState V E B)
    (input : IndependentBandAttachment V)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (attachIndependentBands state input graph_eq conformation_eq).rationalPositions? =
      state.rationalPositions? := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- The ordered role ledger is copied unchanged, with its order and multiplicity. -/
@[simp] theorem attachIndependentBands_roles (state : WholeState V E B)
    (input : IndependentBandAttachment V)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (attachIndependentBands state input graph_eq conformation_eq).roles = state.roles := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- The bond-path family is copied unchanged, including its arbitrary finite edge type `E`. -/
@[simp] theorem attachIndependentBands_paths (state : WholeState V E B)
    (input : IndependentBandAttachment V)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (attachIndependentBands state input graph_eq conformation_eq).paths = state.paths := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- The optional drawing source is copied unchanged. -/
@[simp] theorem attachIndependentBands_diagram (state : WholeState V E B)
    (input : IndependentBandAttachment V)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (attachIndependentBands state input graph_eq conformation_eq).diagram? =
      state.diagram? := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- The optional sparse partial-position channel is copied unchanged. -/
@[simp] theorem attachIndependentBands_diagramPartial (state : WholeState V E B)
    (input : IndependentBandAttachment V)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (attachIndependentBands state input graph_eq conformation_eq).diagramPartial? =
      state.diagramPartial? := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- The sparse raw incidence ledger is copied unchanged. -/
@[simp] theorem attachIndependentBands_diagramIncidence (state : WholeState V E B)
    (input : IndependentBandAttachment V)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (attachIndependentBands state input graph_eq conformation_eq).diagramIncidence =
      state.diagramIncidence := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- The ordered fragment channel is copied unchanged. -/
@[simp] theorem attachIndependentBands_fragments (state : WholeState V E B)
    (input : IndependentBandAttachment V)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (attachIndependentBands state input graph_eq conformation_eq).fragments =
      state.fragments := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- The ordered drawing-convention channel is copied unchanged. -/
@[simp] theorem attachIndependentBands_conventions (state : WholeState V E B)
    (input : IndependentBandAttachment V)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (attachIndependentBands state input graph_eq conformation_eq).conventions =
      state.conventions := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- The ordered numbered cage/face channel is copied unchanged. -/
@[simp] theorem attachIndependentBands_cages (state : WholeState V E B)
    (input : IndependentBandAttachment V)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (attachIndependentBands state input graph_eq conformation_eq).cages = state.cages := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- The optional residue-link and naming-hierarchy channel is copied unchanged. -/
@[simp] theorem attachIndependentBands_residueLedger (state : WholeState V E B)
    (input : IndependentBandAttachment V)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (attachIndependentBands state input graph_eq conformation_eq).residueLedger? =
      state.residueLedger? := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- The ordered frame-annotation channel is copied unchanged, including order and duplicates. -/
@[simp] theorem attachIndependentBands_frames (state : WholeState V E B)
    (input : IndependentBandAttachment V)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (attachIndependentBands state input graph_eq conformation_eq).frames = state.frames := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-! ## The replaced band family -/

/-- The band family of the constructed state is the input's band family, one `BandAttachment` per
input band index.  The old family of the existing state is not used. -/
@[simp] theorem attachIndependentBands_bandFamily (state : WholeState V E B)
    (input : IndependentBandAttachment V)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (attachIndependentBands state input graph_eq conformation_eq).bandFamily =
      fun band => attachedBand input band := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- Each band index of the constructed state carries exactly the corresponding input band. -/
@[simp] theorem attachIndependentBands_bandFamily_apply (state : WholeState V E B)
    (input : IndependentBandAttachment V)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation)
    (band : input.bandIndex) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (attachIndependentBands state input graph_eq conformation_eq).bandFamily band =
      attachedBand input band := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- The geometric band at every index is exactly the input band. -/
@[simp] theorem attachIndependentBands_bandFamily_band (state : WholeState V E B)
    (input : IndependentBandAttachment V)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation)
    (band : input.bandIndex) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    ((attachIndependentBands state input graph_eq conformation_eq).bandFamily band).band =
      input.band band := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- The attachment record type of every index is exactly the input attachment type. -/
@[simp] theorem attachIndependentBands_bandFamily_Attachment (state : WholeState V E B)
    (input : IndependentBandAttachment V)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation)
    (band : input.bandIndex) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    ((attachIndependentBands state input graph_eq conformation_eq).bandFamily band).Attachment =
      input.Attachment band := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- The finiteness evidence of every attachment type is exactly the input's evidence. -/
@[simp] theorem attachIndependentBands_bandFamily_fintypeAttachment (state : WholeState V E B)
    (input : IndependentBandAttachment V)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation)
    (band : input.bandIndex) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    ((attachIndependentBands state input graph_eq conformation_eq).bandFamily
      band).fintypeAttachment = input.fintypeAttachment band := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- The atom map of every index is exactly the input atom map. -/
@[simp] theorem attachIndependentBands_bandFamily_atom (state : WholeState V E B)
    (input : IndependentBandAttachment V)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation)
    (band : input.bandIndex) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    ((attachIndependentBands state input graph_eq conformation_eq).bandFamily band).atom =
      input.atom band := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- The parameter map of every index is exactly the input parameter map. -/
@[simp] theorem attachIndependentBands_bandFamily_parameter (state : WholeState V E B)
    (input : IndependentBandAttachment V)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation)
    (band : input.bandIndex) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    ((attachIndependentBands state input graph_eq conformation_eq).bandFamily band).parameter =
      input.parameter band := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- Every attachment agreement of the constructed state is the input's own agreement, hence
derived rather than assumed. -/
@[simp] theorem attachIndependentBands_band_agreement (state : WholeState V E B)
    (input : IndependentBandAttachment V)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation)
    (band : input.bandIndex) (record : input.Attachment band) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (attachIndependentBands state input graph_eq conformation_eq).band_agreement band record =
      input.agreement band record := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- The full positional agreement equation of one constructed attachment record. -/
theorem attachIndependentBands_band_agreement_apply (state : WholeState V E B)
    (input : IndependentBandAttachment V)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation)
    (band : input.bandIndex) (record : input.Attachment band) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    ((attachIndependentBands state input graph_eq conformation_eq).bandFamily band).band.strip
        (((attachIndependentBands state input graph_eq conformation_eq).bandFamily
          band).parameter record) =
      (attachIndependentBands state input graph_eq conformation_eq).conformation
        (((attachIndependentBands state input graph_eq conformation_eq).bandFamily
          band).atom record) := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  exact (attachIndependentBands state input graph_eq conformation_eq).band_agreement band record

/-! ## Attachment multiplicity without injectivity -/

/-- Two constructed attachment records name the same atom exactly when the two input records do.
No injectivity of the atom map is assumed or introduced. -/
theorem attachIndependentBands_bandFamily_atom_eq_iff (state : WholeState V E B)
    (input : IndependentBandAttachment V)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation)
    (band : input.bandIndex) (first second : input.Attachment band) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    ((attachIndependentBands state input graph_eq conformation_eq).bandFamily band).atom first =
        ((attachIndependentBands state input graph_eq conformation_eq).bandFamily band).atom
          second ↔
      input.atom band first = input.atom band second := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  exact Iff.rfl

/-- Distinct attachment records that name the same atom remain distinct records in the
constructed state, with equal atom values.  Attachment multiplicity is preserved. -/
theorem attachIndependentBands_bandFamily_same_atom_distinct_records
    (state : WholeState V E B)
    (input : IndependentBandAttachment V)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation)
    (band : input.bandIndex) {first second : input.Attachment band}
    (same_atom : input.atom band first = input.atom band second)
    (distinct : first ≠ second) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    ((attachIndependentBands state input graph_eq conformation_eq).bandFamily band).atom first =
        ((attachIndependentBands state input graph_eq conformation_eq).bandFamily band).atom
          second ∧
      first ≠ second := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  exact ⟨same_atom, distinct⟩

/-- The number of attachment records of a band equals the cardinality of the input's own
attachment type. -/
@[simp] theorem attachIndependentBands_bandFamily_card (state : WholeState V E B)
    (input : IndependentBandAttachment V)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation)
    (band : input.bandIndex) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    @Fintype.card
        (((attachIndependentBands state input graph_eq conformation_eq).bandFamily band).Attachment)
        (((attachIndependentBands state input graph_eq conformation_eq).bandFamily
          band).fintypeAttachment) =
      @Fintype.card (input.Attachment band) (input.fintypeAttachment band) := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-! ## Exact recovery of the independent input -/

/-- The existing whole-state extractor applied to the constructed state returns the original
independent band attachment exactly, as a full dependent record equality.  The graph, the whole
conformation, the band index type, every band, every attachment type, atom map, parameter map and
agreement proof are definitionally the input's.  No hidden original input is stored and no inverse
map is postulated. -/
theorem toIndependentBandAttachment_attachIndependentBands (state : WholeState V E B)
    (input : IndependentBandAttachment V)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    toIndependentBandAttachment (attachIndependentBands state input graph_eq conformation_eq) =
      input := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- The recovered graph is the input graph. -/
@[simp] theorem toIndependentBandAttachment_attachIndependentBands_graph
    (state : WholeState V E B)
    (input : IndependentBandAttachment V)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (toIndependentBandAttachment
      (attachIndependentBands state input graph_eq conformation_eq)).graph = input.graph := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- The recovered whole conformation is the input conformation. -/
@[simp] theorem toIndependentBandAttachment_attachIndependentBands_conformation
    (state : WholeState V E B)
    (input : IndependentBandAttachment V)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (toIndependentBandAttachment
      (attachIndependentBands state input graph_eq conformation_eq)).conformation =
        input.conformation := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- Each recovered band is the input band. -/
@[simp] theorem toIndependentBandAttachment_attachIndependentBands_band
    (state : WholeState V E B)
    (input : IndependentBandAttachment V)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation)
    (band : input.bandIndex) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (toIndependentBandAttachment
      (attachIndependentBands state input graph_eq conformation_eq)).band band =
        input.band band := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- Each recovered attachment record type is the input record type. -/
@[simp] theorem toIndependentBandAttachment_attachIndependentBands_Attachment
    (state : WholeState V E B)
    (input : IndependentBandAttachment V)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation)
    (band : input.bandIndex) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (toIndependentBandAttachment
      (attachIndependentBands state input graph_eq conformation_eq)).Attachment band =
        input.Attachment band := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- Each recovered atom map is the input atom map. -/
@[simp] theorem toIndependentBandAttachment_attachIndependentBands_atom
    (state : WholeState V E B)
    (input : IndependentBandAttachment V)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation)
    (band : input.bandIndex) (record : input.Attachment band) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (toIndependentBandAttachment
      (attachIndependentBands state input graph_eq conformation_eq)).atom band record =
        input.atom band record := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-- Each recovered parameter is the input parameter. -/
@[simp] theorem toIndependentBandAttachment_attachIndependentBands_parameter
    (state : WholeState V E B)
    (input : IndependentBandAttachment V)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation)
    (band : input.bandIndex) (record : input.Attachment band) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (toIndependentBandAttachment
      (attachIndependentBands state input graph_eq conformation_eq)).parameter band record =
        input.parameter band record := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

/-! ## The other round trip: attaching a state's own family returns the state -/

/-- Attaching the extractor's own band family to a whole state returns that state unchanged.  The
two required equalities are `rfl`, the band family is structure-eta equal to the original, and the
validity fields are identified by proof irrelevance in `WholeState.extEq`. -/
theorem attachIndependentBands_toIndependentBandAttachment (state : WholeState V E B) :
    letI : Fintype (toIndependentBandAttachment state).bandIndex :=
      (toIndependentBandAttachment state).fintypeBandIndex
    attachIndependentBands state (toIndependentBandAttachment state) rfl rfl = state := by
  letI : Fintype (toIndependentBandAttachment state).bandIndex :=
    (toIndependentBandAttachment state).fintypeBandIndex
  apply WholeState.extEq
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · funext band
    rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-! ## Compatibility with the existing partial-band encoding -/

/-- The existing `encodeFamily` encoding of the constructed state is exactly the existing encoding
of the independent input at every band index.  This connects the ingestion to the repository's
certified partial-band machinery without re-deriving its results. -/
theorem encodedBandFamily_attachIndependentBands (state : WholeState V E B)
    (input : IndependentBandAttachment V)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation)
    (enumeration : V ≃ Fin (Fintype.card V)) (band : input.bandIndex) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    encodedBandFamily (attachIndependentBands state input graph_eq conformation_eq)
        enumeration band =
      encodeFamily input enumeration band := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  show encodeFamily
      (toIndependentBandAttachment (attachIndependentBands state input graph_eq conformation_eq))
      enumeration band = encodeFamily input enumeration band
  rfl

/-! ## Empty band families -/

/-- With no input band index at all, the constructed state has no band family member: every
purported band index is impossible.  The ingestion still succeeds and every other channel,
including the whole conformation, is present. -/
theorem attachIndependentBands_empty_bandFamily (state : WholeState V E B)
    (input : IndependentBandAttachment V)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation)
    [IsEmpty input.bandIndex] (v : V) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    (∀ band : input.bandIndex,
        ((attachIndependentBands state input graph_eq conformation_eq).bandFamily band).band =
          input.band band) ∧
      (attachIndependentBands state input graph_eq conformation_eq).conformation v =
        state.conformation v := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  exact ⟨fun band => isEmptyElim band, congrFun conformation_eq v⟩

end

end OrganicStereoBandStateAttachment
end OneCenter
end TetraStereo
