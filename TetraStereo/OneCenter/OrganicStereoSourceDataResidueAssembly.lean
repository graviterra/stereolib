import TetraStereo.KernelOnly
import TetraStereo.OneCenter.OrganicStereoSourceBoundResidueAssembly
import TetraStereo.OneCenter.OrganicStereoMolecularCanonicalTransport
import Mathlib.Data.List.OfFn

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace TetraStereo.OneCenter

open OrganicStereoIndependentElectronicEncoding
open OrganicStereoMolecularEvidenceAssembly
open OrganicStereoMolecularCanonicalTransport

noncomputable section

variable {V : Type} [DecidableEq V] [Fintype V]
variable {Locant : Type*}

/-!
# Source data composed with source-bound residue assembly and canonical transport

This module composes the approved `FragmentAnnotation.sourceData` channel with the existing
source-bound residue assembly (`OrganicStereoSourceBoundResidueAssembly`) and the existing
canonical finite transport (`OrganicStereoMolecularCanonicalTransport`).

The input is an arbitrary independently supplied `OrganicMolecularEvidence V`, one common atom
enumeration, an **actual** `ResidueIncidenceLedger` over `request.graph.certifiedEncoding` at that
enumeration, its finite `LocantCover`, and one ordered `FragmentSourceDatum V` list per residue.
The `SourceDataSupported` guard requires every anchored atom to be a supported atom of the actual
ledger residue; no anchor is manufactured.

The module proves:

* the derived channel retains the ledger's counts, ordered link list, scoped bindings and naming
  hierarchy, and attaches exactly the supplied ordered source-data lists;
* attaching replaces only the request's `residueLedger?` field (explicit existing-ledger policy);
  graph, conformation, rational positions, electronic, paths, bands, roles, drawing, fragments,
  conventions, cages and frames are unchanged;
* the actual canonical output carries the atom-relabelled channel, and the canonical decoder —
  which reads only the actual output — recovers the full channel, every ordered source-data list
  at every residue (positionally, hence with duplicates and optional payloads), and, separately,
  the original ledger view through the existing `decodeView?`;
* every link retains its actual interaction occurrence index, participant tie and scoped binding;
* the existing request-level inverse applies to attached requests and to arbitrary correlated
  sets of them.

No chemical recognition, residue disjointness, acyclicity or global locant uniqueness is assumed
or derived.  Empty, duplicate, overlapping and cyclic inputs are preserved literally.
-/

/-! ## The real-anchor guard -/

/-- Every anchored atom of every supplied source datum is a supported atom of the actual source
ledger residue, transported through the single encoding atom equivalence.  This is exactly the
invariant required by `encodeWithSourceData`; it is not assumed by this module but supplied by the
caller (family leaves discharge it with the existing `resolveAnchor?` membership lemmas). -/
abbrev SourceDataSupported (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (ledger : ResidueIncidenceLedger Locant (graph.certifiedEncoding eV))
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V)) : Prop :=
  ∀ index, ∀ datum ∈ sourceData index, ∀ atom ∈ datum.atomReferences,
    atom ∈ (ledger.residue index).support.map (encodedAtomEquiv graph eV).symm.toEmbedding

/-! ## The source-data channel -/

/-- The source-bound residue channel extended with ordered per-residue source data.

The channel's declared budgets are the actual ledger residue count and the certified encoding's
actual interaction-list length.  Links, hierarchy and every scoped binding are exactly those of
the existing source-bound encoding; source data are attached alongside each residue's support and
bindings, never instead of them. -/
def sourceDataBoundChannel (codec : LocantCodec Locant) (eV : V ≃ Fin (Fintype.card V))
    (graph : FiniteAtomInteractionHypergraph V)
    (ledger : ResidueIncidenceLedger Locant (graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) graph eV ledger sourceData) :
    ResidueLedgerChannel V where
  residueCount := ledger.residueCount
  interactionCount := (graph.certifiedEncoding eV).input.molecule.interactions.length
  annotation :=
    encodeOfCoverWithSourceData codec (encodedAtomEquiv graph eV) ledger cover sourceData supported

@[simp] theorem sourceDataBoundChannel_residueCount (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (graph : FiniteAtomInteractionHypergraph V)
    (ledger : ResidueIncidenceLedger Locant (graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) graph eV ledger sourceData) :
    (sourceDataBoundChannel codec eV graph ledger cover sourceData supported).residueCount =
      ledger.residueCount := rfl

/-- The channel's interaction budget is exactly the whole graph's actual interaction-list length. -/
@[simp] theorem sourceDataBoundChannel_interactionCount (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (graph : FiniteAtomInteractionHypergraph V)
    (ledger : ResidueIncidenceLedger Locant (graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) graph eV ledger sourceData) :
    (sourceDataBoundChannel codec eV graph ledger cover sourceData supported).interactionCount =
      graph.interactions.length :=
  certifiedEncoding_interactions_length graph eV

/-- The channel's ordered link list is the positional image of the ledger's link list; order and
multiplicity are retained literally. -/
@[simp] theorem sourceDataBoundChannel_links (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (graph : FiniteAtomInteractionHypergraph V)
    (ledger : ResidueIncidenceLedger Locant (graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) graph eV ledger sourceData) :
    (sourceDataBoundChannel codec eV graph ledger cover sourceData supported).annotation.links =
      ledger.links.map (encodeLink codec) := rfl

/-- The optional naming hierarchy is retained verbatim and is independent of the link list. -/
@[simp] theorem sourceDataBoundChannel_hierarchy? (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (graph : FiniteAtomInteractionHypergraph V)
    (ledger : ResidueIncidenceLedger Locant (graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) graph eV ledger sourceData) :
    (sourceDataBoundChannel codec eV graph ledger cover sourceData supported).annotation.hierarchy? =
      ledger.hierarchy? := rfl

theorem sourceDataBoundChannel_links_length (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (graph : FiniteAtomInteractionHypergraph V)
    (ledger : ResidueIncidenceLedger Locant (graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) graph eV ledger sourceData) :
    (sourceDataBoundChannel codec eV graph ledger cover sourceData supported).annotation.links.length =
      ledger.links.length := by
  rw [sourceDataBoundChannel_links, List.length_map]

/-- Positional exactness of the inherited link list: duplicates, order and cycles are preserved. -/
theorem sourceDataBoundChannel_links_getElem? (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (graph : FiniteAtomInteractionHypergraph V)
    (ledger : ResidueIncidenceLedger Locant (graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) graph eV ledger sourceData)
    (index : ℕ) :
    (sourceDataBoundChannel codec eV graph ledger cover sourceData supported).annotation.links[index]? =
      (ledger.links[index]?).map (encodeLink codec) := by
  rw [sourceDataBoundChannel_links, List.getElem?_map]

/-- One encoded residue with its ordered source data attached alongside support and bindings. -/
@[simp] theorem sourceDataBoundChannel_residue (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (graph : FiniteAtomInteractionHypergraph V)
    (ledger : ResidueIncidenceLedger Locant (graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) graph eV ledger sourceData)
    (index : Fin ledger.residueCount) :
    (sourceDataBoundChannel codec eV graph ledger cover sourceData supported).annotation.residue
        index =
      (encodeFragment codec (encodedAtomEquiv graph eV) (ledger.residue index)
        (cover.cover index)).withSourceData (sourceData index) (supported index) := rfl

/-- The encoded support is the actual ledger support moved along the single encoding equivalence;
attaching source data does not change it. -/
@[simp] theorem sourceDataBoundChannel_residue_support (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (graph : FiniteAtomInteractionHypergraph V)
    (ledger : ResidueIncidenceLedger Locant (graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) graph eV ledger sourceData)
    (index : Fin ledger.residueCount) :
    ((sourceDataBoundChannel codec eV graph ledger cover sourceData supported).annotation.residue
        index).support =
      (ledger.residue index).support.map (encodedAtomEquiv graph eV).symm.toEmbedding := by
  rw [sourceDataBoundChannel_residue, FragmentAnnotation.withSourceData_support,
    encodeFragment_support]

/-- The ordered scoped bindings are exactly the existing source-bound encoded bindings. -/
@[simp] theorem sourceDataBoundChannel_residue_bindings (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (graph : FiniteAtomInteractionHypergraph V)
    (ledger : ResidueIncidenceLedger Locant (graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) graph eV ledger sourceData)
    (index : Fin ledger.residueCount) :
    ((sourceDataBoundChannel codec eV graph ledger cover sourceData supported).annotation.residue
        index).bindings =
      (cover.cover index).map (fun locant =>
        (codec.code locant, ((ledger.residue index).incidence locant).map
          (encodedAtomEquiv graph eV).symm)) := by
  rw [sourceDataBoundChannel_residue, FragmentAnnotation.withSourceData_bindings,
    encodeFragment_bindings]

/-- Every residue's ordered source-data list is exactly the supplied list: order, multiplicity and
every constructor payload are retained literally. -/
@[simp] theorem sourceDataBoundChannel_residue_sourceData (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (graph : FiniteAtomInteractionHypergraph V)
    (ledger : ResidueIncidenceLedger Locant (graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) graph eV ledger sourceData)
    (index : Fin ledger.residueCount) :
    ((sourceDataBoundChannel codec eV graph ledger cover sourceData supported).annotation.residue
        index).sourceData = sourceData index := by
  rw [sourceDataBoundChannel_residue]
  simp

/-- Positional lookup in the attached ordered source-data list is positional lookup in the
supplied list (duplicates stay duplicated). -/
theorem sourceDataBoundChannel_residue_sourceDataAt? (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (graph : FiniteAtomInteractionHypergraph V)
    (ledger : ResidueIncidenceLedger Locant (graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) graph eV ledger sourceData)
    (index : Fin ledger.residueCount) (position : ℕ) :
    ((sourceDataBoundChannel codec eV graph ledger cover sourceData supported).annotation.residue
        index).sourceDataAt? position = (sourceData index)[position]? := by
  unfold FragmentAnnotation.sourceDataAt?
  rw [sourceDataBoundChannel_residue_sourceData]

/-- Real-supported anchors: every anchored atom of an attached datum belongs to the encoded
residue support, hence to the actual ledger residue support transported by the encoding. -/
theorem sourceDataBoundChannel_sourceData_supported (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (graph : FiniteAtomInteractionHypergraph V)
    (ledger : ResidueIncidenceLedger Locant (graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) graph eV ledger sourceData)
    (index : Fin ledger.residueCount) {datum : FragmentSourceDatum V}
    (member : datum ∈ sourceData index) {atom : V} (atomMem : atom ∈ datum.atomReferences) :
    atom ∈ ((sourceDataBoundChannel codec eV graph ledger cover sourceData supported).annotation.residue
      index).support := by
  rw [sourceDataBoundChannel_residue_support]
  exact supported index datum member atom atomMem

/-- Empty source data recover the pre-extension source-bound channel exactly, so existing
consumers are unchanged by the source-data extension. -/
theorem sourceDataBoundChannel_empty (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (graph : FiniteAtomInteractionHypergraph V)
    (ledger : ResidueIncidenceLedger Locant (graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (supported : SourceDataSupported (Locant := Locant) graph eV ledger (fun _ => [])) :
    sourceDataBoundChannel codec eV graph ledger cover (fun _ => []) supported =
      residueLedgerChannelOfEncoded codec (encodedAtomEquiv graph eV) ledger cover.cover := by
  unfold sourceDataBoundChannel residueLedgerChannelOfEncoded
  apply congrArg
    (fun annotation =>
      ({ residueCount := ledger.residueCount
         interactionCount := (graph.certifiedEncoding eV).input.molecule.interactions.length
         annotation := annotation } : ResidueLedgerChannel V))
  exact encodeWithSourceData_nil codec (encodedAtomEquiv graph eV) ledger cover.cover

/-! ## Inherited actual link occurrences and endpoint ties -/

/-- Every link of the derived channel is the encoding of a raw ledger link and inherits its actual
source interaction occurrence.  The resolved source atom is a participant of that actual
interaction, its label is a participant of the same interaction, and the scoped binding is the one
stored in the attached channel. -/
theorem sourceDataBoundChannel_link_source_correct (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (graph : FiniteAtomInteractionHypergraph V)
    (ledger : ResidueIncidenceLedger Locant (graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) graph eV ledger sourceData)
    {link : AnnotatedResidueLink ledger.residueCount
      (sourceDataBoundChannel codec eV graph ledger cover sourceData supported).interactionCount}
    (member : link ∈
      (sourceDataBoundChannel codec eV graph ledger cover sourceData supported).annotation.links) :
    ∃ raw ∈ ledger.links, link = encodeLink codec raw ∧
      ∃ atom : Fin (graph.certifiedEncoding eV).input.molecule.atomCount,
        (ledger.residue raw.source).incidence raw.sourceLocant = some atom ∧
        sourceAtomOfEncoded graph eV atom ∈
          (graph.interactions.get
            (residueSourceInteractionIndex graph eV raw.interaction)).1 ∧
        (codec.code raw.sourceLocant, some (sourceAtomOfEncoded graph eV atom)) ∈
          ((sourceDataBoundChannel codec eV graph ledger cover sourceData supported).annotation.residue
            raw.source).bindings := by
  rw [sourceDataBoundChannel_links] at member
  obtain ⟨raw, rawMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨atom, found, participant⟩ := ledger.link_source_mem raw rawMember
  refine ⟨raw, rawMember, rfl, atom, found, ?_, ?_⟩
  · exact sourceAtomOfEncoded_mem_participants graph eV raw.interaction atom participant
  · rw [sourceDataBoundChannel_residue_bindings]
    refine List.mem_map.mpr ⟨raw.sourceLocant,
      cover.covers raw.source raw.sourceLocant atom found, ?_⟩
    simp [found, sourceAtomOfEncoded]

/-- Target-endpoint mirror of `sourceDataBoundChannel_link_source_correct`. -/
theorem sourceDataBoundChannel_link_target_correct (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (graph : FiniteAtomInteractionHypergraph V)
    (ledger : ResidueIncidenceLedger Locant (graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) graph eV ledger sourceData)
    {link : AnnotatedResidueLink ledger.residueCount
      (sourceDataBoundChannel codec eV graph ledger cover sourceData supported).interactionCount}
    (member : link ∈
      (sourceDataBoundChannel codec eV graph ledger cover sourceData supported).annotation.links) :
    ∃ raw ∈ ledger.links, link = encodeLink codec raw ∧
      ∃ atom : Fin (graph.certifiedEncoding eV).input.molecule.atomCount,
        (ledger.residue raw.target).incidence raw.targetLocant = some atom ∧
        sourceAtomOfEncoded graph eV atom ∈
          (graph.interactions.get
            (residueSourceInteractionIndex graph eV raw.interaction)).1 ∧
        (codec.code raw.targetLocant, some (sourceAtomOfEncoded graph eV atom)) ∈
          ((sourceDataBoundChannel codec eV graph ledger cover sourceData supported).annotation.residue
            raw.target).bindings := by
  rw [sourceDataBoundChannel_links] at member
  obtain ⟨raw, rawMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨atom, found, participant⟩ := ledger.link_target_mem raw rawMember
  refine ⟨raw, rawMember, rfl, atom, found, ?_, ?_⟩
  · exact sourceAtomOfEncoded_mem_participants graph eV raw.interaction atom participant
  · rw [sourceDataBoundChannel_residue_bindings]
    refine List.mem_map.mpr ⟨raw.targetLocant,
      cover.covers raw.target raw.targetLocant atom found, ?_⟩
    simp [found, sourceAtomOfEncoded]

/-- Occurrence indices stored in the attached channel are bounded by the actual certified
interaction count. -/
theorem sourceDataBoundChannel_link_occurrence_bound (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (graph : FiniteAtomInteractionHypergraph V)
    (ledger : ResidueIncidenceLedger Locant (graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) graph eV ledger sourceData)
    {link : AnnotatedResidueLink ledger.residueCount
      (sourceDataBoundChannel codec eV graph ledger cover sourceData supported).interactionCount}
    (_member : link ∈
      (sourceDataBoundChannel codec eV graph ledger cover sourceData supported).annotation.links) :
    link.interaction.val <
      (graph.certifiedEncoding eV).input.molecule.interactions.length :=
  link.interaction.isLt

/-! ## Request attachment and the explicit existing-ledger policy -/

/-- Attach a residue channel to an independently supplied request by replacing exactly the
`residueLedger?` field of that request. -/
def attachSourceDataResidueLedgerRequest (request : OrganicMolecularEvidence V)
    (channel : ResidueLedgerChannel V) : OrganicMolecularEvidence V :=
  { request with residueLedger? := some channel }

/-- The explicit existing-ledger policy of the attachment.

The derived source-bound channel is the attached `residueLedger?` value.  A previously supplied
optional ledger channel is superseded in that one field (channels are not merged, because the
schema carries one optional channel).  Every other channel of the request is retained exactly. -/
structure SourceDataAttachmentPolicy (request attached : OrganicMolecularEvidence V)
    (channel : ResidueLedgerChannel V) : Prop where
  /-- The attached request's channel is the derived channel (any earlier one is replaced). -/
  residueLedger_replaced : attached.residueLedger? = some channel
  /-- The input graph is retained. -/
  graph_retained : attached.graph = request.graph
  /-- The shared conformation is retained. -/
  conformation_retained : attached.conformation = request.conformation
  /-- Optional rational provenance is retained. -/
  rationalPositions_retained : attached.rationalPositions? = request.rationalPositions?
  /-- The optional electronic inventory is retained. -/
  electronic_retained : attached.electronic? = request.electronic?
  /-- The optional bond-path family is retained. -/
  paths_retained : attached.paths? = request.paths?
  /-- The optional band family is retained. -/
  bands_retained : attached.bands? = request.bands?
  /-- The ordered role ledger is retained. -/
  roles_retained : attached.roles = request.roles
  /-- Optional drawing data are retained. -/
  diagram_retained : attached.diagram? = request.diagram?
  /-- Optional sparse drawing positions are retained. -/
  diagramPartial_retained : attached.diagramPartial? = request.diagramPartial?
  /-- The sparse incidence ledger is retained. -/
  diagramIncidence_retained : attached.diagramIncidence = request.diagramIncidence
  /-- Ordered fragment metadata are retained. -/
  fragments_retained : attached.fragments = request.fragments
  /-- The convention channel is retained. -/
  conventions_retained : attached.conventions = request.conventions
  /-- Ordered cage metadata are retained. -/
  cages_retained : attached.cages = request.cages
  /-- Ordered frame metadata are retained. -/
  frames_retained : attached.frames = request.frames

/-- The attachment satisfies its explicit policy. -/
theorem attachSourceDataResidueLedgerRequest_policy (request : OrganicMolecularEvidence V)
    (channel : ResidueLedgerChannel V) :
    SourceDataAttachmentPolicy request
      (attachSourceDataResidueLedgerRequest request channel) channel := by
  constructor <;> rfl

@[simp] theorem attachSourceDataResidueLedgerRequest_residueLedger?
    (request : OrganicMolecularEvidence V) (channel : ResidueLedgerChannel V) :
    (attachSourceDataResidueLedgerRequest request channel).residueLedger? = some channel := rfl

@[simp] theorem attachSourceDataResidueLedgerRequest_graph
    (request : OrganicMolecularEvidence V) (channel : ResidueLedgerChannel V) :
    (attachSourceDataResidueLedgerRequest request channel).graph = request.graph := rfl

@[simp] theorem attachSourceDataResidueLedgerRequest_conformation
    (request : OrganicMolecularEvidence V) (channel : ResidueLedgerChannel V) :
    (attachSourceDataResidueLedgerRequest request channel).conformation =
      request.conformation := rfl

@[simp] theorem attachSourceDataResidueLedgerRequest_electronic?
    (request : OrganicMolecularEvidence V) (channel : ResidueLedgerChannel V) :
    (attachSourceDataResidueLedgerRequest request channel).electronic? = request.electronic? := rfl

@[simp] theorem attachSourceDataResidueLedgerRequest_paths?
    (request : OrganicMolecularEvidence V) (channel : ResidueLedgerChannel V) :
    (attachSourceDataResidueLedgerRequest request channel).paths? = request.paths? := rfl

@[simp] theorem attachSourceDataResidueLedgerRequest_bands?
    (request : OrganicMolecularEvidence V) (channel : ResidueLedgerChannel V) :
    (attachSourceDataResidueLedgerRequest request channel).bands? = request.bands? := rfl

@[simp] theorem attachSourceDataResidueLedgerRequest_roles
    (request : OrganicMolecularEvidence V) (channel : ResidueLedgerChannel V) :
    (attachSourceDataResidueLedgerRequest request channel).roles = request.roles := rfl

@[simp] theorem attachSourceDataResidueLedgerRequest_fragments
    (request : OrganicMolecularEvidence V) (channel : ResidueLedgerChannel V) :
    (attachSourceDataResidueLedgerRequest request channel).fragments = request.fragments := rfl

@[simp] theorem attachSourceDataResidueLedgerRequest_conventions
    (request : OrganicMolecularEvidence V) (channel : ResidueLedgerChannel V) :
    (attachSourceDataResidueLedgerRequest request channel).conventions =
      request.conventions := rfl

@[simp] theorem attachSourceDataResidueLedgerRequest_cages
    (request : OrganicMolecularEvidence V) (channel : ResidueLedgerChannel V) :
    (attachSourceDataResidueLedgerRequest request channel).cages = request.cages := rfl

@[simp] theorem attachSourceDataResidueLedgerRequest_frames
    (request : OrganicMolecularEvidence V) (channel : ResidueLedgerChannel V) :
    (attachSourceDataResidueLedgerRequest request channel).frames = request.frames := rfl

/-- The request with the derived source-data channel attached. -/
def sourceDataAttachedRequest (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData) :
    OrganicMolecularEvidence V :=
  attachSourceDataResidueLedgerRequest request
    (sourceDataBoundChannel codec eV request.graph ledger cover sourceData supported)

@[simp] theorem sourceDataAttachedRequest_residueLedger? (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData) :
    (sourceDataAttachedRequest codec eV request ledger cover sourceData supported).residueLedger? =
      some (sourceDataBoundChannel codec eV request.graph ledger cover sourceData supported) := rfl

@[simp] theorem sourceDataAttachedRequest_graph (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData) :
    (sourceDataAttachedRequest codec eV request ledger cover sourceData supported).graph =
      request.graph := rfl

/-! ## Assembly and canonical output -/

/-- The actual assembly carries exactly the derived channel, because every assembly branch copies
the request's optional residue channel unchanged. -/
theorem assemble_sourceDataAttachedRequest_residueLedger? (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData) :
    (assemble (sourceDataAttachedRequest codec eV request ledger cover sourceData supported)).stateResidueLedger? =
      some (sourceDataBoundChannel codec eV request.graph ledger cover sourceData supported) := by
  simpa using
    ((assemble_annotation_projections
      (sourceDataAttachedRequest codec eV request ledger cover sourceData supported)).2.2.2.2.2.2.2.2.1)

/-- The actual canonical output of the attached request. -/
def sourceDataCanonicalOutput (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData) :
    CanonicalOrganicMolecularRepresentation V :=
  canonicalAssemble eV
    (sourceDataAttachedRequest codec eV request ledger cover sourceData supported)

/-! ### Residue-channel projections of the canonical encoder -/

section DescriptionProjections

variable {E B : Type*} [Fintype E] [Fintype B]

/-- Encoding a description into `Fin` coordinates moves only the atom references of the residue
channel; both occurrence budgets, the ordered links and the hierarchy are copied. -/
@[simp] theorem encodeDescription_residueLedger?
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (description : FiniteClassicalStereoDescription V E B) :
    (encodeDescription eV eE eB description).residueLedger? =
      description.residueLedger?.map (ResidueLedgerChannel.relabel eV) := by
  unfold encodeDescription reindexBands reindexEdges relabelDescription relabelWholeState
  rfl

/-- Decoding a canonical description moves the residue channel back along the inverse atom
enumeration; this uses only the encoded payload and the explicit equivalences. -/
@[simp] theorem decodeDescription_residueLedger?
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (encoded : EncodedDescription (Fintype.card V) (Fintype.card E) (Fintype.card B)) :
    (decodeDescription eV eE eB encoded).residueLedger? =
      encoded.residueLedger?.map (ResidueLedgerChannel.relabel eV.symm) := by
  unfold decodeDescription reindexBands reindexEdges relabelDescription relabelWholeState
  rfl

end DescriptionProjections

/-- The actual canonical output carries exactly the atom-relabelled derived channel.  Only the
canonical state and the common enumeration occur on the right-hand side. -/
theorem sourceDataCanonicalOutput_state_residueLedger? (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData) :
    (sourceDataCanonicalOutput codec eV request ledger cover sourceData supported).state.residueLedger? =
      some ((sourceDataBoundChannel codec eV request.graph ledger cover sourceData supported).relabel
        eV) := by
  unfold sourceDataCanonicalOutput
  rw [canonicalAssemble_state]
  simp only [encodeDescription_residueLedger?]
  change Option.map (ResidueLedgerChannel.relabel eV)
      ((assemble (sourceDataAttachedRequest codec eV request ledger cover sourceData
        supported)).stateResidueLedger?) =
    some ((sourceDataBoundChannel codec eV request.graph ledger cover sourceData supported).relabel
      eV)
  rw [assemble_sourceDataAttachedRequest_residueLedger? codec eV request ledger cover sourceData
    supported]
  rfl

/-- The existing request-level inverse applied to the attached request: the decoded canonical
output is exactly the request carrying the derived channel. -/
theorem sourceDataCanonicalOutput_decode (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData) :
    decode (canonicalDecode
        (sourceDataCanonicalOutput codec eV request ledger cover sourceData supported)) =
      sourceDataAttachedRequest codec eV request ledger cover sourceData supported :=
  decode_canonicalAssemble eV _

/-- All non-ledger channels of the decoded canonical output are exactly the original request's
channels, under the explicit existing-ledger policy. -/
theorem sourceDataCanonicalOutput_decode_policy (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData) :
    SourceDataAttachmentPolicy request
      (decode (canonicalDecode
        (sourceDataCanonicalOutput codec eV request ledger cover sourceData supported)))
      (sourceDataBoundChannel codec eV request.graph ledger cover sourceData supported) := by
  rw [sourceDataCanonicalOutput_decode]
  exact attachSourceDataResidueLedgerRequest_policy request _

/-! ## Decoders reading only the actual canonical output -/

/-- Recover the full residue channel from the actual canonical output.  Only the canonical record
is read: the atom enumeration is the one stored in it, and no request or ledger payload is
available to the decoder. -/
def sourceDataResidueChannel? (canonical : CanonicalOrganicMolecularRepresentation V) :
    Option (ResidueLedgerChannel V) :=
  (canonicalDecode canonical).stateResidueLedger?

/-- **Full-channel recovery.**  The canonical decoder returns the complete derived channel:
counts, ordered link list, naming hierarchy, every residue's support/bindings and every ordered
source-data list. -/
theorem sourceDataResidueChannel?_sourceDataCanonicalOutput (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData) :
    sourceDataResidueChannel?
        (sourceDataCanonicalOutput codec eV request ledger cover sourceData supported) =
      some (sourceDataBoundChannel codec eV request.graph ledger cover sourceData supported) := by
  unfold sourceDataResidueChannel? sourceDataCanonicalOutput
  rw [canonicalDecode_canonicalAssemble]
  exact assemble_sourceDataAttachedRequest_residueLedger? codec eV request ledger cover sourceData
    supported

/-- Recover every ordered per-residue source-data list from the actual canonical output.  The
result is the list of residue lists in residue order; no request or ledger payload is read. -/
def decodedSourceDataLists? (canonical : CanonicalOrganicMolecularRepresentation V) :
    Option (List (List (FragmentSourceDatum V))) :=
  (sourceDataResidueChannel? canonical).map fun channel =>
    List.ofFn fun index : Fin channel.residueCount =>
      (channel.annotation.residue index).sourceData

/-- **Ordered source-data recovery.**  The decoded list of residue lists is exactly the supplied
family, preserving every order, duplicate and optional payload. -/
theorem decodedSourceDataLists?_sourceDataCanonicalOutput (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData) :
    decodedSourceDataLists?
        (sourceDataCanonicalOutput codec eV request ledger cover sourceData supported) =
      some (List.ofFn sourceData) := by
  unfold decodedSourceDataLists?
  rw [sourceDataResidueChannel?_sourceDataCanonicalOutput]
  simp only [Option.map_some, Option.some.injEq]
  apply List.ofFn_inj.mpr
  funext index
  exact sourceDataBoundChannel_residue_sourceData codec eV request.graph ledger cover sourceData
    supported index

/-- Positional recovery of one residue's ordered source-data list.  Positions index the list
literal, so repeated data are recovered at every repeated position. -/
theorem decodedSourceDataLists?_getElem? (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData)
    (index : Fin ledger.residueCount) :
    (decodedSourceDataLists?
        (sourceDataCanonicalOutput codec eV request ledger cover sourceData supported)).bind
        (fun lists => lists[index.val]?) = some (sourceData index) := by
  rw [decodedSourceDataLists?_sourceDataCanonicalOutput, Option.bind_some]
  rw [List.getElem?_ofFn, dif_pos index.isLt]

/-- Positional decoder: the ordered source-data list at one residue position, read from the
actual canonical output only. -/
def decodedSourceDataAt? (canonical : CanonicalOrganicMolecularRepresentation V) (index : ℕ) :
    Option (List (FragmentSourceDatum V)) :=
  (decodedSourceDataLists? canonical).bind fun lists => lists[index]?

/-- Positional recovery from the canonical output is exactly the supplied ordered list. -/
theorem decodedSourceDataAt?_sourceDataCanonicalOutput (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData)
    (index : Fin ledger.residueCount) :
    decodedSourceDataAt?
        (sourceDataCanonicalOutput codec eV request ledger cover sourceData supported)
        index.val = some (sourceData index) := by
  unfold decodedSourceDataAt?
  exact decodedSourceDataLists?_getElem? codec eV request ledger cover sourceData supported index

/-- Recover every ordered per-residue source-data list directly at canonical `Fin` atom labels,
without the inverse relabelling.  Only the canonical record is read. -/
def canonicalSourceDataLists? (canonical : CanonicalOrganicMolecularRepresentation V) :
    Option (List (List (FragmentSourceDatum (Fin (Fintype.card V))))) :=
  canonical.state.residueLedger?.map fun channel =>
    List.ofFn fun index : Fin channel.residueCount =>
      (channel.annotation.residue index).sourceData

/-- The actual canonical output carries each supplied list with only the atom reference
relabelled by the common enumeration.  List order, multiplicity and every non-atom payload are
untouched by the relabelling. -/
theorem canonicalSourceDataLists?_sourceDataCanonicalOutput (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData) :
    canonicalSourceDataLists?
        (sourceDataCanonicalOutput codec eV request ledger cover sourceData supported) =
      some (List.ofFn fun index : Fin ledger.residueCount =>
        (sourceData index).map (FragmentSourceDatum.relabel eV)) := by
  unfold canonicalSourceDataLists?
  rw [sourceDataCanonicalOutput_state_residueLedger?]
  simp only [Option.map_some, Option.some.injEq]
  apply List.ofFn_inj.mpr
  funext index
  simp [ResidueLedgerChannel.relabel_annotation, ResidueLedgerAnnotation.relabel_residue,
    FragmentAnnotation.relabel_sourceData, sourceDataBoundChannel_residue_sourceData]

/-- Decode a recovered channel's annotation with the existing view decoder at the encoding
enumeration.  The result does not involve source data. -/
def sourceDataChannelView? (codec : LocantCodec Locant)
    (graph : FiniteAtomInteractionHypergraph V) (eV : V ≃ Fin (Fintype.card V))
    (channel : ResidueLedgerChannel V) :
    Option (ResidueLedgerView Locant
      (graph.certifiedEncoding eV).input.molecule.atomCount
      channel.interactionCount channel.residueCount) :=
  decodeView? codec (encodedAtomEquiv graph eV) channel.annotation

/-- **Separate ledger-view recovery.**  Decoding the derived channel's annotation with the common
codec and enumeration returns exactly the original ledger's observable view: every support, every
scoped incidence, the ordered link list and the naming hierarchy.  This is proved from the
existing `decodeView?` recovery and is independent of source-data attachment. -/
theorem sourceDataChannelView?_sourceDataBoundChannel (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (graph : FiniteAtomInteractionHypergraph V)
    (ledger : ResidueIncidenceLedger Locant (graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) graph eV ledger sourceData) :
    sourceDataChannelView? codec graph eV
        (sourceDataBoundChannel codec eV graph ledger cover sourceData supported) =
      some (viewOfLedger ledger) := by
  unfold sourceDataChannelView? sourceDataBoundChannel
  dsimp only
  exact decodeView?_encodeOfCoverWithSourceData codec (encodedAtomEquiv graph eV) ledger cover
    sourceData supported

/-! ## Bundled recovery facts -/

/-- The canonical output recovers the full channel, every ordered source-data list (with positional
access), and, separately, the original ledger view. -/
theorem sourceDataCanonicalOutput_recovery (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData) :
    sourceDataResidueChannel?
        (sourceDataCanonicalOutput codec eV request ledger cover sourceData supported) =
        some (sourceDataBoundChannel codec eV request.graph ledger cover sourceData supported) ∧
      decodedSourceDataLists?
          (sourceDataCanonicalOutput codec eV request ledger cover sourceData supported) =
        some (List.ofFn sourceData) ∧
      (∀ index : Fin ledger.residueCount,
        (decodedSourceDataLists?
            (sourceDataCanonicalOutput codec eV request ledger cover sourceData supported)).bind
            (fun lists => lists[index.val]?) = some (sourceData index)) ∧
      sourceDataChannelView? codec request.graph eV
        (sourceDataBoundChannel codec eV request.graph ledger cover sourceData supported) =
        some (viewOfLedger ledger) := by
  refine ⟨sourceDataResidueChannel?_sourceDataCanonicalOutput codec eV request ledger cover
      sourceData supported,
    decodedSourceDataLists?_sourceDataCanonicalOutput codec eV request ledger cover sourceData
      supported, ?_,
    sourceDataChannelView?_sourceDataBoundChannel codec eV request.graph ledger cover sourceData
      supported⟩
  intro index
  exact decodedSourceDataLists?_getElem? codec eV request ledger cover sourceData supported index

/-! ## Append / coexistence on one and the same actual source ledger -/

/-- The real-anchor guard for concatenated ordered data follows from guards for the two parts:
no anchor is invented, and the old and new data need not be disjoint. -/
theorem sourceDataSupported_append (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (ledger : ResidueIncidenceLedger Locant (graph.certifiedEncoding eV))
    (oldData newData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (oldSupported : SourceDataSupported (Locant := Locant) graph eV ledger oldData)
    (newSupported : SourceDataSupported (Locant := Locant) graph eV ledger newData) :
    SourceDataSupported (Locant := Locant) graph eV ledger
      (fun index => oldData index ++ newData index) := by
  intro index datum member atom atomMem
  rcases List.mem_append.mp member with oldMember | newMember
  · exact oldSupported index datum oldMember atom atomMem
  · exact newSupported index datum newMember atom atomMem

/-- A channel carrying the existing ordered data followed by new ordered data at every residue,
over the **same actual** certified source ledger and cover.  Existing and new data coexist; no
unrelated ledger is merged and no old annotation data are erased. -/
def sourceDataCoexistingChannel (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (graph : FiniteAtomInteractionHypergraph V)
    (ledger : ResidueIncidenceLedger Locant (graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (oldData newData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (oldSupported : SourceDataSupported (Locant := Locant) graph eV ledger oldData)
    (newSupported : SourceDataSupported (Locant := Locant) graph eV ledger newData) :
    ResidueLedgerChannel V :=
  sourceDataBoundChannel codec eV graph ledger cover
    (fun index => oldData index ++ newData index)
    (sourceDataSupported_append graph eV ledger oldData newData oldSupported newSupported)

/-- The coexisting channel's ordered list is the old list followed by the new list. -/
@[simp] theorem sourceDataCoexistingChannel_residue_sourceData (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (graph : FiniteAtomInteractionHypergraph V)
    (ledger : ResidueIncidenceLedger Locant (graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (oldData newData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (oldSupported : SourceDataSupported (Locant := Locant) graph eV ledger oldData)
    (newSupported : SourceDataSupported (Locant := Locant) graph eV ledger newData)
    (index : Fin ledger.residueCount) :
    ((sourceDataCoexistingChannel codec eV graph ledger cover oldData newData oldSupported
        newSupported).annotation.residue index).sourceData =
      oldData index ++ newData index :=
  sourceDataBoundChannel_residue_sourceData codec eV graph ledger cover
    (fun index => oldData index ++ newData index)
    (sourceDataSupported_append graph eV ledger oldData newData oldSupported newSupported) index

/-- Old ordered data are retained as the exact prefix at every residue. -/
theorem sourceDataCoexistingChannel_old_prefix (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (graph : FiniteAtomInteractionHypergraph V)
    (ledger : ResidueIncidenceLedger Locant (graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (oldData newData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (oldSupported : SourceDataSupported (Locant := Locant) graph eV ledger oldData)
    (newSupported : SourceDataSupported (Locant := Locant) graph eV ledger newData)
    (index : Fin ledger.residueCount) :
    ((sourceDataCoexistingChannel codec eV graph ledger cover oldData newData oldSupported
        newSupported).annotation.residue index).sourceData.take (oldData index).length =
      oldData index := by
  rw [sourceDataCoexistingChannel_residue_sourceData]
  exact List.take_left

/-- New ordered data are the exact suffix, selected by the old prefix length.  This is the
offset-selected read that avoids interpreting the first whole-fragment payload as the new data. -/
theorem sourceDataCoexistingChannel_new_suffix (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (graph : FiniteAtomInteractionHypergraph V)
    (ledger : ResidueIncidenceLedger Locant (graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (oldData newData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (oldSupported : SourceDataSupported (Locant := Locant) graph eV ledger oldData)
    (newSupported : SourceDataSupported (Locant := Locant) graph eV ledger newData)
    (index : Fin ledger.residueCount) :
    ((sourceDataCoexistingChannel codec eV graph ledger cover oldData newData oldSupported
        newSupported).annotation.residue index).sourceData.drop (oldData index).length =
      newData index := by
  rw [sourceDataCoexistingChannel_residue_sourceData]
  exact List.drop_left

/-- The actual ordered link list is unchanged by appending source data. -/
theorem sourceDataCoexistingChannel_links (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (graph : FiniteAtomInteractionHypergraph V)
    (ledger : ResidueIncidenceLedger Locant (graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (oldData newData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (oldSupported : SourceDataSupported (Locant := Locant) graph eV ledger oldData)
    (newSupported : SourceDataSupported (Locant := Locant) graph eV ledger newData) :
    (sourceDataCoexistingChannel codec eV graph ledger cover oldData newData oldSupported
        newSupported).annotation.links =
      (sourceDataBoundChannel codec eV graph ledger cover oldData oldSupported).annotation.links := by
  simp only [sourceDataCoexistingChannel, sourceDataBoundChannel_links]

/-- The optional naming hierarchy is unchanged by appending source data. -/
theorem sourceDataCoexistingChannel_hierarchy? (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (graph : FiniteAtomInteractionHypergraph V)
    (ledger : ResidueIncidenceLedger Locant (graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (oldData newData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (oldSupported : SourceDataSupported (Locant := Locant) graph eV ledger oldData)
    (newSupported : SourceDataSupported (Locant := Locant) graph eV ledger newData) :
    (sourceDataCoexistingChannel codec eV graph ledger cover oldData newData oldSupported
        newSupported).annotation.hierarchy? =
      (sourceDataBoundChannel codec eV graph ledger cover oldData oldSupported).annotation.hierarchy? := by
  simp only [sourceDataCoexistingChannel, sourceDataBoundChannel_hierarchy?]

/-- Every encoded residue support is unchanged by appending source data. -/
theorem sourceDataCoexistingChannel_residue_support (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (graph : FiniteAtomInteractionHypergraph V)
    (ledger : ResidueIncidenceLedger Locant (graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (oldData newData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (oldSupported : SourceDataSupported (Locant := Locant) graph eV ledger oldData)
    (newSupported : SourceDataSupported (Locant := Locant) graph eV ledger newData)
    (index : Fin ledger.residueCount) :
    ((sourceDataCoexistingChannel codec eV graph ledger cover oldData newData oldSupported
        newSupported).annotation.residue index).support =
      ((sourceDataBoundChannel codec eV graph ledger cover oldData oldSupported).annotation.residue
        index).support := by
  simp only [sourceDataCoexistingChannel, sourceDataBoundChannel_residue_support]

/-- Every ordered scoped binding is unchanged by appending source data. -/
theorem sourceDataCoexistingChannel_residue_bindings (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (graph : FiniteAtomInteractionHypergraph V)
    (ledger : ResidueIncidenceLedger Locant (graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (oldData newData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (oldSupported : SourceDataSupported (Locant := Locant) graph eV ledger oldData)
    (newSupported : SourceDataSupported (Locant := Locant) graph eV ledger newData)
    (index : Fin ledger.residueCount) :
    ((sourceDataCoexistingChannel codec eV graph ledger cover oldData newData oldSupported
        newSupported).annotation.residue index).bindings =
      ((sourceDataBoundChannel codec eV graph ledger cover oldData oldSupported).annotation.residue
        index).bindings := by
  simp only [sourceDataCoexistingChannel, sourceDataBoundChannel_residue_bindings]

/-- The request with the coexisting channel attached: existing ordered data first, new ordered
data after, on the same actual source ledger. -/
def sourceDataAppendedRequest (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (oldData newData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (oldSupported : SourceDataSupported (Locant := Locant) request.graph eV ledger oldData)
    (newSupported : SourceDataSupported (Locant := Locant) request.graph eV ledger newData) :
    OrganicMolecularEvidence V :=
  attachSourceDataResidueLedgerRequest request
    (sourceDataCoexistingChannel codec eV request.graph ledger cover oldData newData oldSupported
      newSupported)

@[simp] theorem sourceDataAppendedRequest_residueLedger? (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (oldData newData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (oldSupported : SourceDataSupported (Locant := Locant) request.graph eV ledger oldData)
    (newSupported : SourceDataSupported (Locant := Locant) request.graph eV ledger newData) :
    (sourceDataAppendedRequest codec eV request ledger cover oldData newData oldSupported
        newSupported).residueLedger? =
      some (sourceDataCoexistingChannel codec eV request.graph ledger cover oldData newData
        oldSupported newSupported) := rfl

/-- The actual canonical output of the appended request. -/
def sourceDataAppendedCanonicalOutput (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (oldData newData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (oldSupported : SourceDataSupported (Locant := Locant) request.graph eV ledger oldData)
    (newSupported : SourceDataSupported (Locant := Locant) request.graph eV ledger newData) :
    CanonicalOrganicMolecularRepresentation V :=
  canonicalAssemble eV
    (sourceDataAppendedRequest codec eV request ledger cover oldData newData oldSupported
      newSupported)

/-- The decoder recovers the full coexisting channel from the actual canonical output. -/
theorem sourceDataAppendedCanonicalOutput_channel? (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (oldData newData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (oldSupported : SourceDataSupported (Locant := Locant) request.graph eV ledger oldData)
    (newSupported : SourceDataSupported (Locant := Locant) request.graph eV ledger newData) :
    sourceDataResidueChannel?
        (sourceDataAppendedCanonicalOutput codec eV request ledger cover oldData newData
          oldSupported newSupported) =
      some (sourceDataCoexistingChannel codec eV request.graph ledger cover oldData newData
        oldSupported newSupported) := by
  simpa [sourceDataAppendedCanonicalOutput, sourceDataAppendedRequest,
    sourceDataCoexistingChannel, sourceDataAttachedRequest, sourceDataCanonicalOutput] using
    sourceDataResidueChannel?_sourceDataCanonicalOutput codec eV request ledger cover
      (fun index => oldData index ++ newData index)
      (sourceDataSupported_append request.graph eV ledger oldData newData oldSupported
        newSupported)

/-- The decoder recovers every ordered list as the old list followed by the new list. -/
theorem sourceDataAppendedCanonicalOutput_lists (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (oldData newData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (oldSupported : SourceDataSupported (Locant := Locant) request.graph eV ledger oldData)
    (newSupported : SourceDataSupported (Locant := Locant) request.graph eV ledger newData) :
    decodedSourceDataLists?
        (sourceDataAppendedCanonicalOutput codec eV request ledger cover oldData newData
          oldSupported newSupported) =
      some (List.ofFn fun index : Fin ledger.residueCount =>
        oldData index ++ newData index) := by
  simpa [sourceDataAppendedCanonicalOutput, sourceDataAppendedRequest,
    sourceDataCoexistingChannel, sourceDataAttachedRequest, sourceDataCanonicalOutput] using
    decodedSourceDataLists?_sourceDataCanonicalOutput codec eV request ledger cover
      (fun index => oldData index ++ newData index)
      (sourceDataSupported_append request.graph eV ledger oldData newData oldSupported
        newSupported)

/-- Offset-selected old-prefix read: taking the first `oldData.length` entries of the recovered
list at a residue returns exactly the old ordered list. -/
theorem decodedSourceDataAt?_appended_old_prefix (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (oldData newData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (oldSupported : SourceDataSupported (Locant := Locant) request.graph eV ledger oldData)
    (newSupported : SourceDataSupported (Locant := Locant) request.graph eV ledger newData)
    (index : Fin ledger.residueCount) :
    (decodedSourceDataAt?
        (sourceDataAppendedCanonicalOutput codec eV request ledger cover oldData newData
          oldSupported newSupported) index.val).map
        (fun data => data.take (oldData index).length) = some (oldData index) := by
  unfold decodedSourceDataAt?
  rw [sourceDataAppendedCanonicalOutput_lists, Option.bind_some, List.getElem?_ofFn,
    dif_pos index.isLt, Option.map_some]
  show some ((oldData index ++ newData index).take (oldData index).length) =
    some (oldData index)
  rw [List.take_left]

/-- Offset-selected new-suffix read: dropping the old prefix length from the recovered list at a
residue returns exactly the new ordered list.  The new data are never read as the first payload of
the whole fragment. -/
theorem decodedSourceDataAt?_appended_new_suffix (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (oldData newData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (oldSupported : SourceDataSupported (Locant := Locant) request.graph eV ledger oldData)
    (newSupported : SourceDataSupported (Locant := Locant) request.graph eV ledger newData)
    (index : Fin ledger.residueCount) :
    (decodedSourceDataAt?
        (sourceDataAppendedCanonicalOutput codec eV request ledger cover oldData newData
          oldSupported newSupported) index.val).map
        (fun data => data.drop (oldData index).length) = some (newData index) := by
  unfold decodedSourceDataAt?
  rw [sourceDataAppendedCanonicalOutput_lists, Option.bind_some, List.getElem?_ofFn,
    dif_pos index.isLt, Option.map_some]
  show some ((oldData index ++ newData index).drop (oldData index).length) =
    some (newData index)
  rw [List.drop_left]

/-- **Family coexistence on one actual source ledger.**  If the request's existing ledger is
exactly the same actual source ledger encoded with `oldData` (a structural input tie, not an
assumed output inverse), then the actual canonical output of the appended request:

* carries the coexisting channel, whose links, support, bindings and hierarchy are unchanged;
* retains `oldData` as the exact prefix at every residue;
* exposes `newData` as the exact suffix selected by the old prefix length;
* is decoded using only the actual output record.

No unrelated ledger is merged and no old annotation data are overwritten. -/
theorem sourceDataAppendedCanonicalOutput_recovery (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (oldData newData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (oldSupported : SourceDataSupported (Locant := Locant) request.graph eV ledger oldData)
    (newSupported : SourceDataSupported (Locant := Locant) request.graph eV ledger newData)
    (existing : request.residueLedger? =
      some (sourceDataBoundChannel codec eV request.graph ledger cover oldData oldSupported)) :
    request.residueLedger? =
        some (sourceDataBoundChannel codec eV request.graph ledger cover oldData oldSupported) ∧
      sourceDataResidueChannel?
          (sourceDataAppendedCanonicalOutput codec eV request ledger cover oldData newData
            oldSupported newSupported) =
        some (sourceDataCoexistingChannel codec eV request.graph ledger cover oldData newData
          oldSupported newSupported) ∧
      decodedSourceDataLists?
          (sourceDataAppendedCanonicalOutput codec eV request ledger cover oldData newData
            oldSupported newSupported) =
        some (List.ofFn fun index : Fin ledger.residueCount =>
          oldData index ++ newData index) ∧
      (∀ index : Fin ledger.residueCount,
        (decodedSourceDataAt?
            (sourceDataAppendedCanonicalOutput codec eV request ledger cover oldData newData
              oldSupported newSupported) index.val).map
            (fun data => data.take (oldData index).length) = some (oldData index) ∧
        (decodedSourceDataAt?
            (sourceDataAppendedCanonicalOutput codec eV request ledger cover oldData newData
              oldSupported newSupported) index.val).map
            (fun data => data.drop (oldData index).length) = some (newData index)) ∧
      (sourceDataCoexistingChannel codec eV request.graph ledger cover oldData newData
          oldSupported newSupported).annotation.links =
        (sourceDataBoundChannel codec eV request.graph ledger cover oldData oldSupported).annotation.links ∧
      (sourceDataCoexistingChannel codec eV request.graph ledger cover oldData newData
          oldSupported newSupported).annotation.hierarchy? =
        (sourceDataBoundChannel codec eV request.graph ledger cover oldData oldSupported).annotation.hierarchy? ∧
      (∀ index : Fin ledger.residueCount,
        ((sourceDataCoexistingChannel codec eV request.graph ledger cover oldData newData
            oldSupported newSupported).annotation.residue index).support =
          ((sourceDataBoundChannel codec eV request.graph ledger cover oldData oldSupported).annotation.residue
            index).support ∧
        ((sourceDataCoexistingChannel codec eV request.graph ledger cover oldData newData
            oldSupported newSupported).annotation.residue index).bindings =
          ((sourceDataBoundChannel codec eV request.graph ledger cover oldData oldSupported).annotation.residue
            index).bindings) := by
  refine ⟨existing,
    sourceDataAppendedCanonicalOutput_channel? codec eV request ledger cover oldData newData
      oldSupported newSupported,
    sourceDataAppendedCanonicalOutput_lists codec eV request ledger cover oldData newData
      oldSupported newSupported, ?_,
    sourceDataCoexistingChannel_links codec eV request.graph ledger cover oldData newData
      oldSupported newSupported,
    sourceDataCoexistingChannel_hierarchy? codec eV request.graph ledger cover oldData newData
      oldSupported newSupported, ?_⟩
  · intro index
    exact ⟨decodedSourceDataAt?_appended_old_prefix codec eV request ledger cover oldData newData
        oldSupported newSupported index,
      decodedSourceDataAt?_appended_new_suffix codec eV request ledger cover oldData newData
        oldSupported newSupported index⟩
  · intro index
    exact ⟨sourceDataCoexistingChannel_residue_support codec eV request.graph ledger cover oldData
        newData oldSupported newSupported index,
      sourceDataCoexistingChannel_residue_bindings codec eV request.graph ledger cover oldData
        newData oldSupported newSupported index⟩

/-- Fresh-case exposure: when the request carries no residue channel, the attached request's only
residue channel is the derived source-data channel and the explicit policy still holds. -/
theorem sourceDataAttachedRequest_fresh (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Locant (request.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : SourceDataSupported (Locant := Locant) request.graph eV ledger sourceData)
    (h : request.residueLedger? = none) :
    request.residueLedger? = none ∧
      (sourceDataAttachedRequest codec eV request ledger cover sourceData supported).residueLedger? =
        some (sourceDataBoundChannel codec eV request.graph ledger cover sourceData supported) ∧
      SourceDataAttachmentPolicy request
        (sourceDataAttachedRequest codec eV request ledger cover sourceData supported)
        (sourceDataBoundChannel codec eV request.graph ledger cover sourceData supported) :=
  ⟨h, rfl, attachSourceDataResidueLedgerRequest_policy request _⟩

/-! ## Arbitrary correlated sets of attached requests -/

/-- The existing request inverse applied pointwise to attached requests.  The decoded request is
exactly the attached request, so every channel correlation — including the derived residue channel
and its source data — is retained. -/
theorem decode_canonicalAssemble_sourceDataAttached (eV : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V) (channel : ResidueLedgerChannel V) :
    decode (canonicalDecode
        (canonicalAssemble eV (attachSourceDataResidueLedgerRequest request channel))) =
      attachSourceDataResidueLedgerRequest request channel :=
  decode_canonicalAssemble eV _

/-- **Correlated set recovery.**  For any set of independently supplied requests, any family of
channels attached to them, decoding the actual canonical assembly recovers exactly the attached
requests.  This is the existing set-image inverse; no new chemical claim is made. -/
theorem decode_image_canonicalAssemble_image_sourceDataAttached
    (eV : V ≃ Fin (Fintype.card V)) (requests : Set (OrganicMolecularEvidence V))
    (channelOf : OrganicMolecularEvidence V → ResidueLedgerChannel V) :
    decode '' (canonicalDecode '' (canonicalAssemble eV ''
      ((fun request => attachSourceDataResidueLedgerRequest request (channelOf request)) ''
        requests))) =
      (fun request => attachSourceDataResidueLedgerRequest request (channelOf request)) ''
        requests :=
  decode_image_canonicalDecode_image_canonicalAssemble_image eV _

end

end TetraStereo.OneCenter

/-! Decisive source-binding, recovery and coexistence results are kernel checked. -/
assert_kernel_only TetraStereo.OneCenter.sourceDataBoundChannel_sourceData_supported
assert_kernel_only TetraStereo.OneCenter.sourceDataBoundChannel_link_source_correct
assert_kernel_only TetraStereo.OneCenter.sourceDataBoundChannel_link_target_correct
assert_kernel_only TetraStereo.OneCenter.sourceDataBoundChannel_link_occurrence_bound
assert_kernel_only TetraStereo.OneCenter.sourceDataBoundChannel_links_getElem?
assert_kernel_only TetraStereo.OneCenter.sourceDataBoundChannel_residue_sourceDataAt?
assert_kernel_only TetraStereo.OneCenter.attachSourceDataResidueLedgerRequest_policy
assert_kernel_only TetraStereo.OneCenter.sourceDataCanonicalOutput_state_residueLedger?
assert_kernel_only TetraStereo.OneCenter.sourceDataCanonicalOutput_decode_policy
assert_kernel_only TetraStereo.OneCenter.sourceDataResidueChannel?_sourceDataCanonicalOutput
assert_kernel_only TetraStereo.OneCenter.decodedSourceDataLists?_sourceDataCanonicalOutput
assert_kernel_only TetraStereo.OneCenter.decodedSourceDataLists?_getElem?
assert_kernel_only TetraStereo.OneCenter.decodedSourceDataAt?_sourceDataCanonicalOutput
assert_kernel_only TetraStereo.OneCenter.canonicalSourceDataLists?_sourceDataCanonicalOutput
assert_kernel_only TetraStereo.OneCenter.sourceDataChannelView?_sourceDataBoundChannel
assert_kernel_only TetraStereo.OneCenter.sourceDataCanonicalOutput_recovery
assert_kernel_only TetraStereo.OneCenter.sourceDataSupported_append
assert_kernel_only TetraStereo.OneCenter.sourceDataCoexistingChannel_old_prefix
assert_kernel_only TetraStereo.OneCenter.sourceDataCoexistingChannel_new_suffix
assert_kernel_only TetraStereo.OneCenter.sourceDataCoexistingChannel_links
assert_kernel_only TetraStereo.OneCenter.sourceDataCoexistingChannel_hierarchy?
assert_kernel_only TetraStereo.OneCenter.sourceDataCoexistingChannel_residue_support
assert_kernel_only TetraStereo.OneCenter.sourceDataCoexistingChannel_residue_bindings
assert_kernel_only TetraStereo.OneCenter.sourceDataAppendedCanonicalOutput_channel?
assert_kernel_only TetraStereo.OneCenter.sourceDataAppendedCanonicalOutput_lists
assert_kernel_only TetraStereo.OneCenter.decodedSourceDataAt?_appended_old_prefix
assert_kernel_only TetraStereo.OneCenter.decodedSourceDataAt?_appended_new_suffix
assert_kernel_only TetraStereo.OneCenter.sourceDataAppendedCanonicalOutput_recovery
assert_kernel_only TetraStereo.OneCenter.sourceDataAttachedRequest_fresh
assert_kernel_only TetraStereo.OneCenter.decode_canonicalAssemble_sourceDataAttached
assert_kernel_only TetraStereo.OneCenter.decode_image_canonicalAssemble_image_sourceDataAttached
