import TetraStereo.OneCenter.OrganicStereoFiniteClassicalDescription

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TetraStereo.OneCenter

open OrganicStereoIndependentElectronicEncoding

noncomputable section

variable {V E B : Type*} [DecidableEq V] [Fintype V] [Fintype E] [Fintype B]
variable {Locant : Type*}

/-!
# Source-bound residue-ledger assembly into a whole stereo description

The whole-state record `WholeState V E B` carries an optional residue-link channel
`residueLedger? : Option (ResidueLedgerChannel V)`, and the existing adapter
`residueLedgerChannelOfEncoded` can build such a channel from *any* certified authoritative
input together with an atom equivalence `V ≃ Fin input.molecule.atomCount`.  That adapter does
not relate the supplied input to `state.graph`, so on its own it cannot establish that the
attached links, fragments and naming hierarchy describe the same molecule as the state.

This module closes exactly that gap.  It assembles the channel from a
`ResidueIncidenceLedger Locant (state.graph.certifiedEncoding eV)` — a ledger whose certified
source *is* the whole state's graph at the common enumeration `eV` — and proves:

* the molecule identity `(state.graph.certifiedEncoding eV).input.molecule = state.graph.encode eV`
  (not merely an atom-count equality);
* count alignment of the attached channel against the whole state graph;
* that attaching the channel leaves every physical field of the state unchanged;
* exact recovery of the ordered link list, every scoped fragment support/incidence and the
  optional naming hierarchy (parents and ranks) from the encoded annotation alone, using only
  the caller's `LocantCodec` and `LocantCover`;
* that every actual link endpoint is a participant of the actual whole-state interaction at its
  recorded occurrence index, transported back to a `V`-labelled participant of
  `state.graph.interactions`, and that the same label occurs in the encoded scoped binding of
  the source residue;
* that the full dependent ledger can be reconstructed from encoded data plus a proof-only
  source-bound validity certificate, without storing the original ledger payload in the channel.

A general-source variant treats any supplied `CertifiedAuthoritativeChemicalInput` with an
explicit molecule equality `input.molecule = state.graph.encode eV`.  No chemical recognition,
residue disjointness, acyclicity or global locant uniqueness is assumed or inferred: arbitrary
residue and link counts, duplicate links, overlapping supports and cyclic linkage are preserved
literally.
-/

/-! ## The certified encoding of the whole-state graph -/

/-- The ledger's certified input is the whole state's graph at the common enumeration: this is a
molecule identity, not an atom-count coincidence. -/
theorem certifiedEncoding_molecule_identity (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V)) :
    (graph.certifiedEncoding eV).input.molecule = graph.encode eV := rfl

/-- The encoded atom count is the number of independent atom labels. -/
@[simp] theorem certifiedEncoding_atomCount (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V)) :
    (graph.certifiedEncoding eV).input.molecule.atomCount = Fintype.card V := by
  simp [FiniteAtomInteractionHypergraph.certifiedEncoding_input,
    FiniteAtomInteractionHypergraph.encodeAuthoritative_molecule]

/-- The encoded interaction count is exactly the whole state graph's interaction-list length. -/
@[simp] theorem certifiedEncoding_interactions_length
    (graph : FiniteAtomInteractionHypergraph V) (eV : V ≃ Fin (Fintype.card V)) :
    (graph.certifiedEncoding eV).input.molecule.interactions.length =
      graph.interactions.length := by
  simp [FiniteAtomInteractionHypergraph.certifiedEncoding_input,
    FiniteAtomInteractionHypergraph.encodeAuthoritative_molecule,
    FiniteAtomInteractionHypergraph.encode]

/-- The interaction index of an encoded interaction, transported to the whole-state graph. -/
def residueSourceInteractionIndex (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (index : Fin (graph.certifiedEncoding eV).input.molecule.interactions.length) :
    Fin graph.interactions.length :=
  ⟨index.val, certifiedEncoding_interactions_length graph eV ▸ index.isLt⟩

@[simp] theorem residueSourceInteractionIndex_val (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (index : Fin (graph.certifiedEncoding eV).input.molecule.interactions.length) :
    (residueSourceInteractionIndex graph eV index).val = index.val := rfl

/-- Exact lookup in the encoded interaction list: the encoded interaction at an occurrence index
is precisely the encoding of the whole-state hyperedge at that same index. -/
theorem certifiedEncoding_interactions_get (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (index : Fin (graph.certifiedEncoding eV).input.molecule.interactions.length) :
    (graph.certifiedEncoding eV).input.molecule.interactions.get index =
      FiniteAtomInteractionHypergraph.encodeInteraction eV
        (graph.interactions.get (residueSourceInteractionIndex graph eV index)) := by
  have encodedLookup := listGet?_eq_some_get
    (graph.certifiedEncoding eV).input.molecule.interactions index
  have sourceLookup :=
    FiniteAtomInteractionHypergraph.certifiedEncoding_interactionAt graph eV index.val
      (residueSourceInteractionIndex graph eV index).isLt
  rw [sourceLookup] at encodedLookup
  exact (Option.some.inj encodedLookup).symm

/-- Participant membership in an encoded hyperedge is exactly membership of the enumerated label
in the source hyperedge.  No participant is invented and no order is changed. -/
theorem encodeInteraction_participants_mem_iff (eV : V ≃ Fin (Fintype.card V))
    (edge : List V × SemanticInteractionKind) (value : ℕ) :
    value ∈ (FiniteAtomInteractionHypergraph.encodeInteraction eV edge).participants ↔
      ∃ label ∈ edge.1, (eV label).val = value := by
  simp [FiniteAtomInteractionHypergraph.encodeInteraction]

/-- The `V`-label of an encoded atom: the inverse of the single common enumeration. -/
def sourceAtomOfEncoded (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (atom : Fin (graph.certifiedEncoding eV).input.molecule.atomCount) : V :=
  (encodedAtomEquiv graph eV).symm atom

@[simp] theorem encodedAtomEquiv_sourceAtomOfEncoded
    (graph : FiniteAtomInteractionHypergraph V) (eV : V ≃ Fin (Fintype.card V))
    (atom : Fin (graph.certifiedEncoding eV).input.molecule.atomCount) :
    encodedAtomEquiv graph eV (sourceAtomOfEncoded graph eV atom) = atom :=
  Equiv.apply_symm_apply (encodedAtomEquiv graph eV) atom

/-- An enumeration label with the same numeral as an encoded atom is exactly that atom's inverse
image. -/
theorem eq_sourceAtomOfEncoded_of_val_eq (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V)) {label : V}
    {atom : Fin (graph.certifiedEncoding eV).input.molecule.atomCount}
    (valueEq : (eV label).val = atom.val) :
    label = sourceAtomOfEncoded graph eV atom := by
  have atomEq : encodedAtomEquiv graph eV label = atom :=
    Fin.ext (by simpa using valueEq)
  rw [sourceAtomOfEncoded, ← atomEq, Equiv.symm_apply_apply]

/-- A participant of an encoded whole-state interaction transports to a `V`-labelled participant
of the actual whole-state interaction. -/
theorem sourceAtomOfEncoded_mem_participants
    (graph : FiniteAtomInteractionHypergraph V) (eV : V ≃ Fin (Fintype.card V))
    (index : Fin (graph.certifiedEncoding eV).input.molecule.interactions.length)
    (atom : Fin (graph.certifiedEncoding eV).input.molecule.atomCount)
    (member : atom.val ∈
      ((graph.certifiedEncoding eV).input.molecule.interactions.get index).participants) :
    sourceAtomOfEncoded graph eV atom ∈
      (graph.interactions.get (residueSourceInteractionIndex graph eV index)).1 := by
  have encodedMember : atom.val ∈
      (FiniteAtomInteractionHypergraph.encodeInteraction eV
        (graph.interactions.get (residueSourceInteractionIndex graph eV index))).participants := by
    rwa [← certifiedEncoding_interactions_get graph eV index]
  obtain ⟨label, labelMember, valueEq⟩ :=
    (encodeInteraction_participants_mem_iff eV _ atom.val).mp encodedMember
  rw [← eq_sourceAtomOfEncoded_of_val_eq graph eV valueEq]
  exact labelMember

/-! ## The source-bound channel and its attachment -/

/-- The residue channel assembled from a ledger whose certified source is the whole state's graph
at the common enumeration.  Counts, link order, scoped bindings and the naming hierarchy are those
of the supplied ledger; the atom equivalence is the single `encodedAtomEquiv` already induced by
the graph encoding. -/
def sourceBoundChannel (codec : LocantCodec Locant) (eV : V ≃ Fin (Fintype.card V))
    (state : WholeState V E B)
    (ledger : ResidueIncidenceLedger Locant (state.graph.certifiedEncoding eV))
    (cover : LocantCover ledger) : ResidueLedgerChannel V :=
  residueLedgerChannelOfEncoded codec (encodedAtomEquiv state.graph eV) ledger cover.cover

@[simp] theorem sourceBoundChannel_residueCount (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (state : WholeState V E B)
    (ledger : ResidueIncidenceLedger Locant (state.graph.certifiedEncoding eV))
    (cover : LocantCover ledger) :
    (sourceBoundChannel codec eV state ledger cover).residueCount = ledger.residueCount := rfl

/-- Count alignment against the whole state graph: the channel's interaction budget is exactly
the actual interaction-list length of the state's graph. -/
@[simp] theorem sourceBoundChannel_interactionCount (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (state : WholeState V E B)
    (ledger : ResidueIncidenceLedger Locant (state.graph.certifiedEncoding eV))
    (cover : LocantCover ledger) :
    (sourceBoundChannel codec eV state ledger cover).interactionCount =
      state.graph.interactions.length := by
  unfold sourceBoundChannel residueLedgerChannelOfEncoded
  exact certifiedEncoding_interactions_length state.graph eV

@[simp] theorem sourceBoundChannel_annotation (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (state : WholeState V E B)
    (ledger : ResidueIncidenceLedger Locant (state.graph.certifiedEncoding eV))
    (cover : LocantCover ledger) :
    (sourceBoundChannel codec eV state ledger cover).annotation =
      TetraStereo.OneCenter.encode codec (encodedAtomEquiv state.graph eV) ledger cover.cover :=
  rfl

/-- The attached channel's ordered link list is the positional image of the supplied ledger's
link list; order and multiplicity are retained. -/
@[simp] theorem sourceBoundChannel_links (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (state : WholeState V E B)
    (ledger : ResidueIncidenceLedger Locant (state.graph.certifiedEncoding eV))
    (cover : LocantCover ledger) :
    (sourceBoundChannel codec eV state ledger cover).annotation.links =
      ledger.links.map (encodeLink codec) := rfl

theorem sourceBoundChannel_links_length (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (state : WholeState V E B)
    (ledger : ResidueIncidenceLedger Locant (state.graph.certifiedEncoding eV))
    (cover : LocantCover ledger) :
    (sourceBoundChannel codec eV state ledger cover).annotation.links.length =
      ledger.links.length := by
  rw [sourceBoundChannel_links, List.length_map]

/-- Positional exactness of the attached link list: duplicates and order are preserved literally. -/
theorem sourceBoundChannel_links_getElem? (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (state : WholeState V E B)
    (ledger : ResidueIncidenceLedger Locant (state.graph.certifiedEncoding eV))
    (cover : LocantCover ledger) (index : ℕ) :
    (sourceBoundChannel codec eV state ledger cover).annotation.links[index]? =
      (ledger.links[index]?).map (encodeLink codec) := by
  rw [sourceBoundChannel_links, List.getElem?_map]

/-- Directed link cycles are retained and reflected exactly: no link is deduplicated, linearised
or removed. -/
theorem sourceBoundChannel_twoCycle_iff (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (state : WholeState V E B)
    (ledger : ResidueIncidenceLedger Locant (state.graph.certifiedEncoding eV))
    (cover : LocantCover ledger) :
    AnnotatedLinkTwoCycle (sourceBoundChannel codec eV state ledger cover).annotation.links ↔
      LinkTwoCycle ledger.links := by
  have := encodeLink_twoCycle_iff (input := state.graph.certifiedEncoding eV)
    codec (encodedAtomEquiv state.graph eV) ledger cover.cover
  simpa [sourceBoundChannel, residueLedgerChannelOfEncoded] using this

/-! ## Attaching the channel without changing any physical field -/

/-- Attach a source-bound residue channel to a whole state by a record update.  Every physical
field is untouched. -/
def attachSourceBoundResidueLedger (state : WholeState V E B)
    (channel : ResidueLedgerChannel V) : WholeState V E B :=
  withResidueLedger state channel

@[simp] theorem attachSourceBoundResidueLedger_graph (state : WholeState V E B)
    (channel : ResidueLedgerChannel V) :
    (attachSourceBoundResidueLedger state channel).graph = state.graph := rfl

@[simp] theorem attachSourceBoundResidueLedger_electronic (state : WholeState V E B)
    (channel : ResidueLedgerChannel V) :
    (attachSourceBoundResidueLedger state channel).electronic? = state.electronic? := rfl

@[simp] theorem attachSourceBoundResidueLedger_conformation (state : WholeState V E B)
    (channel : ResidueLedgerChannel V) :
    (attachSourceBoundResidueLedger state channel).conformation = state.conformation := rfl

@[simp] theorem attachSourceBoundResidueLedger_rational (state : WholeState V E B)
    (channel : ResidueLedgerChannel V) :
    (attachSourceBoundResidueLedger state channel).rationalPositions? =
      state.rationalPositions? := rfl

@[simp] theorem attachSourceBoundResidueLedger_roles (state : WholeState V E B)
    (channel : ResidueLedgerChannel V) :
    (attachSourceBoundResidueLedger state channel).roles = state.roles := rfl

@[simp] theorem attachSourceBoundResidueLedger_paths (state : WholeState V E B)
    (channel : ResidueLedgerChannel V) :
    (attachSourceBoundResidueLedger state channel).paths = state.paths := rfl

@[simp] theorem attachSourceBoundResidueLedger_bandFamily (state : WholeState V E B)
    (channel : ResidueLedgerChannel V) :
    (attachSourceBoundResidueLedger state channel).bandFamily = state.bandFamily := rfl

@[simp] theorem attachSourceBoundResidueLedger_diagram (state : WholeState V E B)
    (channel : ResidueLedgerChannel V) :
    (attachSourceBoundResidueLedger state channel).diagram? = state.diagram? := rfl

@[simp] theorem attachSourceBoundResidueLedger_diagramPartial (state : WholeState V E B)
    (channel : ResidueLedgerChannel V) :
    (attachSourceBoundResidueLedger state channel).diagramPartial? = state.diagramPartial? := rfl

@[simp] theorem attachSourceBoundResidueLedger_diagramIncidence (state : WholeState V E B)
    (channel : ResidueLedgerChannel V) :
    (attachSourceBoundResidueLedger state channel).diagramIncidence =
      state.diagramIncidence := rfl

@[simp] theorem attachSourceBoundResidueLedger_fragments (state : WholeState V E B)
    (channel : ResidueLedgerChannel V) :
    (attachSourceBoundResidueLedger state channel).fragments = state.fragments := rfl

@[simp] theorem attachSourceBoundResidueLedger_conventions (state : WholeState V E B)
    (channel : ResidueLedgerChannel V) :
    (attachSourceBoundResidueLedger state channel).conventions = state.conventions := rfl

@[simp] theorem attachSourceBoundResidueLedger_cages (state : WholeState V E B)
    (channel : ResidueLedgerChannel V) :
    (attachSourceBoundResidueLedger state channel).cages = state.cages := rfl

@[simp] theorem attachSourceBoundResidueLedger_residueLedger (state : WholeState V E B)
    (channel : ResidueLedgerChannel V) :
    (attachSourceBoundResidueLedger state channel).residueLedger? = some channel := rfl

/-- The whole state with the supplied ledger attached at the state's own graph encoding. -/
def sourceBoundResidueState (codec : LocantCodec Locant) (eV : V ≃ Fin (Fintype.card V))
    (state : WholeState V E B)
    (ledger : ResidueIncidenceLedger Locant (state.graph.certifiedEncoding eV))
    (cover : LocantCover ledger) : WholeState V E B :=
  attachSourceBoundResidueLedger state (sourceBoundChannel codec eV state ledger cover)

@[simp] theorem sourceBoundResidueState_residueLedger (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (state : WholeState V E B)
    (ledger : ResidueIncidenceLedger Locant (state.graph.certifiedEncoding eV))
    (cover : LocantCover ledger) :
    (sourceBoundResidueState codec eV state ledger cover).residueLedger? =
      some (sourceBoundChannel codec eV state ledger cover) := rfl

@[simp] theorem sourceBoundResidueState_graph (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (state : WholeState V E B)
    (ledger : ResidueIncidenceLedger Locant (state.graph.certifiedEncoding eV))
    (cover : LocantCover ledger) :
    (sourceBoundResidueState codec eV state ledger cover).graph = state.graph := rfl

@[simp] theorem sourceBoundResidueState_conformation (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (state : WholeState V E B)
    (ledger : ResidueIncidenceLedger Locant (state.graph.certifiedEncoding eV))
    (cover : LocantCover ledger) :
    (sourceBoundResidueState codec eV state ledger cover).conformation =
      state.conformation := rfl

/-! ## Exact recovery of the encoded observable content -/

/-- Decoding the attached annotation with the same `LocantCodec` and the encoding enumeration
recovers exactly the ledger's observable content. -/
theorem sourceBoundChannel_decodeView (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (state : WholeState V E B)
    (ledger : ResidueIncidenceLedger Locant (state.graph.certifiedEncoding eV))
    (cover : LocantCover ledger) :
    decodeView? codec (encodedAtomEquiv state.graph eV)
        (sourceBoundChannel codec eV state ledger cover).annotation =
      some (viewOfLedger ledger) := by
  unfold sourceBoundChannel
  exact decodeView?_residueLedgerChannelOfEncoded codec (encodedAtomEquiv state.graph eV)
    ledger cover.cover cover.nodup cover.covers

/-- The recovered ordered link list is exactly the supplied ledger's link list, in the same
order and with the same multiplicities. -/
theorem sourceBoundChannel_links_recovered (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (state : WholeState V E B)
    (ledger : ResidueIncidenceLedger Locant (state.graph.certifiedEncoding eV))
    (cover : LocantCover ledger) :
    (decodeView? codec (encodedAtomEquiv state.graph eV)
        (sourceBoundChannel codec eV state ledger cover).annotation).map
        (fun view => view.links) = some ledger.links := by
  rw [sourceBoundChannel_decodeView]
  rfl

/-- Every recovered fragment support is exactly the source residue support. -/
theorem sourceBoundChannel_support_recovered (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (state : WholeState V E B)
    (ledger : ResidueIncidenceLedger Locant (state.graph.certifiedEncoding eV))
    (cover : LocantCover ledger) (index : Fin ledger.residueCount) :
    (decodeView? codec (encodedAtomEquiv state.graph eV)
        (sourceBoundChannel codec eV state ledger cover).annotation).map
        (fun view => (view.residue index).support) = some (ledger.residue index).support := by
  rw [sourceBoundChannel_decodeView]
  rfl

/-- Every recovered scoped locant incidence is exactly the source residue's incidence. -/
theorem sourceBoundChannel_incidence_recovered (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (state : WholeState V E B)
    (ledger : ResidueIncidenceLedger Locant (state.graph.certifiedEncoding eV))
    (cover : LocantCover ledger) (index : Fin ledger.residueCount) (locant : Locant) :
    (decodeView? codec (encodedAtomEquiv state.graph eV)
        (sourceBoundChannel codec eV state ledger cover).annotation).map
        (fun view => (view.residue index).incidence locant) =
      some ((ledger.residue index).incidence locant) := by
  rw [sourceBoundChannel_decodeView]
  rfl

/-- The optional naming parent hierarchy is recovered exactly. -/
theorem sourceBoundChannel_hierarchy_recovered (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (state : WholeState V E B)
    (ledger : ResidueIncidenceLedger Locant (state.graph.certifiedEncoding eV))
    (cover : LocantCover ledger) :
    (decodeView? codec (encodedAtomEquiv state.graph eV)
        (sourceBoundChannel codec eV state ledger cover).annotation).map
        (fun view => view.hierarchy?) = some ledger.hierarchy? := by
  rw [sourceBoundChannel_decodeView]
  rfl

/-- The recovered naming parent of every residue is exactly the source parent: nomenclature
parentage stays independent of directed connectivity. -/
theorem sourceBoundChannel_hierarchyParent_recovered (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (state : WholeState V E B)
    (ledger : ResidueIncidenceLedger Locant (state.graph.certifiedEncoding eV))
    (cover : LocantCover ledger) (index : Fin ledger.residueCount) :
    (decodeView? codec (encodedAtomEquiv state.graph eV)
        (sourceBoundChannel codec eV state ledger cover).annotation).map
        (fun view => view.hierarchy?.bind fun hierarchy => hierarchy.parent index) =
      some (ledger.hierarchy?.bind fun hierarchy => hierarchy.parent index) := by
  rw [sourceBoundChannel_decodeView]
  rfl

/-- The recovered naming rank of every residue is exactly the source rank. -/
theorem sourceBoundChannel_hierarchyRank_recovered (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (state : WholeState V E B)
    (ledger : ResidueIncidenceLedger Locant (state.graph.certifiedEncoding eV))
    (cover : LocantCover ledger) (index : Fin ledger.residueCount) :
    (decodeView? codec (encodedAtomEquiv state.graph eV)
        (sourceBoundChannel codec eV state ledger cover).annotation).map
        (fun view => view.hierarchy?.map fun hierarchy => hierarchy.rank index) =
      some (ledger.hierarchy?.map fun hierarchy => hierarchy.rank index) := by
  rw [sourceBoundChannel_decodeView]
  rfl

/-! ## Actual source binding: participants of the whole-state graph -/

/-- A resolved locant binding is stored in the attached channel's residue fragment with its
`V` label, not merely as an encoded number. -/
theorem sourceBoundChannel_binding_of_incidence (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (state : WholeState V E B)
    (ledger : ResidueIncidenceLedger Locant (state.graph.certifiedEncoding eV))
    (cover : LocantCover ledger) (index : Fin ledger.residueCount) (locant : Locant)
    (atom : Fin (state.graph.certifiedEncoding eV).input.molecule.atomCount)
    (found : (ledger.residue index).incidence locant = some atom)
    (coverMember : locant ∈ cover.cover index) :
    (codec.code locant, some (sourceAtomOfEncoded state.graph eV atom)) ∈
      ((sourceBoundChannel codec eV state ledger cover).annotation.residue index).bindings := by
  rw [sourceBoundChannel_annotation, TetraStereo.OneCenter.encode_residue,
    encodeFragment_bindings]
  refine List.mem_map.mpr ⟨locant, coverMember, ?_⟩
  rw [found]
  rfl

/-- Every link of the supplied ledger resolves its source locant to an encoded atom that is a
participant of the actual whole-state interaction at the link's occurrence index, whose `V`
label is a participant of that same whole-state interaction, and that label occurs in the
attached channel's own scoped binding.  In particular the source residue support contains the
label. -/
theorem sourceBoundChannel_link_source_correct (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (state : WholeState V E B)
    (ledger : ResidueIncidenceLedger Locant (state.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    {link : AnnotatedResidueLink ledger.residueCount
      (sourceBoundChannel codec eV state ledger cover).interactionCount}
    (member : link ∈ (sourceBoundChannel codec eV state ledger cover).annotation.links) :
    ∃ raw ∈ ledger.links, link = encodeLink codec raw ∧
      ∃ atom : Fin (state.graph.certifiedEncoding eV).input.molecule.atomCount,
        (ledger.residue raw.source).incidence raw.sourceLocant = some atom ∧
        sourceAtomOfEncoded state.graph eV atom ∈
          (state.graph.interactions.get
            (residueSourceInteractionIndex state.graph eV raw.interaction)).1 ∧
        (codec.code raw.sourceLocant, some (sourceAtomOfEncoded state.graph eV atom)) ∈
          ((sourceBoundChannel codec eV state ledger cover).annotation.residue
            raw.source).bindings := by
  rw [sourceBoundChannel_links] at member
  obtain ⟨raw, rawMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨atom, found, participant⟩ := ledger.link_source_mem raw rawMember
  refine ⟨raw, rawMember, rfl, atom, found, ?_, ?_⟩
  · exact sourceAtomOfEncoded_mem_participants state.graph eV raw.interaction atom participant
  · exact sourceBoundChannel_binding_of_incidence codec eV state ledger cover raw.source
      raw.sourceLocant atom found (cover.covers raw.source raw.sourceLocant atom found)

/-- Target-endpoint mirror of `sourceBoundChannel_link_source_correct`. -/
theorem sourceBoundChannel_link_target_correct (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (state : WholeState V E B)
    (ledger : ResidueIncidenceLedger Locant (state.graph.certifiedEncoding eV))
    (cover : LocantCover ledger)
    {link : AnnotatedResidueLink ledger.residueCount
      (sourceBoundChannel codec eV state ledger cover).interactionCount}
    (member : link ∈ (sourceBoundChannel codec eV state ledger cover).annotation.links) :
    ∃ raw ∈ ledger.links, link = encodeLink codec raw ∧
      ∃ atom : Fin (state.graph.certifiedEncoding eV).input.molecule.atomCount,
        (ledger.residue raw.target).incidence raw.targetLocant = some atom ∧
        sourceAtomOfEncoded state.graph eV atom ∈
          (state.graph.interactions.get
            (residueSourceInteractionIndex state.graph eV raw.interaction)).1 ∧
        (codec.code raw.targetLocant, some (sourceAtomOfEncoded state.graph eV atom)) ∈
          ((sourceBoundChannel codec eV state ledger cover).annotation.residue
            raw.target).bindings := by
  rw [sourceBoundChannel_links] at member
  obtain ⟨raw, rawMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨atom, found, participant⟩ := ledger.link_target_mem raw rawMember
  refine ⟨raw, rawMember, rfl, atom, found, ?_, ?_⟩
  · exact sourceAtomOfEncoded_mem_participants state.graph eV raw.interaction atom participant
  · exact sourceBoundChannel_binding_of_incidence codec eV state ledger cover raw.target
      raw.targetLocant atom found (cover.covers raw.target raw.targetLocant atom found)

/-- Every actual link of the supplied source ledger binds both endpoints into the actual
whole-state graph, independently of whether the annotation is decoded. -/
theorem sourceBound_ledger_link_source_correct (eV : V ≃ Fin (Fintype.card V))
    (state : WholeState V E B)
    (ledger : ResidueIncidenceLedger Locant (state.graph.certifiedEncoding eV))
    {link : DirectedResidueLink Locant (Fin ledger.residueCount)
      (state.graph.certifiedEncoding eV).input.molecule.interactions.length}
    (member : link ∈ ledger.links) :
    ∃ atom : Fin (state.graph.certifiedEncoding eV).input.molecule.atomCount,
      (ledger.residue link.source).incidence link.sourceLocant = some atom ∧
      sourceAtomOfEncoded state.graph eV atom ∈
        (state.graph.interactions.get
          (residueSourceInteractionIndex state.graph eV link.interaction)).1 := by
  obtain ⟨atom, found, participant⟩ := ledger.link_source_mem link member
  exact ⟨atom, found,
    sourceAtomOfEncoded_mem_participants state.graph eV link.interaction atom participant⟩

/-! ## Reconstruction from encoded data plus a proof-only validity certificate -/

/-- Source-bound validity of a decoded view: every recovered link endpoint resolves, inside its
recovered residue, to an encoded atom that is an actual participant of the encoded whole-state
interaction at the link's occurrence index.  This is a proposition over the *decoded* view; it
stores no ledger payload. -/
structure SourceBoundViewValidity {Locant : Type*}
    (graph : FiniteAtomInteractionHypergraph V) (eV : V ≃ Fin (Fintype.card V))
    {residueCount : ℕ}
    (view : ResidueLedgerView Locant
      (graph.certifiedEncoding eV).input.molecule.atomCount
      (graph.certifiedEncoding eV).input.molecule.interactions.length residueCount) : Prop where
  /-- Every link's source endpoint resolves to a participant of its actual interaction. -/
  link_source_mem : ∀ link ∈ view.links,
    ∃ atom : Fin (graph.certifiedEncoding eV).input.molecule.atomCount,
      (view.residue link.source).incidence link.sourceLocant = some atom ∧
        atom.val ∈
          ((graph.certifiedEncoding eV).input.molecule.interactions.get link.interaction).participants
  /-- Every link's target endpoint resolves to a participant of its actual interaction. -/
  link_target_mem : ∀ link ∈ view.links,
    ∃ atom : Fin (graph.certifiedEncoding eV).input.molecule.atomCount,
      (view.residue link.target).incidence link.targetLocant = some atom ∧
        atom.val ∈
          ((graph.certifiedEncoding eV).input.molecule.interactions.get link.interaction).participants

/-- The source-bound validity certificate induced by a supplied ledger's own participant facts.
Nothing is assumed about the desired recovered ledger. -/
def sourceBoundViewValidityOfLedger (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V))
    (ledger : ResidueIncidenceLedger Locant (graph.certifiedEncoding eV)) :
    SourceBoundViewValidity (Locant := Locant) graph eV (viewOfLedger ledger) where
  link_source_mem link member := ledger.link_source_mem link member
  link_target_mem link member := ledger.link_target_mem link member

/-- Full dependent reconstruction: the attached channel's encoded annotation, decoded with the
same enumeration, yields the recovered view; the supplied source-bound validity (derived from the
ledger's participant facts) rebuilds the dependent ledger exactly, with no original ledger payload
stored in the state. -/
theorem sourceBoundChannel_reconstruct (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (state : WholeState V E B)
    (ledger : ResidueIncidenceLedger Locant (state.graph.certifiedEncoding eV))
    (cover : LocantCover ledger) :
    ∃ view : ResidueLedgerView Locant
        (state.graph.certifiedEncoding eV).input.molecule.atomCount
        (state.graph.certifiedEncoding eV).input.molecule.interactions.length
        ledger.residueCount,
      decodeView? codec (encodedAtomEquiv state.graph eV)
          (sourceBoundChannel codec eV state ledger cover).annotation = some view ∧
      ∃ valid : SourceBoundViewValidity (Locant := Locant) state.graph eV view,
        viewToLedger view valid.link_source_mem valid.link_target_mem = ledger := by
  refine ⟨viewOfLedger ledger, sourceBoundChannel_decodeView codec eV state ledger cover,
    sourceBoundViewValidityOfLedger state.graph eV ledger, ?_⟩
  exact viewToLedger_viewOfLedger ledger

/-! ## General supplied source with an explicit molecule identity -/

/-- The atom equivalence induced by a general supplied input whose molecule is explicitly the
whole-state graph's encoding at the common enumeration. -/
noncomputable def generalSourceAtomEquiv (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V)) (input : CertifiedAuthoritativeChemicalInput)
    (moleculeEq : input.input.molecule = graph.encode eV) :
    V ≃ Fin input.input.molecule.atomCount :=
  (encodedAtomEquiv graph eV).trans
    (finCastEquiv (by
      rw [FiniteAtomInteractionHypergraph.encodeAuthoritative_molecule, moleculeEq]))

@[simp] theorem generalSourceAtomEquiv_apply_val (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V)) (input : CertifiedAuthoritativeChemicalInput)
    (moleculeEq : input.input.molecule = graph.encode eV) (label : V) :
    ((generalSourceAtomEquiv graph eV input moleculeEq label).val) = (eV label).val := rfl

/-- The interaction index of a general input's interaction, transported to the whole-state graph
along the molecule identity. -/
def generalSourceInteractionIndex (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V)) (input : CertifiedAuthoritativeChemicalInput)
    (moleculeEq : input.input.molecule = graph.encode eV)
    (index : Fin input.input.molecule.interactions.length) : Fin graph.interactions.length :=
  ⟨index.val, by
    have hlen : input.input.molecule.interactions.length = graph.interactions.length := by
      rw [moleculeEq]
      exact FiniteAtomInteractionHypergraph.encode_interactions_length graph eV
    exact hlen ▸ index.isLt⟩

/-- Exact lookup of a general input's interaction, identified with the whole-state graph's
interaction through the explicit molecule identity. -/
theorem generalSource_interactions_get (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V)) (input : CertifiedAuthoritativeChemicalInput)
    (moleculeEq : input.input.molecule = graph.encode eV)
    (index : Fin input.input.molecule.interactions.length) :
    input.input.molecule.interactions.get index =
      FiniteAtomInteractionHypergraph.encodeInteraction eV
        (graph.interactions.get
          (generalSourceInteractionIndex graph eV input moleculeEq index)) := by
  have interactionsEq :
      input.input.molecule.interactions = (graph.encode eV).interactions :=
    congrArg SemanticMolecule.interactions moleculeEq
  have encodedLookup := listGet?_eq_some_get input.input.molecule.interactions index
  have inputLookup : listGet? input.input.molecule.interactions index.val =
      listGet? (graph.encode eV).interactions index.val :=
    congrArg (fun values => listGet? values index.val) interactionsEq
  have encodedLookup' : listGet? (graph.encode eV).interactions index.val =
      some (input.input.molecule.interactions.get index) := by
    rw [← inputLookup]
    exact encodedLookup
  have graphLookup := FiniteAtomInteractionHypergraph.encode_interactionAt graph eV index.val
    (generalSourceInteractionIndex graph eV input moleculeEq index).isLt
  rw [graphLookup] at encodedLookup'
  exact (Option.some.inj encodedLookup').symm

/-- The source-bound residue channel for a general supplied certified input with an explicit
molecule identity to the whole-state graph encoding. -/
def generalSourceBoundChannel (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (state : WholeState V E B)
    (input : CertifiedAuthoritativeChemicalInput)
    (moleculeEq : input.input.molecule = state.graph.encode eV)
    (ledger : ResidueIncidenceLedger Locant input) (cover : LocantCover ledger) :
    ResidueLedgerChannel V :=
  residueLedgerChannelOfEncoded codec
    (generalSourceAtomEquiv state.graph eV input moleculeEq) ledger cover.cover

@[simp] theorem generalSourceBoundChannel_residueCount (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (state : WholeState V E B)
    (input : CertifiedAuthoritativeChemicalInput)
    (moleculeEq : input.input.molecule = state.graph.encode eV)
    (ledger : ResidueIncidenceLedger Locant input) (cover : LocantCover ledger) :
    (generalSourceBoundChannel codec eV state input moleculeEq ledger cover).residueCount =
      ledger.residueCount := rfl

/-- Count alignment for a general supplied source: the channel's interaction budget is the
whole-state graph's actual interaction-list length. -/
@[simp] theorem generalSourceBoundChannel_interactionCount (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (state : WholeState V E B)
    (input : CertifiedAuthoritativeChemicalInput)
    (moleculeEq : input.input.molecule = state.graph.encode eV)
    (ledger : ResidueIncidenceLedger Locant input) (cover : LocantCover ledger) :
    (generalSourceBoundChannel codec eV state input moleculeEq ledger cover).interactionCount =
      state.graph.interactions.length := by
  show input.input.molecule.interactions.length = state.graph.interactions.length
  rw [moleculeEq]
  exact FiniteAtomInteractionHypergraph.encode_interactions_length state.graph eV

theorem generalSourceBoundChannel_decodeView (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (state : WholeState V E B)
    (input : CertifiedAuthoritativeChemicalInput)
    (moleculeEq : input.input.molecule = state.graph.encode eV)
    (ledger : ResidueIncidenceLedger Locant input) (cover : LocantCover ledger) :
    decodeView? codec (generalSourceAtomEquiv state.graph eV input moleculeEq)
        (generalSourceBoundChannel codec eV state input moleculeEq ledger cover).annotation =
      some (viewOfLedger ledger) := by
  unfold generalSourceBoundChannel
  exact decodeView?_residueLedgerChannelOfEncoded codec
    (generalSourceAtomEquiv state.graph eV input moleculeEq) ledger cover.cover
    cover.nodup cover.covers

theorem generalSourceBoundChannel_links_recovered (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (state : WholeState V E B)
    (input : CertifiedAuthoritativeChemicalInput)
    (moleculeEq : input.input.molecule = state.graph.encode eV)
    (ledger : ResidueIncidenceLedger Locant input) (cover : LocantCover ledger) :
    (decodeView? codec (generalSourceAtomEquiv state.graph eV input moleculeEq)
        (generalSourceBoundChannel codec eV state input moleculeEq ledger cover).annotation).map
        (fun view => view.links) = some ledger.links := by
  rw [generalSourceBoundChannel_decodeView]
  rfl

/-- An enumeration label with a given encoded numeral is the inverse image of the encoded atom
under the general source atom equivalence. -/
theorem eq_generalSourceAtomEquiv_symm_of_val_eq (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V)) (input : CertifiedAuthoritativeChemicalInput)
    (moleculeEq : input.input.molecule = graph.encode eV) {label : V}
    {atom : Fin input.input.molecule.atomCount}
    (valueEq : (eV label).val = atom.val) :
    label = (generalSourceAtomEquiv graph eV input moleculeEq).symm atom := by
  have atomEq : generalSourceAtomEquiv graph eV input moleculeEq label = atom :=
    Fin.ext (by simpa using valueEq)
  rw [← atomEq, Equiv.symm_apply_apply]

/-- A resolved locant binding in a general supplied source is stored with its `V` label in the
attached channel, exactly as in the specialized case. -/
theorem generalSourceBoundChannel_binding_of_incidence (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (state : WholeState V E B)
    (input : CertifiedAuthoritativeChemicalInput)
    (moleculeEq : input.input.molecule = state.graph.encode eV)
    (ledger : ResidueIncidenceLedger Locant input) (cover : LocantCover ledger)
    (index : Fin ledger.residueCount) (locant : Locant)
    (atom : Fin input.input.molecule.atomCount)
    (found : (ledger.residue index).incidence locant = some atom)
    (coverMember : locant ∈ cover.cover index) :
    (codec.code locant,
        some ((generalSourceAtomEquiv state.graph eV input moleculeEq).symm atom)) ∈
      ((generalSourceBoundChannel codec eV state input moleculeEq ledger cover).annotation.residue
        index).bindings := by
  unfold generalSourceBoundChannel residueLedgerChannelOfEncoded
  rw [TetraStereo.OneCenter.encode_residue, encodeFragment_bindings]
  refine List.mem_map.mpr ⟨locant, coverMember, ?_⟩
  simp [found]

/-- Every actual link of a general supplied ledger binds its source endpoint into the actual
whole-state graph, using only the explicit molecule identity: the endpoint atom is a participant
of the whole-state interaction at the link's occurrence index, its `V` label is a participant of
that same interaction, and the label occurs in the attached scoped binding. -/
theorem generalSourceBoundChannel_link_source_correct (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (state : WholeState V E B)
    (input : CertifiedAuthoritativeChemicalInput)
    (moleculeEq : input.input.molecule = state.graph.encode eV)
    (ledger : ResidueIncidenceLedger Locant input) (cover : LocantCover ledger)
    {link : AnnotatedResidueLink ledger.residueCount
      (generalSourceBoundChannel codec eV state input moleculeEq ledger cover).interactionCount}
    (member : link ∈
      (generalSourceBoundChannel codec eV state input moleculeEq ledger cover).annotation.links) :
    ∃ raw ∈ ledger.links, link = encodeLink codec raw ∧
      ∃ atom : Fin input.input.molecule.atomCount,
        (ledger.residue raw.source).incidence raw.sourceLocant = some atom ∧
        atom.val ∈ (input.input.molecule.interactions.get raw.interaction).participants ∧
        (generalSourceAtomEquiv state.graph eV input moleculeEq).symm atom ∈
          (state.graph.interactions.get
            (generalSourceInteractionIndex state.graph eV input moleculeEq
              raw.interaction)).1 ∧
        (codec.code raw.sourceLocant,
            some ((generalSourceAtomEquiv state.graph eV input moleculeEq).symm atom)) ∈
          ((generalSourceBoundChannel codec eV state input moleculeEq ledger cover).annotation.residue
            raw.source).bindings := by
  have linksEq :
      (generalSourceBoundChannel codec eV state input moleculeEq ledger cover).annotation.links =
        ledger.links.map (encodeLink codec) := rfl
  rw [linksEq] at member
  obtain ⟨raw, rawMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨atom, found, participant⟩ := ledger.link_source_mem raw rawMember
  refine ⟨raw, rawMember, rfl, atom, found, participant, ?_, ?_⟩
  · have encodedParticipant : atom.val ∈
        (FiniteAtomInteractionHypergraph.encodeInteraction eV
          (state.graph.interactions.get
            (generalSourceInteractionIndex state.graph eV input moleculeEq
              raw.interaction))).participants := by
      rw [← generalSource_interactions_get state.graph eV input moleculeEq raw.interaction]
      exact participant
    obtain ⟨label, labelMember, valueEq⟩ :=
      (encodeInteraction_participants_mem_iff eV _ atom.val).mp encodedParticipant
    rw [← eq_generalSourceAtomEquiv_symm_of_val_eq state.graph eV input moleculeEq valueEq]
    exact labelMember
  · exact generalSourceBoundChannel_binding_of_incidence codec eV state input moleculeEq
      ledger cover raw.source raw.sourceLocant atom found
      (cover.covers raw.source raw.sourceLocant atom found)

/-- Target-endpoint mirror of `generalSourceBoundChannel_link_source_correct`. -/
theorem generalSourceBoundChannel_link_target_correct (codec : LocantCodec Locant)
    (eV : V ≃ Fin (Fintype.card V)) (state : WholeState V E B)
    (input : CertifiedAuthoritativeChemicalInput)
    (moleculeEq : input.input.molecule = state.graph.encode eV)
    (ledger : ResidueIncidenceLedger Locant input) (cover : LocantCover ledger)
    {link : AnnotatedResidueLink ledger.residueCount
      (generalSourceBoundChannel codec eV state input moleculeEq ledger cover).interactionCount}
    (member : link ∈
      (generalSourceBoundChannel codec eV state input moleculeEq ledger cover).annotation.links) :
    ∃ raw ∈ ledger.links, link = encodeLink codec raw ∧
      ∃ atom : Fin input.input.molecule.atomCount,
        (ledger.residue raw.target).incidence raw.targetLocant = some atom ∧
        atom.val ∈ (input.input.molecule.interactions.get raw.interaction).participants ∧
        (generalSourceAtomEquiv state.graph eV input moleculeEq).symm atom ∈
          (state.graph.interactions.get
            (generalSourceInteractionIndex state.graph eV input moleculeEq
              raw.interaction)).1 ∧
        (codec.code raw.targetLocant,
            some ((generalSourceAtomEquiv state.graph eV input moleculeEq).symm atom)) ∈
          ((generalSourceBoundChannel codec eV state input moleculeEq ledger cover).annotation.residue
            raw.target).bindings := by
  have linksEq :
      (generalSourceBoundChannel codec eV state input moleculeEq ledger cover).annotation.links =
        ledger.links.map (encodeLink codec) := rfl
  rw [linksEq] at member
  obtain ⟨raw, rawMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨atom, found, participant⟩ := ledger.link_target_mem raw rawMember
  refine ⟨raw, rawMember, rfl, atom, found, participant, ?_, ?_⟩
  · have encodedParticipant : atom.val ∈
        (FiniteAtomInteractionHypergraph.encodeInteraction eV
          (state.graph.interactions.get
            (generalSourceInteractionIndex state.graph eV input moleculeEq
              raw.interaction))).participants := by
      rw [← generalSource_interactions_get state.graph eV input moleculeEq raw.interaction]
      exact participant
    obtain ⟨label, labelMember, valueEq⟩ :=
      (encodeInteraction_participants_mem_iff eV _ atom.val).mp encodedParticipant
    rw [← eq_generalSourceAtomEquiv_symm_of_val_eq state.graph eV input moleculeEq valueEq]
    exact labelMember
  · exact generalSourceBoundChannel_binding_of_incidence codec eV state input moleculeEq
      ledger cover raw.target raw.targetLocant atom found
      (cover.covers raw.target raw.targetLocant atom found)

end

end TetraStereo.OneCenter
