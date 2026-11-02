import TetraStereo.OneCenter.OrganicStereoPathDescriptionIngress
import TetraStereo.OneCenter.OrganicStereoElectronicStateAttachment

set_option autoImplicit false

namespace TetraStereo.OneCenter

open scoped unitInterval

open OrganicStereoIndependentElectronicEncoding
open OrganicStereoElectronicSites
open OrganicStereoElectronicStateAttachment
open OrganicStereoElectronicDescriptionIngress

/-!
# Replacing only the bond-path channel of an arbitrary whole state

`OrganicStereoPathDescriptionIngress` constructs a whole state from independent bond-path data, but
only at the empty electronic/rational/drawing/band/metadata configuration.  This module removes
that restriction in the direction needed for composition:

Given

* an arbitrary existing `WholeState V E B` (any finite edge type `E`, any finite band index type
  `B`), carrying its electronic inventory and evidence, conformation, rational provenance, role
  ledger, band attachments and agreement, drawing data, partial positions, incidence ledger,
  fragment/convention/cage metadata, residue ledger, and the caller-supplied frame annotations
  (`frames`, including the newly added frame channel);
* an independent physical record `input : IndependentBondPathData V NewE`;
* the honest physical compatibility data `input.graph = state.graph` and
  `input.conformation = state.conformation`,

we build `attachIndependentBondPathData state input graph_eq conformation_eq : WholeState V NewE B`
whose **only** changed channel is the bond-path family: `paths`, `path_valid`,
`path_source_endpoint` and `path_target_endpoint` are taken from the supplied independent record,
transported through the two equalities.  Every other field is copied verbatim from `state` by a
single record update, so channels added to `WholeState` later (such as `frames`) are preserved
automatically and cannot silently be dropped.

The construction is not a decoder and assumes no hidden payload: the only inputs are the arbitrary
state, the supplied independent record, and the two equalities.  The old path information is
intentionally replaced and is **not** recovered here; the recovery theorem below recovers the
supplied independent record from the *new* path channel, which is the intended result.

Main results:

* `attachIndependentBondPathData` — the record update that replaces the path channel;
* `pathGeometryValid_attachIndependentBondPathData` — the domain's own `PathGeometryValid`
  predicate for the result, derived from the independent geometry axioms transported along the
  source/geometry equalities;
* `toIndependentBondPathData_attachIndependentBondPathData` — the existing domain adapter applied
  to the result returns the supplied independent record *in full* (all proposition-valued fields by
  proof irrelevance), reusing the extensionality lemma already proved in the ingress module;
* projection lemmas showing every unrelated channel is unchanged, including `frames`;
* `attachIndependentBondPathData_withFrames` — attachment commutes with the existing frame updater;
* `attachIndependentBondPathData_attachElectronic` — attachment commutes with the approved
  electronic-state attachment (which changes `electronic?`/`electronic_unpaired` and no path
  field), so the two operations compose in either order;
* `attachIndependentBondPathData_coexistence` — simultaneous path, band, electronic and frame data
  on one state.

No chemical embedding existence, no rational realizability and no completeness of the documented
pair-bond subset is claimed.  The equalities `input.graph = state.graph` and
`input.conformation = state.conformation` are the full physical compatibility requirement; no
generic decoder laws are used.
-/

variable {V E NewE B : Type*} [DecidableEq V] [Fintype V] [Fintype E] [Fintype NewE] [Fintype B]

/-! ## Transport of the independent path facts through the source and geometry equalities -/

/-- The independent occurrence bound, transported to the existing state's interaction list.  This
is the bound used by the replaced `path_valid` field. -/
theorem attach_transport_interactionOccurrence_lt
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph) (edge : NewE) :
    input.interactionOccurrence edge < state.graph.interactions.length := by
  rw [← graph_eq]
  exact input.interactionOccurrence_lt edge

/-- The independent participant-list compatibility, transported to the existing state's graph.
The interaction occurrence, the ordered participant list and the two oriented endpoint labels are
literal input data; only the graph reference is moved along `graph_eq`. -/
theorem attach_transport_participants_exact
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph) (edge : NewE) :
    (state.graph.interactions.get
        ⟨input.interactionOccurrence edge,
          attach_transport_interactionOccurrence_lt state input graph_eq edge⟩).1 =
      [input.source edge, input.target edge] := by
  have hlist : state.graph.interactions = input.graph.interactions := by rw [← graph_eq]
  have h := getElem_congr_coll (c := state.graph.interactions)
    (d := input.graph.interactions) (i := input.interactionOccurrence edge)
    (w := attach_transport_interactionOccurrence_lt state input graph_eq edge) hlist
  have h' : (state.graph.interactions.get
        ⟨input.interactionOccurrence edge,
          attach_transport_interactionOccurrence_lt state input graph_eq edge⟩).1 =
      (input.graph.interactions.get (input.interactionIndex edge)).1 := by
    simpa [List.get_eq_getElem] using congrArg Prod.fst h
  rw [h']
  exact input.participants_exact edge

/-- The independent selected-pair-kind compatibility, transported to the existing state's graph. -/
theorem attach_transport_kind_selected
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph) (edge : NewE) :
    SemanticInteractionKind.isSelectedPairKind
        (state.graph.interactions.get
          ⟨input.interactionOccurrence edge,
            attach_transport_interactionOccurrence_lt state input graph_eq edge⟩).2 = true := by
  have hlist : state.graph.interactions = input.graph.interactions := by rw [← graph_eq]
  have h := getElem_congr_coll (c := state.graph.interactions)
    (d := input.graph.interactions) (i := input.interactionOccurrence edge)
    (w := attach_transport_interactionOccurrence_lt state input graph_eq edge) hlist
  have h' : (state.graph.interactions.get
        ⟨input.interactionOccurrence edge,
          attach_transport_interactionOccurrence_lt state input graph_eq edge⟩).2 =
      (input.graph.interactions.get (input.interactionIndex edge)).2 := by
    simpa [List.get_eq_getElem] using congrArg Prod.snd h
  rw [h']
  exact input.kind_selected edge

/-- The independent arc-start agreement, transported to the existing state's conformation. -/
theorem attach_transport_source_endpoint
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (conformation_eq : input.conformation = state.conformation) (edge : NewE) :
    input.arc edge 0 = state.conformation (input.source edge) := by
  rw [← conformation_eq]
  exact input.source_endpoint edge

/-- The independent arc-end agreement, transported to the existing state's conformation. -/
theorem attach_transport_target_endpoint
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (conformation_eq : input.conformation = state.conformation) (edge : NewE) :
    input.arc edge 1 = state.conformation (input.target edge) := by
  rw [← conformation_eq]
  exact input.target_endpoint edge

/-! ## The attachment -/

/-- Replace the bond-path channel of an arbitrary whole state by the supplied independent physical
bond-path record.

The graph and the shared real conformation remain those of `state` (the equalities say that the
input agrees with them); every unrelated field is copied by the single record update.  In
particular the optional electronic inventory and its unpaired evidence, the rational provenance,
the ordered role ledger, the whole band family with all per-band attachment records and their
positional agreement, the drawing data, the sparse partial positions, the sparse incidence ledger,
fragments, conventions, cages, the residue ledger and the caller-supplied frame annotations are
retained exactly.

Only `paths`, `path_valid`, `path_source_endpoint` and `path_target_endpoint` are replaced.  The
new validity fields are the independent record's own proofs transported through `graph_eq` and
`conformation_eq`; nothing is assumed. -/
def attachIndependentBondPathData
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    WholeState V NewE B :=
  { state with
    paths := fun edge => input.toPathAnnotation edge
    path_valid := by
      intro edge
      refine ⟨attach_transport_interactionOccurrence_lt state input graph_eq edge, ?_, ?_⟩
      · simpa [IndependentBondPathData.toPathAnnotation] using
          attach_transport_participants_exact state input graph_eq edge
      · simpa [IndependentBondPathData.toPathAnnotation] using
          attach_transport_kind_selected state input graph_eq edge
    path_source_endpoint := by
      intro edge
      simpa [IndependentBondPathData.toPathAnnotation] using
        attach_transport_source_endpoint state input conformation_eq edge
    path_target_endpoint := by
      intro edge
      simpa [IndependentBondPathData.toPathAnnotation] using
        attach_transport_target_endpoint state input conformation_eq edge }

/-! ## The replaced path channel -/

/-- The new path channel is the supplied independent annotation, edge by edge. -/
@[simp] theorem attachIndependentBondPathData_paths
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) (edge : NewE) :
    (attachIndependentBondPathData state input graph_eq conformation_eq).paths edge =
      input.toPathAnnotation edge := rfl

/-- The new interaction occurrence is the supplied independent occurrence. -/
@[simp] theorem attachIndependentBondPathData_paths_interactionIndex
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) (edge : NewE) :
    ((attachIndependentBondPathData state input graph_eq conformation_eq).paths
        edge).interactionIndex = input.interactionOccurrence edge := rfl

/-- The new oriented source endpoint is the supplied one. -/
@[simp] theorem attachIndependentBondPathData_paths_source
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) (edge : NewE) :
    ((attachIndependentBondPathData state input graph_eq conformation_eq).paths edge).source =
      input.source edge := rfl

/-- The new oriented target endpoint is the supplied one. -/
@[simp] theorem attachIndependentBondPathData_paths_target
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) (edge : NewE) :
    ((attachIndependentBondPathData state input graph_eq conformation_eq).paths edge).target =
      input.target edge := rfl

/-- The new continuous arc is the supplied one. -/
@[simp] theorem attachIndependentBondPathData_paths_arc
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) (edge : NewE) :
    ((attachIndependentBondPathData state input graph_eq conformation_eq).paths edge).arc =
      input.arc edge := rfl

/-! ## Every unrelated channel is unchanged -/

/-- The interaction graph is unchanged. -/
@[simp] theorem attachIndependentBondPathData_graph
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    (attachIndependentBondPathData state input graph_eq conformation_eq).graph = state.graph :=
  rfl

/-- The optional electronic inventory is unchanged, including its genuine absence. -/
@[simp] theorem attachIndependentBondPathData_electronic?
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    (attachIndependentBondPathData state input graph_eq conformation_eq).electronic? =
      state.electronic? := rfl

/-- The electronic unpaired-electron evidence is unchanged. -/
@[simp] theorem attachIndependentBondPathData_electronic_unpaired
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    (attachIndependentBondPathData state input graph_eq conformation_eq).electronic_unpaired =
      state.electronic_unpaired := rfl

/-- The shared real conformation is unchanged. -/
@[simp] theorem attachIndependentBondPathData_conformation
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    (attachIndependentBondPathData state input graph_eq conformation_eq).conformation =
      state.conformation := rfl

/-- The optional exact rational provenance is unchanged, including genuine absence. -/
@[simp] theorem attachIndependentBondPathData_rationalPositions?
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    (attachIndependentBondPathData state input graph_eq conformation_eq).rationalPositions? =
      state.rationalPositions? := rfl

/-- The rational-provenance validity evidence is unchanged. -/
@[simp] theorem attachIndependentBondPathData_rationalPositions_valid
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    (attachIndependentBondPathData state input graph_eq conformation_eq).rationalPositions_valid =
      state.rationalPositions_valid := rfl

/-- The ordered role ledger is unchanged, including order and multiplicity. -/
@[simp] theorem attachIndependentBondPathData_roles
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    (attachIndependentBondPathData state input graph_eq conformation_eq).roles = state.roles :=
  rfl

/-- The role-validity evidence is unchanged. -/
@[simp] theorem attachIndependentBondPathData_role_valid
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    (attachIndependentBondPathData state input graph_eq conformation_eq).role_valid =
      state.role_valid := rfl

/-- The whole band attachment family is unchanged. -/
@[simp] theorem attachIndependentBondPathData_bandFamily
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    (attachIndependentBondPathData state input graph_eq conformation_eq).bandFamily =
      state.bandFamily := rfl

/-- Every per-band positional agreement is unchanged. -/
@[simp] theorem attachIndependentBondPathData_band_agreement
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    (attachIndependentBondPathData state input graph_eq conformation_eq).band_agreement =
      state.band_agreement := rfl

/-- The optional drawing source is unchanged, including genuine absence. -/
@[simp] theorem attachIndependentBondPathData_diagram?
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    (attachIndependentBondPathData state input graph_eq conformation_eq).diagram? =
      state.diagram? := rfl

/-- The optional sparse partial drawing positions are unchanged. -/
@[simp] theorem attachIndependentBondPathData_diagramPartial?
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    (attachIndependentBondPathData state input graph_eq conformation_eq).diagramPartial? =
      state.diagramPartial? := rfl

/-- The sparse incidence ledger is unchanged. -/
@[simp] theorem attachIndependentBondPathData_diagramIncidence
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    (attachIndependentBondPathData state input graph_eq conformation_eq).diagramIncidence =
      state.diagramIncidence := rfl

/-- The incidence-validity evidence is unchanged. -/
@[simp] theorem attachIndependentBondPathData_diagram_valid
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    (attachIndependentBondPathData state input graph_eq conformation_eq).diagram_valid =
      state.diagram_valid := rfl

/-- The ordered fragment metadata is unchanged. -/
@[simp] theorem attachIndependentBondPathData_fragments
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    (attachIndependentBondPathData state input graph_eq conformation_eq).fragments =
      state.fragments := rfl

/-- The ordered convention channel is unchanged. -/
@[simp] theorem attachIndependentBondPathData_conventions
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    (attachIndependentBondPathData state input graph_eq conformation_eq).conventions =
      state.conventions := rfl

/-- The ordered cage/face metadata is unchanged. -/
@[simp] theorem attachIndependentBondPathData_cages
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    (attachIndependentBondPathData state input graph_eq conformation_eq).cages = state.cages :=
  rfl

/-- The optional residue ledger is unchanged, including genuine absence. -/
@[simp] theorem attachIndependentBondPathData_residueLedger?
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    (attachIndependentBondPathData state input graph_eq conformation_eq).residueLedger? =
      state.residueLedger? := rfl

/-- The caller-supplied frame annotations (the newly added frame channel) are unchanged, including
order and duplicates. -/
@[simp] theorem attachIndependentBondPathData_frames
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    (attachIndependentBondPathData state input graph_eq conformation_eq).frames = state.frames :=
  rfl

/-! ## The domain geometry predicate for the attached state -/

/-- The existing `PathGeometryValid` predicate for the attached state.  The occurrence injectivity,
atom injectivity, arc injectivity, interior avoidance and common-endpoint intersection conditions
are the supplied independent record's own axioms; only the graph and conformation references are
transported through `graph_eq` and `conformation_eq`. -/
theorem pathGeometryValid_attachIndependentBondPathData
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    PathGeometryValid (attachIndependentBondPathData state input graph_eq conformation_eq) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro first second equal
    apply input.interactionOccurrence_injective
    simpa using equal
  · show Function.Injective state.conformation
    exact conformation_eq ▸ input.atom_injective
  · intro edge
    show Function.Injective (input.arc edge)
    exact input.arc_injective edge
  · intro edge t ht0 ht1 atom
    show input.arc edge t ≠ state.conformation atom
    rw [← conformation_eq]
    exact input.interior_avoids_atoms edge t ht0 ht1 atom
  · intro edge other t s different meet
    have meet' : input.arc edge t = input.arc other s := by
      simpa using meet
    obtain ⟨atom, hfirst, hsecond⟩ :=
      input.intersects_only_at_common_endpoints edge other t s different meet'
    exact ⟨atom, by simpa using hfirst, by simpa using hsecond⟩

/-! ## Full recovery of the supplied independent record -/

/-- **Full recovery.**  The existing domain adapter `toIndependentBondPathData`, applied to the
attached state, returns the supplied independent record in full.  The six data fields are the
supplied graph, conformation, occurrence map, oriented endpoints and arcs; the eleven remaining
fields are proposition-valued and are identified by proof irrelevance in the reuse of the ingress
module's extensionality lemma.  The chosen `PathGeometryValid` proof is irrelevant. -/
theorem toIndependentBondPathData_attachIndependentBondPathData
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation)
    (valid : PathGeometryValid
      (attachIndependentBondPathData state input graph_eq conformation_eq)) :
    toIndependentBondPathData
        (attachIndependentBondPathData state input graph_eq conformation_eq) valid = input := by
  apply independentBondPathData_extEq
  · show state.graph = input.graph
    exact graph_eq.symm
  · show state.conformation = input.conformation
    exact conformation_eq.symm
  · rfl
  · rfl
  · rfl
  · rfl

/-- Recovery of the supplied independent graph. -/
@[simp] theorem toIndependentBondPathData_attachIndependentBondPathData_graph
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation)
    (valid : PathGeometryValid
      (attachIndependentBondPathData state input graph_eq conformation_eq)) :
    (toIndependentBondPathData
        (attachIndependentBondPathData state input graph_eq conformation_eq) valid).graph =
      input.graph := by
  rw [toIndependentBondPathData_attachIndependentBondPathData state input graph_eq
    conformation_eq valid]

/-- Recovery of the supplied independent conformation. -/
@[simp] theorem toIndependentBondPathData_attachIndependentBondPathData_conformation
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation)
    (valid : PathGeometryValid
      (attachIndependentBondPathData state input graph_eq conformation_eq)) :
    (toIndependentBondPathData
        (attachIndependentBondPathData state input graph_eq conformation_eq) valid).conformation =
      input.conformation := by
  rw [toIndependentBondPathData_attachIndependentBondPathData state input graph_eq
    conformation_eq valid]

/-- Recovery of the supplied independent occurrence map. -/
@[simp] theorem toIndependentBondPathData_attachIndependentBondPathData_interactionOccurrence
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation)
    (valid : PathGeometryValid
      (attachIndependentBondPathData state input graph_eq conformation_eq)) :
    (toIndependentBondPathData
        (attachIndependentBondPathData state input graph_eq conformation_eq)
        valid).interactionOccurrence = input.interactionOccurrence := by
  rw [toIndependentBondPathData_attachIndependentBondPathData state input graph_eq
    conformation_eq valid]

/-- Recovery of every supplied bounded occurrence index. -/
@[simp] theorem toIndependentBondPathData_attachIndependentBondPathData_interactionIndex
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation)
    (valid : PathGeometryValid
      (attachIndependentBondPathData state input graph_eq conformation_eq)) (edge : NewE) :
    (toIndependentBondPathData
        (attachIndependentBondPathData state input graph_eq conformation_eq)
        valid).interactionIndex edge =
      Fin.cast
        (congrArg (fun graph : FiniteAtomInteractionHypergraph V =>
          graph.interactions.length) graph_eq)
        (input.interactionIndex edge) := by
  apply Fin.ext
  exact congrFun
    (toIndependentBondPathData_attachIndependentBondPathData_interactionOccurrence
      state input graph_eq conformation_eq valid) edge

/-- Recovery of every supplied oriented source endpoint. -/
@[simp] theorem toIndependentBondPathData_attachIndependentBondPathData_source
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation)
    (valid : PathGeometryValid
      (attachIndependentBondPathData state input graph_eq conformation_eq)) :
    (toIndependentBondPathData
        (attachIndependentBondPathData state input graph_eq conformation_eq) valid).source =
      input.source := by
  rw [toIndependentBondPathData_attachIndependentBondPathData state input graph_eq
    conformation_eq valid]

/-- Recovery of every supplied oriented target endpoint. -/
@[simp] theorem toIndependentBondPathData_attachIndependentBondPathData_target
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation)
    (valid : PathGeometryValid
      (attachIndependentBondPathData state input graph_eq conformation_eq)) :
    (toIndependentBondPathData
        (attachIndependentBondPathData state input graph_eq conformation_eq) valid).target =
      input.target := by
  rw [toIndependentBondPathData_attachIndependentBondPathData state input graph_eq
    conformation_eq valid]

/-- Recovery of every supplied continuous arc. -/
@[simp] theorem toIndependentBondPathData_attachIndependentBondPathData_arc
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation)
    (valid : PathGeometryValid
      (attachIndependentBondPathData state input graph_eq conformation_eq)) :
    (toIndependentBondPathData
        (attachIndependentBondPathData state input graph_eq conformation_eq) valid).arc =
      input.arc := by
  rw [toIndependentBondPathData_attachIndependentBondPathData state input graph_eq
    conformation_eq valid]

/-- Pointwise recovery of every supplied arc value. -/
@[simp] theorem toIndependentBondPathData_attachIndependentBondPathData_arc_apply
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation)
    (valid : PathGeometryValid
      (attachIndependentBondPathData state input graph_eq conformation_eq))
    (edge : NewE) (t : I) :
    (toIndependentBondPathData
        (attachIndependentBondPathData state input graph_eq conformation_eq)
        valid).arc edge t = input.arc edge t := by
  rw [toIndependentBondPathData_attachIndependentBondPathData state input graph_eq
    conformation_eq valid]

/-! ## Compatibility with the existing frame updater -/

/-- Attaching paths commutes with attaching frames.  Both operations are record updates, so the
frame channel (the newly added field) and the path channel coexist without interference. -/
theorem attachIndependentBondPathData_withFrames
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation)
    (frames : List (FrameAnnotation V)) :
    attachIndependentBondPathData (withFrames state frames) input graph_eq conformation_eq =
      withFrames
        (attachIndependentBondPathData state input graph_eq conformation_eq) frames :=
  rfl

/-- Conversely, attaching frames to the attached state leaves the replacement path channel intact:
the frame updater only changes `frames`. -/
@[simp] theorem withFrames_attachIndependentBondPathData_paths
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation)
    (frames : List (FrameAnnotation V)) (edge : NewE) :
    (withFrames
        (attachIndependentBondPathData state input graph_eq conformation_eq) frames).paths edge =
      input.toPathAnnotation edge := rfl

/-! ## Commutation with the approved electronic-state attachment -/

/-- Attaching independent paths commutes with the approved electronic-state attachment.

`OrganicStereoElectronicStateAttachment.attachElectronic` changes only `electronic?` and
`electronic_unpaired` and retains the path channel; `attachIndependentBondPathData` changes only the
four path fields and retains the electronic channel.  Since each is a record update on a disjoint
set of fields, the two operations commute definitionally, in either order.  The electronic source
is stated at `state.graph`, which is also the graph of the path-attached state. -/
theorem attachIndependentBondPathData_attachElectronic
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation)
    (source : IndependentElectronicSiteSource state.graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence) :
    attachElectronic (attachIndependentBondPathData state input graph_eq conformation_eq)
        source assignment =
      attachIndependentBondPathData (attachElectronic state source assignment) input
        graph_eq conformation_eq :=
  rfl

/-- The same commutation read in the other direction: attaching electrons to a path-attached state
is the path attachment of the electronically attached state. -/
theorem attachElectronic_attachIndependentBondPathData
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation)
    (source : IndependentElectronicSiteSource state.graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence) :
    attachIndependentBondPathData (attachElectronic state source assignment) input
        graph_eq conformation_eq =
      attachElectronic (attachIndependentBondPathData state input graph_eq conformation_eq)
        source assignment :=
  rfl

/-- After the two commuting attachments, the path channel still recovers the supplied independent
record, and the electronic inventory is exactly the supplied ingress channel.  This is the
composed coexistence guarantee: neither operation consumes the other's data. -/
theorem attachIndependentBondPathData_attachElectronic_paths_and_electronic
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation)
    (source : IndependentElectronicSiteSource state.graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence)
    (valid : PathGeometryValid
      (attachIndependentBondPathData (attachElectronic state source assignment) input
        graph_eq conformation_eq)) :
    (toIndependentBondPathData
        (attachIndependentBondPathData (attachElectronic state source assignment) input
          graph_eq conformation_eq) valid) = input ∧
      (attachElectronic (attachIndependentBondPathData state input graph_eq conformation_eq)
          source assignment).electronic? =
        some (ingressChannel source assignment) :=
  ⟨toIndependentBondPathData_attachIndependentBondPathData
      (attachElectronic state source assignment) input graph_eq conformation_eq valid,
    attachElectronic_electronic? (attachIndependentBondPathData state input graph_eq
      conformation_eq) source assignment⟩

/-! ## Simultaneous coexistence of paths, bands, electronic data and frames -/

/-- The attached state carries the supplied path geometry and the supplied independent record,
while retaining the existing band family and its agreement evidence, the existing electronic
inventory and its evidence, and the existing frame annotations.  This is the coexistence statement
needed for downstream composition; no channel is sacrificed for another. -/
theorem attachIndependentBondPathData_coexistence
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation)
    (valid : PathGeometryValid
      (attachIndependentBondPathData state input graph_eq conformation_eq)) :
    PathGeometryValid (attachIndependentBondPathData state input graph_eq conformation_eq) ∧
      toIndependentBondPathData
          (attachIndependentBondPathData state input graph_eq conformation_eq) valid = input ∧
        (attachIndependentBondPathData state input graph_eq conformation_eq).bandFamily =
            state.bandFamily ∧
          (attachIndependentBondPathData state input graph_eq conformation_eq).band_agreement =
              state.band_agreement ∧
            (attachIndependentBondPathData state input graph_eq conformation_eq).electronic? =
                state.electronic? ∧
              (attachIndependentBondPathData state input graph_eq conformation_eq).frames =
                state.frames :=
  ⟨pathGeometryValid_attachIndependentBondPathData state input graph_eq conformation_eq,
    toIndependentBondPathData_attachIndependentBondPathData state input graph_eq conformation_eq
      valid,
    rfl, rfl, rfl, rfl⟩

/-- The same coexistence statement with the geometry proof derived internally rather than supplied
by the caller. -/
theorem attachIndependentBondPathData_coexistence_derived
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    let attached := attachIndependentBondPathData state input graph_eq conformation_eq
    PathGeometryValid attached ∧
      toIndependentBondPathData attached
          (pathGeometryValid_attachIndependentBondPathData state input graph_eq conformation_eq) =
        input ∧
        attached.bandFamily = state.bandFamily ∧
          attached.electronic? = state.electronic? ∧
            attached.frames = state.frames :=
  ⟨pathGeometryValid_attachIndependentBondPathData state input graph_eq conformation_eq,
    toIndependentBondPathData_attachIndependentBondPathData state input graph_eq conformation_eq
      (pathGeometryValid_attachIndependentBondPathData state input graph_eq conformation_eq),
    rfl, rfl, rfl⟩

end TetraStereo.OneCenter
