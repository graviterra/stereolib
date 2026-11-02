import TetraStereo.KernelOnly
import TetraStereo.OneCenter.OrganicStereoFiniteGraphEmbedding
import TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# Structural molecular inhabitance for every finite atom interaction hypergraph

Two accepted results are composed here, with no hypothesis left over:

* `OrganicStereoFiniteGraphEmbedding.finiteGraphEmbedded` constructs an `EmbeddedGraph src dst`
  for *every* finite loopless multigraph (`[Fintype V]`, `[Fintype E]`, `∀ e, src e ≠ dst e`).
* `OrganicStereoEmbeddedMolecularGraphCoverage` turns *one supplied* global embedding of the
  canonical selected-bond realization of a finite atom interaction hypergraph into the actual
  `IndependentBondPathData`, its derived `CompleteForSourcePairBonds` proof, the accepted
  source-bound record, and the molecular-evidence assembly / canonical transport inverse.

This module removes the supplied embedding.  For an arbitrary `FiniteAtomInteractionHypergraph V`
and an arbitrary atom enumeration, the selected-bond graph is the multigraph with edge type
`SelectedBondIndex graph` and endpoint maps `selectedSource graph` / `selectedTarget graph`.  Its
per-edge non-loop condition is *derived* from the source hypergraph's independent
`participants_nodup` field (`selectedSource_ne_target`), so `finiteGraphEmbedded` applies.  The
resulting embedding `inhabitedEmbedding graph` is then fed to the coverage layer, producing

* `inhabitedGeometry graph` and `inhabitedData graph` with the exact source graph, the exact
  oriented selected endpoints, the exact occurrence indices, the constructed moment-curve
  positions, and every derived geometric law;
* derived completeness for every enumeration, with the documented set exhibited as the image of
  the selected occurrence subtype (so parallel bonds between the same two atoms remain distinct);
* the molecular-evidence request `inhabitedEvidence graph` and exact recovery through the actual
  assembly and canonical finite transport.

## What the construction is, and what it is not

The vertex positions are the moment-curve images of a finite enumeration of `V ⊕ SelectedBondIndex`
(the `SelectedBondIndex` summand is the private subdivision point of each selected occurrence).
They are *constructed*: they are not prescribed atom coordinates, they are not extracted from any
source geometry, and no supplied map, arc family, geometric law, coverage hypothesis or
inhabitance hypothesis is an input.  The result is *structural inhabitance* only.  It asserts no
chemical realizability, no electron/wavefunction semantics, no knot or link classification, and no
spatial realization of unselected hyperedges; every unselected interaction (multicenter, ionic,
metallic, hydrogen-bond, `.other`, and selected-kind interactions with more than two participants)
is retained verbatim in the source interaction list and is never realized as a path.
-/

namespace TetraStereo.OneCenter
namespace OrganicStereoFiniteGraphMolecularInhabitance

open scoped unitInterval

open TetraStereo.OneCenter.JointCoreEncoding
open TetraStereo.OneCenter.OrganicStereoEmbeddedGraphRealization
open TetraStereo.OneCenter.OrganicStereoFiniteGraphEmbedding
open TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage
open TetraStereo.OneCenter.OrganicStereoMolecularEvidenceAssembly

noncomputable section

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The selected endpoints are loopless

The finite-graph embedding theorem is stated for a loopless multigraph.  The selected-bond graph
of an arbitrary source hypergraph is loopless for free: its endpoints are positions `0` and `1` of
a `Nodup` participant list of length two. -/

/-- **Derived non-loop condition.**  Every selected binary occurrence has distinct oriented
endpoints.  No non-loop hypothesis is supplied to the construction: this is the source graph's own
`participants_nodup` field, decoded through the positional description of a length-two
occurrence. -/
theorem selectedNoLoops (graph : FiniteAtomInteractionHypergraph V) :
    ∀ edge : SelectedBondIndex graph,
      selectedSource graph edge ≠ selectedTarget graph edge :=
  selectedSource_ne_target graph

/-! ## The self-contained embedding

`finiteGraphEmbedded` is applied to the selected-bond graph of `graph`.  Its construction uses the
moment curve in `ℝ³`: the vertex `w` is placed at `(vp w, (vp w)², (vp w)³)` and the selected
occurrence `e` is the two-segment polyline through the private point `ep e`.  The parameters come
from an enumeration of `V ⊕ SelectedBondIndex graph`, so parallel selected occurrences receive
distinct private parameters. -/

/-- The global embedding of the canonical selected-bond realization, constructed for the source
graph alone.  Neither a map, nor arcs, nor local geometric laws, nor an inhabitance hypothesis is
an input. -/
def inhabitedEmbedding (graph : FiniteAtomInteractionHypergraph V) :
    EmbeddedGraph (selectedSource graph) (selectedTarget graph) :=
  finiteGraphEmbedded (selectedSource graph) (selectedTarget graph) (selectedNoLoops graph)

/-- The constructed global map is literally the finite-graph construction's `globalMap`. -/
theorem inhabitedEmbedding_map (graph : FiniteAtomInteractionHypergraph V) :
    (inhabitedEmbedding graph).map =
      ⟨globalMap (selectedSource graph) (selectedTarget graph),
        globalMap_continuous (selectedSource graph) (selectedTarget graph)⟩ :=
  finiteGraphEmbedded_map (selectedSource graph) (selectedTarget graph)
    (selectedNoLoops graph)

/-- **The positions are constructed, not prescribed.**  The position of the atom `w` is the
moment-curve point of the vertex label parameter.  No source coordinate appears. -/
theorem inhabitedEmbedding_conformation (graph : FiniteAtomInteractionHypergraph V) (w : V) :
    (inhabitedEmbedding graph).conformation w =
      momentCurve
        (labelParam (V := V) (E := SelectedBondIndex graph) (Sum.inl w)) :=
  finiteGraphEmbedded_conformation (selectedSource graph) (selectedTarget graph)
    (selectedNoLoops graph) w

/-- The position map of the constructed embedding is injective. -/
theorem inhabitedEmbedding_atom_injective (graph : FiniteAtomInteractionHypergraph V) :
    Function.Injective (inhabitedEmbedding graph).conformation :=
  (inhabitedEmbedding graph).atom_injective

/-- Every selected arc of the constructed embedding is injective on the unit interval. -/
theorem inhabitedEmbedding_arc_injective (graph : FiniteAtomInteractionHypergraph V)
    (edge : SelectedBondIndex graph) :
    Function.Injective ((inhabitedEmbedding graph).arc edge) :=
  (inhabitedEmbedding graph).arc_injective edge (selectedNoLoops graph edge)

/-- Arc interiors of the constructed embedding avoid every atom position. -/
theorem inhabitedEmbedding_interior_avoids_atoms (graph : FiniteAtomInteractionHypergraph V)
    (edge : SelectedBondIndex graph) (t : I) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (atom : V) :
    (inhabitedEmbedding graph).arc edge t ≠
      (inhabitedEmbedding graph).conformation atom :=
  (inhabitedEmbedding graph).interior_avoids_atoms edge t ht0 ht1 atom

/-- Distinct selected arcs of the constructed embedding meet only at a common endpoint atom. -/
theorem inhabitedEmbedding_intersects_only_at_common_endpoints
    (graph : FiniteAtomInteractionHypergraph V) (edge other : SelectedBondIndex graph)
    (t s : I) (hne : edge ≠ other)
    (h : (inhabitedEmbedding graph).arc edge t =
      (inhabitedEmbedding graph).arc other s) :
    ∃ atom : V,
      sourceEndpointAt? (selectedSource graph) (selectedTarget graph) edge t = some atom ∧
        sourceEndpointAt? (selectedSource graph) (selectedTarget graph) other s = some atom :=
  (inhabitedEmbedding graph).intersects_only_at_common_endpoints edge other t s hne h

/-! ## The constructed selected path core

The coverage layer's geometry adapter is applied to the constructed embedding.  Every field of
`SelectedGeometry` — and hence every field of `IndependentBondPathData` — is derived; none is
supplied. -/

/-- The selected geometry derived from the constructed embedding. -/
def inhabitedGeometry (graph : FiniteAtomInteractionHypergraph V) :
    SelectedGeometry graph :=
  selectedGeometryOfEmbedding graph (inhabitedEmbedding graph)

/-- The actual independent bond-path data of the source graph, constructed from the source graph
alone.  Its edge type is the selected occurrence subtype, so parallel occurrences stay distinct,
and its participant/kind/endpoint/occurrence fields are structural. -/
def inhabitedData (graph : FiniteAtomInteractionHypergraph V) :
    IndependentBondPathData V (SelectedBondIndex graph) :=
  selectedDataOfEmbedding graph (inhabitedEmbedding graph)

@[simp] theorem inhabitedData_graph (graph : FiniteAtomInteractionHypergraph V) :
    (inhabitedData graph).graph = graph :=
  selectedDataOfEmbedding_graph graph (inhabitedEmbedding graph)

@[simp] theorem inhabitedData_conformation (graph : FiniteAtomInteractionHypergraph V) :
    (inhabitedData graph).conformation = (inhabitedEmbedding graph).conformation :=
  selectedDataOfEmbedding_conformation graph (inhabitedEmbedding graph)

@[simp] theorem inhabitedData_arc (graph : FiniteAtomInteractionHypergraph V)
    (edge : SelectedBondIndex graph) :
    (inhabitedData graph).arc edge = (inhabitedEmbedding graph).arc edge :=
  selectedDataOfEmbedding_arc graph (inhabitedEmbedding graph) edge

@[simp] theorem inhabitedData_source (graph : FiniteAtomInteractionHypergraph V)
    (edge : SelectedBondIndex graph) :
    (inhabitedData graph).source edge = selectedSource graph edge :=
  selectedDataOfEmbedding_source graph (inhabitedEmbedding graph) edge

@[simp] theorem inhabitedData_target (graph : FiniteAtomInteractionHypergraph V)
    (edge : SelectedBondIndex graph) :
    (inhabitedData graph).target edge = selectedTarget graph edge :=
  selectedDataOfEmbedding_target graph (inhabitedEmbedding graph) edge

@[simp] theorem inhabitedData_occurrence (graph : FiniteAtomInteractionHypergraph V)
    (edge : SelectedBondIndex graph) :
    (inhabitedData graph).interactionOccurrence edge = selectedOccurrence graph edge :=
  selectedDataOfEmbedding_occurrence graph (inhabitedEmbedding graph) edge

/-- The constructed data's source graph retains the whole interaction list of the source, in
order.  Unselected hyperedges are never dropped. -/
theorem inhabitedData_interactions_eq (graph : FiniteAtomInteractionHypergraph V) :
    (inhabitedData graph).graph.interactions = graph.interactions := rfl

/-- The oriented endpoints of the constructed data are distinct. -/
theorem inhabitedData_source_ne_target (graph : FiniteAtomInteractionHypergraph V) :
    ∀ edge : SelectedBondIndex graph,
      (inhabitedData graph).source edge ≠ (inhabitedData graph).target edge :=
  (inhabitedData graph).source_ne_target

/-- **Occurrence injectivity.**  Two selected occurrences are never identified, including two
parallel bonds between the same pair of atoms. -/
theorem inhabitedData_occurrence_injective (graph : FiniteAtomInteractionHypergraph V) :
    Function.Injective (inhabitedData graph).interactionOccurrence :=
  (inhabitedData graph).interactionOccurrence_injective

/-- Distinct selected occurrences induce distinct occurrence indices.  This is the explicit
parallel-edge identity statement: sharing both endpoints does not merge occurrences. -/
theorem inhabitedData_parallel_occurrences_distinct
    (graph : FiniteAtomInteractionHypergraph V)
    {first second : SelectedBondIndex graph} (hne : first ≠ second) :
    selectedOccurrence graph first ≠ selectedOccurrence graph second :=
  fun equal => hne (selectedOccurrence_injective graph equal)

/-- The constructed conformation is injective. -/
theorem inhabitedData_atom_injective (graph : FiniteAtomInteractionHypergraph V) :
    Function.Injective (inhabitedData graph).conformation :=
  (inhabitedData graph).atom_injective

/-- Every constructed selected arc is injective on the unit interval. -/
theorem inhabitedData_arc_injective (graph : FiniteAtomInteractionHypergraph V)
    (edge : SelectedBondIndex graph) :
    Function.Injective ((inhabitedData graph).arc edge) :=
  (inhabitedData graph).arc_injective edge

/-- Constructed arc interiors avoid every atom position. -/
theorem inhabitedData_interior_avoids_atoms (graph : FiniteAtomInteractionHypergraph V)
    (edge : SelectedBondIndex graph) (t : I) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (atom : V) :
    (inhabitedData graph).arc edge t ≠ (inhabitedData graph).conformation atom :=
  (inhabitedData graph).interior_avoids_atoms edge t ht0 ht1 atom

/-- Distinct constructed arcs meet only at a common endpoint atom. -/
theorem inhabitedData_intersects_only_at_common_endpoints
    (graph : FiniteAtomInteractionHypergraph V) (edge other : SelectedBondIndex graph)
    (t s : I) (hne : edge ≠ other)
    (h : (inhabitedData graph).arc edge t = (inhabitedData graph).arc other s) :
    ∃ atom : V,
      sourceEndpointAt? (inhabitedData graph).source (inhabitedData graph).target edge t =
          some atom ∧
        sourceEndpointAt? (inhabitedData graph).source (inhabitedData graph).target other s =
          some atom :=
  (inhabitedData graph).intersects_only_at_common_endpoints edge other t s hne h

/-- Structural participant compatibility at the constructed occurrence index. -/
theorem inhabitedData_participants_exact (graph : FiniteAtomInteractionHypergraph V)
    (edge : SelectedBondIndex graph) :
    ((inhabitedData graph).graph.interactions.get
        ((inhabitedData graph).interactionIndex edge)).1 =
      [(inhabitedData graph).source edge, (inhabitedData graph).target edge] :=
  (inhabitedData graph).participants_exact edge

/-- Structural kind compatibility at the constructed occurrence index. -/
theorem inhabitedData_kind_selected (graph : FiniteAtomInteractionHypergraph V)
    (edge : SelectedBondIndex graph) :
    SemanticInteractionKind.isSelectedPairKind
      ((inhabitedData graph).graph.interactions.get
        ((inhabitedData graph).interactionIndex edge)).2 = true :=
  (inhabitedData graph).kind_selected edge

/-- **Derived completeness.**  For every atom enumeration, every selected binary pair bond of the
encoded source graph is documented by the constructed path family.  This is a theorem of the
construction, not a hypothesis. -/
theorem inhabitedData_complete (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (inhabitedData graph).CompleteForSourcePairBonds enumeration :=
  selectedDataOfEmbedding_completeForSourcePairBonds graph (inhabitedEmbedding graph)
    enumeration

/-- The documented set is exactly the image of the selected occurrence subtype.  In particular no
unselected hyperedge is documented, and no selected occurrence is silently merged. -/
theorem inhabitedData_documented_eq_selected_image
    (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (inhabitedData graph).documented enumeration =
      Finset.univ.image (fun edge : SelectedBondIndex graph =>
        encodedIndex graph enumeration edge.1) :=
  SelectedGeometry.documented_eq_selected_image (inhabitedGeometry graph) enumeration

/-- Every selected occurrence is documented. -/
theorem inhabitedData_selected_mem_documented (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) (edge : SelectedBondIndex graph) :
    encodedIndex graph enumeration edge.1 ∈ (inhabitedData graph).documented enumeration :=
  SelectedGeometry.selected_mem_documented (inhabitedGeometry graph) enumeration edge

/-! ## The constructed molecular-evidence request and its exact recovery

The actual `OrganicMolecularEvidence` request is constructed from the constructed path data.  It is
not supplied: the graph, the conformation and the path channel are the construction's own, and
every optional channel is genuinely absent/empty. -/

/-- The constructed molecular-evidence request. -/
def inhabitedEvidence (graph : FiniteAtomInteractionHypergraph V) : OrganicMolecularEvidence V :=
  selectedEvidenceOfEmbedding graph (inhabitedEmbedding graph)

@[simp] theorem inhabitedEvidence_graph (graph : FiniteAtomInteractionHypergraph V) :
    (inhabitedEvidence graph).graph = graph :=
  selectedEvidenceOfEmbedding_graph graph (inhabitedEmbedding graph)

@[simp] theorem inhabitedEvidence_conformation (graph : FiniteAtomInteractionHypergraph V) :
    (inhabitedEvidence graph).conformation = (inhabitedEmbedding graph).conformation :=
  selectedEvidenceOfEmbedding_conformation graph (inhabitedEmbedding graph)

@[simp] theorem inhabitedEvidence_paths (graph : FiniteAtomInteractionHypergraph V) :
    (inhabitedEvidence graph).paths? =
      some (independentPathFamily (inhabitedData graph)) :=
  selectedEvidenceOfEmbedding_paths graph (inhabitedEmbedding graph)

/-- The actual molecular assembly of the constructed request has exactly the source graph. -/
theorem assemble_stateGraph_inhabitedEvidence (graph : FiniteAtomInteractionHypergraph V) :
    (OrganicStereoMolecularEvidenceAssembly.assemble
        (inhabitedEvidence graph)).stateGraph = graph :=
  assemble_stateGraph_selectedEvidenceOfEmbedding graph (inhabitedEmbedding graph)

/-- The actual molecular assembly retains exactly the constructed positions. -/
theorem assemble_stateConformation_inhabitedEvidence
    (graph : FiniteAtomInteractionHypergraph V) :
    (OrganicStereoMolecularEvidenceAssembly.assemble
        (inhabitedEvidence graph)).stateConformation =
      (inhabitedEmbedding graph).conformation :=
  assemble_stateConformation_selectedEvidenceOfEmbedding graph (inhabitedEmbedding graph)

/-- The assembled path channel is exactly the constructed path family. -/
theorem decodedPaths?_assemble_inhabitedEvidence
    (graph : FiniteAtomInteractionHypergraph V) :
    OrganicStereoMolecularEvidenceAssembly.decodedPaths?
        (OrganicStereoMolecularEvidenceAssembly.assemble (inhabitedEvidence graph)) =
      some (independentPathFamily (inhabitedData graph)) :=
  decodedPaths?_assemble_selectedEvidenceOfEmbedding graph (inhabitedEmbedding graph)

/-- Canonical finite transport also recovers exactly the constructed path family. -/
theorem decodedPaths?_canonicalAssemble_inhabitedEvidence
    (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    OrganicStereoMolecularEvidenceAssembly.decodedPaths?
        (OrganicStereoMolecularCanonicalTransport.canonicalDecode
          (OrganicStereoMolecularCanonicalTransport.canonicalAssemble enumeration
            (inhabitedEvidence graph))) =
      some (independentPathFamily (inhabitedData graph)) :=
  decodedPaths?_canonicalAssemble_selectedEvidenceOfEmbedding graph (inhabitedEmbedding graph)
    enumeration

/-- The actual assembly decodes back to exactly the constructed request. -/
theorem decode_assemble_inhabitedEvidence (graph : FiniteAtomInteractionHypergraph V) :
    OrganicStereoMolecularEvidenceAssembly.decode
        (OrganicStereoMolecularEvidenceAssembly.assemble (inhabitedEvidence graph)) =
      inhabitedEvidence graph :=
  decode_assemble_selectedEvidenceOfEmbedding graph (inhabitedEmbedding graph)

/-- The canonical assembly decodes back to exactly the constructed request. -/
theorem decode_canonicalAssemble_inhabitedEvidence
    (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    OrganicStereoMolecularEvidenceAssembly.decode
        (OrganicStereoMolecularCanonicalTransport.canonicalDecode
          (OrganicStereoMolecularCanonicalTransport.canonicalAssemble enumeration
            (inhabitedEvidence graph))) =
      inhabitedEvidence graph :=
  decode_canonicalAssemble_selectedEvidenceOfEmbedding graph (inhabitedEmbedding graph)
    enumeration

/-! ## The accepted source-bound encoding of the constructed data -/

/-- The accepted `SourceBoundEmbeddedBondPaths` record built from the constructed data. -/
def inhabitedSourceBound (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv :
      SelectedBondIndex graph ≃ Fin (Fintype.card (SelectedBondIndex graph))) :
    SourceBoundEmbeddedBondPaths :=
  selectedSourceBoundOfEmbedding graph (inhabitedEmbedding graph) enumeration edgeEquiv

/-- The source-bound record retains the whole encoded authoritative source. -/
@[simp] theorem inhabitedSourceBound_source (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv :
      SelectedBondIndex graph ≃ Fin (Fintype.card (SelectedBondIndex graph))) :
    (inhabitedSourceBound graph enumeration edgeEquiv).source =
      graph.encodeAuthoritative enumeration := rfl

/-- The source-bound record retains every source interaction in order. -/
@[simp] theorem inhabitedSourceBound_interactions (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv :
      SelectedBondIndex graph ≃ Fin (Fintype.card (SelectedBondIndex graph))) :
    (inhabitedSourceBound graph enumeration edgeEquiv).source.molecule.interactions =
      graph.interactions.map
        (FiniteAtomInteractionHypergraph.encodeInteraction enumeration) := rfl

/-- Every parametrized arc is exactly the constructed embedding's arc. -/
theorem inhabitedSourceBound_arc (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv :
      SelectedBondIndex graph ≃ Fin (Fintype.card (SelectedBondIndex graph)))
    (edge : SelectedBondIndex graph) (t : I) :
    ((inhabitedSourceBound graph enumeration edgeEquiv).table.edge (edgeEquiv edge)).arc t =
      (inhabitedEmbedding graph).arc edge t :=
  selectedSourceBoundOfEmbedding_arc graph (inhabitedEmbedding graph) enumeration edgeEquiv
    edge t

/-! ## The typed universal construction

`ConstructedInhabitant` records the whole specification of the construction as data.  Its
constructor `constructedInhabitant` is a definition that takes only the source graph and the atom
enumeration; no field is a supplied input. -/

/-- The complete constructed inhabitant of a finite atom interaction hypergraph at an atom
enumeration: the global embedding, the selected path core, the molecular-evidence request, and
their exact recovery and completeness laws. -/
structure ConstructedInhabitant (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) where
  /-- The constructed global embedding of the selected-bond realization. -/
  embedding : EmbeddedGraph (selectedSource graph) (selectedTarget graph)
  /-- The constructed independent bond-path data. -/
  data : IndependentBondPathData V (SelectedBondIndex graph)
  /-- The constructed molecular-evidence request. -/
  evidence : OrganicMolecularEvidence V
  /-- The embedding's global map is the finite-graph construction's moment-curve map. -/
  embedding_map : embedding.map =
    ⟨globalMap (selectedSource graph) (selectedTarget graph),
      globalMap_continuous (selectedSource graph) (selectedTarget graph)⟩
  /-- The data's graph is exactly the source graph. -/
  data_graph : data.graph = graph
  /-- The whole interaction list is retained in order. -/
  data_interactions : data.graph.interactions = graph.interactions
  /-- Oriented first endpoints are the structural source participants. -/
  data_source : ∀ edge : SelectedBondIndex graph, data.source edge = selectedSource graph edge
  /-- Oriented second endpoints are the structural target participants. -/
  data_target : ∀ edge : SelectedBondIndex graph, data.target edge = selectedTarget graph edge
  /-- Occurrence indices are the structural selected occurrence indices. -/
  data_occurrence :
    ∀ edge : SelectedBondIndex graph, data.interactionOccurrence edge = selectedOccurrence graph edge
  /-- Parametrized arcs are the embedding's arcs. -/
  data_arc : ∀ edge : SelectedBondIndex graph, data.arc edge = embedding.arc edge
  /-- Selected endpoints are distinct. -/
  data_source_ne_target :
    ∀ edge : SelectedBondIndex graph, data.source edge ≠ data.target edge
  /-- Parallel selected occurrences stay distinct. -/
  data_occurrence_injective : Function.Injective data.interactionOccurrence
  /-- Atom positions are distinct. -/
  data_atom_injective : Function.Injective data.conformation
  /-- Every selected arc is injective on the unit interval. -/
  data_arc_injective : ∀ edge : SelectedBondIndex graph, Function.Injective (data.arc edge)
  /-- Participant compatibility at the constructed occurrence index. -/
  data_participants : ∀ edge : SelectedBondIndex graph,
    (data.graph.interactions.get (data.interactionIndex edge)).1 =
      [data.source edge, data.target edge]
  /-- Kind compatibility at the constructed occurrence index. -/
  data_kind : ∀ edge : SelectedBondIndex graph,
    SemanticInteractionKind.isSelectedPairKind
      (data.graph.interactions.get (data.interactionIndex edge)).2 = true
  /-- Derived completeness for the given enumeration. -/
  data_complete : data.CompleteForSourcePairBonds enumeration
  /-- The documented set is exactly the selected-index image of the data itself. -/
  data_documented : data.documented enumeration =
    Finset.univ.image (fun edge : SelectedBondIndex graph =>
      encodedIndex data.graph enumeration (data.interactionIndex edge))
  /-- The evidence request's graph is the source graph. -/
  evidence_graph : evidence.graph = graph
  /-- The evidence request's conformation is the embedding's. -/
  evidence_conformation : evidence.conformation = embedding.conformation
  /-- The evidence request carries exactly the constructed path family. -/
  evidence_paths : evidence.paths? = some (independentPathFamily data)
  /-- The actual assembly recovers the source graph. -/
  assembled_graph :
    (OrganicStereoMolecularEvidenceAssembly.assemble evidence).stateGraph = graph
  /-- The actual assembly recovers the constructed positions. -/
  assembled_conformation :
    (OrganicStereoMolecularEvidenceAssembly.assemble evidence).stateConformation =
      embedding.conformation
  /-- The actual assembly recovers exactly the constructed path family. -/
  assembled_paths :
    OrganicStereoMolecularEvidenceAssembly.decodedPaths?
        (OrganicStereoMolecularEvidenceAssembly.assemble evidence) =
      some (independentPathFamily data)
  /-- Canonical finite transport decodes back to exactly the constructed request. -/
  canonical_decode :
    OrganicStereoMolecularEvidenceAssembly.decode
        (OrganicStereoMolecularCanonicalTransport.canonicalDecode
          (OrganicStereoMolecularCanonicalTransport.canonicalAssemble enumeration evidence)) =
      evidence

/-- **The typed universal construction.**  Every finite atom interaction hypergraph and every atom
enumeration yield the constructed inhabitant.  No map, arc, geometric law, coverage hypothesis or
inhabitance hypothesis is an input. -/
def constructedInhabitant (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    ConstructedInhabitant graph enumeration where
  embedding := inhabitedEmbedding graph
  data := inhabitedData graph
  evidence := inhabitedEvidence graph
  embedding_map := inhabitedEmbedding_map graph
  data_graph := inhabitedData_graph graph
  data_interactions := inhabitedData_interactions_eq graph
  data_source := inhabitedData_source graph
  data_target := inhabitedData_target graph
  data_occurrence := inhabitedData_occurrence graph
  data_arc := inhabitedData_arc graph
  data_source_ne_target := inhabitedData_source_ne_target graph
  data_occurrence_injective := inhabitedData_occurrence_injective graph
  data_atom_injective := inhabitedData_atom_injective graph
  data_arc_injective := inhabitedData_arc_injective graph
  data_participants := inhabitedData_participants_exact graph
  data_kind := inhabitedData_kind_selected graph
  data_complete := inhabitedData_complete graph enumeration
  data_documented := rfl
  evidence_graph := inhabitedEvidence_graph graph
  evidence_conformation := inhabitedEvidence_conformation graph
  evidence_paths := inhabitedEvidence_paths graph
  assembled_graph := assemble_stateGraph_inhabitedEvidence graph
  assembled_conformation := assemble_stateConformation_inhabitedEvidence graph
  assembled_paths := decodedPaths?_assemble_inhabitedEvidence graph
  canonical_decode := decode_canonicalAssemble_inhabitedEvidence graph enumeration

/-- **Typed universal construction theorem.**  For every actual finite atom interaction hypergraph
and every atom enumeration, the constructed inhabitant has the exact source graph and interaction
list, the structural selected endpoints and occurrence indices, injective positions, derived
completeness, the exact molecular-evidence request, and exact assembled/canonical recovery.  All
components are produced by `constructedInhabitant`; nothing is assumed. -/
theorem universal_finiteGraph_molecular_inhabitance
    (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (constructedInhabitant graph enumeration).data.graph = graph ∧
      (constructedInhabitant graph enumeration).data.graph.interactions = graph.interactions ∧
      (∀ edge : SelectedBondIndex graph,
        (constructedInhabitant graph enumeration).data.source edge = selectedSource graph edge) ∧
      (∀ edge : SelectedBondIndex graph,
        (constructedInhabitant graph enumeration).data.target edge = selectedTarget graph edge) ∧
      (∀ edge : SelectedBondIndex graph,
        (constructedInhabitant graph enumeration).data.interactionOccurrence edge =
          selectedOccurrence graph edge) ∧
      Function.Injective
        (constructedInhabitant graph enumeration).data.interactionOccurrence ∧
      Function.Injective
        (constructedInhabitant graph enumeration).data.conformation ∧
      (constructedInhabitant graph enumeration).data.CompleteForSourcePairBonds enumeration ∧
      (constructedInhabitant graph enumeration).evidence.graph = graph ∧
      (OrganicStereoMolecularEvidenceAssembly.assemble
          (constructedInhabitant graph enumeration).evidence).stateGraph = graph ∧
      OrganicStereoMolecularEvidenceAssembly.decodedPaths?
          (OrganicStereoMolecularEvidenceAssembly.assemble
            (constructedInhabitant graph enumeration).evidence) =
        some (independentPathFamily (constructedInhabitant graph enumeration).data) ∧
      OrganicStereoMolecularEvidenceAssembly.decode
          (OrganicStereoMolecularCanonicalTransport.canonicalDecode
            (OrganicStereoMolecularCanonicalTransport.canonicalAssemble enumeration
              (constructedInhabitant graph enumeration).evidence)) =
        (constructedInhabitant graph enumeration).evidence :=
  ⟨(constructedInhabitant graph enumeration).data_graph,
   (constructedInhabitant graph enumeration).data_interactions,
   (constructedInhabitant graph enumeration).data_source,
   (constructedInhabitant graph enumeration).data_target,
   (constructedInhabitant graph enumeration).data_occurrence,
   (constructedInhabitant graph enumeration).data_occurrence_injective,
   (constructedInhabitant graph enumeration).data_atom_injective,
   (constructedInhabitant graph enumeration).data_complete,
   (constructedInhabitant graph enumeration).evidence_graph,
   (constructedInhabitant graph enumeration).assembled_graph,
   (constructedInhabitant graph enumeration).assembled_paths,
   (constructedInhabitant graph enumeration).canonical_decode⟩

/-! ## Empty selected-edge fixture

The accepted one-atom interaction-free fixture is a genuine source with no selected occurrences.
The construction still applies: the embedding is the moment-curve point of the unique atom label,
the path family is empty, and completeness is vacuous. -/

/-- The interaction-free fixture has no selected occurrences. -/
theorem fixtureSelected_card : Fintype.card (SelectedBondIndex fixtureGraph) = 0 :=
  Fintype.card_eq_zero_iff.mpr inferInstance

/-- **Empty case.**  The construction is inhabited for the interaction-free source: the data's
graph is exactly the source, the path family is complete for the canonical enumeration, and the
documented table is empty. -/
theorem fixture_inhabitance :
    (inhabitedData fixtureGraph).graph = fixtureGraph ∧
      (inhabitedData fixtureGraph).CompleteForSourcePairBonds (Equiv.refl (Fin 1)) ∧
      ((inhabitedData fixtureGraph).toBondPathTable (Equiv.refl (Fin 1))).documented.card = 0 := by
  refine ⟨inhabitedData_graph fixtureGraph,
    inhabitedData_complete fixtureGraph (Equiv.refl (Fin 1)), ?_⟩
  rw [IndependentBondPathData.card_documented_eq_card_edges]
  exact fixtureSelected_card

/-- The constructed molecular-evidence request of the interaction-free fixture still recovers its
exact source graph through the actual assembly. -/
theorem fixture_assembled_graph :
    (OrganicStereoMolecularEvidenceAssembly.assemble
        (inhabitedEvidence fixtureGraph)).stateGraph = fixtureGraph :=
  assemble_stateGraph_inhabitedEvidence fixtureGraph

/-! ## Nonempty one-bond fixture

The accepted two-atom one-bond fixture is used to exhibit a nonempty selected occurrence type and
a real constructed arc.  The positioned atoms are moment-curve points of the constructed label
parameters, and the arc endpoints are those constructed positions exactly. -/

/-- The nonempty one-bond fixture has exactly one selected occurrence. -/
theorem toySelected_card_inhabitance :
    Fintype.card (SelectedBondIndex toySourceGraph) = 1 :=
  toySelected_card

/-- The constructed positions of the two fixture atoms are distinct moment-curve points. -/
theorem toy_conformation_distinct :
    (inhabitedEmbedding toySourceGraph).conformation false ≠
      (inhabitedEmbedding toySourceGraph).conformation true := by
  intro equal
  exact Bool.false_ne_true
    ((inhabitedEmbedding toySourceGraph).atom_injective equal)

/-- The constructed position of `false` is the moment-curve image of its label parameter. -/
theorem toy_conformation_false :
    (inhabitedEmbedding toySourceGraph).conformation false =
      momentCurve
        (labelParam (V := Bool) (E := SelectedBondIndex toySourceGraph)
          (Sum.inl false)) :=
  inhabitedEmbedding_conformation toySourceGraph false

/-- The constructed position of `true` is the moment-curve image of its label parameter. -/
theorem toy_conformation_true :
    (inhabitedEmbedding toySourceGraph).conformation true =
      momentCurve
        (labelParam (V := Bool) (E := SelectedBondIndex toySourceGraph)
          (Sum.inl true)) :=
  inhabitedEmbedding_conformation toySourceGraph true

/-- **Nonempty case.**  The construction is inhabited with exactly one selected occurrence: the
data retains the exact source graph, the path family is complete for the canonical enumeration,
the documented table has cardinality one, the oriented endpoints are `false`/`true`, and the
constructed arcs start and end at the constructed positions of those atoms. -/
theorem toy_inhabitance :
    Fintype.card (SelectedBondIndex toySourceGraph) = 1 ∧
      (inhabitedData toySourceGraph).graph = toySourceGraph ∧
      (inhabitedData toySourceGraph).CompleteForSourcePairBonds (Fintype.equivFin Bool) ∧
      ((inhabitedData toySourceGraph).toBondPathTable
        (Fintype.equivFin Bool)).documented.card = 1 ∧
      (∀ edge : SelectedBondIndex toySourceGraph,
        (inhabitedData toySourceGraph).source edge = false) ∧
      (∀ edge : SelectedBondIndex toySourceGraph,
        (inhabitedData toySourceGraph).target edge = true) ∧
      (∀ edge : SelectedBondIndex toySourceGraph,
        (inhabitedData toySourceGraph).arc edge 0 =
          (inhabitedEmbedding toySourceGraph).conformation false) ∧
      (∀ edge : SelectedBondIndex toySourceGraph,
        (inhabitedData toySourceGraph).arc edge 1 =
          (inhabitedEmbedding toySourceGraph).conformation true) := by
  refine ⟨toySelected_card, inhabitedData_graph toySourceGraph,
    inhabitedData_complete toySourceGraph (Fintype.equivFin Bool), ?_, ?_, ?_, ?_, ?_⟩
  · rw [IndependentBondPathData.card_documented_eq_card_edges, toySelected_card]
  · intro edge
    rw [inhabitedData_source, toySelected_source edge]
  · intro edge
    rw [inhabitedData_target, toySelected_target edge]
  · intro edge
    rw [inhabitedData_arc, EmbeddedGraph.arc_zero, toySelected_source edge]
  · intro edge
    rw [inhabitedData_arc, EmbeddedGraph.arc_one, toySelected_target edge]

/-! ## Unselected hyperedges are preserved verbatim

A source with one selected binary bond and one unselected ternary multicenter interaction is used
to exhibit the boundary: the selected bond is realized, the ternary interaction stays in the
source interaction list, and the selected occurrence type is nonempty. -/

/-- Three atoms: one selected binary covalent bond and one unselected ternary multicenter
interaction. -/
def mixedFixtureGraph : FiniteAtomInteractionHypergraph (Fin 3) where
  atomData := fun _ => fixtureAtom
  interactions :=
    [([0, 1], SemanticInteractionKind.unspecifiedCovalent),
     ([0, 1, 2], SemanticInteractionKind.multicenter 4)]
  arity_ge_two := by
    intro edge member
    simp at member
    rcases member with rfl | rfl <;> decide
  participants_nodup := by
    intro edge member
    simp at member
    rcases member with rfl | rfl <;> decide

/-- The selected binary occurrence of the mixed fixture. -/
def mixedFixtureBond : SelectedBondIndex mixedFixtureGraph :=
  ⟨⟨0, by decide⟩, by decide, by decide⟩

/-- The mixed fixture has a nonempty selected occurrence type. -/
theorem mixedFixture_selected_nonempty : Nonempty (SelectedBondIndex mixedFixtureGraph) :=
  ⟨mixedFixtureBond⟩

/-- **Unselected preservation.**  The ternary multicenter interaction remains in the constructed
data's source interaction list; it is not dropped and not realized as a path. -/
theorem mixedFixture_unselected_preserved :
    ([0, 1, 2], SemanticInteractionKind.multicenter 4) ∈
      (inhabitedData mixedFixtureGraph).graph.interactions := by
  rw [inhabitedData_interactions_eq]
  simp [mixedFixtureGraph]

/-- Derived completeness of the mixed fixture at any atom enumeration. -/
theorem mixedFixture_complete (enumeration : Fin 3 ≃ Fin (Fintype.card (Fin 3))) :
    (inhabitedData mixedFixtureGraph).CompleteForSourcePairBonds enumeration :=
  inhabitedData_complete mixedFixtureGraph enumeration

/-! ## Kernel-authority checks

The following commands check that the closures of the construction and of its headline endpoints
use only the standard logical principles `propext`, `Classical.choice` and `Quot.sound`.  No
`sorryAx`, no project axiom, no native-evaluator trust and no compiler trust is permitted. -/

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphMolecularInhabitance.selectedNoLoops
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphMolecularInhabitance.inhabitedEmbedding
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphMolecularInhabitance.inhabitedEmbedding_map
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphMolecularInhabitance.inhabitedEmbedding_conformation
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphMolecularInhabitance.inhabitedGeometry
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphMolecularInhabitance.inhabitedData
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphMolecularInhabitance.inhabitedData_complete
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphMolecularInhabitance.inhabitedData_documented_eq_selected_image
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphMolecularInhabitance.inhabitedData_selected_mem_documented
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphMolecularInhabitance.inhabitedData_parallel_occurrences_distinct
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphMolecularInhabitance.inhabitedEvidence
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphMolecularInhabitance.assemble_stateGraph_inhabitedEvidence
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphMolecularInhabitance.decodedPaths?_assemble_inhabitedEvidence
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphMolecularInhabitance.decodedPaths?_canonicalAssemble_inhabitedEvidence
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphMolecularInhabitance.decode_canonicalAssemble_inhabitedEvidence
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphMolecularInhabitance.inhabitedSourceBound_arc
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphMolecularInhabitance.constructedInhabitant
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphMolecularInhabitance.universal_finiteGraph_molecular_inhabitance
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphMolecularInhabitance.fixture_inhabitance
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphMolecularInhabitance.toy_inhabitance
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphMolecularInhabitance.mixedFixture_unselected_preserved
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoFiniteGraphMolecularInhabitance.mixedFixture_complete

end

end OrganicStereoFiniteGraphMolecularInhabitance
end TetraStereo.OneCenter
