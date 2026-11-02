/-
# Kernel-authority certificate for global-embedding structural coverage

This module imports the accepted

* `OrganicStereoEmbeddedGraphRealization` — the finite multigraph topological realization, its
  coinduced (gluing) topology, the universal property, the derived global/local arc laws, and the
  concrete inhabited single-edge toy embedding in real three-space;
* `OrganicStereoEmbeddedMolecularGraphCoverage` — the noncircular structural coverage layer that
  constructs the selected binary occurrence type, derives `SelectedGeometry` from one global
  embedding, constructs the actual `IndependentBondPathData`, proves
  `CompleteForSourcePairBonds` and exact unique coverage, recovers the accepted source-bound
  table, composes with the actual molecular assembly and canonical finite transport, and supplies
  the nonempty one-bond toy fixture;

simultaneously, so the single build is also a namespace/type integration check across the two
accepted modules and the kernel-only assertion facility.

## What is checked

The `assert_kernel_only` commands below check kernel closure (standard logical axioms only:
`propext`, `Classical.choice`, `Quot.sound`) of the decisive endpoints:

* the realization gluing map's continuity and surjectivity, the coinduced universal property, the
  edge-interval maps, edge injectivity for non-self-loops, the exact vertex/collision forms, and
  the derived global/local arc laws of a supplied `EmbeddedGraph` (endpoint equations, atom
  injectivity, arc injectivity, interior/atom avoidance, the common-endpoint intersection law, and
  edge identity from an interior meeting);
* the structural selected-occurrence construction (`selectedParticipants`,
  `selectedSource_ne_target`, occurrence injectivity), the noncircular decoding theorem
  `exists_selected_of_genuine`, the constructed `IndependentBondPathData`, derived
  `CompleteForSourcePairBonds`, the documented-image description, exact unique coverage, and every
  source-bound occurrence/source/target/arc recovery law;
* the decisive input-domain theorem `exists_complete_selected_path_data_of_global_embedding` and
  the molecular-assembly endpoint `exists_molecular_evidence_of_global_embedding`;
* the actual assembly decode inverse, the canonical finite-transport request inverse, and the
  set-level inverse for the image of the generated request family;
* the concrete `toySourceGraph` fixture: its selected occurrence type has cardinality one, its
  generated data is complete, its documented table has cardinality one, its arc endpoint and
  interior values are exact, and its parametrized arcs agree with the global embedding's arcs.

## Typed example certificates

The typed certificates below take the strongest endpoint assumptions only:

`graph` + one continuous injective global map
`map : C(Realization (selectedSource graph) (selectedTarget graph), EmbeddedReal3)` + an atom
`enumeration`.  No `SelectedGeometry`, no bond-path table, no completeness hypothesis, no arc
family, no local geometric law and no ring/component restriction is an input; every conclusion is
produced from the supplied global embedding by the accepted construction.

## Scope and residual work

These are representation/coverage/exact-recovery results.  Only selected binary interaction kinds
are geometrically realized; every other interaction (multicenter, ionic, metallic, hydrogen-bond,
`.other`, and selected-kind interactions with more than two participants) is retained verbatim in
the source graph and is not geometrically realized.  The realization is conditional on a supplied
global classical embedding; nothing here constructs such an embedding for an arbitrary molecule or
asserts chemical admissibility, descriptor correctness or any full chemistry coverage claim.
Set-level recovery is stated for the image of the generated request family (and for a set of
supplied embeddings), not for an arbitrary preimage set of molecular evidence.
-/

import TetraStereo.KernelOnly
import TetraStereo.OneCenter.OrganicStereoEmbeddedGraphRealization
import TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace TetraStereo.Examples.OrganicStereoStructuralCoverageKernelCertificate

open scoped unitInterval

open TetraStereo.OneCenter
open TetraStereo.OneCenter.JointCoreEncoding
open TetraStereo.OneCenter.OrganicStereoEmbeddedGraphRealization
open TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage

noncomputable section

universe u v

/-! ## Kernel-closure checks: realization gluing, continuity and global/local arc laws -/

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedGraphRealization.glue_continuous
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedGraphRealization.continuous_iff_continuous_comp_glue
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedGraphRealization.continuous_of_continuous_comp_glue
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedGraphRealization.glue_surjective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedGraphRealization.edgePoint_continuous
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedGraphRealization.edgePoint_zero
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedGraphRealization.edgePoint_one
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedGraphRealization.edgePoint_interior
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedGraphRealization.edgePoint_injective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedGraphRealization.edge_eq_of_interior_edgePoint_eq
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedGraphRealization.not_edgePoint_injective_of_selfLoop
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedGraphRealization.edgePoint_eq_vertex_of_sourceEndpointAt?
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedGraphRealization.edgePoint_collision
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedGraphRealization.edgePoint_eq_vertex_iff
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedGraphRealization.edgePoint_eq_iff

/-! ### The supplied global embedding and its derived local laws -/

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedGraphRealization.EmbeddedGraph.arc_zero
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedGraphRealization.EmbeddedGraph.arc_one
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedGraphRealization.EmbeddedGraph.atom_injective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedGraphRealization.EmbeddedGraph.arc_injective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedGraphRealization.EmbeddedGraph.interior_avoids_atoms
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedGraphRealization.EmbeddedGraph.intersects_only_at_common_endpoints
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedGraphRealization.EmbeddedGraph.edge_eq_of_interior_meet
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedGraphRealization.EmbeddedGraph.arc_injective_of_noSelfLoops

/-! ### The concrete single-edge realization in real three-space -/

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedGraphRealization.toyMap_continuous
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedGraphRealization.toyMap_injective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedGraphRealization.toy_source_ne_dst
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedGraphRealization.toy_arc_injective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedGraphRealization.toy_conformation_injective

/-! ## Kernel-closure checks: chemical construction and structural coverage -/

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.selectedParticipants
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.selectedSource_ne_target
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.selectedOccurrence_injective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.exists_selected_of_genuine

/-! ### The constructed path data from derived geometry -/

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.SelectedGeometry.toIndependentBondPathData
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.SelectedGeometry.completeForSourcePairBonds
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.SelectedGeometry.documented_eq_selected_image
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.SelectedGeometry.mem_documented_iff_selected
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.SelectedGeometry.exact_coverage
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.SelectedGeometry.card_documented_eq_card_selected
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.SelectedGeometry.toSourceBound
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.SelectedGeometry.toSourceBound_occurrence
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.SelectedGeometry.toSourceBound_arc
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.sourceBound_exact_coverage

/-! ### The geometry adapter from one global embedding -/

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.embeddedGraphOfMap
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.selectedGeometryOfEmbedding
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.selectedGeometryOfMap
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.selectedDataOfEmbedding
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.selectedDataOfMap
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.selectedDataOfEmbedding_completeForSourcePairBonds
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.selectedDataOfMap_completeForSourcePairBonds
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.exists_complete_selected_path_data_of_global_embedding
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.selectedDataOfEmbedding_exact_coverage
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.selectedDataOfMap_exact_coverage

/-! ### Exact recovery in the accepted source-bound table -/

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.selectedSourceBoundOfEmbedding
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.selectedSourceBoundOfEmbedding_molecule
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.selectedSourceBoundOfEmbedding_interactions
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.selectedSourceBoundOfEmbedding_occurrence
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.selectedSourceBoundOfEmbedding_source_val
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.selectedSourceBoundOfEmbedding_target_val
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.selectedSourceBoundOfEmbedding_recovered_source
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.selectedSourceBoundOfEmbedding_recovered_target
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.selectedSourceBoundOfEmbedding_arc
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.selectedSourceBoundOfEmbedding_exact_coverage

/-! ### Molecular assembly and canonical request inverse -/

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.selectedEvidenceOfEmbedding
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.selectedEvidenceOfMap
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.decode_assemble_selectedEvidenceOfEmbedding
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.decode_canonicalAssemble_selectedEvidenceOfEmbedding
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.decode_canonicalAssemble_selectedEvidenceOfEmbedding_image
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.assemble_stateGraph_selectedEvidenceOfEmbedding
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.assemble_stateConformation_selectedEvidenceOfEmbedding
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.decodedPaths?_assemble_selectedEvidenceOfEmbedding
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.decodedPaths?_canonicalAssemble_selectedEvidenceOfEmbedding
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.exists_molecular_evidence_of_global_embedding

/-! ### Nonempty one-bond toy fixture -/

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.toySelected_card
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.toyConstructedData
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.toyConstructedData_complete
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.toyConstructedData_graph
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.toyConstructedData_documented_card
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.toyConstructedData_arc_zero
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.toyConstructedData_arc_one
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.toyConstructedData_arc_interior
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.toySourceMap_continuous
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.toySourceMap_injective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.toySelected_source
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage.toySelected_target

/-! ## Typed example certificates

Each certificate below is instantiated at the strongest endpoint assumptions: an arbitrary finite
atom-labelled interaction hypergraph, ONE continuous injective global map on the canonical
realization of its selected-bond graph, and an atom enumeration.  No `SelectedGeometry`, no bond
path table, no completeness hypothesis and no local geometric or coverage input appears in any
signature. -/

/-- **Derived local geometric laws from one global map (no geometry input).**

For an arbitrary finite atom-labelled interaction hypergraph and one continuous injective map on
the canonical realization of its selected-bond graph, the packaged embedding's conformation is
injective, every selected arc is injective on the unit interval, the arc endpoints are the
oriented source/target atom positions, arc interiors avoid every atom position, and two distinct
arcs meet only at a common endpoint atom.  `SelectedGeometry` is not supplied: it is the derived
object. -/
theorem globalEmbeddingDerivedLaws_certificate
    {V : Type} [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V)
    (map : C(Realization (selectedSource graph) (selectedTarget graph), EmbeddedReal3))
    (injective : Function.Injective map) :
    Function.Injective (embeddedGraphOfMap graph map injective).conformation ∧
      (∀ edge : SelectedBondIndex graph,
        Function.Injective ((embeddedGraphOfMap graph map injective).arc edge)) ∧
      (∀ edge : SelectedBondIndex graph,
        (embeddedGraphOfMap graph map injective).arc edge 0 =
          (embeddedGraphOfMap graph map injective).conformation (selectedSource graph edge)) ∧
      (∀ edge : SelectedBondIndex graph,
        (embeddedGraphOfMap graph map injective).arc edge 1 =
          (embeddedGraphOfMap graph map injective).conformation (selectedTarget graph edge)) ∧
      (∀ (edge : SelectedBondIndex graph) (t : I), t ≠ 0 → t ≠ 1 → ∀ atom : V,
        (embeddedGraphOfMap graph map injective).arc edge t ≠
          (embeddedGraphOfMap graph map injective).conformation atom) ∧
      (∀ (edge other : SelectedBondIndex graph) (t s : I), edge ≠ other →
        (embeddedGraphOfMap graph map injective).arc edge t =
          (embeddedGraphOfMap graph map injective).arc other s →
        ∃ atom : V,
          sourceEndpointAt? (selectedSource graph) (selectedTarget graph) edge t = some atom ∧
            sourceEndpointAt? (selectedSource graph) (selectedTarget graph) other s =
              some atom) :=
  ⟨(embeddedGraphOfMap graph map injective).atom_injective,
   fun edge =>
     (embeddedGraphOfMap graph map injective).arc_injective edge
       (selectedSource_ne_target graph edge),
   fun edge => (embeddedGraphOfMap graph map injective).arc_zero edge,
   fun edge => (embeddedGraphOfMap graph map injective).arc_one edge,
   fun edge t h0 h1 atom =>
     (embeddedGraphOfMap graph map injective).interior_avoids_atoms edge t h0 h1 atom,
   fun edge other t s hne h =>
     (embeddedGraphOfMap graph map injective).intersects_only_at_common_endpoints
       edge other t s hne h⟩

/-- **Structural coverage certificate from one global map.**

The actual independent bond-path data constructed from one global continuous injective map has
exactly the source graph, exactly the embedding's conformation and parametrized arcs, exactly the
structurally selected oriented endpoints and occurrence indices, and is complete for every
selected binary source pair bond at the given enumeration.  No path table and no completeness
hypothesis is an input. -/
theorem structuralCoverage_certificate
    {V : Type} [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V)
    (map : C(Realization (selectedSource graph) (selectedTarget graph), EmbeddedReal3))
    (injective : Function.Injective map)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (selectedDataOfMap graph map injective).graph = graph ∧
      (selectedDataOfMap graph map injective).conformation =
        (embeddedGraphOfMap graph map injective).conformation ∧
      (∀ edge : SelectedBondIndex graph,
        (selectedDataOfMap graph map injective).arc edge =
          (embeddedGraphOfMap graph map injective).arc edge) ∧
      (∀ edge : SelectedBondIndex graph,
        (selectedDataOfMap graph map injective).source edge = selectedSource graph edge) ∧
      (∀ edge : SelectedBondIndex graph,
        (selectedDataOfMap graph map injective).target edge = selectedTarget graph edge) ∧
      (∀ edge : SelectedBondIndex graph,
        (selectedDataOfMap graph map injective).interactionOccurrence edge =
          selectedOccurrence graph edge) ∧
      (selectedDataOfMap graph map injective).CompleteForSourcePairBonds enumeration := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_,
    selectedDataOfMap_completeForSourcePairBonds graph map injective enumeration⟩
  · simpa only [selectedDataOfMap] using
      selectedDataOfEmbedding_graph graph (embeddedGraphOfMap graph map injective)
  · simpa only [selectedDataOfMap] using
      selectedDataOfEmbedding_conformation graph (embeddedGraphOfMap graph map injective)
  · intro edge
    simpa only [selectedDataOfMap] using
      selectedDataOfEmbedding_arc graph (embeddedGraphOfMap graph map injective) edge
  · intro edge
    simpa only [selectedDataOfMap] using
      selectedDataOfEmbedding_source graph (embeddedGraphOfMap graph map injective) edge
  · intro edge
    simpa only [selectedDataOfMap] using
      selectedDataOfEmbedding_target graph (embeddedGraphOfMap graph map injective) edge
  · intro edge
    simpa only [selectedDataOfMap] using
      selectedDataOfEmbedding_occurrence graph (embeddedGraphOfMap graph map injective) edge

/-- **Source-bound exact recovery certificate (all parameters).**

The accepted `SourceBoundEmbeddedBondPaths` record built from one global embedding retains the
exact encoded source molecule and the whole interaction list in order, recovers every oriented
occurrence index and encoded source/target atom index, recovers the physical source/target atom
labels through the shared atom equivalence, and agrees with the global embedding's parametrized
arc at every edge and every parameter `t`.  Unselected interactions remain in the source; only the
selected occurrence subtype is realized as arcs. -/
theorem sourceBoundRecovery_certificate
    {V : Type} [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V)
    (G : EmbeddedGraph (selectedSource graph) (selectedTarget graph))
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : SelectedBondIndex graph ≃
      Fin (Fintype.card (SelectedBondIndex graph))) :
    (selectedSourceBoundOfEmbedding graph G enumeration edgeEquiv).source.molecule =
        graph.encode enumeration ∧
      (selectedSourceBoundOfEmbedding graph G enumeration edgeEquiv).source.molecule.interactions =
        graph.interactions.map
          (FiniteAtomInteractionHypergraph.encodeInteraction enumeration) ∧
      (∀ edge : SelectedBondIndex graph,
        ((selectedSourceBoundOfEmbedding graph G enumeration edgeEquiv).table.edge
          (edgeEquiv edge)).sourceInteraction.val = selectedOccurrence graph edge) ∧
      (∀ edge : SelectedBondIndex graph,
        ((selectedSourceBoundOfEmbedding graph G enumeration edgeEquiv).table.edge
          (edgeEquiv edge)).source.val = (enumeration (selectedSource graph edge)).val) ∧
      (∀ edge : SelectedBondIndex graph,
        ((selectedSourceBoundOfEmbedding graph G enumeration edgeEquiv).table.edge
          (edgeEquiv edge)).target.val = (enumeration (selectedTarget graph edge)).val) ∧
      (∀ edge : SelectedBondIndex graph,
        (sourceAtomEquiv graph enumeration).symm
          ((selectedSourceBoundOfEmbedding graph G enumeration edgeEquiv).table.edge
            (edgeEquiv edge)).source = selectedSource graph edge) ∧
      (∀ edge : SelectedBondIndex graph,
        (sourceAtomEquiv graph enumeration).symm
          ((selectedSourceBoundOfEmbedding graph G enumeration edgeEquiv).table.edge
            (edgeEquiv edge)).target = selectedTarget graph edge) ∧
      (∀ (edge : SelectedBondIndex graph) (t : I),
        ((selectedSourceBoundOfEmbedding graph G enumeration edgeEquiv).table.edge
          (edgeEquiv edge)).arc t = G.arc edge t) :=
  ⟨selectedSourceBoundOfEmbedding_molecule graph G enumeration edgeEquiv,
   selectedSourceBoundOfEmbedding_interactions graph G enumeration edgeEquiv,
   fun edge =>
     selectedSourceBoundOfEmbedding_occurrence graph G enumeration edgeEquiv edge,
   fun edge =>
     selectedSourceBoundOfEmbedding_source_val graph G enumeration edgeEquiv edge,
   fun edge =>
     selectedSourceBoundOfEmbedding_target_val graph G enumeration edgeEquiv edge,
   fun edge =>
     selectedSourceBoundOfEmbedding_recovered_source graph G enumeration edgeEquiv edge,
   fun edge =>
     selectedSourceBoundOfEmbedding_recovered_target graph G enumeration edgeEquiv edge,
   fun edge t => selectedSourceBoundOfEmbedding_arc graph G enumeration edgeEquiv edge t⟩

/-- **Exact unique coverage certificate from one global map.**

For every genuine selected binary pair bond of the encoded source graph, the accepted source-bound
table produced from one global embedding has a unique realizing selected occurrence, indexed by the
supplied edge equivalence.  The genuine-pair-bond predicate is a property of the encoded source
interaction, not a coverage assumption supplied to the construction. -/
theorem exactCoverage_certificate
    {V : Type} [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V)
    (map : C(Realization (selectedSource graph) (selectedTarget graph), EmbeddedReal3))
    (injective : Function.Injective map)
    (enumeration : V ≃ Fin (Fintype.card V))
    (edgeEquiv : SelectedBondIndex graph ≃
      Fin (Fintype.card (SelectedBondIndex graph)))
    {index : Fin (graph.encode enumeration).interactions.length}
    (genuine : IsGenuinePairBondAt (graph.encode enumeration) index) :
    ∃! edge : SelectedBondIndex graph,
      ((selectedSourceBoundOfEmbedding graph (embeddedGraphOfMap graph map injective)
        enumeration edgeEquiv).table.edge (edgeEquiv edge)).sourceInteraction = index :=
  selectedSourceBoundOfEmbedding_exact_coverage graph
    (embeddedGraphOfMap graph map injective) enumeration edgeEquiv genuine

/-- **Canonical request inverse and generated-image Set inverse certificate.**

The generated molecular-evidence request decodes back exactly after the actual assembly and after
canonical finite transport; the assembled path channel is exactly the generated family; and
decoding the canonically assembled image of any set of supplied embeddings recovers exactly the
generated request image.  Only the image of the generated family is inverted, as stated. -/
theorem canonicalRequestInverse_certificate
    {V : Type} [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V)
    (map : C(Realization (selectedSource graph) (selectedTarget graph), EmbeddedReal3))
    (injective : Function.Injective map)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    OrganicStereoMolecularEvidenceAssembly.decode
        (OrganicStereoMolecularCanonicalTransport.canonicalDecode
          (OrganicStereoMolecularCanonicalTransport.canonicalAssemble enumeration
            (selectedEvidenceOfMap graph map injective))) =
      selectedEvidenceOfMap graph map injective ∧
      OrganicStereoMolecularEvidenceAssembly.decode
          (OrganicStereoMolecularEvidenceAssembly.assemble
            (selectedEvidenceOfMap graph map injective)) =
        selectedEvidenceOfMap graph map injective ∧
      OrganicStereoMolecularEvidenceAssembly.decodedPaths?
          (OrganicStereoMolecularEvidenceAssembly.assemble
            (selectedEvidenceOfMap graph map injective)) =
        some (independentPathFamily (selectedDataOfMap graph map injective)) ∧
      ∀ embeddingSet : Set (EmbeddedGraph (selectedSource graph) (selectedTarget graph)),
        (fun G =>
          OrganicStereoMolecularEvidenceAssembly.decode
            (OrganicStereoMolecularCanonicalTransport.canonicalDecode
              (OrganicStereoMolecularCanonicalTransport.canonicalAssemble enumeration
                (selectedEvidenceOfEmbedding graph G)))) '' embeddingSet =
          selectedEvidenceOfEmbedding graph '' embeddingSet :=
  ⟨by
    simpa only [selectedEvidenceOfMap] using
      decode_canonicalAssemble_selectedEvidenceOfEmbedding graph
        (embeddedGraphOfMap graph map injective) enumeration,
   by
    simpa only [selectedEvidenceOfMap] using
      decode_assemble_selectedEvidenceOfEmbedding graph
        (embeddedGraphOfMap graph map injective),
   by
    simpa only [selectedEvidenceOfMap, selectedDataOfMap] using
      decodedPaths?_assemble_selectedEvidenceOfEmbedding graph
        (embeddedGraphOfMap graph map injective),
   fun embeddingSet =>
     decode_canonicalAssemble_selectedEvidenceOfEmbedding_image graph enumeration embeddingSet⟩

/-- **Molecular-evidence endpoint certificate from one global map.**

One continuous injective global map yields actual `OrganicMolecularEvidence` whose graph is the
exact source graph, whose conformation and path family are the embedding's derived ones, whose
actual assembly has exactly the source graph and the embedding's conformation, whose assembled
path channel is exactly the generated family, and whose canonical assembly decodes back to the
same generated request. -/
theorem molecularEvidence_certificate
    {V : Type} [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V)
    (map : C(Realization (selectedSource graph) (selectedTarget graph), EmbeddedReal3))
    (injective : Function.Injective map)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    ∃ evidence : OrganicStereoMolecularEvidenceAssembly.OrganicMolecularEvidence V,
      evidence.graph = graph ∧
      evidence.conformation = (embeddedGraphOfMap graph map injective).conformation ∧
      evidence.paths? = some (independentPathFamily
        (selectedDataOfMap graph map injective)) ∧
      (OrganicStereoMolecularEvidenceAssembly.assemble evidence).stateGraph = graph ∧
      (OrganicStereoMolecularEvidenceAssembly.assemble evidence).stateConformation =
        (embeddedGraphOfMap graph map injective).conformation ∧
      OrganicStereoMolecularEvidenceAssembly.decodedPaths?
          (OrganicStereoMolecularEvidenceAssembly.assemble evidence) =
        some (independentPathFamily (selectedDataOfMap graph map injective)) ∧
      OrganicStereoMolecularEvidenceAssembly.decode
          (OrganicStereoMolecularCanonicalTransport.canonicalDecode
            (OrganicStereoMolecularCanonicalTransport.canonicalAssemble enumeration
              evidence)) = evidence :=
  exists_molecular_evidence_of_global_embedding graph map injective enumeration

/-- **Nonempty one-bond toy fixture certificate.**

The concrete two-atom source graph has exactly one selected binary occurrence; its generated data
is complete and retains the exact source graph; its documented table has cardinality one; the arc
starts at `0`, ends at the chosen nonzero point, and takes the exact value `t • p` at every
interior parameter; every parametrized arc agrees with the global embedding's arc; and the oriented
source/target endpoints are `false`/`true` on every selected occurrence. -/
theorem toyOneBond_certificate :
    Fintype.card (SelectedBondIndex toySourceGraph) = 1 ∧
      toyConstructedData.graph = toySourceGraph ∧
      toyConstructedData.CompleteForSourcePairBonds (Fintype.equivFin Bool) ∧
      (toyConstructedData.toBondPathTable (Fintype.equivFin Bool)).documented.card = 1 ∧
      (∀ edge : SelectedBondIndex toySourceGraph, toyConstructedData.arc edge 0 = 0) ∧
      (∀ edge : SelectedBondIndex toySourceGraph,
        toyConstructedData.arc edge 1 = toyNonzeroPoint) ∧
      (∀ (edge : SelectedBondIndex toySourceGraph) (t : I), t ≠ 0 → t ≠ 1 →
        toyConstructedData.arc edge t = (t : ℝ) • toyNonzeroPoint) ∧
      (∀ (edge : SelectedBondIndex toySourceGraph) (t : I),
        toyConstructedData.arc edge t = toySourceEmbeddedGraph.arc edge t) ∧
      (∀ edge : SelectedBondIndex toySourceGraph, selectedSource toySourceGraph edge = false) ∧
      (∀ edge : SelectedBondIndex toySourceGraph, selectedTarget toySourceGraph edge = true) :=
  ⟨toySelected_card, toyConstructedData_graph, toyConstructedData_complete,
   toyConstructedData_documented_card,
   fun edge => toyConstructedData_arc_zero edge,
   fun edge => toyConstructedData_arc_one edge,
   fun edge t h0 h1 => toyConstructedData_arc_interior edge t h0 h1,
   fun edge t => by
     show (selectedDataOfEmbedding toySourceGraph toySourceEmbeddedGraph).arc edge t =
       toySourceEmbeddedGraph.arc edge t
     rw [selectedDataOfEmbedding_arc],
   fun edge => toySelected_source edge,
   fun edge => toySelected_target edge⟩

/-- **Toy source-bound all-parameter arc equality.**

For the nonempty one-bond fixture, the accepted source-bound table's parametrized arc agrees with
the concrete global embedding's arc at every selected occurrence and every parameter. -/
theorem toySourceBoundArc_certificate
    (edgeEquiv : SelectedBondIndex toySourceGraph ≃
      Fin (Fintype.card (SelectedBondIndex toySourceGraph)))
    (edge : SelectedBondIndex toySourceGraph) (t : I) :
    ((selectedSourceBoundOfEmbedding toySourceGraph toySourceEmbeddedGraph
        (Fintype.equivFin Bool) edgeEquiv).table.edge (edgeEquiv edge)).arc t =
      toySourceEmbeddedGraph.arc edge t :=
  selectedSourceBoundOfEmbedding_arc toySourceGraph toySourceEmbeddedGraph
    (Fintype.equivFin Bool) edgeEquiv edge t

end

end TetraStereo.Examples.OrganicStereoStructuralCoverageKernelCertificate
