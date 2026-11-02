import TetraStereo.OneCenter.OrganicStereoFiniteGraphMolecularInhabitance
import TetraStereo.OneCenter.OrganicStereoPrescribedPositionGraphEmbedding

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Prescribed molecular path completion

`OrganicStereoPrescribedPositionGraphEmbedding` proves that every finite loopless multigraph,
together with every injective family of prescribed atom positions, allows an `EmbeddedGraph` whose
conformation is exactly that family.  `OrganicStereoEmbeddedMolecularGraphCoverage` (re-exported by
`OrganicStereoFiniteGraphMolecularInhabitance`) turns one supplied global embedding of the canonical
selected-bond realization of a finite atom interaction hypergraph into the actual
`IndependentBondPathData`, its derived `CompleteForSourcePairBonds` proof and the molecular-evidence
assembly.

This module composes the two, with *no supplied embedding and no supplied geometric law*:

* `prescribedData graph position injective` is the actual independent bond-path data of the exact
  source graph at the exact prescribed positions.  Its edge type is the selected occurrence subtype
  `SelectedBondIndex graph`, so parallel bonds between the same two atoms stay distinct; its
  occurrence indices are the structural selected occurrence indices; its arcs start and end at the
  prescribed positions of the structural endpoints; and it is complete for every atom enumeration.
  The endpoint maps are `selectedSource` / `selectedTarget` and the non-loop condition is the
  derived `selectedSource_ne_target`; neither a loop hypothesis nor a geometric hypothesis is an
  input.

* `completeMissingPaths request absent injective` fills a genuinely absent path channel of an
  arbitrary `OrganicMolecularEvidence` request.  Only `paths?` and the two dependent
  graph/conformation compatibility proofs are updated; every other field is copied literally,
  including the optional rational coordinates and their existing `rationalPositions_valid` proof.
  The added family is exactly `independentPathFamily (prescribedData request.graph
  request.conformation injective)`.

* `erasePaths` removes the added channel and `erasePaths_completeMissingPaths` proves that erasing
  the completed request returns the original request, given that the original channel was absent.
  The completed request is *not* equal to the original request: the path channel changed from
  `none` to `some`.  Ordinary decoding therefore returns the completed request, not the original
  absence; absence is recovered only by the explicit erasure.

## Scope

The added arcs are the two-segment polylines of the prescribed-position construction through
private waypoints.  This module asserts nothing about bond lengths, bond angles, knot or link type,
energies, or chemical realizability, and it does not turn any sparse rational or drawing
observation into a total rational coordinate channel.  Unselected interactions (multicenter,
ionic, metallic, hydrogen-bond, `.other`, and selected-kind interactions that are not binary) are
retained verbatim in the source interaction list and are never realized as paths.
-/

namespace TetraStereo.OneCenter
namespace OrganicStereoPrescribedMolecularPathCompletion

open scoped unitInterval

open TetraStereo.OneCenter.JointCoreEncoding
open TetraStereo.OneCenter.OrganicStereoEmbeddedGraphRealization
open TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage
open TetraStereo.OneCenter.OrganicStereoMolecularEvidenceAssembly
open TetraStereo.OneCenter.OrganicStereoMolecularCanonicalTransport
open TetraStereo.OneCenter.OrganicStereoPrescribedPositionGraphEmbedding

noncomputable section

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 1. The prescribed-position embedding of the selected-bond graph -/

/-- The prescribed-position embedding of the canonical selected-bond realization of a finite atom
interaction hypergraph.  The vertex family is exactly the supplied `position`; the non-loop
condition is the derived `selectedSource_ne_target`. -/
def prescribedEmbedding (graph : FiniteAtomInteractionHypergraph V)
    (position : MolecularConformation V) (injective : Function.Injective position) :
    EmbeddedGraph (selectedSource graph) (selectedTarget graph) :=
  prescribedPositionEmbedded (selectedSource graph) (selectedTarget graph)
    (selectedSource_ne_target graph) position injective

/-- The conformation of the prescribed-position embedding is exactly the supplied family. -/
theorem prescribedEmbedding_conformation (graph : FiniteAtomInteractionHypergraph V)
    (position : MolecularConformation V) (injective : Function.Injective position) :
    (prescribedEmbedding graph position injective).conformation = position :=
  conformation_equality (selectedSource graph) (selectedTarget graph)
    (selectedSource_ne_target graph) position injective

/-! ## 2. Actual bond-path data from arbitrary prescribed injective positions -/

/-- **The prescribed bond-path data.**  For an arbitrary finite atom interaction hypergraph and an
arbitrary injective family of prescribed atom positions, the actual independent bond-path data of
the selected-bond realization: the exact source graph, the exact occurrence indices, the structural
oriented endpoints, the derived geometric laws, and the exact prescribed positions.

No embedding, arc family, coverage hypothesis or geometric law is an input. -/
def prescribedData (graph : FiniteAtomInteractionHypergraph V)
    (position : MolecularConformation V) (injective : Function.Injective position) :
    IndependentBondPathData V (SelectedBondIndex graph) :=
  selectedDataOfEmbedding graph (prescribedEmbedding graph position injective)

/-- The constructed data's graph is exactly the source graph. -/
@[simp] theorem prescribedData_graph (graph : FiniteAtomInteractionHypergraph V)
    (position : MolecularConformation V) (injective : Function.Injective position) :
    (prescribedData graph position injective).graph = graph :=
  selectedDataOfEmbedding_graph graph (prescribedEmbedding graph position injective)

/-- The constructed data's conformation is exactly the prescribed atom positions. -/
@[simp] theorem prescribedData_conformation (graph : FiniteAtomInteractionHypergraph V)
    (position : MolecularConformation V) (injective : Function.Injective position) :
    (prescribedData graph position injective).conformation = position :=
  (selectedDataOfEmbedding_conformation graph
      (prescribedEmbedding graph position injective)).trans
    (prescribedEmbedding_conformation graph position injective)

/-- The occurrence index of a constructed edge is its structural selected occurrence index. -/
@[simp] theorem prescribedData_occurrence (graph : FiniteAtomInteractionHypergraph V)
    (position : MolecularConformation V) (injective : Function.Injective position)
    (edge : SelectedBondIndex graph) :
    (prescribedData graph position injective).interactionOccurrence edge =
      selectedOccurrence graph edge :=
  selectedDataOfEmbedding_occurrence graph (prescribedEmbedding graph position injective) edge

/-- The oriented first endpoint of a constructed edge is the structural source participant. -/
@[simp] theorem prescribedData_source (graph : FiniteAtomInteractionHypergraph V)
    (position : MolecularConformation V) (injective : Function.Injective position)
    (edge : SelectedBondIndex graph) :
    (prescribedData graph position injective).source edge = selectedSource graph edge :=
  selectedDataOfEmbedding_source graph (prescribedEmbedding graph position injective) edge

/-- The oriented second endpoint of a constructed edge is the structural target participant. -/
@[simp] theorem prescribedData_target (graph : FiniteAtomInteractionHypergraph V)
    (position : MolecularConformation V) (injective : Function.Injective position)
    (edge : SelectedBondIndex graph) :
    (prescribedData graph position injective).target edge = selectedTarget graph edge :=
  selectedDataOfEmbedding_target graph (prescribedEmbedding graph position injective) edge

/-- The constructed arc of an edge is the prescription's own arc. -/
@[simp] theorem prescribedData_arc (graph : FiniteAtomInteractionHypergraph V)
    (position : MolecularConformation V) (injective : Function.Injective position)
    (edge : SelectedBondIndex graph) :
    (prescribedData graph position injective).arc edge =
      (prescribedEmbedding graph position injective).arc edge :=
  selectedDataOfEmbedding_arc graph (prescribedEmbedding graph position injective) edge

/-- Two selected occurrences are never identified, including two parallel bonds between the same
pair of atoms. -/
theorem prescribedData_occurrence_injective (graph : FiniteAtomInteractionHypergraph V)
    (position : MolecularConformation V) (injective : Function.Injective position) :
    Function.Injective (prescribedData graph position injective).interactionOccurrence :=
  (prescribedData graph position injective).interactionOccurrence_injective

/-- Distinct selected occurrences have distinct occurrence indices. -/
theorem prescribedData_parallel_occurrences_distinct (graph : FiniteAtomInteractionHypergraph V)
    (position : MolecularConformation V) (injective : Function.Injective position)
    {first second : SelectedBondIndex graph} (hne : first ≠ second) :
    (prescribedData graph position injective).interactionOccurrence first ≠
      (prescribedData graph position injective).interactionOccurrence second :=
  fun equal =>
    hne ((prescribedData graph position injective).interactionOccurrence_injective equal)

/-- The two oriented endpoints of every constructed edge are distinct atoms. -/
theorem prescribedData_source_ne_target (graph : FiniteAtomInteractionHypergraph V)
    (position : MolecularConformation V) (injective : Function.Injective position) :
    ∀ edge : SelectedBondIndex graph,
      (prescribedData graph position injective).source edge ≠
        (prescribedData graph position injective).target edge :=
  (prescribedData graph position injective).source_ne_target

/-- The constructed positions are injective, because the supplied positions are. -/
theorem prescribedData_atom_injective (graph : FiniteAtomInteractionHypergraph V)
    (position : MolecularConformation V) (injective : Function.Injective position) :
    Function.Injective (prescribedData graph position injective).conformation :=
  (prescribedData graph position injective).atom_injective

/-- Every constructed arc is injective on the unit interval. -/
theorem prescribedData_arc_injective (graph : FiniteAtomInteractionHypergraph V)
    (position : MolecularConformation V) (injective : Function.Injective position)
    (edge : SelectedBondIndex graph) :
    Function.Injective ((prescribedData graph position injective).arc edge) :=
  (prescribedData graph position injective).arc_injective edge

/-- Participant compatibility at the constructed occurrence index. -/
theorem prescribedData_participants_exact (graph : FiniteAtomInteractionHypergraph V)
    (position : MolecularConformation V) (injective : Function.Injective position)
    (edge : SelectedBondIndex graph) :
    ((prescribedData graph position injective).graph.interactions.get
        ((prescribedData graph position injective).interactionIndex edge)).1 =
      [(prescribedData graph position injective).source edge,
        (prescribedData graph position injective).target edge] :=
  (prescribedData graph position injective).participants_exact edge

/-- Kind compatibility at the constructed occurrence index. -/
theorem prescribedData_kind_selected (graph : FiniteAtomInteractionHypergraph V)
    (position : MolecularConformation V) (injective : Function.Injective position)
    (edge : SelectedBondIndex graph) :
    SemanticInteractionKind.isSelectedPairKind
      ((prescribedData graph position injective).graph.interactions.get
        ((prescribedData graph position injective).interactionIndex edge)).2 = true :=
  (prescribedData graph position injective).kind_selected edge

/-- The start of a constructed arc is the prescribed position of its structural source atom. -/
theorem prescribedData_source_endpoint (graph : FiniteAtomInteractionHypergraph V)
    (position : MolecularConformation V) (injective : Function.Injective position)
    (edge : SelectedBondIndex graph) :
    (prescribedData graph position injective).arc edge 0 =
      position ((prescribedData graph position injective).source edge) := by
  change (selectedDataOfEmbedding graph
      (prescribedEmbedding graph position injective)).arc edge 0 =
    position ((selectedDataOfEmbedding graph
      (prescribedEmbedding graph position injective)).source edge)
  rw [selectedDataOfEmbedding_source_endpoint, selectedDataOfEmbedding_conformation,
    prescribedEmbedding_conformation]

/-- The end of a constructed arc is the prescribed position of its structural target atom. -/
theorem prescribedData_target_endpoint (graph : FiniteAtomInteractionHypergraph V)
    (position : MolecularConformation V) (injective : Function.Injective position)
    (edge : SelectedBondIndex graph) :
    (prescribedData graph position injective).arc edge 1 =
      position ((prescribedData graph position injective).target edge) := by
  change (selectedDataOfEmbedding graph
      (prescribedEmbedding graph position injective)).arc edge 1 =
    position ((selectedDataOfEmbedding graph
      (prescribedEmbedding graph position injective)).target edge)
  rw [selectedDataOfEmbedding_target_endpoint, selectedDataOfEmbedding_conformation,
    prescribedEmbedding_conformation]

/-- Constructed arc interiors avoid every prescribed atom position. -/
theorem prescribedData_interior_avoids_atoms (graph : FiniteAtomInteractionHypergraph V)
    (position : MolecularConformation V) (injective : Function.Injective position)
    (edge : SelectedBondIndex graph) (t : I) (ht0 : t ≠ 0) (ht1 : t ≠ 1) (atom : V) :
    (prescribedData graph position injective).arc edge t ≠ position atom := by
  have h := (prescribedData graph position injective).interior_avoids_atoms
    edge t ht0 ht1 atom
  rwa [prescribedData_conformation] at h

/-- Distinct constructed arcs meet only at a common endpoint atom. -/
theorem prescribedData_intersects_only_at_common_endpoints
    (graph : FiniteAtomInteractionHypergraph V)
    (position : MolecularConformation V) (injective : Function.Injective position)
    (edge other : SelectedBondIndex graph) (t s : I) (hne : edge ≠ other)
    (h : (prescribedData graph position injective).arc edge t =
      (prescribedData graph position injective).arc other s) :
    ∃ atom : V,
      sourceEndpointAt? (prescribedData graph position injective).source
          (prescribedData graph position injective).target edge t = some atom ∧
        sourceEndpointAt? (prescribedData graph position injective).source
          (prescribedData graph position injective).target other s = some atom :=
  (prescribedData graph position injective).intersects_only_at_common_endpoints
    edge other t s hne h

/-- **Derived completeness.**  For every atom enumeration, every selected binary pair bond of the
encoded source graph is documented by the prescribed data.  This is a theorem of the construction,
not a hypothesis. -/
theorem prescribedData_complete (graph : FiniteAtomInteractionHypergraph V)
    (position : MolecularConformation V) (injective : Function.Injective position)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (prescribedData graph position injective).CompleteForSourcePairBonds enumeration :=
  selectedDataOfEmbedding_completeForSourcePairBonds graph
    (prescribedEmbedding graph position injective) enumeration

/-- The documented encoded occurrences are exactly the images of the selected source occurrences,
for every enumeration. -/
theorem prescribedData_documented_eq_selected_image (graph : FiniteAtomInteractionHypergraph V)
    (position : MolecularConformation V) (injective : Function.Injective position)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (prescribedData graph position injective).documented enumeration =
      Finset.univ.image (fun edge : SelectedBondIndex graph =>
        encodedIndex graph enumeration edge.1) :=
  SelectedGeometry.documented_eq_selected_image
    (selectedGeometryOfEmbedding graph (prescribedEmbedding graph position injective))
    enumeration

/-- Exact unique coverage of every genuine selected source pair bond by the constructed complete
table. -/
theorem prescribedData_exact_coverage (graph : FiniteAtomInteractionHypergraph V)
    (position : MolecularConformation V) (injective : Function.Injective position)
    (enumeration : V ≃ Fin (Fintype.card V))
    {index : Fin (graph.encode enumeration).interactions.length}
    (genuine : IsGenuinePairBondAt (graph.encode enumeration) index) :
    ∃! edge : SelectedBondIndex graph,
      ((((selectedGeometryOfEmbedding graph
          (prescribedEmbedding graph position injective)).toCompleteBondPathTable
        enumeration).table.edge edge).sourceInteraction) = index :=
  (selectedGeometryOfEmbedding graph
    (prescribedEmbedding graph position injective)).exact_coverage enumeration genuine

/-- The whole interaction list of the source is retained, in order, including every unselected
higher-arity or non-bond interaction. -/
@[simp] theorem prescribedData_interactions (graph : FiniteAtomInteractionHypergraph V)
    (position : MolecularConformation V) (injective : Function.Injective position) :
    (prescribedData graph position injective).graph.interactions = graph.interactions := rfl

/-- An unselected interaction occurrence (not binary, or not a selected pair kind) is never
realized as a path by the construction. -/
theorem prescribedData_occurrence_unselected_absent
    (graph : FiniteAtomInteractionHypergraph V)
    (position : MolecularConformation V) (injective : Function.Injective position)
    (index : Fin graph.interactions.length)
    (hunselected : ¬ ((graph.interactions.get index).1.length = 2 ∧
      SemanticInteractionKind.isSelectedPairKind (graph.interactions.get index).2 = true))
    (edge : SelectedBondIndex graph) :
    (prescribedData graph position injective).interactionOccurrence edge ≠ index.val := by
  intro equal
  have hedge : edge.1.val = index.val := equal
  have hidx : edge.1 = index := Fin.ext hedge
  subst hidx
  exact hunselected ⟨selectedLength graph edge, selectedKind graph edge⟩

/-- **Headline existence theorem.**  Every finite atom interaction hypergraph and every injective
prescribed position family allow actual independent bond-path data with the exact source graph,
the exact prescribed conformation, the structural occurrence indices and oriented endpoints,
occurrence injectivity, injective positions, and completeness for *every* atom enumeration.  No
supplied embedding, loop hypothesis, coverage hypothesis or geometric law is an input. -/
theorem exists_prescribedData (graph : FiniteAtomInteractionHypergraph V)
    (position : MolecularConformation V) (injective : Function.Injective position) :
    ∃ data : IndependentBondPathData V (SelectedBondIndex graph),
      data.graph = graph ∧
      data.conformation = position ∧
      (∀ edge : SelectedBondIndex graph,
        data.interactionOccurrence edge = selectedOccurrence graph edge) ∧
      (∀ edge : SelectedBondIndex graph, data.source edge = selectedSource graph edge) ∧
      (∀ edge : SelectedBondIndex graph, data.target edge = selectedTarget graph edge) ∧
      Function.Injective data.interactionOccurrence ∧
      Function.Injective data.conformation ∧
      (∀ enumeration : V ≃ Fin (Fintype.card V),
        data.CompleteForSourcePairBonds enumeration) :=
  ⟨prescribedData graph position injective,
    prescribedData_graph graph position injective,
    prescribedData_conformation graph position injective,
    fun edge => prescribedData_occurrence graph position injective edge,
    fun edge => prescribedData_source graph position injective edge,
    fun edge => prescribedData_target graph position injective edge,
    prescribedData_occurrence_injective graph position injective,
    prescribedData_atom_injective graph position injective,
    fun enumeration => prescribedData_complete graph position injective enumeration⟩

/-! ## 3. Completing a genuinely absent path channel -/

/-- **Complete the missing path channel of a request.**

Only the path option and its two dependent graph/conformation compatibility proofs are updated.
Every other field of the request is copied literally: the common graph, the common conformation,
the optional exact rational coordinates together with their existing `rationalPositions_valid`
proof, the optional electronic inventory and its unpaired tie, the optional band record, and every
role/drawing/fragment/convention/cage/residue/frame metadata channel. -/
def completeMissingPaths (request : OrganicMolecularEvidence V)
    (absent : request.paths? = none)
    (injective : Function.Injective request.conformation) :
    OrganicMolecularEvidence V where
  graph := request.graph
  conformation := request.conformation
  rationalPositions? := request.rationalPositions?
  rationalPositions_valid := request.rationalPositions_valid
  electronic? := request.electronic?
  electronic_unpaired := request.electronic_unpaired
  paths? := some (independentPathFamily
    (prescribedData request.graph request.conformation injective))
  paths_graph_eq := by
    intro family present
    have familyEq : family = independentPathFamily
        (prescribedData request.graph request.conformation injective) :=
      (Option.some.inj present).symm
    subst familyEq
    rw [independentPathFamily_graph, prescribedData_graph]
  paths_conformation_eq := by
    intro family present
    have familyEq : family = independentPathFamily
        (prescribedData request.graph request.conformation injective) :=
      (Option.some.inj present).symm
    subst familyEq
    rw [independentPathFamily_conformation, prescribedData_conformation]
  bands? := request.bands?
  bands_graph_eq := request.bands_graph_eq
  bands_conformation_eq := request.bands_conformation_eq
  roles := request.roles
  role_valid := request.role_valid
  diagram? := request.diagram?
  diagramPartial? := request.diagramPartial?
  diagramIncidence := request.diagramIncidence
  diagram_valid := request.diagram_valid
  fragments := request.fragments
  conventions := request.conventions
  cages := request.cages
  residueLedger? := request.residueLedger?
  frames := request.frames

/-- The completed request retains the exact source graph. -/
@[simp] theorem completeMissingPaths_graph (request : OrganicMolecularEvidence V)
    (absent : request.paths? = none)
    (injective : Function.Injective request.conformation) :
    (completeMissingPaths request absent injective).graph = request.graph := rfl

/-- The completed request retains the exact supplied conformation. -/
@[simp] theorem completeMissingPaths_conformation (request : OrganicMolecularEvidence V)
    (absent : request.paths? = none)
    (injective : Function.Injective request.conformation) :
    (completeMissingPaths request absent injective).conformation = request.conformation := rfl

/-- The completed request retains the exact optional rational coordinates. -/
@[simp] theorem completeMissingPaths_rationalPositions? (request : OrganicMolecularEvidence V)
    (absent : request.paths? = none)
    (injective : Function.Injective request.conformation) :
    (completeMissingPaths request absent injective).rationalPositions? =
      request.rationalPositions? := rfl

/-- The completed request retains the exact optional electronic inventory. -/
@[simp] theorem completeMissingPaths_electronic? (request : OrganicMolecularEvidence V)
    (absent : request.paths? = none)
    (injective : Function.Injective request.conformation) :
    (completeMissingPaths request absent injective).electronic? = request.electronic? := rfl

/-- The completed request retains the exact optional band record. -/
@[simp] theorem completeMissingPaths_bands? (request : OrganicMolecularEvidence V)
    (absent : request.paths? = none)
    (injective : Function.Injective request.conformation) :
    (completeMissingPaths request absent injective).bands? = request.bands? := rfl

/-- The completed request retains the ordered role ledger literally. -/
@[simp] theorem completeMissingPaths_roles (request : OrganicMolecularEvidence V)
    (absent : request.paths? = none)
    (injective : Function.Injective request.conformation) :
    (completeMissingPaths request absent injective).roles = request.roles := rfl

/-- The completed request retains the optional drawing source literally. -/
@[simp] theorem completeMissingPaths_diagram? (request : OrganicMolecularEvidence V)
    (absent : request.paths? = none)
    (injective : Function.Injective request.conformation) :
    (completeMissingPaths request absent injective).diagram? = request.diagram? := rfl

/-- The completed request retains the optional sparse drawing-position observations literally.
These are drawing-sidecar coordinates, not the total rational coordinate channel. -/
@[simp] theorem completeMissingPaths_diagramPartial? (request : OrganicMolecularEvidence V)
    (absent : request.paths? = none)
    (injective : Function.Injective request.conformation) :
    (completeMissingPaths request absent injective).diagramPartial? =
      request.diagramPartial? := rfl

/-- The completed request retains the sparse incidence ledger literally. -/
@[simp] theorem completeMissingPaths_diagramIncidence (request : OrganicMolecularEvidence V)
    (absent : request.paths? = none)
    (injective : Function.Injective request.conformation) :
    (completeMissingPaths request absent injective).diagramIncidence =
      request.diagramIncidence := rfl

/-- The completed request retains the ordered fragment metadata literally. -/
@[simp] theorem completeMissingPaths_fragments (request : OrganicMolecularEvidence V)
    (absent : request.paths? = none)
    (injective : Function.Injective request.conformation) :
    (completeMissingPaths request absent injective).fragments = request.fragments := rfl

/-- The completed request retains the ordered convention metadata literally. -/
@[simp] theorem completeMissingPaths_conventions (request : OrganicMolecularEvidence V)
    (absent : request.paths? = none)
    (injective : Function.Injective request.conformation) :
    (completeMissingPaths request absent injective).conventions = request.conventions := rfl

/-- The completed request retains the ordered cage metadata literally. -/
@[simp] theorem completeMissingPaths_cages (request : OrganicMolecularEvidence V)
    (absent : request.paths? = none)
    (injective : Function.Injective request.conformation) :
    (completeMissingPaths request absent injective).cages = request.cages := rfl

/-- The completed request retains the optional residue ledger literally. -/
@[simp] theorem completeMissingPaths_residueLedger? (request : OrganicMolecularEvidence V)
    (absent : request.paths? = none)
    (injective : Function.Injective request.conformation) :
    (completeMissingPaths request absent injective).residueLedger? =
      request.residueLedger? := rfl

/-- The completed request retains the ordered frame metadata literally. -/
@[simp] theorem completeMissingPaths_frames (request : OrganicMolecularEvidence V)
    (absent : request.paths? = none)
    (injective : Function.Injective request.conformation) :
    (completeMissingPaths request absent injective).frames = request.frames := rfl

/-- The path channel of the completed request is exactly the prescribed generated family. -/
@[simp] theorem completeMissingPaths_paths (request : OrganicMolecularEvidence V)
    (absent : request.paths? = none)
    (injective : Function.Injective request.conformation) :
    (completeMissingPaths request absent injective).paths? =
      some (independentPathFamily
        (prescribedData request.graph request.conformation injective)) := rfl

/-- **Literal channel preservation.**  Completing the path channel changes no channel other than
the path option and its dependent compatibility proofs. -/
theorem completeMissingPaths_preserves_channels (request : OrganicMolecularEvidence V)
    (absent : request.paths? = none)
    (injective : Function.Injective request.conformation) :
    (completeMissingPaths request absent injective).graph = request.graph ∧
    (completeMissingPaths request absent injective).conformation = request.conformation ∧
    (completeMissingPaths request absent injective).rationalPositions? =
      request.rationalPositions? ∧
    (completeMissingPaths request absent injective).electronic? = request.electronic? ∧
    (completeMissingPaths request absent injective).bands? = request.bands? ∧
    (completeMissingPaths request absent injective).roles = request.roles ∧
    (completeMissingPaths request absent injective).diagram? = request.diagram? ∧
    (completeMissingPaths request absent injective).diagramPartial? =
      request.diagramPartial? ∧
    (completeMissingPaths request absent injective).diagramIncidence =
      request.diagramIncidence ∧
    (completeMissingPaths request absent injective).fragments = request.fragments ∧
    (completeMissingPaths request absent injective).conventions = request.conventions ∧
    (completeMissingPaths request absent injective).cages = request.cages ∧
    (completeMissingPaths request absent injective).residueLedger? =
      request.residueLedger? ∧
    (completeMissingPaths request absent injective).frames = request.frames :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The existing rational-coordinate proof of the request still certifies exact rational-real
agreement against the (unchanged) conformation of the completed request.  No new rationality
assumption is introduced. -/
theorem completeMissingPaths_rationalPositions_valid (request : OrganicMolecularEvidence V)
    (absent : request.paths? = none)
    (injective : Function.Injective request.conformation)
    {positions : V → CartesianPoint3}
    (present : (completeMissingPaths request absent injective).rationalPositions? =
      some positions) (atom : V) :
    (positions atom).toEuclideanPoint =
      (completeMissingPaths request absent injective).conformation atom :=
  (completeMissingPaths request absent injective).rationalPositions_valid positions present atom

/-- The completed request has a present path channel. -/
theorem completeMissingPaths_paths_ne_none (request : OrganicMolecularEvidence V)
    (absent : request.paths? = none)
    (injective : Function.Injective request.conformation) :
    (completeMissingPaths request absent injective).paths? ≠ none := by
  rw [completeMissingPaths_paths]
  exact Option.some_ne_none _

/-- The completed request is never the original request: a genuinely absent path channel has
become present. -/
theorem completeMissingPaths_ne_self (request : OrganicMolecularEvidence V)
    (absent : request.paths? = none)
    (injective : Function.Injective request.conformation) :
    completeMissingPaths request absent injective ≠ request := by
  intro equal
  have image := congrArg OrganicMolecularEvidence.paths? equal
  rw [completeMissingPaths_paths, absent] at image
  exact Option.some_ne_none _ image

/-! ## 4. Erasing the added path channel -/

/-- Erase the path channel of a request, changing nothing else.  The two path compatibility proofs
become vacuous. -/
def erasePaths (request : OrganicMolecularEvidence V) : OrganicMolecularEvidence V where
  graph := request.graph
  conformation := request.conformation
  rationalPositions? := request.rationalPositions?
  rationalPositions_valid := request.rationalPositions_valid
  electronic? := request.electronic?
  electronic_unpaired := request.electronic_unpaired
  paths? := none
  paths_graph_eq := by
    intro family present
    cases present
  paths_conformation_eq := by
    intro family present
    cases present
  bands? := request.bands?
  bands_graph_eq := request.bands_graph_eq
  bands_conformation_eq := request.bands_conformation_eq
  roles := request.roles
  role_valid := request.role_valid
  diagram? := request.diagram?
  diagramPartial? := request.diagramPartial?
  diagramIncidence := request.diagramIncidence
  diagram_valid := request.diagram_valid
  fragments := request.fragments
  conventions := request.conventions
  cages := request.cages
  residueLedger? := request.residueLedger?
  frames := request.frames

/-- Erasure produces genuine absence of the path channel. -/
@[simp] theorem erasePaths_paths (request : OrganicMolecularEvidence V) :
    (erasePaths request).paths? = none := rfl

/-- Erasure retains the exact source graph. -/
@[simp] theorem erasePaths_graph (request : OrganicMolecularEvidence V) :
    (erasePaths request).graph = request.graph := rfl

/-- Erasure retains the exact conformation. -/
@[simp] theorem erasePaths_conformation (request : OrganicMolecularEvidence V) :
    (erasePaths request).conformation = request.conformation := rfl

/-- Erasure retains the exact optional rational coordinates. -/
@[simp] theorem erasePaths_rationalPositions? (request : OrganicMolecularEvidence V) :
    (erasePaths request).rationalPositions? = request.rationalPositions? := rfl

/-- Erasure retains the optional sparse drawing-position observations. -/
@[simp] theorem erasePaths_diagramPartial? (request : OrganicMolecularEvidence V) :
    (erasePaths request).diagramPartial? = request.diagramPartial? := rfl

/-- **Erasure recovers the original request.**  If the original path channel was absent, erasing
the channel added by `completeMissingPaths` returns the original request exactly.  This is *not*
an equality between the completed and the original request: the completed request differs in its
path channel. -/
theorem erasePaths_completeMissingPaths (request : OrganicMolecularEvidence V)
    (absent : request.paths? = none)
    (injective : Function.Injective request.conformation) :
    erasePaths (completeMissingPaths request absent injective) = request := by
  apply OrganicMolecularEvidence.extEq
  · rfl
  · rfl
  · rfl
  · rfl
  · exact absent.symm
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-! ## 5. Assembly and canonical recovery of the completed request -/

/-- The actual assembly of the completed request retains the exact source graph. -/
theorem assembled_stateGraph_completed (request : OrganicMolecularEvidence V)
    (absent : request.paths? = none)
    (injective : Function.Injective request.conformation) :
    (OrganicStereoMolecularEvidenceAssembly.assemble
        (completeMissingPaths request absent injective)).stateGraph = request.graph := by
  cases hb : request.bands? with
  | none =>
      rw [OrganicStereoMolecularEvidenceAssembly.assemble_graph_of_no_bands _
        (by rw [completeMissingPaths_bands?]; exact hb)]
      rfl
  | some bands =>
      rw [OrganicStereoMolecularEvidenceAssembly.assemble_graph_of_bands _ bands
        (by rw [completeMissingPaths_bands?]; exact hb)]
      exact request.bands_graph_eq bands hb

/-- The actual assembly of the completed request retains the exact conformation. -/
theorem assembled_stateConformation_completed (request : OrganicMolecularEvidence V)
    (absent : request.paths? = none)
    (injective : Function.Injective request.conformation) :
    (OrganicStereoMolecularEvidenceAssembly.assemble
        (completeMissingPaths request absent injective)).stateConformation =
      request.conformation := by
  cases hb : request.bands? with
  | none =>
      rw [OrganicStereoMolecularEvidenceAssembly.assemble_conformation_of_no_bands _
        (by rw [completeMissingPaths_bands?]; exact hb)]
      rfl
  | some bands =>
      rw [OrganicStereoMolecularEvidenceAssembly.assemble_conformation_of_bands _ bands
        (by rw [completeMissingPaths_bands?]; exact hb)]
      exact request.bands_conformation_eq bands hb

/-- The actual assembly of the completed request retains the exact rational coordinate channel. -/
theorem assembled_stateRationalPositions?_completed (request : OrganicMolecularEvidence V)
    (absent : request.paths? = none)
    (injective : Function.Injective request.conformation) :
    (OrganicStereoMolecularEvidenceAssembly.assemble
        (completeMissingPaths request absent injective)).stateRationalPositions? =
      request.rationalPositions? :=
  (OrganicStereoMolecularEvidenceAssembly.assemble_annotation_projections
    (completeMissingPaths request absent injective)).1

/-- **Exact generated path recovery through the actual assembly.**  Decoding the assembled
completed request returns exactly the prescribed generated family. -/
theorem decodedPaths?_assemble_completed (request : OrganicMolecularEvidence V)
    (absent : request.paths? = none)
    (injective : Function.Injective request.conformation) :
    OrganicStereoMolecularEvidenceAssembly.decodedPaths?
        (OrganicStereoMolecularEvidenceAssembly.assemble
          (completeMissingPaths request absent injective)) =
      some (independentPathFamily
        (prescribedData request.graph request.conformation injective)) := by
  rw [OrganicStereoMolecularEvidenceAssembly.assemble_paths?, completeMissingPaths_paths]

/-- The ordinary decoder sees a present path channel: the original absence is not recovered by
decoding. -/
theorem decodedPaths?_assemble_completed_ne_none (request : OrganicMolecularEvidence V)
    (absent : request.paths? = none)
    (injective : Function.Injective request.conformation) :
    OrganicStereoMolecularEvidenceAssembly.decodedPaths?
        (OrganicStereoMolecularEvidenceAssembly.assemble
          (completeMissingPaths request absent injective)) ≠ none := by
  rw [decodedPaths?_assemble_completed]
  exact Option.some_ne_none _

/-- The decoded family carries exactly the prescribed data. -/
theorem decodedPaths?_assemble_completed_data (request : OrganicMolecularEvidence V)
    (absent : request.paths? = none)
    (injective : Function.Injective request.conformation) :
    ∃ paths : IndependentBondPathData V (SelectedBondIndex request.graph),
      OrganicStereoMolecularEvidenceAssembly.decodedPaths?
          (OrganicStereoMolecularEvidenceAssembly.assemble
            (completeMissingPaths request absent injective)) =
        some (independentPathFamily paths) ∧
        paths = prescribedData request.graph request.conformation injective :=
  ⟨prescribedData request.graph request.conformation injective,
    decodedPaths?_assemble_completed request absent injective, rfl⟩

/-- **Decoding the completed request.**  The actual assembly decoder recovers the completed
request exactly, including the new path channel and every retained channel. -/
theorem decode_assemble_completed (request : OrganicMolecularEvidence V)
    (absent : request.paths? = none)
    (injective : Function.Injective request.conformation) :
    OrganicStereoMolecularEvidenceAssembly.decode
        (OrganicStereoMolecularEvidenceAssembly.assemble
          (completeMissingPaths request absent injective)) =
      completeMissingPaths request absent injective :=
  OrganicStereoMolecularEvidenceAssembly.decode_assemble _

/-- **Canonical exact generated path recovery.**  Canonical finite transport followed by the
ordinary decoder also returns exactly the prescribed generated family. -/
theorem decodedPaths?_canonicalAssemble_completed (request : OrganicMolecularEvidence V)
    (absent : request.paths? = none)
    (injective : Function.Injective request.conformation)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    OrganicStereoMolecularEvidenceAssembly.decodedPaths?
        (OrganicStereoMolecularCanonicalTransport.canonicalDecode
          (OrganicStereoMolecularCanonicalTransport.canonicalAssemble enumeration
            (completeMissingPaths request absent injective))) =
      some (independentPathFamily
        (prescribedData request.graph request.conformation injective)) := by
  rw [OrganicStereoMolecularCanonicalTransport.decodedPaths?_canonicalAssemble,
    completeMissingPaths_paths]

/-- **Canonical decoding of the completed request.**  The canonical assembly decodes back to
exactly the completed request. -/
theorem decode_canonicalAssemble_completed (request : OrganicMolecularEvidence V)
    (absent : request.paths? = none)
    (injective : Function.Injective request.conformation)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    OrganicStereoMolecularEvidenceAssembly.decode
        (OrganicStereoMolecularCanonicalTransport.canonicalDecode
          (OrganicStereoMolecularCanonicalTransport.canonicalAssemble enumeration
            (completeMissingPaths request absent injective))) =
      completeMissingPaths request absent injective :=
  OrganicStereoMolecularCanonicalTransport.decode_canonicalAssemble enumeration _

/-- The packaging `independentPathFamily` is injective on the underlying data at a fixed finite
edge index. -/
theorem independentPathFamily_data_eq {E : Type} [Fintype E]
    {first second : IndependentBondPathData V E}
    (equal : independentPathFamily first = independentPathFamily second) : first = second := by
  change (⟨E, ‹Fintype E›, first⟩ : IndependentPathFamily V) =
    ⟨E, ‹Fintype E›, second⟩ at equal
  cases equal
  rfl

/-- **Complete selected binary bond coverage of the decoded completed request.**  Every family
decoded from the assembled completed request is complete for every atom enumeration. -/
theorem completed_decoded_complete (request : OrganicMolecularEvidence V)
    (absent : request.paths? = none)
    (injective : Function.Injective request.conformation)
    (enumeration : V ≃ Fin (Fintype.card V))
    {paths : IndependentBondPathData V (SelectedBondIndex request.graph)}
    (present : OrganicStereoMolecularEvidenceAssembly.decodedPaths?
        (OrganicStereoMolecularEvidenceAssembly.assemble
          (completeMissingPaths request absent injective)) =
      some (independentPathFamily paths)) :
    paths.CompleteForSourcePairBonds enumeration := by
  have someEq : some (independentPathFamily paths) =
      some (independentPathFamily
        (prescribedData request.graph request.conformation injective)) := by
    rw [← present, decodedPaths?_assemble_completed]
  have pathsEq : paths =
      prescribedData request.graph request.conformation injective :=
    independentPathFamily_data_eq (Option.some.inj someEq)
  subst pathsEq
  exact prescribedData_complete request.graph request.conformation injective enumeration

/-- The documented encoded occurrences of the completed request's family are exactly the images of
the selected source occurrences. -/
theorem completed_decoded_documented (request : OrganicMolecularEvidence V)
    (absent : request.paths? = none)
    (injective : Function.Injective request.conformation)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    (prescribedData request.graph request.conformation injective).documented enumeration =
      Finset.univ.image (fun edge : SelectedBondIndex request.graph =>
        encodedIndex request.graph enumeration edge.1) :=
  prescribedData_documented_eq_selected_image request.graph request.conformation injective
    enumeration

/-! ## 6. Fixtures

The fixtures use the coplanar four-atom family of the prescribed-position embedding module, with
two parallel selected bonds and one unselected ternary interaction. -/

/-- Four atoms: two parallel selected binary bonds `0–1`, one selected binary bond `2–3`, and one
unselected ternary multicenter interaction `0,1,2`.  The two parallel occurrences are distinct list
entries, and the ternary interaction is not a selected binary pair. -/
def fixtureGraph : FiniteAtomInteractionHypergraph (Fin 4) where
  atomData := fun _ => fixtureAtom
  interactions :=
    [([0, 1], SemanticInteractionKind.unspecifiedCovalent),
     ([0, 1], SemanticInteractionKind.unspecifiedCovalent),
     ([2, 3], SemanticInteractionKind.unspecifiedCovalent),
     ([0, 1, 2], SemanticInteractionKind.multicenter 4)]
  arity_ge_two := by
    intro edge member
    simp at member
    rcases member with rfl | rfl | rfl | rfl <;> decide
  participants_nodup := by
    intro edge member
    simp at member
    rcases member with rfl | rfl | rfl | rfl <;> decide

/-- The first occurrence of the parallel `0–1` bond. -/
def fixtureLeft : SelectedBondIndex fixtureGraph :=
  ⟨⟨0, by decide⟩, by decide, by decide⟩

/-- The second occurrence of the parallel `0–1` bond. -/
def fixtureRight : SelectedBondIndex fixtureGraph :=
  ⟨⟨1, by decide⟩, by decide, by decide⟩

/-- The two parallel occurrences are distinct edges. -/
theorem fixtureLeft_ne_fixtureRight : fixtureLeft ≠ fixtureRight := by
  intro equal
  have values := congrArg (fun edge : SelectedBondIndex fixtureGraph => edge.1.val) equal
  exact Nat.zero_ne_one values

/-- The prescribed data of the coplanar fixture at the given coplanar injective positions. -/
def fixtureData : IndependentBondPathData (Fin 4) (SelectedBondIndex fixtureGraph) :=
  prescribedData fixtureGraph coplanarPosition coplanarPosition_injective

/-- The fixture data's graph is the fixture graph exactly. -/
theorem fixtureData_graph : fixtureData.graph = fixtureGraph :=
  prescribedData_graph fixtureGraph coplanarPosition coplanarPosition_injective

/-- The fixture data's conformation is exactly the prescribed coplanar family. -/
theorem fixtureData_conformation : fixtureData.conformation = coplanarPosition :=
  prescribedData_conformation fixtureGraph coplanarPosition coplanarPosition_injective

/-- The fixture data is complete for every atom enumeration. -/
theorem fixtureData_complete (enumeration : Fin 4 ≃ Fin (Fintype.card (Fin 4))) :
    fixtureData.CompleteForSourcePairBonds enumeration :=
  prescribedData_complete fixtureGraph coplanarPosition coplanarPosition_injective enumeration

/-- The two parallel occurrences receive distinct occurrence indices. -/
theorem fixtureData_parallel_occurrences_distinct :
    fixtureData.interactionOccurrence fixtureLeft ≠
      fixtureData.interactionOccurrence fixtureRight :=
  prescribedData_parallel_occurrences_distinct fixtureGraph coplanarPosition
    coplanarPosition_injective fixtureLeft_ne_fixtureRight

/-- The two parallel occurrences share both oriented endpoints. -/
theorem fixtureData_parallel_endpoints :
    fixtureData.source fixtureLeft = fixtureData.source fixtureRight ∧
      fixtureData.target fixtureLeft = fixtureData.target fixtureRight :=
  ⟨prescribedData_source fixtureGraph coplanarPosition coplanarPosition_injective _,
    prescribedData_target fixtureGraph coplanarPosition coplanarPosition_injective _⟩

/-- The unselected ternary interaction is retained verbatim in the fixture data's source list. -/
theorem fixtureData_unselected_preserved :
    ([0, 1, 2], SemanticInteractionKind.multicenter 4) ∈ fixtureData.graph.interactions := by
  rw [fixtureData_graph]
  simp [fixtureGraph]

/-- The ternary interaction occurrence is never realized as a path. -/
theorem fixtureData_unselected_not_realized (edge : SelectedBondIndex fixtureGraph) :
    fixtureData.interactionOccurrence edge ≠ 3 :=
  prescribedData_occurrence_unselected_absent fixtureGraph coplanarPosition
    coplanarPosition_injective ⟨3, by decide⟩ (by decide) edge

/-- The fixture's documented occurrences are exactly the selected occurrence images. -/
theorem fixtureData_documented_eq_selected_image
    (enumeration : Fin 4 ≃ Fin (Fintype.card (Fin 4))) :
    fixtureData.documented enumeration =
      Finset.univ.image (fun edge : SelectedBondIndex fixtureGraph =>
        encodedIndex fixtureGraph enumeration edge.1) :=
  prescribedData_documented_eq_selected_image fixtureGraph coplanarPosition
    coplanarPosition_injective enumeration

/-! ### Empty fixture -/

/-- The single atom of the interaction-free fixture sits at the origin. -/
def emptyFixturePosition : MolecularConformation (Fin 1) := fun _ => 0

/-- The interaction-free fixture's position family is injective. -/
theorem emptyFixturePosition_injective : Function.Injective emptyFixturePosition := by
  intro first second _
  exact Subsingleton.elim first second

/-- **Empty case.**  The prescribed data of the interaction-free fixture is complete for every
atom enumeration; there are no selected occurrences to realize. -/
theorem emptyFixture_complete (enumeration : Fin 1 ≃ Fin (Fintype.card (Fin 1))) :
    (prescribedData OrganicStereoEmbeddedMolecularGraphCoverage.fixtureGraph
        emptyFixturePosition emptyFixturePosition_injective).CompleteForSourcePairBonds
      enumeration :=
  prescribedData_complete OrganicStereoEmbeddedMolecularGraphCoverage.fixtureGraph
    emptyFixturePosition emptyFixturePosition_injective enumeration

/-! ### A request with non-default optional channels -/

/-- Exact rational coordinates of the coplanar four-atom family. -/
def fixtureRationalCoplanar : Fin 4 → CartesianPoint3 :=
  fun atom => ⟨(atom : ℚ), (atom : ℚ) ^ 2, 0⟩

/-- The rational coordinates are exactly the prescribed real coplanar points. -/
theorem fixtureRationalCoplanar_valid (atom : Fin 4) :
    (fixtureRationalCoplanar atom).toEuclideanPoint = coplanarPosition atom := by
  apply WithLp.ofLp_injective
  funext coordinate
  fin_cases coordinate <;>
    simp [CartesianPoint3.toEuclideanPoint, coplanarPosition, fixtureRationalCoplanar]

/-- Sparse drawing observations: one atom has a coordinate, the others do not. -/
def fixturePartialPositions : SourcePartialPositions (Fin 4) where
  positions := fun atom => if atom = 0 then some ⟨1 / 2, 3 / 2⟩ else none

/-- A request with a genuinely absent path channel and non-default optional channels: exact
rational coordinates with their agreement proof, and sparse drawing positions. -/
def fixtureRequest : OrganicMolecularEvidence (Fin 4) where
  graph := fixtureGraph
  conformation := coplanarPosition
  rationalPositions? := some fixtureRationalCoplanar
  rationalPositions_valid := by
    intro positions present atom
    have positionsEq : positions = fixtureRationalCoplanar :=
      (Option.some.inj present).symm
    subst positionsEq
    exact fixtureRationalCoplanar_valid atom
  electronic? := none
  electronic_unpaired := by
    intro evidence present
    cases present
  paths? := none
  paths_graph_eq := by
    intro family present
    cases present
  paths_conformation_eq := by
    intro family present
    cases present
  bands? := none
  bands_graph_eq := by
    intro bands present
    cases present
  bands_conformation_eq := by
    intro bands present
    cases present
  roles := []
  role_valid := by
    intro annotation member
    simp at member
  diagram? := none
  diagramPartial? := some fixturePartialPositions
  diagramIncidence := []
  diagram_valid := by
    intro row member
    simp at member
  fragments := []
  conventions := []
  cages := []
  residueLedger? := none
  frames := []

/-- The fixture request has a genuinely absent path channel. -/
theorem fixtureRequest_paths_absent : fixtureRequest.paths? = none := rfl

/-- The completed fixture request. -/
def fixtureCompleted : OrganicMolecularEvidence (Fin 4) :=
  completeMissingPaths fixtureRequest fixtureRequest_paths_absent coplanarPosition_injective

/-- The completed fixture retains the exact source graph. -/
theorem fixtureCompleted_graph : fixtureCompleted.graph = fixtureGraph := rfl

/-- The completed fixture retains the exact coplanar conformation. -/
theorem fixtureCompleted_conformation : fixtureCompleted.conformation = coplanarPosition := rfl

/-- The completed fixture retains the rational coordinate channel exactly. -/
theorem fixtureCompleted_rationalPositions :
    fixtureCompleted.rationalPositions? = some fixtureRationalCoplanar := rfl

/-- The completed fixture retains the sparse drawing observations exactly. -/
theorem fixtureCompleted_diagramPartial :
    fixtureCompleted.diagramPartial? = some fixturePartialPositions := rfl

/-- The completed fixture retains the absence of the electronic channel. -/
theorem fixtureCompleted_electronic : fixtureCompleted.electronic? = none := rfl

/-- The completed fixture's path channel is exactly the prescribed generated family. -/
theorem fixtureCompleted_paths :
    fixtureCompleted.paths? = some (independentPathFamily fixtureData) := rfl

/-- Erasing the completed fixture's path channel returns the original request exactly. -/
theorem fixtureCompleted_erase : erasePaths fixtureCompleted = fixtureRequest :=
  erasePaths_completeMissingPaths fixtureRequest fixtureRequest_paths_absent
    coplanarPosition_injective

/-- The completed fixture is not the original request. -/
theorem fixtureCompleted_ne_request : fixtureCompleted ≠ fixtureRequest :=
  completeMissingPaths_ne_self fixtureRequest fixtureRequest_paths_absent
    coplanarPosition_injective

/-- The actual assembly of the completed fixture retains the exact source graph. -/
theorem fixtureCompleted_assembled_graph :
    (OrganicStereoMolecularEvidenceAssembly.assemble fixtureCompleted).stateGraph =
      fixtureGraph :=
  assembled_stateGraph_completed fixtureRequest fixtureRequest_paths_absent
    coplanarPosition_injective

/-- The actual assembly of the completed fixture retains the exact coplanar conformation. -/
theorem fixtureCompleted_assembled_conformation :
    (OrganicStereoMolecularEvidenceAssembly.assemble fixtureCompleted).stateConformation =
      coplanarPosition :=
  assembled_stateConformation_completed fixtureRequest fixtureRequest_paths_absent
    coplanarPosition_injective

/-- The actual assembly of the completed fixture retains the rational coordinate channel. -/
theorem fixtureCompleted_assembled_rational :
    (OrganicStereoMolecularEvidenceAssembly.assemble fixtureCompleted).stateRationalPositions? =
      some fixtureRationalCoplanar :=
  assembled_stateRationalPositions?_completed fixtureRequest fixtureRequest_paths_absent
    coplanarPosition_injective

/-- The ordinary decoder returns exactly the prescribed generated family for the fixture. -/
theorem fixtureCompleted_decodedPaths :
    OrganicStereoMolecularEvidenceAssembly.decodedPaths?
        (OrganicStereoMolecularEvidenceAssembly.assemble fixtureCompleted) =
      some (independentPathFamily fixtureData) :=
  decodedPaths?_assemble_completed fixtureRequest fixtureRequest_paths_absent
    coplanarPosition_injective

/-- The decoded fixture family is complete for every atom enumeration. -/
theorem fixtureCompleted_decoded_complete
    (enumeration : Fin 4 ≃ Fin (Fintype.card (Fin 4))) :
    fixtureData.CompleteForSourcePairBonds enumeration :=
  completed_decoded_complete fixtureRequest fixtureRequest_paths_absent
    coplanarPosition_injective enumeration
    (fixtureCompleted_decodedPaths)

/-- Canonical finite transport also returns exactly the prescribed generated family. -/
theorem fixtureCompleted_canonical_decodedPaths
    (enumeration : Fin 4 ≃ Fin (Fintype.card (Fin 4))) :
    OrganicStereoMolecularEvidenceAssembly.decodedPaths?
        (OrganicStereoMolecularCanonicalTransport.canonicalDecode
          (OrganicStereoMolecularCanonicalTransport.canonicalAssemble
            enumeration fixtureCompleted)) =
      some (independentPathFamily fixtureData) :=
  decodedPaths?_canonicalAssemble_completed fixtureRequest fixtureRequest_paths_absent
    coplanarPosition_injective enumeration

/-! ## Kernel-level assertions -/

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPrescribedMolecularPathCompletion.prescribedEmbedding
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPrescribedMolecularPathCompletion.prescribedData
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPrescribedMolecularPathCompletion.prescribedData_complete
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPrescribedMolecularPathCompletion.prescribedData_occurrence_unselected_absent
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPrescribedMolecularPathCompletion.exists_prescribedData
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPrescribedMolecularPathCompletion.completeMissingPaths
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPrescribedMolecularPathCompletion.completeMissingPaths_paths
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPrescribedMolecularPathCompletion.completeMissingPaths_preserves_channels
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPrescribedMolecularPathCompletion.erasePaths
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPrescribedMolecularPathCompletion.erasePaths_completeMissingPaths
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPrescribedMolecularPathCompletion.decodedPaths?_assemble_completed
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPrescribedMolecularPathCompletion.decode_assemble_completed
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPrescribedMolecularPathCompletion.decodedPaths?_canonicalAssemble_completed
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPrescribedMolecularPathCompletion.completed_decoded_complete
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPrescribedMolecularPathCompletion.fixtureData_complete
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPrescribedMolecularPathCompletion.fixtureData_parallel_occurrences_distinct
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPrescribedMolecularPathCompletion.fixtureData_unselected_preserved
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPrescribedMolecularPathCompletion.fixtureCompleted_rationalPositions
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPrescribedMolecularPathCompletion.fixtureCompleted_erase

end

end OrganicStereoPrescribedMolecularPathCompletion
end TetraStereo.OneCenter
