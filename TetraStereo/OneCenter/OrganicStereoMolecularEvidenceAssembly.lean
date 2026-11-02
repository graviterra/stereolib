import TetraStereo.OneCenter.OrganicStereoElectronicStateAttachment
import TetraStereo.OneCenter.OrganicStereoPathStateAttachment
import TetraStereo.OneCenter.OrganicStereoBandStateAttachment
import TetraStereo.OneCenter.OrganicStereoFiniteClassicalDescription

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

namespace TetraStereo.OneCenter

namespace OrganicStereoMolecularEvidenceAssembly

open scoped unitInterval

open OrganicStereoElectronicSites
open OrganicStereoIndependentElectronicEncoding
open OrganicStereoIndependentBandEncoding
open OrganicStereoElectronicDescriptionIngress
open OrganicStereoElectronicStateAttachment
open OrganicStereoBandStateAttachment
open JointCoreEncoding

noncomputable section

variable {V : Type} [DecidableEq V] [Fintype V]

/-!
# Independent molecular evidence assembled into the whole-state description

This module supplies the missing *independent molecular-evidence ingress* into the existing
`WholeState` finite classical description, and proves that the ingress is a genuine left inverse on
the entire independently supplied request.

The independent request `OrganicMolecularEvidence V` contains only supplied physical/source data
and raw metadata:

* one finite atom-labelled interaction hypergraph and one real conformation shared by every
  channel;
* optional exact rational coordinates together with their pointwise agreement with the shared
  conformation;
* optional counted electronic inventory together with a complete per-identity evidence
  assignment and the single source-semantic unpaired-electron tie to the graph;
* an optional packaged finite bond-path family (a finite edge index type, its `Fintype` instance,
  the existing `IndependentBondPathData`, and the exact graph/conformation equalities);
* an optional `IndependentBandAttachment` together with its exact graph/conformation equalities;
* ordered role, drawing, incidence, fragment, convention, cage and frame metadata and an optional
  residue ledger.

The construction is compositional, not a new schema:

1. `baseState` builds a `WholeState V (Fin 0) (Fin 0)` at the supplied graph, conformation and
   metadata, with genuinely absent electronic/path/band channels.
2. `attachElectronicOption` applies the existing electronic ingress operation when an inventory
   was supplied and leaves the state untouched otherwise.
3. `attachIndependentBands` replaces the (empty) band family by the supplied one, changing the
   band index type to the supplied finite type.
4. `attachIndependentBondPathData` replaces the (empty) path family by the supplied one.

The result is an `OrganicMolecularRepresentation V`: the effective finite edge/band index types and
their instances, the assembled whole state, and two explicit presence tags.  The only proof-valued
extra datum is the `PathGeometryValid` evidence required by the public `toIndependentBondPathData`
decoder; it contains no data and is proof-irrelevant.  No copy of the original request, path input,
band input or electronic source is stored.

`decode` reads the assembled state and the two tags through the public projection adapters
`toIndependentBondPathData`, `toIndependentBandAttachment` and the electronic channel, and
`decode_assemble` proves `decode (assemble request) = request` for **every** request, with all
proposition-valued fields identified by proof irrelevance.  Consequently `assemble` is injective and
recovers the image of an arbitrary set of requests, so correlations between all channels are
retained.
-/

/-! ## Graph-independent packaged input data -/

/-- A supplied electronic inventory and its complete per-identity evidence assignment.  The type
does not mention the interaction graph: the single unpaired-electron tie to the graph is kept as a
separate proposition-valued field of the request, so the present/absent data type is independent of
the other channels. -/
structure IndependentElectronicEvidence (V : Type) [DecidableEq V] [Fintype V] where
  /-- The supplied per-atom-label counts. -/
  siteCounts : IndependentSiteCounts V
  /-- Complete evidence at every counted owner/kind/slot identity. -/
  assignment : IndependentSiteAssignment siteCounts ReferenceGeometryEvidence

/-- Build the existing independent electronic *source* from the graph-independent evidence and the
request's own graph tie.  The tie proof is the supplied physical compatibility, not an assumption. -/
def IndependentElectronicEvidence.toSiteSource (evidence : IndependentElectronicEvidence V)
    (graph : FiniteAtomInteractionHypergraph V)
    (tied : ∀ owner, (evidence.siteCounts.counts owner).unpairedElectronPositions =
      (graph.atomData owner).unpairedElectrons) :
    IndependentElectronicSiteSource graph where
  siteCounts := evidence.siteCounts
  unpaired_tied := tied

/-- A packaged finite bond-path family: the supplied finite edge index type, its finiteness
instance, and the existing independent bond-path data.  The graph/conformation compatibility
equalities are kept in the request, so this package is independent of those fields. -/
structure IndependentPathFamily (V : Type) [DecidableEq V] [Fintype V] where
  /-- The supplied finite path/edge index type. -/
  edgeIndex : Type
  /-- Finiteness of the supplied edge index type. -/
  fintypeEdgeIndex : Fintype edgeIndex
  /-- The existing independent bond-path data at that index type. -/
  data : @IndependentBondPathData V _ _ edgeIndex fintypeEdgeIndex

/-- The graph of a packaged path family, read through the family's own finiteness instance. -/
def IndependentPathFamily.graph (family : IndependentPathFamily V) :
    FiniteAtomInteractionHypergraph V :=
  letI : Fintype family.edgeIndex := family.fintypeEdgeIndex
  family.data.graph

/-- The conformation of a packaged path family, read through the family's own finiteness
instance. -/
def IndependentPathFamily.conformation (family : IndependentPathFamily V) :
    MolecularConformation V :=
  letI : Fintype family.edgeIndex := family.fintypeEdgeIndex
  family.data.conformation

/-- A packaged path family is determined by its `IndependentBondPathData` component. -/
theorem IndependentPathFamily.eq_of_data_eq {family : IndependentPathFamily V}
    {data : @IndependentBondPathData V _ _ family.edgeIndex family.fintypeEdgeIndex}
    (data_eq : family.data = data) :
    (⟨family.edgeIndex, family.fintypeEdgeIndex, data⟩ : IndependentPathFamily V) = family := by
  cases family with
  | mk edgeIndex fintypeEdgeIndex familyData =>
    dsimp only at data_eq
    rw [← data_eq]

/-! ## The independent molecular-evidence request -/

/-- The complete independently supplied molecular evidence.  Every field is either supplied
physical/source data or raw metadata; the proposition-valued fields are exactly the physical
compatibilities the later operations need.  In particular, absent optional channels impose no
geometric non-degeneracy or source-realization obligation. -/
structure OrganicMolecularEvidence (V : Type) [DecidableEq V] [Fintype V] where
  /-- The common finite atom-labelled interaction hypergraph. -/
  graph : FiniteAtomInteractionHypergraph V
  /-- The single shared real conformation. -/
  conformation : MolecularConformation V
  /-- Optional exact rational coordinates.  Genuine absence is `none`. -/
  rationalPositions? : Option (V → CartesianPoint3) := none
  /-- Every supplied rational point is exactly the shared real point. -/
  rationalPositions_valid : ∀ positions, rationalPositions? = some positions →
    ∀ atom, (positions atom).toEuclideanPoint = conformation atom
  /-- Optional counted electronic inventory and its complete assignment. -/
  electronic? : Option (IndependentElectronicEvidence V) := none
  /-- The supplied inventory's unpaired-electron count is the graph atom data, pointwise. -/
  electronic_unpaired : ∀ evidence, electronic? = some evidence → ∀ owner,
    (evidence.siteCounts.counts owner).unpairedElectronPositions =
      (graph.atomData owner).unpairedElectrons
  /-- Optional packaged finite bond-path family.  `none` is genuine absence, not an empty family. -/
  paths? : Option (IndependentPathFamily V) := none
  /-- The supplied path record's graph is exactly the common graph. -/
  paths_graph_eq : ∀ family, paths? = some family → family.graph = graph
  /-- The supplied path record's conformation is exactly the shared conformation. -/
  paths_conformation_eq : ∀ family, paths? = some family → family.conformation = conformation
  /-- Optional independent band attachment. -/
  bands? : Option (IndependentBandAttachment V) := none
  /-- The supplied band record's graph is exactly the common graph. -/
  bands_graph_eq : ∀ bands, bands? = some bands → bands.graph = graph
  /-- The supplied band record's conformation is exactly the shared conformation. -/
  bands_conformation_eq : ∀ bands, bands? = some bands → bands.conformation = conformation
  /-- Ordered role ledger. -/
  roles : List (RoleAnnotation V) := []
  /-- Every role annotation names an actual compatible source interaction occurrence. -/
  role_valid : ∀ annotation ∈ roles,
    ∃ bound : annotation.interactionIndex < graph.interactions.length,
      Compatible graph ⟨annotation.interactionIndex, bound⟩ annotation.role
  /-- Optional drawing data. -/
  diagram? : Option (OrganicDiagramSource V) := none
  /-- Optional sparse per-atom drawing coordinates. -/
  diagramPartial? : Option (SourcePartialPositions V) := none
  /-- Sparse raw incidence ledger. -/
  diagramIncidence : List DiagramIncidenceRow := []
  /-- Every incidence row is backed by actual drawing and source membership. -/
  diagram_valid : ∀ row ∈ diagramIncidence,
    ∃ source : OrganicDiagramSource V,
      diagram? = some source ∧
        ∃ bondBound : row.bondIndex < source.bonds.length,
          ∃ interactionBound : row.interactionIndex < graph.interactions.length,
            (source.bonds.get ⟨row.bondIndex, bondBound⟩).source ∈
                (graph.interactions.get ⟨row.interactionIndex, interactionBound⟩).1 ∧
              (source.bonds.get ⟨row.bondIndex, bondBound⟩).target ∈
                (graph.interactions.get ⟨row.interactionIndex, interactionBound⟩).1
  /-- Ordered fragment metadata. -/
  fragments : List (FragmentAnnotation V) := []
  /-- Ordered drawing-convention metadata. -/
  conventions : ConventionChannel V := []
  /-- Ordered cage metadata. -/
  cages : List (NumberedCageAnnotation V) := []
  /-- Optional residue metadata. -/
  residueLedger? : Option (ResidueLedgerChannel V) := none
  /-- Ordered frame metadata. -/
  frames : List (FrameAnnotation V) := []

/-- Extensionality for independent molecular evidence.  All data field types are independent of
the other data fields by construction; the proposition-valued physical-compatibility fields are
identified by proof irrelevance once the data agree. -/
theorem OrganicMolecularEvidence.extEq {first second : OrganicMolecularEvidence V}
    (graph : first.graph = second.graph)
    (conformation : first.conformation = second.conformation)
    (rationalPositions : first.rationalPositions? = second.rationalPositions?)
    (electronic : first.electronic? = second.electronic?)
    (paths : first.paths? = second.paths?)
    (bands : first.bands? = second.bands?)
    (roles : first.roles = second.roles)
    (diagram : first.diagram? = second.diagram?)
    (diagramPartial : first.diagramPartial? = second.diagramPartial?)
    (diagramIncidence : first.diagramIncidence = second.diagramIncidence)
    (fragments : first.fragments = second.fragments)
    (conventions : first.conventions = second.conventions)
    (cages : first.cages = second.cages)
    (residueLedger : first.residueLedger? = second.residueLedger?)
    (frames : first.frames = second.frames) :
    first = second := by
  obtain ⟨graph₁, conformation₁, rational₁, rationalValid₁, electronic₁, unpaired₁,
    paths₁, pathsGraph₁, pathsConformation₁, bands₁, bandsGraph₁, bandsConformation₁,
    roles₁, roleValid₁, diagram₁, diagramPartial₁, incidence₁, diagramValid₁,
    fragments₁, conventions₁, cages₁, residue₁, frames₁⟩ := first
  obtain ⟨graph₂, conformation₂, rational₂, rationalValid₂, electronic₂, unpaired₂,
    paths₂, pathsGraph₂, pathsConformation₂, bands₂, bandsGraph₂, bandsConformation₂,
    roles₂, roleValid₂, diagram₂, diagramPartial₂, incidence₂, diagramValid₂,
    fragments₂, conventions₂, cages₂, residue₂, frames₂⟩ := second
  dsimp only at graph
  dsimp only at conformation
  dsimp only at rationalPositions
  dsimp only at electronic
  dsimp only at paths
  dsimp only at bands
  dsimp only at roles
  dsimp only at diagram
  dsimp only at diagramPartial
  dsimp only at diagramIncidence
  dsimp only at fragments
  dsimp only at conventions
  dsimp only at cages
  dsimp only at residueLedger
  dsimp only at frames
  cases graph
  cases conformation
  cases rationalPositions
  cases electronic
  cases paths
  cases bands
  cases roles
  cases diagram
  cases diagramPartial
  cases diagramIncidence
  cases fragments
  cases conventions
  cases cages
  cases residueLedger
  cases frames
  have rationalValid : rationalValid₁ = rationalValid₂ := by
    funext positions present atom
    exact Subsingleton.elim _ _
  have unpaired : unpaired₁ = unpaired₂ := by
    funext evidence present owner
    exact Subsingleton.elim _ _
  have pathsGraph : pathsGraph₁ = pathsGraph₂ := by
    funext family present
    exact Subsingleton.elim _ _
  have pathsConformation : pathsConformation₁ = pathsConformation₂ := by
    funext family present
    exact Subsingleton.elim _ _
  have bandsGraph : bandsGraph₁ = bandsGraph₂ := by
    funext bands present
    exact Subsingleton.elim _ _
  have bandsConformation : bandsConformation₁ = bandsConformation₂ := by
    funext bands present
    exact Subsingleton.elim _ _
  have roleValid : roleValid₁ = roleValid₂ := by
    funext annotation member
    exact Subsingleton.elim _ _
  have diagramValid : diagramValid₁ = diagramValid₂ := by
    funext row member
    exact Subsingleton.elim _ _
  cases rationalValid
  cases unpaired
  cases pathsGraph
  cases pathsConformation
  cases bandsGraph
  cases bandsConformation
  cases roleValid
  cases diagramValid
  rfl

/-! ## The assembled representation -/

/-- The constructed representation of a request.  The effective finite edge and band index types
and their finiteness instances are recorded explicitly, together with the assembled whole state.
`pathPresent`/`bandPresent` are the explicit presence tags which distinguish a supplied empty family
from genuine absence.  `pathGeometryValid` is the only extra datum: a proof-only geometric witness
required by the public path decoder. -/
structure OrganicMolecularRepresentation (V : Type) [DecidableEq V] [Fintype V] where
  /-- Presence tag for the bond-path channel. -/
  pathPresent : Bool
  /-- The effective finite path/index type.  For absent paths this is the canonical empty type. -/
  edgeIndex : Type
  /-- Finiteness of the effective path index type. -/
  fintypeEdgeIndex : Fintype edgeIndex
  /-- Presence tag for the band channel. -/
  bandPresent : Bool
  /-- The effective finite band index type.  For absent bands this is the canonical empty type. -/
  bandIndex : Type
  /-- Finiteness of the effective band index type. -/
  fintypeBandIndex : Fintype bandIndex
  /-- The assembled correlated whole state at the effective index types. -/
  state : @WholeState V edgeIndex bandIndex _ _ fintypeEdgeIndex fintypeBandIndex
  /-- Proof-only geometric non-degeneracy needed to read the supplied path family back through the
  public `toIndependentBondPathData` adapter.  It is vacuous when no paths were supplied. -/
  pathGeometryValid : pathPresent = true → PathGeometryValid state

/-- Package the components of an assembled representation. -/
def representation
    (pathPresent : Bool) (edgeIndex : Type) (fintypeEdgeIndex : Fintype edgeIndex)
    (bandPresent : Bool) (bandIndex : Type) (fintypeBandIndex : Fintype bandIndex)
    (state : @WholeState V edgeIndex bandIndex _ _ fintypeEdgeIndex fintypeBandIndex)
    (valid : pathPresent = true → PathGeometryValid state) :
    OrganicMolecularRepresentation V where
  pathPresent := pathPresent
  edgeIndex := edgeIndex
  fintypeEdgeIndex := fintypeEdgeIndex
  bandPresent := bandPresent
  bandIndex := bandIndex
  fintypeBandIndex := fintypeBandIndex
  state := state
  pathGeometryValid := valid

/-- The evidence read from a whole state through its present channel.  Absent stays absent. -/
def stateElectronicEvidence? {E B : Type} [Fintype E] [Fintype B]
    (state : WholeState V E B) : Option (IndependentElectronicEvidence V) :=
  match state.electronic? with
  | none => none
  | some channel => some ⟨channel.counts, channel.toSiteAssignment⟩

/-! ## Reading the assembled state at its own effective index types

The whole-state projections need the finiteness instances of the effective index types.  These
accessors supply the representation's own instances explicitly, so later statements about the
assembled state need no ambient type-class assumptions. -/

/-- The assembled graph. -/
@[simp] def OrganicMolecularRepresentation.stateGraph
    (representation : OrganicMolecularRepresentation V) :
    FiniteAtomInteractionHypergraph V :=
  letI : Fintype representation.edgeIndex := representation.fintypeEdgeIndex
  letI : Fintype representation.bandIndex := representation.fintypeBandIndex
  representation.state.graph

/-- The assembled conformation. -/
@[simp] def OrganicMolecularRepresentation.stateConformation
    (representation : OrganicMolecularRepresentation V) :
    MolecularConformation V :=
  letI : Fintype representation.edgeIndex := representation.fintypeEdgeIndex
  letI : Fintype representation.bandIndex := representation.fintypeBandIndex
  representation.state.conformation

/-- The assembled optional rational coordinates. -/
@[simp] def OrganicMolecularRepresentation.stateRationalPositions?
    (representation : OrganicMolecularRepresentation V) :
    Option (V → CartesianPoint3) :=
  letI : Fintype representation.edgeIndex := representation.fintypeEdgeIndex
  letI : Fintype representation.bandIndex := representation.fintypeBandIndex
  representation.state.rationalPositions?

/-- The assembled electronic evidence option. -/
@[simp] def OrganicMolecularRepresentation.stateElectronicEvidence
    (representation : OrganicMolecularRepresentation V) :
    Option (IndependentElectronicEvidence V) :=
  letI : Fintype representation.edgeIndex := representation.fintypeEdgeIndex
  letI : Fintype representation.bandIndex := representation.fintypeBandIndex
  TetraStereo.OneCenter.OrganicStereoMolecularEvidenceAssembly.stateElectronicEvidence?
    representation.state

/-- The assembled role ledger. -/
@[simp] def OrganicMolecularRepresentation.stateRoles
    (representation : OrganicMolecularRepresentation V) :
    List (RoleAnnotation V) :=
  letI : Fintype representation.edgeIndex := representation.fintypeEdgeIndex
  letI : Fintype representation.bandIndex := representation.fintypeBandIndex
  representation.state.roles

/-- The assembled drawing source. -/
@[simp] def OrganicMolecularRepresentation.stateDiagram?
    (representation : OrganicMolecularRepresentation V) :
    Option (OrganicDiagramSource V) :=
  letI : Fintype representation.edgeIndex := representation.fintypeEdgeIndex
  letI : Fintype representation.bandIndex := representation.fintypeBandIndex
  representation.state.diagram?

/-- The assembled partial drawing positions. -/
@[simp] def OrganicMolecularRepresentation.stateDiagramPartial?
    (representation : OrganicMolecularRepresentation V) :
    Option (SourcePartialPositions V) :=
  letI : Fintype representation.edgeIndex := representation.fintypeEdgeIndex
  letI : Fintype representation.bandIndex := representation.fintypeBandIndex
  representation.state.diagramPartial?

/-- The assembled sparse incidence ledger. -/
@[simp] def OrganicMolecularRepresentation.stateDiagramIncidence
    (representation : OrganicMolecularRepresentation V) :
    List DiagramIncidenceRow :=
  letI : Fintype representation.edgeIndex := representation.fintypeEdgeIndex
  letI : Fintype representation.bandIndex := representation.fintypeBandIndex
  representation.state.diagramIncidence

/-- The assembled fragment metadata. -/
@[simp] def OrganicMolecularRepresentation.stateFragments
    (representation : OrganicMolecularRepresentation V) :
    List (FragmentAnnotation V) :=
  letI : Fintype representation.edgeIndex := representation.fintypeEdgeIndex
  letI : Fintype representation.bandIndex := representation.fintypeBandIndex
  representation.state.fragments

/-- The assembled convention channel. -/
@[simp] def OrganicMolecularRepresentation.stateConventions
    (representation : OrganicMolecularRepresentation V) :
    ConventionChannel V :=
  letI : Fintype representation.edgeIndex := representation.fintypeEdgeIndex
  letI : Fintype representation.bandIndex := representation.fintypeBandIndex
  representation.state.conventions

/-- The assembled cage metadata. -/
@[simp] def OrganicMolecularRepresentation.stateCages
    (representation : OrganicMolecularRepresentation V) :
    List (NumberedCageAnnotation V) :=
  letI : Fintype representation.edgeIndex := representation.fintypeEdgeIndex
  letI : Fintype representation.bandIndex := representation.fintypeBandIndex
  representation.state.cages

/-- The assembled residue ledger. -/
@[simp] def OrganicMolecularRepresentation.stateResidueLedger?
    (representation : OrganicMolecularRepresentation V) :
    Option (ResidueLedgerChannel V) :=
  letI : Fintype representation.edgeIndex := representation.fintypeEdgeIndex
  letI : Fintype representation.bandIndex := representation.fintypeBandIndex
  representation.state.residueLedger?

/-- The assembled frame metadata. -/
@[simp] def OrganicMolecularRepresentation.stateFrames
    (representation : OrganicMolecularRepresentation V) :
    List (FrameAnnotation V) :=
  letI : Fintype representation.edgeIndex := representation.fintypeEdgeIndex
  letI : Fintype representation.bandIndex := representation.fintypeBandIndex
  representation.state.frames

/-! ## The base state with Fin 0 paths and bands -/

/-- The base `WholeState V (Fin 0) (Fin 0)` containing exactly the request's graph, conformation and
metadata, with genuinely absent electronic inventory, paths and bands.  The optional data remain
absent; the validity fields are the request's own physical evidence. -/
def baseState (request : OrganicMolecularEvidence V) : WholeState V (Fin 0) (Fin 0) where
  graph := request.graph
  electronic? := none
  electronic_unpaired := by
    intro channel present
    cases present
  conformation := request.conformation
  rationalPositions? := request.rationalPositions?
  rationalPositions_valid := request.rationalPositions_valid
  roles := request.roles
  role_valid := request.role_valid
  paths := fun edge => Fin.elim0 edge
  path_valid := fun edge => Fin.elim0 edge
  path_source_endpoint := fun edge => Fin.elim0 edge
  path_target_endpoint := fun edge => Fin.elim0 edge
  bandFamily := fun band => Fin.elim0 band
  band_agreement := fun band => Fin.elim0 band
  diagram? := request.diagram?
  diagramPartial? := request.diagramPartial?
  diagramIncidence := request.diagramIncidence
  diagram_valid := request.diagram_valid
  fragments := request.fragments
  conventions := request.conventions
  cages := request.cages
  residueLedger? := request.residueLedger?
  frames := request.frames

@[simp] theorem baseState_graph (request : OrganicMolecularEvidence V) :
    (baseState request).graph = request.graph := rfl

@[simp] theorem baseState_conformation (request : OrganicMolecularEvidence V) :
    (baseState request).conformation = request.conformation := rfl

@[simp] theorem baseState_rationalPositions? (request : OrganicMolecularEvidence V) :
    (baseState request).rationalPositions? = request.rationalPositions? := rfl

@[simp] theorem baseState_roles (request : OrganicMolecularEvidence V) :
    (baseState request).roles = request.roles := rfl

@[simp] theorem baseState_diagram? (request : OrganicMolecularEvidence V) :
    (baseState request).diagram? = request.diagram? := rfl

@[simp] theorem baseState_diagramPartial? (request : OrganicMolecularEvidence V) :
    (baseState request).diagramPartial? = request.diagramPartial? := rfl

@[simp] theorem baseState_diagramIncidence (request : OrganicMolecularEvidence V) :
    (baseState request).diagramIncidence = request.diagramIncidence := rfl

@[simp] theorem baseState_fragments (request : OrganicMolecularEvidence V) :
    (baseState request).fragments = request.fragments := rfl

@[simp] theorem baseState_conventions (request : OrganicMolecularEvidence V) :
    (baseState request).conventions = request.conventions := rfl

@[simp] theorem baseState_cages (request : OrganicMolecularEvidence V) :
    (baseState request).cages = request.cages := rfl

@[simp] theorem baseState_residueLedger? (request : OrganicMolecularEvidence V) :
    (baseState request).residueLedger? = request.residueLedger? := rfl

@[simp] theorem baseState_frames (request : OrganicMolecularEvidence V) :
    (baseState request).frames = request.frames := rfl

@[simp] theorem baseState_electronic? (request : OrganicMolecularEvidence V) :
    (baseState request).electronic? = none := rfl

/-! ## Electronic ingress composition -/

/-- Apply the existing electronic attachment when the request supplies an inventory, and leave the
state untouched otherwise.  The supplied source is reconstructed from the graph-independent
evidence and the request's own unpaired tie; nothing else is assumed. -/
def attachElectronicOption (request : OrganicMolecularEvidence V) {E B : Type}
    [Fintype E] [Fintype B] (state : WholeState V E B)
    (graph_eq : state.graph = request.graph) : WholeState V E B :=
  match h : request.electronic? with
  | none => state
  | some evidence =>
      attachElectronic state
        (evidence.toSiteSource state.graph (by
          intro owner
          rw [graph_eq]
          exact request.electronic_unpaired evidence h owner))
        evidence.assignment

@[simp] theorem attachElectronicOption_graph {E B : Type} [Fintype E] [Fintype B]
    (request : OrganicMolecularEvidence V) (state : WholeState V E B)
    (graph_eq : state.graph = request.graph) :
    (attachElectronicOption request state graph_eq).graph = state.graph := by
  unfold attachElectronicOption
  split <;> rfl

@[simp] theorem attachElectronicOption_conformation {E B : Type} [Fintype E] [Fintype B]
    (request : OrganicMolecularEvidence V) (state : WholeState V E B)
    (graph_eq : state.graph = request.graph) :
    (attachElectronicOption request state graph_eq).conformation = state.conformation := by
  unfold attachElectronicOption
  split <;> rfl

@[simp] theorem attachElectronicOption_rationalPositions? {E B : Type} [Fintype E] [Fintype B]
    (request : OrganicMolecularEvidence V) (state : WholeState V E B)
    (graph_eq : state.graph = request.graph) :
    (attachElectronicOption request state graph_eq).rationalPositions? =
      state.rationalPositions? := by
  unfold attachElectronicOption
  split <;> rfl

@[simp] theorem attachElectronicOption_roles {E B : Type} [Fintype E] [Fintype B]
    (request : OrganicMolecularEvidence V) (state : WholeState V E B)
    (graph_eq : state.graph = request.graph) :
    (attachElectronicOption request state graph_eq).roles = state.roles := by
  unfold attachElectronicOption
  split <;> rfl

@[simp] theorem attachElectronicOption_paths {E B : Type} [Fintype E] [Fintype B]
    (request : OrganicMolecularEvidence V) (state : WholeState V E B)
    (graph_eq : state.graph = request.graph) :
    (attachElectronicOption request state graph_eq).paths = state.paths := by
  unfold attachElectronicOption
  split <;> rfl

@[simp] theorem attachElectronicOption_bandFamily {E B : Type} [Fintype E] [Fintype B]
    (request : OrganicMolecularEvidence V) (state : WholeState V E B)
    (graph_eq : state.graph = request.graph) :
    (attachElectronicOption request state graph_eq).bandFamily = state.bandFamily := by
  unfold attachElectronicOption
  split <;> rfl

@[simp] theorem attachElectronicOption_diagram? {E B : Type} [Fintype E] [Fintype B]
    (request : OrganicMolecularEvidence V) (state : WholeState V E B)
    (graph_eq : state.graph = request.graph) :
    (attachElectronicOption request state graph_eq).diagram? = state.diagram? := by
  unfold attachElectronicOption
  split <;> rfl

@[simp] theorem attachElectronicOption_diagramPartial? {E B : Type} [Fintype E] [Fintype B]
    (request : OrganicMolecularEvidence V) (state : WholeState V E B)
    (graph_eq : state.graph = request.graph) :
    (attachElectronicOption request state graph_eq).diagramPartial? = state.diagramPartial? := by
  unfold attachElectronicOption
  split <;> rfl

@[simp] theorem attachElectronicOption_diagramIncidence {E B : Type} [Fintype E] [Fintype B]
    (request : OrganicMolecularEvidence V) (state : WholeState V E B)
    (graph_eq : state.graph = request.graph) :
    (attachElectronicOption request state graph_eq).diagramIncidence =
      state.diagramIncidence := by
  unfold attachElectronicOption
  split <;> rfl

@[simp] theorem attachElectronicOption_fragments {E B : Type} [Fintype E] [Fintype B]
    (request : OrganicMolecularEvidence V) (state : WholeState V E B)
    (graph_eq : state.graph = request.graph) :
    (attachElectronicOption request state graph_eq).fragments = state.fragments := by
  unfold attachElectronicOption
  split <;> rfl

@[simp] theorem attachElectronicOption_conventions {E B : Type} [Fintype E] [Fintype B]
    (request : OrganicMolecularEvidence V) (state : WholeState V E B)
    (graph_eq : state.graph = request.graph) :
    (attachElectronicOption request state graph_eq).conventions = state.conventions := by
  unfold attachElectronicOption
  split <;> rfl

@[simp] theorem attachElectronicOption_cages {E B : Type} [Fintype E] [Fintype B]
    (request : OrganicMolecularEvidence V) (state : WholeState V E B)
    (graph_eq : state.graph = request.graph) :
    (attachElectronicOption request state graph_eq).cages = state.cages := by
  unfold attachElectronicOption
  split <;> rfl

@[simp] theorem attachElectronicOption_residueLedger? {E B : Type} [Fintype E] [Fintype B]
    (request : OrganicMolecularEvidence V) (state : WholeState V E B)
    (graph_eq : state.graph = request.graph) :
    (attachElectronicOption request state graph_eq).residueLedger? =
      state.residueLedger? := by
  unfold attachElectronicOption
  split <;> rfl

@[simp] theorem attachElectronicOption_frames {E B : Type} [Fintype E] [Fintype B]
    (request : OrganicMolecularEvidence V) (state : WholeState V E B)
    (graph_eq : state.graph = request.graph) :
    (attachElectronicOption request state graph_eq).frames = state.frames := by
  unfold attachElectronicOption
  split <;> rfl

/-- The electronic state built from the canonical base state has exactly the request's graph. -/
theorem attachElectronicOption_base_graph (request : OrganicMolecularEvidence V) :
    (attachElectronicOption request (baseState request) rfl).graph = request.graph :=
  (attachElectronicOption_graph request (baseState request) rfl).trans (baseState_graph request)

/-- The electronic state built from the canonical base state has exactly the request's
conformation. -/
theorem attachElectronicOption_base_conformation (request : OrganicMolecularEvidence V) :
    (attachElectronicOption request (baseState request) rfl).conformation =
      request.conformation :=
  (attachElectronicOption_conformation request (baseState request) rfl).trans
    (baseState_conformation request)

/-! ## Recovery of the supplied electronic evidence -/

/-- The ingress channel's counts are exactly the supplied counts and its complete assignment is
exactly the supplied assignment, packaged as graph-independent evidence. -/
theorem ingressEvidence_eq {graph : FiniteAtomInteractionHypergraph V}
    (source : IndependentElectronicSiteSource graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence) :
    (⟨(ingressChannel source assignment).counts,
        (ingressChannel source assignment).toSiteAssignment⟩ :
        IndependentElectronicEvidence V) =
      ⟨source.siteCounts, assignment⟩ := by
  have h : (ingressChannel source assignment).toSiteAssignment = assignment := by
    apply IndependentSiteAssignment.ext
    intro identity
    exact ingressEvidence_get source assignment identity.owner identity.kind identity.slot _
  rw [h]
  rfl

/-- The unpaired-electron tie of the evidence read from a state is the state's own tie. -/
theorem stateElectronicEvidence?_unpaired {E B : Type} [Fintype E] [Fintype B]
    (state : WholeState V E B) :
    ∀ evidence, stateElectronicEvidence? state = some evidence → ∀ owner,
      (evidence.siteCounts.counts owner).unpairedElectronPositions =
        (state.graph.atomData owner).unpairedElectrons := by
  intro evidence present owner
  cases h : state.electronic? with
  | none =>
      simp [stateElectronicEvidence?, h] at present
  | some channel =>
      simp only [stateElectronicEvidence?, h] at present
      cases present
      exact state.electronic_unpaired channel h owner

/-- The evidence read from a state after the electronic attachment is exactly the supplied
assignment, packaged with the supplied source's counts. -/
theorem stateElectronicEvidence?_attachElectronic {E B : Type} [Fintype E] [Fintype B]
    (state : WholeState V E B) (source : IndependentElectronicSiteSource state.graph)
    (assignment : IndependentSiteAssignment source.siteCounts ReferenceGeometryEvidence) :
    stateElectronicEvidence? (attachElectronic state source assignment) =
      some ⟨source.siteCounts, assignment⟩ := by
  simp only [stateElectronicEvidence?, attachElectronic_electronic?]
  exact congrArg some (ingressEvidence_eq source assignment)

/-- Attaching the optional electronic inventory and then reading the evidence back returns exactly
the supplied evidence option. -/
theorem stateElectronicEvidence?_attachElectronicOption {E B : Type} [Fintype E] [Fintype B]
    (request : OrganicMolecularEvidence V) (state : WholeState V E B)
    (graph_eq : state.graph = request.graph) (hstate : state.electronic? = none) :
    stateElectronicEvidence? (attachElectronicOption request state graph_eq) =
      request.electronic? := by
  unfold attachElectronicOption
  split
  · rename_i he
    simp only [stateElectronicEvidence?, hstate]
    exact he.symm
  · rename_i evidence he
    rw [stateElectronicEvidence?_attachElectronic]
    have hsrc : ∀ tied : ∀ owner,
        (evidence.siteCounts.counts owner).unpairedElectronPositions =
          (state.graph.atomData owner).unpairedElectrons,
        (⟨(evidence.toSiteSource state.graph tied).siteCounts,
          evidence.assignment⟩ : IndependentElectronicEvidence V) = evidence := by
      intro tied
      rfl
    exact (congrArg some (hsrc _)).trans he.symm

/-- Reading the electronic evidence through further band attachments is unchanged: those
operations only copy the electronic channel. -/
@[simp] theorem stateElectronicEvidence?_attachIndependentBands
    {E B : Type} [Fintype E] [Fintype B]
    (state : WholeState V E B) (input : IndependentBandAttachment V)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    letI : Fintype input.bandIndex := input.fintypeBandIndex
    stateElectronicEvidence? (attachIndependentBands state input graph_eq conformation_eq) =
      stateElectronicEvidence? state := by
  letI : Fintype input.bandIndex := input.fintypeBandIndex
  rfl

@[simp] theorem stateElectronicEvidence?_attachIndependentBondPathData
    {E NewE B : Type} [Fintype E] [Fintype NewE] [Fintype B]
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    stateElectronicEvidence? (attachIndependentBondPathData state input graph_eq conformation_eq) =
      stateElectronicEvidence? state := rfl

/-! ## The public band adapter after path replacement -/

/-- The public band extractor is untouched by replacing the path channel. -/
@[simp] theorem toIndependentBandAttachment_attachIndependentBondPathData
    {E NewE B : Type} [Fintype E] [Fintype NewE] [Fintype B]
    (state : WholeState V E B) (input : IndependentBondPathData V NewE)
    (graph_eq : input.graph = state.graph)
    (conformation_eq : input.conformation = state.conformation) :
    toIndependentBandAttachment
        (attachIndependentBondPathData state input graph_eq conformation_eq) =
      toIndependentBandAttachment state := rfl

/-! ## The four concrete assembly branches -/

/-- Assembly with no electronic-unrelated optional physical channel: no paths and no bands. -/
def assembleBase (request : OrganicMolecularEvidence V) : OrganicMolecularRepresentation V :=
  representation false (Fin 0) inferInstance false (Fin 0) inferInstance
    (attachElectronicOption request (baseState request) rfl)
    (fun h => by cases h)

/-- Assembly with a supplied path family and no bands. -/
def assemblePath (request : OrganicMolecularEvidence V) (family : IndependentPathFamily V)
    (hp : request.paths? = some family) : OrganicMolecularRepresentation V :=
  letI : Fintype family.edgeIndex := family.fintypeEdgeIndex
  let electronicState := attachElectronicOption request (baseState request) rfl
  let graph_eq : family.data.graph = electronicState.graph :=
    (show family.data.graph = request.graph from by
      rw [show family.data.graph = family.graph from rfl]
      exact request.paths_graph_eq family hp).trans
      (attachElectronicOption_base_graph request).symm
  let conformation_eq : family.data.conformation = electronicState.conformation :=
    (show family.data.conformation = request.conformation from by
      rw [show family.data.conformation = family.conformation from rfl]
      exact request.paths_conformation_eq family hp).trans
      (attachElectronicOption_base_conformation request).symm
  let state := attachIndependentBondPathData electronicState family.data graph_eq conformation_eq
  representation true family.edgeIndex family.fintypeEdgeIndex false (Fin 0) inferInstance state
    (fun _ => pathGeometryValid_attachIndependentBondPathData electronicState family.data graph_eq
      conformation_eq)

/-- Assembly with a supplied band attachment and no paths. -/
def assembleBands (request : OrganicMolecularEvidence V) (bands : IndependentBandAttachment V)
    (hb : request.bands? = some bands) : OrganicMolecularRepresentation V :=
  letI : Fintype bands.bandIndex := bands.fintypeBandIndex
  let electronicState := attachElectronicOption request (baseState request) rfl
  let graph_eq : bands.graph = electronicState.graph :=
    (request.bands_graph_eq bands hb).trans (attachElectronicOption_base_graph request).symm
  let conformation_eq : bands.conformation = electronicState.conformation :=
    (request.bands_conformation_eq bands hb).trans
      (attachElectronicOption_base_conformation request).symm
  let state := attachIndependentBands electronicState bands graph_eq conformation_eq
  representation false (Fin 0) inferInstance true bands.bandIndex bands.fintypeBandIndex state
    (fun h => by cases h)

/-- Assembly with both a supplied band attachment and a supplied path family. -/
def assembleBandsPath (request : OrganicMolecularEvidence V) (bands : IndependentBandAttachment V)
    (family : IndependentPathFamily V) (hb : request.bands? = some bands)
    (hp : request.paths? = some family) : OrganicMolecularRepresentation V :=
  letI : Fintype bands.bandIndex := bands.fintypeBandIndex
  letI : Fintype family.edgeIndex := family.fintypeEdgeIndex
  let electronicState := attachElectronicOption request (baseState request) rfl
  let bandGraph_eq : bands.graph = electronicState.graph :=
    (request.bands_graph_eq bands hb).trans (attachElectronicOption_base_graph request).symm
  let bandConformation_eq : bands.conformation = electronicState.conformation :=
    (request.bands_conformation_eq bands hb).trans
      (attachElectronicOption_base_conformation request).symm
  let bandState := attachIndependentBands electronicState bands bandGraph_eq bandConformation_eq
  let graph_eq : family.data.graph = bandState.graph :=
    (show family.data.graph = request.graph from by
      rw [show family.data.graph = family.graph from rfl]
      exact request.paths_graph_eq family hp).trans
      ((attachElectronicOption_base_graph request).symm.trans
        (attachIndependentBands_graph electronicState bands bandGraph_eq
          bandConformation_eq).symm)
  let conformation_eq : family.data.conformation = bandState.conformation :=
    (show family.data.conformation = request.conformation from by
      rw [show family.data.conformation = family.conformation from rfl]
      exact request.paths_conformation_eq family hp).trans
      ((attachElectronicOption_base_conformation request).symm.trans
        (attachIndependentBands_conformation electronicState bands bandGraph_eq
          bandConformation_eq).symm)
  let state := attachIndependentBondPathData bandState family.data graph_eq conformation_eq
  representation true family.edgeIndex family.fintypeEdgeIndex true bands.bandIndex
    bands.fintypeBandIndex state
    (fun _ => pathGeometryValid_attachIndependentBondPathData bandState family.data graph_eq
      conformation_eq)

/-! ## The assembly -/

/-- Compose the existing operations from the base state: electronic ingress, then band replacement,
then path replacement.  The match on the two optional channels is what fixes the effective finite
index types and the two presence tags. -/
def assemble (request : OrganicMolecularEvidence V) : OrganicMolecularRepresentation V :=
  match hb : request.bands? with
  | none =>
      match hp : request.paths? with
      | none => assembleBase request
      | some family => assemblePath request family hp
  | some bands =>
      match hp : request.paths? with
      | none => assembleBands request bands hb
      | some family => assembleBandsPath request bands family hb hp

/-! ## The decoder -/

/-- The path family decoded from a representation whose path tag is true, read through the public
`toIndependentBondPathData` adapter at the representation's own effective index type. -/
def OrganicMolecularRepresentation.decodedPathFamily
    (representation : OrganicMolecularRepresentation V)
    (hp : representation.pathPresent = true) : IndependentPathFamily V :=
  letI : Fintype representation.edgeIndex := representation.fintypeEdgeIndex
  letI : Fintype representation.bandIndex := representation.fintypeBandIndex
  ⟨representation.edgeIndex, representation.fintypeEdgeIndex,
    toIndependentBondPathData representation.state (representation.pathGeometryValid hp)⟩

/-- The decoded path family's graph is the assembled graph. -/
@[simp] theorem decodedPathFamily_graph (representation : OrganicMolecularRepresentation V)
    (hp : representation.pathPresent = true) :
    (representation.decodedPathFamily hp).graph = representation.stateGraph := rfl

/-- The decoded path family's conformation is the assembled conformation. -/
@[simp] theorem decodedPathFamily_conformation
    (representation : OrganicMolecularRepresentation V)
    (hp : representation.pathPresent = true) :
    (representation.decodedPathFamily hp).conformation =
      representation.stateConformation := rfl

/-- The decoded path family does not depend on the particular proof of the presence tag. -/
theorem decodedPathFamily_congr (representation : OrganicMolecularRepresentation V)
    {hp hq : representation.pathPresent = true} :
    representation.decodedPathFamily hp = representation.decodedPathFamily hq := by
  letI : Fintype representation.edgeIndex := representation.fintypeEdgeIndex
  letI : Fintype representation.bandIndex := representation.fintypeBandIndex
  unfold OrganicMolecularRepresentation.decodedPathFamily
  apply congrArg
    (fun data => (⟨representation.edgeIndex, representation.fintypeEdgeIndex, data⟩ :
      IndependentPathFamily V))
  exact independentBondPathData_extEq rfl rfl rfl rfl rfl rfl

/-- The path channel read from the assembled representation.  The explicit presence tag decides
between genuine absence and a supplied family (including a supplied empty family). -/
def decodedPaths? (representation : OrganicMolecularRepresentation V) :
    Option (IndependentPathFamily V) :=
  match hp : representation.pathPresent with
  | false => none
  | true => some (representation.decodedPathFamily hp)

theorem decodedPaths?_eq_none (representation : OrganicMolecularRepresentation V)
    (hp : representation.pathPresent = false) : decodedPaths? representation = none := by
  unfold decodedPaths?
  split
  · rfl
  · rename_i h
    exact absurd h (by rw [hp] at h; exact Bool.noConfusion h)

theorem decodedPaths?_eq_some (representation : OrganicMolecularRepresentation V)
    (hp : representation.pathPresent = true) :
    decodedPaths? representation = some (representation.decodedPathFamily hp) := by
  unfold decodedPaths?
  split
  · rename_i h
    exact absurd hp (by rw [h] at hp; exact Bool.noConfusion hp)
  · exact congrArg some (decodedPathFamily_congr representation)

/-- The recovered path family's graph is the assembled graph. -/
theorem decodedPaths?_graph_eq (representation : OrganicMolecularRepresentation V) :
    ∀ family, decodedPaths? representation = some family →
      family.graph = representation.stateGraph := by
  intro family present
  cases hp : representation.pathPresent with
  | false =>
      rw [decodedPaths?_eq_none representation hp] at present
      cases present
  | true =>
      rw [decodedPaths?_eq_some representation hp] at present
      cases present
      exact decodedPathFamily_graph representation hp

/-- The recovered path family's conformation is the assembled conformation. -/
theorem decodedPaths?_conformation_eq (representation : OrganicMolecularRepresentation V) :
    ∀ family, decodedPaths? representation = some family →
      family.conformation = representation.stateConformation := by
  intro family present
  cases hp : representation.pathPresent with
  | false =>
      rw [decodedPaths?_eq_none representation hp] at present
      cases present
  | true =>
      rw [decodedPaths?_eq_some representation hp] at present
      cases present
      exact decodedPathFamily_conformation representation hp

/-- The band attachment decoded from a representation whose band tag is true. -/
def OrganicMolecularRepresentation.decodedBandAttachment
    (representation : OrganicMolecularRepresentation V) : IndependentBandAttachment V :=
  letI : Fintype representation.edgeIndex := representation.fintypeEdgeIndex
  letI : Fintype representation.bandIndex := representation.fintypeBandIndex
  toIndependentBandAttachment representation.state

/-- The recovered band attachment's graph is the assembled graph. -/
@[simp] theorem decodedBandAttachment_graph
    (representation : OrganicMolecularRepresentation V) :
    representation.decodedBandAttachment.graph = representation.stateGraph := rfl

/-- The recovered band attachment's conformation is the assembled conformation. -/
@[simp] theorem decodedBandAttachment_conformation
    (representation : OrganicMolecularRepresentation V) :
    representation.decodedBandAttachment.conformation =
      representation.stateConformation := rfl

/-- The band channel read from the assembled representation. -/
def decodedBands? (representation : OrganicMolecularRepresentation V) :
    Option (IndependentBandAttachment V) :=
  match representation.bandPresent with
  | false => none
  | true => some representation.decodedBandAttachment

theorem decodedBands?_eq_none (representation : OrganicMolecularRepresentation V)
    (hb : representation.bandPresent = false) : decodedBands? representation = none := by
  simp only [decodedBands?, hb]

theorem decodedBands?_eq_some (representation : OrganicMolecularRepresentation V)
    (hb : representation.bandPresent = true) :
    decodedBands? representation = some representation.decodedBandAttachment := by
  simp only [decodedBands?, hb]

/-- The recovered band attachment's graph is the assembled graph. -/
theorem decodedBands?_graph_eq (representation : OrganicMolecularRepresentation V) :
    ∀ bands, decodedBands? representation = some bands →
      bands.graph = representation.stateGraph := by
  intro bands present
  cases hb : representation.bandPresent with
  | false =>
      rw [decodedBands?_eq_none representation hb] at present
      cases present
  | true =>
      rw [decodedBands?_eq_some representation hb] at present
      cases present
      exact decodedBandAttachment_graph representation

/-- The recovered band attachment's conformation is the assembled conformation. -/
theorem decodedBands?_conformation_eq (representation : OrganicMolecularRepresentation V) :
    ∀ bands, decodedBands? representation = some bands →
      bands.conformation = representation.stateConformation := by
  intro bands present
  cases hb : representation.bandPresent with
  | false =>
      rw [decodedBands?_eq_none representation hb] at present
      cases present
  | true =>
      rw [decodedBands?_eq_some representation hb] at present
      cases present
      exact decodedBandAttachment_conformation representation

/-- Decode a constructed representation into the independent request.  Only the assembled state and
the two explicit tags are read; the supplied path family, band family and electronic source are
recovered through the existing public adapters, not from a stored copy. -/
def decode (representation : OrganicMolecularRepresentation V) :
    OrganicMolecularEvidence V := by
  letI : Fintype representation.edgeIndex := representation.fintypeEdgeIndex
  letI : Fintype representation.bandIndex := representation.fintypeBandIndex
  exact
    { graph := representation.state.graph
      conformation := representation.state.conformation
      rationalPositions? := representation.state.rationalPositions?
      rationalPositions_valid := representation.state.rationalPositions_valid
      electronic? := stateElectronicEvidence? representation.state
      electronic_unpaired := stateElectronicEvidence?_unpaired representation.state
      paths? := decodedPaths? representation
      paths_graph_eq := decodedPaths?_graph_eq representation
      paths_conformation_eq := decodedPaths?_conformation_eq representation
      bands? := decodedBands? representation
      bands_graph_eq := decodedBands?_graph_eq representation
      bands_conformation_eq := decodedBands?_conformation_eq representation
      roles := representation.state.roles
      role_valid := representation.state.role_valid
      diagram? := representation.state.diagram?
      diagramPartial? := representation.state.diagramPartial?
      diagramIncidence := representation.state.diagramIncidence
      diagram_valid := representation.state.diagram_valid
      fragments := representation.state.fragments
      conventions := representation.state.conventions
      cages := representation.state.cages
      residueLedger? := representation.state.residueLedger?
      frames := representation.state.frames }

/-! ## Assembly projection lemmas -/

/-- All non-optional metadata channels are copied literally by every assembly branch. -/
theorem assemble_annotation_projections (request : OrganicMolecularEvidence V) :
    (assemble request).stateRationalPositions? = request.rationalPositions? ∧
    (assemble request).stateRoles = request.roles ∧
    (assemble request).stateDiagram? = request.diagram? ∧
    (assemble request).stateDiagramPartial? = request.diagramPartial? ∧
    (assemble request).stateDiagramIncidence = request.diagramIncidence ∧
    (assemble request).stateFragments = request.fragments ∧
    (assemble request).stateConventions = request.conventions ∧
    (assemble request).stateCages = request.cages ∧
    (assemble request).stateResidueLedger? = request.residueLedger? ∧
    (assemble request).stateFrames = request.frames := by
  unfold assemble
  split <;> split <;>
    simp [assembleBase, assemblePath, assembleBands, assembleBandsPath,
      representation, baseState,
      OrganicMolecularRepresentation.stateRationalPositions?,
      OrganicMolecularRepresentation.stateRoles,
      OrganicMolecularRepresentation.stateDiagram?,
      OrganicMolecularRepresentation.stateDiagramPartial?,
      OrganicMolecularRepresentation.stateDiagramIncidence,
      OrganicMolecularRepresentation.stateFragments,
      OrganicMolecularRepresentation.stateConventions,
      OrganicMolecularRepresentation.stateCages,
      OrganicMolecularRepresentation.stateResidueLedger?,
      OrganicMolecularRepresentation.stateFrames]

/-- With no supplied bands, the assembled graph is the request graph. -/
theorem assemble_graph_of_no_bands (request : OrganicMolecularEvidence V)
    (hb : request.bands? = none) :
    (assemble request).stateGraph = request.graph := by
  unfold assemble
  split <;> split <;>
    simp_all [assembleBase, assemblePath, assembleBands, assembleBandsPath,
      representation, OrganicMolecularRepresentation.stateGraph,
      attachIndependentBondPathData_graph, attachIndependentBands_graph,
      attachElectronicOption_base_graph]

/-- With a supplied band record, the assembled graph is the band record's graph. -/
theorem assemble_graph_of_bands (request : OrganicMolecularEvidence V)
    (bands : IndependentBandAttachment V) (hb : request.bands? = some bands) :
    (assemble request).stateGraph = bands.graph := by
  unfold assemble
  split <;> split <;>
    simp_all [assembleBase, assemblePath, assembleBands, assembleBandsPath,
      representation, OrganicMolecularRepresentation.stateGraph,
      attachIndependentBondPathData_graph, attachIndependentBands_graph,
      attachElectronicOption_base_graph, request.bands_graph_eq bands hb]

/-- With no supplied bands, the assembled conformation is the request conformation. -/
theorem assemble_conformation_of_no_bands (request : OrganicMolecularEvidence V)
    (hb : request.bands? = none) :
    (assemble request).stateConformation = request.conformation := by
  unfold assemble
  split <;> split <;>
    simp_all [assembleBase, assemblePath, assembleBands, assembleBandsPath,
      representation, OrganicMolecularRepresentation.stateConformation,
      attachIndependentBondPathData_conformation, attachIndependentBands_conformation,
      attachElectronicOption_base_conformation]

/-- With a supplied band record, the assembled conformation is the band record's conformation. -/
theorem assemble_conformation_of_bands (request : OrganicMolecularEvidence V)
    (bands : IndependentBandAttachment V) (hb : request.bands? = some bands) :
    (assemble request).stateConformation = bands.conformation := by
  unfold assemble
  split <;> split <;>
    simp_all [assembleBase, assemblePath, assembleBands, assembleBandsPath,
      representation, OrganicMolecularRepresentation.stateConformation,
      attachIndependentBondPathData_conformation, attachIndependentBands_conformation,
      attachElectronicOption_base_conformation,
      request.bands_conformation_eq bands hb]

/-- The assembled electronic evidence option is exactly the supplied one. -/
theorem assemble_electronic? (request : OrganicMolecularEvidence V) :
    (assemble request).stateElectronicEvidence = request.electronic? := by
  unfold assemble
  split <;> split <;>
    simp_all [assembleBase, assemblePath, assembleBands, assembleBandsPath,
      representation, baseState,
      OrganicMolecularRepresentation.stateElectronicEvidence,
      stateElectronicEvidence?_attachElectronicOption,
      stateElectronicEvidence?_attachIndependentBands,
      stateElectronicEvidence?_attachIndependentBondPathData]

/-- The decoded path option is exactly the supplied one, including presence/absence and the full
`IndependentBondPathData` payload. -/
theorem assemble_paths? (request : OrganicMolecularEvidence V) :
    decodedPaths? (assemble request) = request.paths? := by
  unfold assemble
  split <;> split <;>
    simp_all [assembleBase, assemblePath, assembleBands, assembleBandsPath,
      representation, baseState, attachElectronicOption, decodedPaths?,
      OrganicMolecularRepresentation.decodedPathFamily,
      toIndependentBondPathData_attachIndependentBondPathData,
      pathGeometryValid_attachIndependentBondPathData]

/-- The decoded band option is exactly the supplied one, including presence/absence and the full
`IndependentBandAttachment` payload. -/
theorem assemble_bands? (request : OrganicMolecularEvidence V) :
    decodedBands? (assemble request) = request.bands? := by
  unfold assemble
  split <;> split <;>
    simp_all [assembleBase, assemblePath, assembleBands, assembleBandsPath,
      representation, baseState, attachElectronicOption, decodedBands?,
      OrganicMolecularRepresentation.decodedBandAttachment,
      toIndependentBandAttachment_attachIndependentBondPathData,
      toIndependentBandAttachment_attachIndependentBands]

/-! ## Exact recovery of the whole request -/

/-- **Main result.**  Every independently supplied compatible request is recovered exactly from its
constructed representation.  All proposition-valued physical-compatibility fields are identified by
proof irrelevance; no shape equivalence is needed because the effective finite index types are the
supplied ones. -/
theorem decode_assemble (request : OrganicMolecularEvidence V) :
    decode (assemble request) = request := by
  apply OrganicMolecularEvidence.extEq
  · cases hb : request.bands? with
    | none => exact assemble_graph_of_no_bands request hb
    | some bands =>
        exact (assemble_graph_of_bands request bands hb).trans
          (request.bands_graph_eq bands hb)
  · cases hb : request.bands? with
    | none => exact assemble_conformation_of_no_bands request hb
    | some bands =>
        exact (assemble_conformation_of_bands request bands hb).trans
          (request.bands_conformation_eq bands hb)
  · exact (assemble_annotation_projections request).1
  · simpa [decode, OrganicMolecularRepresentation.stateElectronicEvidence]
      using assemble_electronic? request
  · exact assemble_paths? request
  · exact assemble_bands? request
  · exact (assemble_annotation_projections request).2.1
  · exact (assemble_annotation_projections request).2.2.1
  · exact (assemble_annotation_projections request).2.2.2.1
  · exact (assemble_annotation_projections request).2.2.2.2.1
  · exact (assemble_annotation_projections request).2.2.2.2.2.1
  · exact (assemble_annotation_projections request).2.2.2.2.2.2.1
  · exact (assemble_annotation_projections request).2.2.2.2.2.2.2.1
  · exact (assemble_annotation_projections request).2.2.2.2.2.2.2.2.1
  · exact (assemble_annotation_projections request).2.2.2.2.2.2.2.2.2

/-- The assembly is injective: distinct requests have distinct constructed representations. -/
theorem assemble_injective :
    Function.Injective (assemble : OrganicMolecularEvidence V → OrganicMolecularRepresentation V) := by
  intro first second equal
  have applied : decode (assemble first) = decode (assemble second) := congrArg decode equal
  rwa [decode_assemble first, decode_assemble second] at applied

/-- **Set-image recovery.**  The image of an arbitrary set of requests under the assembly is
recovered exactly by the decoder, so every correlation between the supplied channels is preserved. -/
theorem decode_image_assemble_image (requests : Set (OrganicMolecularEvidence V)) :
    decode '' (assemble '' requests) = requests := by
  ext request
  constructor
  · rintro ⟨assembled, ⟨original, member, rfl⟩, decoded⟩
    rw [← decoded, decode_assemble]
    exact member
  · intro member
    exact ⟨assemble request, ⟨request, member, rfl⟩, decode_assemble request⟩

end

end OrganicStereoMolecularEvidenceAssembly

end TetraStereo.OneCenter
