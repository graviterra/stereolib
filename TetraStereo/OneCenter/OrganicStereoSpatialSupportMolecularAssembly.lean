import TetraStereo.OneCenter.OrganicStereoOccurrenceSpatialSupportExperiment
import TetraStereo.OneCenter.OrganicStereoMolecularCanonicalTransport
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

namespace TetraStereo.OneCenter
namespace OrganicStereoSpatialSupportMolecularAssembly

open JointCoreEncoding
open OrganicStereoMolecularEvidenceAssembly
open OrganicStereoMolecularCanonicalTransport
open OccurrenceSpatialSupportExperiment

noncomputable section

variable {V : Type} [DecidableEq V] [Fintype V]




































/-! ## Heterogeneous molecular spatial cells -/

/-- One occurrence-bound geometric cell of the independent molecular request.

The dimension is *data*, so cells of different dimensions can coexist in one finite family; each
dimension is at most three.  The full continuous map is stored physically.  All ties to a concrete
interaction graph are proposition-valued fields of `OrganicSpatialMolecularEvidence`, so this cell
type itself is independent of the core. -/
structure SpatialMolecularCell (V : Type) where
  /-- The simplex dimension of this cell. -/
  dimension : ℕ
  /-- The honest bound: every cell has dimension at most three. -/
  dimension_le : dimension ≤ 3
  /-- The actual ordered interaction occurrence index (as a number checked by the request). -/
  occurrenceIndex : ℕ
  /-- The complete continuous spatial map. -/
  map : C(Delta dimension, EmbeddedReal3)
  /-- One participant atom anchor per simplex vertex. -/
  anchors : Fin (dimension + 1) → V
  /-- Explicit positions in the actual ordered core role ledger; may be empty or repeat. -/
  rolePositions : List ℕ

/-- Extensionality for molecular spatial cells.  The dimension bound is proposition-valued; the
map and anchor families are compared heterogeneously along the dimension equality. -/
theorem SpatialMolecularCell.extEq {first second : SpatialMolecularCell V}
    (dimension : first.dimension = second.dimension)
    (occurrenceIndex : first.occurrenceIndex = second.occurrenceIndex)
    (map : HEq first.map second.map)
    (anchors : HEq first.anchors second.anchors)
    (rolePositions : first.rolePositions = second.rolePositions) : first = second := by
  obtain ⟨firstDimension, firstBound, firstOccurrence, firstMap, firstAnchors, firstRoles⟩ :=
    first
  obtain ⟨secondDimension, secondBound, secondOccurrence, secondMap, secondAnchors,
    secondRoles⟩ := second
  dsimp only at dimension occurrenceIndex map anchors rolePositions
  cases dimension
  cases occurrenceIndex
  have mapEq : firstMap = secondMap := eq_of_heq map
  cases mapEq
  have anchorsEq : firstAnchors = secondAnchors := eq_of_heq anchors
  cases anchorsEq
  cases rolePositions
  have boundEq : firstBound = secondBound := Subsingleton.elim _ _
  cases boundEq
  rfl

/-- The independent molecular request enriched by an occurrence-bound heterogeneous cell family.

The cell data are plain `SpatialMolecularCell`s.  The four proposition-valued fields tie every cell
to the *actual* core graph, conformation and ordered role ledger: the occurrence is a real bounded
interaction index, every anchor is a participant of that occurrence and evaluates exactly to the
shared conformation, and every explicit role position resolves to an actual core role annotation
of the same occurrence. -/
structure OrganicSpatialMolecularEvidence (V : Type) [DecidableEq V] [Fintype V] where
  /-- The actual independent molecular-evidence core. -/
  core : OrganicMolecularEvidence V
  /-- The finite heterogeneous cell family. -/
  cells : List (SpatialMolecularCell V)
  /-- Every cell occurrence is a real bounded occurrence of the core graph. -/
  occurrence_bound : ∀ cell ∈ cells, cell.occurrenceIndex < core.graph.interactions.length
  /-- Every atom anchor is a participant of the bound occurrence. -/
  anchors_mem : ∀ cell (member : cell ∈ cells) i,
    cell.anchors i ∈
      (core.graph.interactions.get ⟨cell.occurrenceIndex, occurrence_bound cell member⟩).1
  /-- Every simplex vertex maps exactly to the shared core conformation at its anchor. -/
  anchor_value : ∀ cell (_ : cell ∈ cells) i,
    cell.map (Delta.vertex (d := cell.dimension) i) = core.conformation (cell.anchors i)
  /-- Every explicit role position resolves to an actual ordered core ledger entry annotating the
  same occurrence. -/
  role_reference : ∀ cell (member : cell ∈ cells) position
      (_ : position ∈ cell.rolePositions),
    ∃ annotation : RoleAnnotation V,
      core.roles[position]? = some annotation ∧
        annotation.interactionIndex = cell.occurrenceIndex ∧
        Compatible core.graph ⟨cell.occurrenceIndex, occurrence_bound cell member⟩ annotation.role

/-- Extensionality for the enriched request.  The core and the cell family determine everything;
all four compatibility fields are proposition-valued. -/
theorem OrganicSpatialMolecularEvidence.extEq
    {first second : OrganicSpatialMolecularEvidence V}
    (core : first.core = second.core) (cells : first.cells = second.cells) :
    first = second := by
  obtain ⟨firstCore, firstCells, firstBound, firstMemory, firstAnchor, firstRole⟩ := first
  obtain ⟨secondCore, secondCells, secondBound, secondMemory, secondAnchor, secondRole⟩ := second
  dsimp only at core cells
  cases core
  cases cells
  have bound : firstBound = secondBound := by
    funext cell member
    exact Subsingleton.elim _ _
  cases bound
  have memory : firstMemory = secondMemory := by
    funext cell member i
    exact Subsingleton.elim _ _
  cases memory
  have anchor : firstAnchor = secondAnchor := by
    funext cell member i
    exact Subsingleton.elim _ _
  cases anchor
  have role : firstRole = secondRole := by
    funext cell member position positionMem
    exact Subsingleton.elim _ _
  cases role
  rfl

/-! ## Converting the actual core role ledger to broad annotations -/

/-- Convert one actual core role annotation, together with the core's own compatibility evidence,
to an existing `BroadAnnotation` of the core graph.  The bound and compatibility are derived from
`OrganicMolecularEvidence.role_valid`; no second ledger is introduced. -/
def broadOfRole {graph : FiniteAtomInteractionHypergraph V} (annotation : RoleAnnotation V)
    (bound : annotation.interactionIndex < graph.interactions.length)
    (compatible : Compatible graph ⟨annotation.interactionIndex, bound⟩ annotation.role) :
    BroadAnnotation graph where
  index := ⟨annotation.interactionIndex, bound⟩
  role := annotation.role
  compatible := compatible

/-- The conversion of a role annotation at a concrete core ledger position. -/
def coreBroadAt (request : OrganicMolecularEvidence V) (index : Fin request.roles.length) :
    BroadAnnotation request.graph :=
  let annotation := request.roles.get index
  let bound := (request.role_valid annotation (List.get_mem request.roles index)).choose
  let compatible := (request.role_valid annotation (List.get_mem request.roles index)).choose_spec
  broadOfRole annotation bound compatible

/-- The finite broad ledger derived from the actual ordered core role ledger, entry by entry. -/
def coreBroadLedger (request : OrganicMolecularEvidence V) : List (BroadAnnotation request.graph) :=
  List.ofFn (coreBroadAt request)

/-- The broad ledger has exactly the length of the actual core role ledger. -/
theorem coreBroadLedger_length (request : OrganicMolecularEvidence V) :
    (coreBroadLedger request).length = request.roles.length := by
  simp [coreBroadLedger]

/-- **Positional equality of the conversion.**  The broad ledger entry at a valid position is the
conversion of the actual core role annotation at that same position. -/
theorem coreBroadLedger_getElem? (request : OrganicMolecularEvidence V) (position : ℕ)
    (bound : position < request.roles.length) :
    (coreBroadLedger request)[position]? = some (coreBroadAt request ⟨position, bound⟩) := by
  unfold coreBroadLedger
  rw [List.getElem?_ofFn]
  simp [bound]

/-- Forgetting the conversion's compatibility proof recovers the conversion's occurrence index. -/
@[simp] theorem coreBroadAt_index (request : OrganicMolecularEvidence V)
    (index : Fin request.roles.length) :
    (coreBroadAt request index).index.val = (request.roles.get index).interactionIndex := rfl

/-- Forgetting the conversion's compatibility proof recovers the conversion's role. -/
@[simp] theorem coreBroadAt_role (request : OrganicMolecularEvidence V)
    (index : Fin request.roles.length) :
    (coreBroadAt request index).role = (request.roles.get index).role := rfl

/-- Forget the compatibility proof of a broad annotation, retaining its occurrence index and role
as an actual `RoleAnnotation`. -/
def broadToRole {graph : FiniteAtomInteractionHypergraph V} (annotation : BroadAnnotation graph) :
    RoleAnnotation V where
  interactionIndex := annotation.index.val
  role := annotation.role

/-- **List equality of the conversion.**  Mapping the derived broad ledger back to role
annotations returns exactly the actual ordered core role ledger, with order, multiplicity and
position preserved. -/
theorem coreBroadLedger_map_broadToRole (request : OrganicMolecularEvidence V) :
    (coreBroadLedger request).map broadToRole = request.roles := by
  apply List.ext_getElem?
  intro position
  by_cases bound : position < request.roles.length
  · rw [List.getElem?_map, coreBroadLedger_getElem?, List.getElem?_eq_getElem bound]
    rfl
  · have noBound : request.roles.length ≤ position := Nat.le_of_not_lt bound
    have ledgerNoBound : (coreBroadLedger request).length ≤ position := by
      rw [coreBroadLedger_length]
      exact noBound
    rw [List.getElem?_map, List.getElem?_eq_none ledgerNoBound,
      List.getElem?_eq_none noBound]
    rfl

/-! ## Encoded spatial cells indexed by the actual output channels -/

/-- One encoded spatial cell.  It is indexed by the *actual* output graph, conformation and ordered
role ledger, stores the occurrence as a real bounded index, stores every anchor as an actual
encoded atom index, and keeps the full continuous map. -/
structure EncodedSpatialMolecularCell (n : ℕ)
    (G : FiniteAtomInteractionHypergraph (Fin n))
    (conformation : MolecularConformation (Fin n))
    (roles : List (RoleAnnotation (Fin n))) where
  /-- The simplex dimension of this cell. -/
  dimension : ℕ
  /-- Every cell dimension is at most three. -/
  dimension_le : dimension ≤ 3
  /-- The actual encoded interaction occurrence index. -/
  occurrenceIndex : ℕ
  /-- The bound proving that the occurrence index is a real occurrence of the output graph. -/
  occurrence_bound : occurrenceIndex < G.interactions.length
  /-- The full continuous map, not a vertex image or a centroid. -/
  map : C(Delta dimension, EmbeddedReal3)
  /-- One actual encoded atom index per simplex vertex. -/
  anchors : Fin (dimension + 1) → Fin n
  /-- Every anchor is a participant of the encoded output occurrence. -/
  anchors_mem : ∀ i,
    anchors i ∈ (G.interactions.get ⟨occurrenceIndex, occurrence_bound⟩).1
  /-- Every vertex maps exactly to the actual output conformation at its anchor. -/
  anchor_value : ∀ i,
    map (Delta.vertex (d := dimension) i) = conformation (anchors i)
  /-- Explicit positions in the actual output role ledger. -/
  rolePositions : List ℕ
  /-- Every explicit position resolves to an actual output role annotation of the same occurrence. -/
  role_reference : ∀ position ∈ rolePositions,
    ∃ annotation : RoleAnnotation (Fin n),
      roles[position]? = some annotation ∧
        annotation.interactionIndex = occurrenceIndex ∧
        Compatible G ⟨occurrenceIndex, occurrence_bound⟩ annotation.role

/-- The concrete occurrence `Fin` carried by an encoded cell. -/
def EncodedSpatialMolecularCell.occurrence {n : ℕ}
    {G : FiniteAtomInteractionHypergraph (Fin n)}
    {conformation : MolecularConformation (Fin n)}
    {roles : List (RoleAnnotation (Fin n))}
    (cell : EncodedSpatialMolecularCell n G conformation roles) :
    Fin G.interactions.length :=
  ⟨cell.occurrenceIndex, cell.occurrence_bound⟩

/-- The concrete occurrence value is the stored occurrence index. -/
@[simp] theorem EncodedSpatialMolecularCell.occurrence_val {n : ℕ}
    {G : FiniteAtomInteractionHypergraph (Fin n)}
    {conformation : MolecularConformation (Fin n)}
    {roles : List (RoleAnnotation (Fin n))}
    (cell : EncodedSpatialMolecularCell n G conformation roles) :
    cell.occurrence.val = cell.occurrenceIndex := rfl

/-- The actual assembled output plus its encoded spatial cells.  The cell family's type is indexed
by the actual canonical output graph, conformation and ordered role ledger, never by an original
request or graph parameter. -/
structure SpatialMolecularRepresentation (V : Type) [DecidableEq V] [Fintype V] where
  /-- The actual canonical assembly of the independent molecular core. -/
  canonical : CanonicalOrganicMolecularRepresentation V
  /-- The encoded heterogeneous cell family over the actual output channels. -/
  cells : List (EncodedSpatialMolecularCell (Fintype.card V)
    canonical.state.graph canonical.state.conformation canonical.state.roles)

/-! ## Projections of the canonical assembly -/

/-- The canonical assembly of a request has exactly the canonically relabelled core graph. -/
theorem canonicalAssemble_state_graph (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V) :
    (canonicalAssemble enumeration request).state.graph =
      relabelGraph enumeration request.graph := by
  have stateGraph : (canonicalAssemble enumeration request).state.graph =
      relabelGraph enumeration (assemble request).stateGraph := rfl
  rw [stateGraph]
  cases hb : request.bands? with
  | none => rw [assemble_graph_of_no_bands request hb]
  | some bands =>
      rw [assemble_graph_of_bands request bands hb, request.bands_graph_eq bands hb]

/-- The canonical assembly of a request has exactly the canonically reindexed core conformation. -/
theorem canonicalAssemble_state_conformation (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V) :
    (canonicalAssemble enumeration request).state.conformation =
      MolecularConformation.reindex enumeration request.conformation := by
  have stateConformation : (canonicalAssemble enumeration request).state.conformation =
      MolecularConformation.reindex enumeration (assemble request).stateConformation := rfl
  rw [stateConformation]
  cases hb : request.bands? with
  | none => rw [assemble_conformation_of_no_bands request hb]
  | some bands =>
      rw [assemble_conformation_of_bands request bands hb,
        request.bands_conformation_eq bands hb]

/-- The canonical assembly of a request has exactly the canonically relabelled core role ledger. -/
theorem canonicalAssemble_state_roles (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V) :
    (canonicalAssemble enumeration request).state.roles =
      request.roles.map (relabelRoleAnnotation enumeration) := by
  have stateRoles : (canonicalAssemble enumeration request).state.roles =
      (assemble request).stateRoles.map (relabelRoleAnnotation enumeration) := rfl
  rw [stateRoles, (assemble_annotation_projections request).2.1]

/-- The canonical assembly retains the supplied atom enumeration literally. -/
@[simp] theorem canonicalAssemble_atomEquiv (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V) :
    (canonicalAssemble enumeration request).atomEquiv = enumeration := rfl

/-- The canonical output graph has the same number of interactions as the request graph. -/
theorem canonicalAssemble_graph_length (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V) :
    (canonicalAssemble enumeration request).state.graph.interactions.length =
      request.graph.interactions.length := by
  rw [canonicalAssemble_state_graph, relabelGraph_interactions_length]

/-- The value of the canonical output conformation at an encoded atom is the core value at the
source atom. -/
theorem canonicalAssemble_conformation_apply (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V) (atom : V) :
    (canonicalAssemble enumeration request).state.conformation (enumeration atom) =
      request.conformation atom := by
  rw [canonicalAssemble_state_conformation]
  simp [MolecularConformation.reindex]

/-- Exact participant lookup in the canonical output graph.  The encoded occurrence is the relabel
of a source occurrence, and its participant list is the source participant list mapped through the
same atom enumeration. -/
theorem canonicalInteractions_get (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V)
    (index : Fin (canonicalAssemble enumeration request).state.graph.interactions.length)
    (sourceIndex : Fin request.graph.interactions.length)
    (indexValue : index.val = sourceIndex.val) :
    ((canonicalAssemble enumeration request).state.graph.interactions.get index).1 =
      (request.graph.interactions.get sourceIndex).1.map enumeration := by
  generalize hGraph : (canonicalAssemble enumeration request).state.graph = G at index ⊢
  have hRelabel : G = relabelGraph enumeration request.graph := by
    rw [← hGraph]
    exact canonicalAssemble_state_graph enumeration request
  clear hGraph
  subst G
  simp [relabelGraph, relabelInteractionEdge, List.get_eq_getElem, List.getElem_map,
    indexValue]

/-- Source compatibility transports to the actual canonical output occurrence. -/
theorem compatible_canonical_of_source (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V)
    (sourceIndex : Fin request.graph.interactions.length)
    (canonicalIndex : Fin (canonicalAssemble enumeration request).state.graph.interactions.length)
    (indexValue : canonicalIndex.val = sourceIndex.val) {role : PhysicalRole V}
    (compatible : Compatible request.graph sourceIndex role) :
    Compatible (canonicalAssemble enumeration request).state.graph canonicalIndex
      (relabelPhysicalRole enumeration role) := by
  generalize hGraph : (canonicalAssemble enumeration request).state.graph = G at canonicalIndex ⊢
  have hRelabel : G = relabelGraph enumeration request.graph := by
    rw [← hGraph]
    exact canonicalAssemble_state_graph enumeration request
  clear hGraph
  subst G
  have indexEq : canonicalIndex = relabelInteractionIndex enumeration sourceIndex :=
    Fin.ext indexValue
  rw [indexEq]
  exact compatible_relabel enumeration compatible

/-! ## Encoding one cell -/

/-- Encode a source cell through the one common atom enumeration, the actual canonical assembly of
the core, and the actual output graph/conformation/role ledger.  All occurrence, participant,
conformation and role proofs are transported from the request's own evidence. -/
def encodeSpatialCell (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicSpatialMolecularEvidence V) (cell : SpatialMolecularCell V)
    (member : cell ∈ request.cells) :
    EncodedSpatialMolecularCell (Fintype.card V)
      (canonicalAssemble enumeration request.core).state.graph
      (canonicalAssemble enumeration request.core).state.conformation
      (canonicalAssemble enumeration request.core).state.roles :=
  let canonical := canonicalAssemble enumeration request.core
  let occurrenceBound : cell.occurrenceIndex < canonical.state.graph.interactions.length := by
    rw [canonicalAssemble_graph_length enumeration request.core]
    exact request.occurrence_bound cell member
  { dimension := cell.dimension
    dimension_le := cell.dimension_le
    occurrenceIndex := cell.occurrenceIndex
    occurrence_bound := occurrenceBound
    map := cell.map
    anchors := fun i => enumeration (cell.anchors i)
    anchors_mem := by
      intro i
      rw [canonicalInteractions_get enumeration request.core
        ⟨cell.occurrenceIndex, occurrenceBound⟩
        ⟨cell.occurrenceIndex, request.occurrence_bound cell member⟩ rfl]
      exact List.mem_map.mpr ⟨cell.anchors i, request.anchors_mem cell member i, rfl⟩
    anchor_value := by
      intro i
      rw [canonicalAssemble_conformation_apply enumeration request.core (cell.anchors i)]
      exact request.anchor_value cell member i
    rolePositions := cell.rolePositions
    role_reference := by
      intro position positionMem
      obtain ⟨annotation, lookup, occurrenceEq, compatible⟩ :=
        request.role_reference cell member position positionMem
      refine ⟨relabelRoleAnnotation enumeration annotation, ?_, ?_, ?_⟩
      · rw [canonicalAssemble_state_roles, List.getElem?_map, lookup]
        rfl
      · simpa [relabelRoleAnnotation] using occurrenceEq
      · exact compatible_canonical_of_source enumeration request.core
          ⟨cell.occurrenceIndex, request.occurrence_bound cell member⟩
          ⟨cell.occurrenceIndex, occurrenceBound⟩
          rfl compatible }

/-! ## The assembled representation -/

/-- Assemble an enriched request into the actual canonical output plus encoded cells.  The cell
family is attached through the subtype membership proofs, so every cell is encoded with its own
occurrence/anchor/compatibility evidence. -/
def assembleSpatial (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicSpatialMolecularEvidence V) : SpatialMolecularRepresentation V where
  canonical := canonicalAssemble enumeration request.core
  cells := request.cells.attach.map
    (fun entry => encodeSpatialCell enumeration request entry.1 entry.2)

/-- The assembled representation's canonical record is the actual canonical assembly of the core. -/
@[simp] theorem assembleSpatial_canonical (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicSpatialMolecularEvidence V) :
    (assembleSpatial enumeration request).canonical =
      canonicalAssemble enumeration request.core := rfl

/-- The assembled cell family is the attached encoding of the request cells. -/
@[simp] theorem assembleSpatial_cells (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicSpatialMolecularEvidence V) :
    (assembleSpatial enumeration request).cells =
      request.cells.attach.map
        (fun entry => encodeSpatialCell enumeration request entry.1 entry.2) := rfl

/-- The actual output graph of the assembled representation is the canonically relabelled core
graph. -/
theorem assembleSpatial_state_graph (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicSpatialMolecularEvidence V) :
    (assembleSpatial enumeration request).canonical.state.graph =
      relabelGraph enumeration request.core.graph :=
  canonicalAssemble_state_graph enumeration request.core

/-- The actual output conformation of the assembled representation is the canonically reindexed
core conformation. -/
theorem assembleSpatial_state_conformation (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicSpatialMolecularEvidence V) :
    (assembleSpatial enumeration request).canonical.state.conformation =
      MolecularConformation.reindex enumeration request.core.conformation :=
  canonicalAssemble_state_conformation enumeration request.core

/-- The actual output role ledger of the assembled representation is the canonically relabelled
core role ledger. -/
theorem assembleSpatial_state_roles (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicSpatialMolecularEvidence V) :
    (assembleSpatial enumeration request).canonical.state.roles =
      request.core.roles.map (relabelRoleAnnotation enumeration) :=
  canonicalAssemble_state_roles enumeration request.core

/-! ## Decoding one cell -/

/-- The decoded molecular core of an actual canonical representation.  This is the existing
upstream decoder applied to the existing canonical decoder; no original core is stored. -/
def decodedCore (canonical : CanonicalOrganicMolecularRepresentation V) :
    OrganicMolecularEvidence V :=
  decode (canonicalDecode canonical)

/-- The decoded core graph is the decoded description graph, hence the canonical output graph
relabelled by the inverse of the actual atom enumeration. -/
theorem decodedCore_graph (canonical : CanonicalOrganicMolecularRepresentation V) :
    (decodedCore canonical).graph =
      relabelGraph canonical.atomEquiv.symm canonical.state.graph := rfl

/-- The decoded core conformation is the canonical output conformation reindexed by the inverse of
the actual atom enumeration. -/
theorem decodedCore_conformation (canonical : CanonicalOrganicMolecularRepresentation V) :
    (decodedCore canonical).conformation =
      MolecularConformation.reindex canonical.atomEquiv.symm canonical.state.conformation := rfl

/-- The decoded core role ledger is the actual output role ledger relabelled by the inverse of the
actual atom enumeration. -/
theorem decodedCore_roles (canonical : CanonicalOrganicMolecularRepresentation V) :
    (decodedCore canonical).roles =
      canonical.state.roles.map (relabelRoleAnnotation canonical.atomEquiv.symm) := rfl

/-- The decoded core graph has the same interaction count as the actual output graph. -/
theorem decodedCore_graph_length (canonical : CanonicalOrganicMolecularRepresentation V) :
    (decodedCore canonical).graph.interactions.length =
      canonical.state.graph.interactions.length := by
  rw [decodedCore_graph, relabelGraph_interactions_length]

/-- Decode one encoded cell to a source molecular cell: the occurrence is the encoded occurrence
index, the anchors are the actual encoded atom indices read through the inverse enumeration, and
the full continuous map and role positions are retained. -/
def decodeSpatialCell (canonical : CanonicalOrganicMolecularRepresentation V)
    {G : FiniteAtomInteractionHypergraph (Fin (Fintype.card V))}
    {conformation : MolecularConformation (Fin (Fintype.card V))}
    {roles : List (RoleAnnotation (Fin (Fintype.card V)))}
    (cell : EncodedSpatialMolecularCell (Fintype.card V) G conformation roles) :
    SpatialMolecularCell V where
  dimension := cell.dimension
  dimension_le := cell.dimension_le
  occurrenceIndex := cell.occurrenceIndex
  map := cell.map
  anchors := fun i => canonical.atomEquiv.symm (cell.anchors i)
  rolePositions := cell.rolePositions

/-- Encoding a decoded cell returns exactly the original cell.  The occurrence index, dimension,
full continuous map, atom anchors and role positions are all recovered. -/
theorem decodeSpatialCell_encodeSpatialCell (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicSpatialMolecularEvidence V) (cell : SpatialMolecularCell V)
    (member : cell ∈ request.cells) :
    decodeSpatialCell (canonicalAssemble enumeration request.core)
      (encodeSpatialCell enumeration request cell member) = cell := by
  obtain ⟨dimension, bound, occurrence, map, anchors, roles⟩ := cell
  apply SpatialMolecularCell.extEq
  · rfl
  · rfl
  · exact HEq.refl map
  · apply heq_of_eq
    funext i
    simp [decodeSpatialCell, encodeSpatialCell, canonicalAssemble_atomEquiv,
      Equiv.symm_apply_apply]
  · rfl

/-- Decoded participant membership is exactly source participant membership at the decoded
occurrence. -/
theorem decodedCell_anchors_mem (canonical : CanonicalOrganicMolecularRepresentation V)
    (cell : EncodedSpatialMolecularCell (Fintype.card V)
      canonical.state.graph canonical.state.conformation canonical.state.roles)
    (bound : cell.occurrenceIndex < (decodedCore canonical).graph.interactions.length) (i) :
    canonical.atomEquiv.symm (cell.anchors i) ∈
      ((decodedCore canonical).graph.interactions.get
        ⟨cell.occurrenceIndex, bound⟩).1 := by
  change canonical.atomEquiv.symm (cell.anchors i) ∈
    ((relabelGraph canonical.atomEquiv.symm canonical.state.graph).interactions.get
      ⟨cell.occurrenceIndex, bound⟩).1
  have indexEq : (⟨cell.occurrenceIndex, bound⟩ :
      Fin (relabelGraph canonical.atomEquiv.symm canonical.state.graph).interactions.length) =
      relabelInteractionIndex canonical.atomEquiv.symm
        ⟨cell.occurrenceIndex, cell.occurrence_bound⟩ := Fin.ext rfl
  rw [indexEq, relabelGraph_interactions_get]
  exact List.mem_map.mpr ⟨cell.anchors i, cell.anchors_mem i, rfl⟩

/-- Decoded role references resolve to actual decoded core ledger entries of the same occurrence. -/
theorem decodedCell_role_reference (canonical : CanonicalOrganicMolecularRepresentation V)
    (cell : EncodedSpatialMolecularCell (Fintype.card V)
      canonical.state.graph canonical.state.conformation canonical.state.roles)
    (bound : cell.occurrenceIndex < (decodedCore canonical).graph.interactions.length)
    (position : ℕ) (positionMem : position ∈ cell.rolePositions) :
    ∃ annotation : RoleAnnotation V,
      (decodedCore canonical).roles[position]? = some annotation ∧
        annotation.interactionIndex = cell.occurrenceIndex ∧
        Compatible (decodedCore canonical).graph
          ⟨cell.occurrenceIndex, bound⟩ annotation.role := by
  obtain ⟨annotation, lookup, occurrenceEq, compatible⟩ :=
    cell.role_reference position positionMem
  refine ⟨relabelRoleAnnotation canonical.atomEquiv.symm annotation, ?_, ?_, ?_⟩
  · rw [decodedCore_roles, List.getElem?_map, lookup]
    rfl
  · simpa [relabelRoleAnnotation] using occurrenceEq
  · change Compatible
      (relabelGraph canonical.atomEquiv.symm canonical.state.graph)
      ⟨cell.occurrenceIndex, bound⟩
      (relabelPhysicalRole canonical.atomEquiv.symm annotation.role)
    have indexEq : (⟨cell.occurrenceIndex, bound⟩ :
        Fin (relabelGraph canonical.atomEquiv.symm canonical.state.graph).interactions.length) =
        relabelInteractionIndex canonical.atomEquiv.symm
          ⟨cell.occurrenceIndex, cell.occurrence_bound⟩ := Fin.ext rfl
    rw [indexEq]
    exact compatible_relabel canonical.atomEquiv.symm compatible

/-! ## The decoder -/

/-- Decode an actual assembled representation back into the enriched independent request.

The core is reconstructed with the existing upstream decoder applied to the existing canonical
decoder.  Every cell is reconstructed through its encoded occurrence and encoded atom references;
every anchor/role proof is re-established against the *decoded actual output* core. -/
def decodeSpatial (_enumeration : V ≃ Fin (Fintype.card V))
    (representation : SpatialMolecularRepresentation V) :
    OrganicSpatialMolecularEvidence V := by
  let core := decodedCore representation.canonical
  let cells := representation.cells.map (decodeSpatialCell representation.canonical)
  let bound : ∀ cell ∈ cells,
      cell.occurrenceIndex < (decodedCore representation.canonical).graph.interactions.length := by
    intro cell member
    obtain ⟨encodedCell, _, rfl⟩ := List.mem_map.mp member
    show encodedCell.occurrenceIndex <
      (decodedCore representation.canonical).graph.interactions.length
    rw [decodedCore_graph_length]
    exact encodedCell.occurrence_bound
  refine
    { core := core
      cells := cells
      occurrence_bound := bound
      anchors_mem := ?_
      anchor_value := ?_
      role_reference := ?_ }
  · intro cell member i
    obtain ⟨encodedCell, _, rfl⟩ := List.mem_map.mp member
    exact decodedCell_anchors_mem representation.canonical encodedCell
      (bound _ member) i
  · intro cell member i
    obtain ⟨encodedCell, _, rfl⟩ := List.mem_map.mp member
    have original := encodedCell.anchor_value i
    have conformationEq : core.conformation =
        MolecularConformation.reindex representation.canonical.atomEquiv.symm
          representation.canonical.state.conformation := rfl
    rw [conformationEq]
    simpa [decodeSpatialCell, MolecularConformation.reindex] using original
  · intro cell member position positionMem
    obtain ⟨encodedCell, _, rfl⟩ := List.mem_map.mp member
    exact decodedCell_role_reference representation.canonical encodedCell
      (bound _ member) position positionMem

/-- The decoded core of the assembled representation is exactly the original core. -/
theorem decodeSpatial_assembleSpatial_core (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicSpatialMolecularEvidence V) :
    (decodeSpatial enumeration (assembleSpatial enumeration request)).core = request.core := by
  change decode (canonicalDecode (canonicalAssemble enumeration request.core)) = request.core
  exact decode_canonicalAssemble enumeration request.core

/-- The decoded cells of the assembled representation are exactly the original cells. -/
theorem decodeSpatial_assembleSpatial_cells (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicSpatialMolecularEvidence V) :
    (decodeSpatial enumeration (assembleSpatial enumeration request)).cells = request.cells := by
  change (request.cells.attach.map
      (fun entry => encodeSpatialCell enumeration request entry.1 entry.2)).map
      (decodeSpatialCell (canonicalAssemble enumeration request.core)) = request.cells
  rw [List.map_map]
  have composed : (decodeSpatialCell (canonicalAssemble enumeration request.core) ∘
      (fun entry : { cell // cell ∈ request.cells } =>
        encodeSpatialCell enumeration request entry.1 entry.2)) = Subtype.val := by
    funext entry
    exact decodeSpatialCell_encodeSpatialCell enumeration request entry.1 entry.2
  rw [composed, List.attach_map_subtype_val request.cells]

/-- **Main left-inverse theorem.**  Decoding the assembled representation of an arbitrary enriched
request returns the whole request exactly: the actual core with every optional channel, and the
whole heterogeneous cell family with every occurrence, full map, atom anchor and role position.
The interaction graph and all core fields vary with the request; only the atom type and its
enumeration are fixed. -/
theorem decodeSpatial_assembleSpatial (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicSpatialMolecularEvidence V) :
    decodeSpatial enumeration (assembleSpatial enumeration request) = request := by
  apply OrganicSpatialMolecularEvidence.extEq
  · exact decodeSpatial_assembleSpatial_core enumeration request
  · exact decodeSpatial_assembleSpatial_cells enumeration request

/-- Assembly is injective: distinct enriched requests have distinct actual assembled outputs. -/
theorem assembleSpatial_injective (enumeration : V ≃ Fin (Fintype.card V)) :
    Function.Injective (assembleSpatial enumeration) := by
  intro first second equal
  have applied : decodeSpatial enumeration (assembleSpatial enumeration first) =
      decodeSpatial enumeration (assembleSpatial enumeration second) :=
    congrArg (decodeSpatial enumeration) equal
  rwa [decodeSpatial_assembleSpatial, decodeSpatial_assembleSpatial] at applied

/-- **Joint correlated set-image recovery.**  For every set of enriched requests, decoding the
assembled image recovers exactly the original set.  Since the whole request is recovered
pointwise, correlations between the core graph, conformation, optional electronic/path/band/
drawing/source data and the geometric cell family are retained. -/
theorem decodeSpatial_image_assembleSpatial_image
    (enumeration : V ≃ Fin (Fintype.card V))
    (requests : Set (OrganicSpatialMolecularEvidence V)) :
    decodeSpatial enumeration '' (assembleSpatial enumeration '' requests) = requests := by
  rw [Set.image_image]
  have pointwise :
      (fun request => decodeSpatial enumeration (assembleSpatial enumeration request)) = id := by
    funext request
    exact decodeSpatial_assembleSpatial enumeration request
  rw [pointwise, Set.image_id]

/-! ## Preservation of the optional core channels -/

/-- The delegated upstream decoder of the assembled canonical core recovers the exact optional path
channel of the request core, including `none` versus a supplied empty family. -/
theorem assembleSpatial_paths? (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicSpatialMolecularEvidence V) :
    decodedPaths? ((assembleSpatial enumeration request).canonical |> canonicalDecode) =
      request.core.paths? :=
  decodedPaths?_canonicalAssemble enumeration request.core

/-- The delegated upstream decoder of the assembled canonical core recovers the exact optional band
channel of the request core. -/
theorem assembleSpatial_bands? (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicSpatialMolecularEvidence V) :
    decodedBands? ((assembleSpatial enumeration request).canonical |> canonicalDecode) =
      request.core.bands? :=
  decodedBands?_canonicalAssemble enumeration request.core



/-- The physical core shared by the straight and curved lifts.  It is an actual independent
molecular-evidence request with the ternary witness graph, the witness conformation and the two
ordered role annotations of the same occurrence. -/
def witnessCore : OrganicMolecularEvidence (Fin 3) where
  graph := witnessGraph
  conformation := witnessConformation
  rationalPositions_valid := by
    intro positions present
    cases present
  electronic_unpaired := by
    intro evidence present
    cases present
  paths_graph_eq := by
    intro family present
    cases present
  paths_conformation_eq := by
    intro family present
    cases present
  bands_graph_eq := by
    intro bands present
    cases present
  bands_conformation_eq := by
    intro bands present
    cases present
  roles := [⟨0, witnessRoleA⟩, ⟨0, witnessRoleB⟩]
  role_valid := by
    intro annotation member
    simp at member
    rcases member with rfl | rfl
    · exact ⟨witnessOccurrence.isLt, by simpa using witnessAnnotationA.compatible⟩
    · exact ⟨witnessOccurrence.isLt, by simpa using witnessAnnotationB.compatible⟩
  diagram_valid := by
    intro row member
    simp at member

/-- The straight source cell over the shared witness core. -/
def witnessMolecularCellStraight : SpatialMolecularCell (Fin 3) where
  dimension := 2
  dimension_le := by norm_num
  occurrenceIndex := 0
  map := F0
  anchors := fun i => i
  rolePositions := [0]

/-- The curved source cell over the shared witness core.  It has the same occurrence, anchors and
role positions as the straight cell. -/
def witnessMolecularCellCurved : SpatialMolecularCell (Fin 3) where
  dimension := 2
  dimension_le := by norm_num
  occurrenceIndex := 0
  map := F1
  anchors := fun i => i
  rolePositions := [0]

/-- The straight enriched request. -/
def witnessRequestStraight : OrganicSpatialMolecularEvidence (Fin 3) where
  core := witnessCore
  cells := [witnessMolecularCellStraight]
  occurrence_bound := by
    intro cell member
    obtain rfl := List.mem_singleton.mp member
    exact witnessOccurrence.isLt
  anchors_mem := by
    intro cell member i
    obtain rfl := List.mem_singleton.mp member
    fin_cases i <;>
      simp [witnessMolecularCellStraight, witnessCore, witnessGraph, witnessOccurrence]
  anchor_value := by
    intro cell member i
    obtain rfl := List.mem_singleton.mp member
    fin_cases i <;> simp [witnessMolecularCellStraight, witnessCore, witnessConformation]
  role_reference := by
    intro cell member position positionMem
    obtain rfl := List.mem_singleton.mp member
    simp [witnessMolecularCellStraight] at positionMem
    subst positionMem
    refine ⟨⟨0, witnessRoleA⟩, ?_, ?_, ?_⟩
    · simp [witnessCore]
    · rfl
    · simpa [witnessCore, witnessOccurrence] using witnessAnnotationA.compatible

/-- The curved enriched request.  It has the same core as the straight request. -/
def witnessRequestCurved : OrganicSpatialMolecularEvidence (Fin 3) where
  core := witnessCore
  cells := [witnessMolecularCellCurved]
  occurrence_bound := by
    intro cell member
    obtain rfl := List.mem_singleton.mp member
    exact witnessOccurrence.isLt
  anchors_mem := by
    intro cell member i
    obtain rfl := List.mem_singleton.mp member
    fin_cases i <;>
      simp [witnessMolecularCellCurved, witnessCore, witnessGraph, witnessOccurrence]
  anchor_value := by
    intro cell member i
    obtain rfl := List.mem_singleton.mp member
    fin_cases i <;>
      simp [witnessMolecularCellCurved, witnessCore, witnessConformation,
        F1Fun_vertex_eq_F0Fun_vertex]
  role_reference := by
    intro cell member position positionMem
    obtain rfl := List.mem_singleton.mp member
    simp [witnessMolecularCellCurved] at positionMem
    subst positionMem
    refine ⟨⟨0, witnessRoleA⟩, ?_, ?_, ?_⟩
    · simp [witnessCore]
    · rfl
    · simpa [witnessCore, witnessOccurrence] using witnessAnnotationA.compatible

/-- The two requests share the exact same physical core. -/
theorem witnessRequests_same_core :
    witnessRequestStraight.core = witnessRequestCurved.core := rfl

/-- The straight actual assembled output. -/
def witnessRepresentationStraight : SpatialMolecularRepresentation (Fin 3) :=
  assembleSpatial witnessEnumeration witnessRequestStraight

/-- The curved actual assembled output. -/
def witnessRepresentationCurved : SpatialMolecularRepresentation (Fin 3) :=
  assembleSpatial witnessEnumeration witnessRequestCurved

/-- The two actual assembled outputs have exactly the same canonical core. -/
theorem witnessRepresentations_same_canonical :
    witnessRepresentationStraight.canonical = witnessRepresentationCurved.canonical := rfl

/-- The encoded straight cell produced by the actual assembly. -/
def witnessEncodedCellStraight : EncodedSpatialMolecularCell (Fintype.card (Fin 3))
    (canonicalAssemble witnessEnumeration witnessCore).state.graph
    (canonicalAssemble witnessEnumeration witnessCore).state.conformation
    (canonicalAssemble witnessEnumeration witnessCore).state.roles :=
  encodeSpatialCell witnessEnumeration witnessRequestStraight witnessMolecularCellStraight
    (by simp [witnessRequestStraight])

/-- The encoded curved cell produced by the actual assembly. -/
def witnessEncodedCellCurved : EncodedSpatialMolecularCell (Fintype.card (Fin 3))
    (canonicalAssemble witnessEnumeration witnessCore).state.graph
    (canonicalAssemble witnessEnumeration witnessCore).state.conformation
    (canonicalAssemble witnessEnumeration witnessCore).state.roles :=
  encodeSpatialCell witnessEnumeration witnessRequestCurved witnessMolecularCellCurved
    (by simp [witnessRequestCurved])

/-- The assembled straight cell family is exactly the single encoded straight cell. -/
theorem witnessRepresentationStraight_cells :
    witnessRepresentationStraight.cells = [witnessEncodedCellStraight] := by
  simp [witnessRepresentationStraight, assembleSpatial, witnessRequestStraight,
    witnessEncodedCellStraight]

/-- The assembled curved cell family is exactly the single encoded curved cell. -/
theorem witnessRepresentationCurved_cells :
    witnessRepresentationCurved.cells = [witnessEncodedCellCurved] := by
  simp [witnessRepresentationCurved, assembleSpatial, witnessRequestCurved,
    witnessEncodedCellCurved]

/-- Evaluate an encoded cell at the barycentre when its dimension is two, and at zero otherwise.
This is a total function of the encoded cell, so it can be mapped over a heterogeneous cell
family to compare actual interior geometry. -/
def encodedInteriorValue {n : ℕ} {G : FiniteAtomInteractionHypergraph (Fin n)}
    {conformation : MolecularConformation (Fin n)} {roles : List (RoleAnnotation (Fin n))}
    (cell : EncodedSpatialMolecularCell n G conformation roles) : EmbeddedReal3 :=
  if h : cell.dimension = 2 then
    ((h ▸ cell.map) : C(Delta 2, EmbeddedReal3)) Delta.barycentre
  else 0

/-- The encoded straight cell has dimension two. -/
@[simp] theorem witnessEncodedCellStraight_dimension :
    witnessEncodedCellStraight.dimension = 2 := rfl

/-- The encoded curved cell has dimension two. -/
@[simp] theorem witnessEncodedCellCurved_dimension :
    witnessEncodedCellCurved.dimension = 2 := rfl

/-- The encoded straight interior value is the straight barycentre value. -/
theorem witnessEncodedCellStraight_interior :
    encodedInteriorValue witnessEncodedCellStraight = F0Fun Delta.barycentre := by
  unfold encodedInteriorValue
  rw [dif_pos (show witnessEncodedCellStraight.dimension = 2 from rfl)]
  rfl

/-- The encoded curved interior value is the curved barycentre value. -/
theorem witnessEncodedCellCurved_interior :
    encodedInteriorValue witnessEncodedCellCurved = F1Fun Delta.barycentre := by
  unfold encodedInteriorValue
  rw [dif_pos (show witnessEncodedCellCurved.dimension = 2 from rfl)]
  rfl

/-- Actual assembled straight interior. -/
theorem witnessRepresentationStraight_interior :
    witnessRepresentationStraight.cells.map encodedInteriorValue =
      [F0Fun Delta.barycentre] := by
  rw [witnessRepresentationStraight_cells]
  simp [witnessEncodedCellStraight_interior]

/-- Actual assembled curved interior. -/
theorem witnessRepresentationCurved_interior :
    witnessRepresentationCurved.cells.map encodedInteriorValue =
      [F1Fun Delta.barycentre] := by
  rw [witnessRepresentationCurved_cells]
  simp [witnessEncodedCellCurved_interior]

/-- **Integration does not erase the distinction.**  The two actual assembled molecular outputs
have the same physical core and the same canonical output core, but different encoded cell
families. -/
theorem witnessRepresentation_encoded_cells_differ :
    witnessRepresentationStraight.cells ≠ witnessRepresentationCurved.cells := by
  intro equal
  have mapped : witnessRepresentationStraight.cells.map encodedInteriorValue =
      witnessRepresentationCurved.cells.map encodedInteriorValue :=
    congrArg (fun cells => cells.map encodedInteriorValue) equal
  rw [witnessRepresentationStraight_interior, witnessRepresentationCurved_interior] at mapped
  have pointEqual : F0Fun Delta.barycentre = F1Fun Delta.barycentre := by
    simpa using mapped
  exact F0Fun_barycentre_ne_F1Fun_barycentre pointEqual

/-- The two actual assembled cells have exactly the same encoded atom anchors. -/
theorem witnessEncodedCells_same_anchors :
    witnessEncodedCellStraight.anchors = witnessEncodedCellCurved.anchors := rfl

/-- The two actual assembled cells have exactly the same encoded role positions. -/
theorem witnessEncodedCells_same_rolePositions :
    witnessEncodedCellStraight.rolePositions = witnessEncodedCellCurved.rolePositions := rfl

/-- The two actual assembled cells have exactly the same encoded occurrence index. -/
theorem witnessEncodedCells_same_occurrenceIndex :
    witnessEncodedCellStraight.occurrenceIndex = witnessEncodedCellCurved.occurrenceIndex := rfl

/-- The two actual assembled cells agree pointwise on the entire boundary of the two-simplex,
although their full maps differ. -/
theorem witnessEncodedCells_boundary_agreement (w : Delta 2) (boundary : Delta.Boundary w) :
    witnessEncodedCellStraight.map w = witnessEncodedCellCurved.map w := by
  simpa [witnessEncodedCellStraight, witnessEncodedCellCurved, encodeSpatialCell,
    witnessMolecularCellStraight, witnessMolecularCellCurved] using
    F0Fun_eq_F1Fun_of_boundary w boundary

/-- In particular the two actual assembled cells agree at every simplex vertex, i.e. at every
participant anchor value. -/
theorem witnessEncodedCells_vertex_agreement (i : Fin 3) :
    witnessEncodedCellStraight.map (Delta.vertex (d := 2) i) =
      witnessEncodedCellCurved.map (Delta.vertex (d := 2) i) := by
  simpa [witnessEncodedCellStraight, witnessEncodedCellCurved, encodeSpatialCell,
    witnessMolecularCellStraight, witnessMolecularCellCurved] using
    F0Fun_vertex_eq_F1Fun_vertex i

/-- The straight actual assembled interior has third coordinate zero. -/
theorem witnessRepresentationStraight_interior_third :
    (witnessRepresentationStraight.cells.map encodedInteriorValue).map
        (fun point => point 2) = [0] := by
  rw [witnessRepresentationStraight_interior]
  simp [F0Fun, Delta.barycentre]

/-- The curved actual assembled interior has third coordinate `1/27`. -/
theorem witnessRepresentationCurved_interior_third :
    (witnessRepresentationCurved.cells.map encodedInteriorValue).map
        (fun point => point 2) = [1 / 27] := by
  rw [witnessRepresentationCurved_interior]
  simp [F1Fun, Delta.barycentre]
  norm_num

end

end OrganicStereoSpatialSupportMolecularAssembly
end TetraStereo.OneCenter

/-! ## Kernel checks of the decisive endpoints -/

#print axioms TetraStereo.OneCenter.OrganicStereoSpatialSupportMolecularAssembly.decodeSpatial_assembleSpatial
#print axioms TetraStereo.OneCenter.OrganicStereoSpatialSupportMolecularAssembly.assembleSpatial_injective
#print axioms TetraStereo.OneCenter.OrganicStereoSpatialSupportMolecularAssembly.decodeSpatial_image_assembleSpatial_image
#print axioms TetraStereo.OneCenter.OrganicStereoSpatialSupportMolecularAssembly.coreBroadLedger_map_broadToRole
#print axioms TetraStereo.OneCenter.OrganicStereoSpatialSupportMolecularAssembly.witnessRepresentation_encoded_cells_differ
#print axioms TetraStereo.OneCenter.OrganicStereoSpatialSupportMolecularAssembly.witnessEncodedCells_boundary_agreement

/-! ## Kernel-authority guards for the decisive endpoints

The informational `#print axioms` lines above document the closures.  The following
`assert_kernel_only` guards make the dependency whitelist a build-time obligation: any
compiler-trust, `sorryAx`, or project axiom in these closures is rejected. -/

assert_kernel_only TetraStereo.OneCenter.OrganicStereoSpatialSupportMolecularAssembly.decodeSpatial_assembleSpatial
assert_kernel_only TetraStereo.OneCenter.OrganicStereoSpatialSupportMolecularAssembly.assembleSpatial_injective
assert_kernel_only TetraStereo.OneCenter.OrganicStereoSpatialSupportMolecularAssembly.decodeSpatial_image_assembleSpatial_image
assert_kernel_only TetraStereo.OneCenter.OrganicStereoSpatialSupportMolecularAssembly.coreBroadLedger_map_broadToRole
assert_kernel_only TetraStereo.OneCenter.OrganicStereoSpatialSupportMolecularAssembly.witnessRepresentation_encoded_cells_differ
assert_kernel_only TetraStereo.OneCenter.OrganicStereoSpatialSupportMolecularAssembly.witnessEncodedCells_boundary_agreement
