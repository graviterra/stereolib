import Mathlib.Data.Finset.Image
import TetraStereo.OneCenter.OrganicStereoFiniteClassicalDescription
import TetraStereo.OneCenter.OrganicStereoSuppliedCitationIngress

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter

/-!
# Transport of the supplied-citation satellite across an atom equivalence

`OrganicStereoSuppliedCitationIngress` builds a `SuppliedCitationSatellite V` from a bounded raw
source: P-91 annotated-name syntax, an ordered list of P-93 located assignments whose physical
units use vertices of `V` instead of raw `Nat` indices, an optional external
`OfficialDetectedUnit V`, and a composition-context interaction graph over `V`.

This module adds the missing representation-transport layer.  One equivalence `e : V ≃ W` is used
for *every* atom reference at once:

* every constructor of `SuppliedPhysicalUnit` is mapped (`atomCenter`, `bond`, ordered `axis` and
  `helix` paths, unordered `plane` members, `polyhedron` centre and positions);
* the interaction graph is relabelled with the existing
  `FiniteAtomInteractionHypergraph.relabelGraph`, and its inverse is the existing
  `relabelGraph_symm`;
* every `OfficialDetectedUnit` field is carried: `support` by `Finset.image`, `anchor?` by
  `Option.map`, and `kind`, `nodeKind?`, `nodeRootDistance?` and `initialValues` literally;
* the P-91 annotated name, including arbitrary `BaseName`, `Numbering`, `Locant`, `Prefix`
  syntax, is copied as typed metadata.  None of those types is assumed to be an atom index;
* the ordered assignment list keeps its order and multiplicity.

The transport is a genuine record-level codec: the encoded satellite has exactly the fields of
`SuppliedCitationSatellite (Fin n)`, with no hidden copy of the `V`-labelled source.  Both inverse
laws are proved as full-record equalities, together with explicit `Fin` encode/decode functions,
injectivity/bijectivity, and recovery of arbitrary sets of satellites.

What is *not* claimed: an arbitrary permutation need not preserve the policy predicate
`P93AuthorityPhysicalUnit.ValidFor` (in particular the canonical `first < second` normalisation of
a bond unit).  This is lossless *representation* transport only; semantic validity can be
recovered by decoding back and re-checking it against the original source.  The final composition
theorem passes every bounded supplied source through the canonical satellite, into `Fin n`, back,
and recovers the original record, including the optional external unit identity.
-/

namespace OrganicStereoSuppliedCitationTransport

open OrganicStereoSuppliedCitationIngress

variable {V W : Type*}
variable {BaseName Numbering Locant Prefix : Type*}

/-! ## Physical units -/

section PhysicalUnits

variable [DecidableEq V] [DecidableEq W]

/-- Map every atom reference of a supplied physical unit by one equivalence.  Constructors,
ordered path order, and unordered membership are retained; only the vertex type changes. -/
def relabelSuppliedPhysicalUnit (e : V ≃ W) :
    SuppliedPhysicalUnit V → SuppliedPhysicalUnit W
  | .atomCenter center => .atomCenter (e center)
  | .bond first second => .bond (e first) (e second)
  | .axis path => .axis (path.map e)
  | .plane members => .plane (members.image e)
  | .helix path => .helix (path.map e)
  | .polyhedron center positions => .polyhedron (e center) (positions.image e)

/-- Decode every atom reference of a supplied physical unit by the inverse equivalence. -/
def unrelabelSuppliedPhysicalUnit (e : V ≃ W) :
    SuppliedPhysicalUnit W → SuppliedPhysicalUnit V
  | .atomCenter center => .atomCenter (e.symm center)
  | .bond first second => .bond (e.symm first) (e.symm second)
  | .axis path => .axis (path.map e.symm)
  | .plane members => .plane (members.image e.symm)
  | .helix path => .helix (path.map e.symm)
  | .polyhedron center positions => .polyhedron (e.symm center) (positions.image e.symm)

/-- Decoding a relabelled unit recovers the original unit, constructor by constructor. -/
theorem unrelabelSuppliedPhysicalUnit_relabelSuppliedPhysicalUnit
    (e : V ≃ W) (unit : SuppliedPhysicalUnit V) :
    unrelabelSuppliedPhysicalUnit e (relabelSuppliedPhysicalUnit e unit) = unit := by
  cases unit with
  | atomCenter center =>
      simp [relabelSuppliedPhysicalUnit, unrelabelSuppliedPhysicalUnit]
  | bond first second =>
      simp [relabelSuppliedPhysicalUnit, unrelabelSuppliedPhysicalUnit]
  | axis path =>
      simp [relabelSuppliedPhysicalUnit, unrelabelSuppliedPhysicalUnit]
  | plane members =>
      simp [relabelSuppliedPhysicalUnit, unrelabelSuppliedPhysicalUnit, Finset.image_image]
  | helix path =>
      simp [relabelSuppliedPhysicalUnit, unrelabelSuppliedPhysicalUnit]
  | polyhedron center positions =>
      simp [relabelSuppliedPhysicalUnit, unrelabelSuppliedPhysicalUnit, Finset.image_image]

/-- Relabelling a decoded unit recovers the original unit, constructor by constructor. -/
theorem relabelSuppliedPhysicalUnit_unrelabelSuppliedPhysicalUnit
    (e : V ≃ W) (unit : SuppliedPhysicalUnit W) :
    relabelSuppliedPhysicalUnit e (unrelabelSuppliedPhysicalUnit e unit) = unit := by
  cases unit with
  | atomCenter center =>
      simp [relabelSuppliedPhysicalUnit, unrelabelSuppliedPhysicalUnit]
  | bond first second =>
      simp [relabelSuppliedPhysicalUnit, unrelabelSuppliedPhysicalUnit]
  | axis path =>
      simp [relabelSuppliedPhysicalUnit, unrelabelSuppliedPhysicalUnit]
  | plane members =>
      simp [relabelSuppliedPhysicalUnit, unrelabelSuppliedPhysicalUnit, Finset.image_image]
  | helix path =>
      simp [relabelSuppliedPhysicalUnit, unrelabelSuppliedPhysicalUnit]
  | polyhedron center positions =>
      simp [relabelSuppliedPhysicalUnit, unrelabelSuppliedPhysicalUnit, Finset.image_image]

end PhysicalUnits

/-! ## Located assignments -/

section Assignments

variable [DecidableEq V] [DecidableEq W]

/-- Relabel the physical unit of a located assignment.  The citation token and descriptor are
nomenclature data and are copied literally. -/
def relabelSuppliedLocatedAssignment (e : V ≃ W)
    (assignment : SuppliedLocatedAssignment V) : SuppliedLocatedAssignment W where
  unit := relabelSuppliedPhysicalUnit e assignment.unit
  citation := assignment.citation
  descriptor := assignment.descriptor

/-- Decode the physical unit of a located assignment, retaining citation and descriptor. -/
def unrelabelSuppliedLocatedAssignment (e : V ≃ W)
    (assignment : SuppliedLocatedAssignment W) : SuppliedLocatedAssignment V where
  unit := unrelabelSuppliedPhysicalUnit e assignment.unit
  citation := assignment.citation
  descriptor := assignment.descriptor

@[simp] theorem relabelSuppliedLocatedAssignment_unit (e : V ≃ W)
    (assignment : SuppliedLocatedAssignment V) :
    (relabelSuppliedLocatedAssignment e assignment).unit =
      relabelSuppliedPhysicalUnit e assignment.unit := rfl

@[simp] theorem relabelSuppliedLocatedAssignment_citation (e : V ≃ W)
    (assignment : SuppliedLocatedAssignment V) :
    (relabelSuppliedLocatedAssignment e assignment).citation = assignment.citation := rfl

@[simp] theorem relabelSuppliedLocatedAssignment_descriptor (e : V ≃ W)
    (assignment : SuppliedLocatedAssignment V) :
    (relabelSuppliedLocatedAssignment e assignment).descriptor = assignment.descriptor := rfl

/-- Decoding a relabelled assignment recovers the original assignment exactly. -/
theorem unrelabelSuppliedLocatedAssignment_relabelSuppliedLocatedAssignment
    (e : V ≃ W) (assignment : SuppliedLocatedAssignment V) :
    unrelabelSuppliedLocatedAssignment e
        (relabelSuppliedLocatedAssignment e assignment) = assignment := by
  rcases assignment with ⟨unit, citation, descriptor⟩
  change ({ unit := unrelabelSuppliedPhysicalUnit e
              (relabelSuppliedPhysicalUnit e unit),
            citation := citation,
            descriptor := descriptor } : SuppliedLocatedAssignment V) =
    { unit := unit, citation := citation, descriptor := descriptor }
  rw [unrelabelSuppliedPhysicalUnit_relabelSuppliedPhysicalUnit e unit]

/-- Relabelling a decoded assignment recovers the original assignment exactly. -/
theorem relabelSuppliedLocatedAssignment_unrelabelSuppliedLocatedAssignment
    (e : V ≃ W) (assignment : SuppliedLocatedAssignment W) :
    relabelSuppliedLocatedAssignment e
        (unrelabelSuppliedLocatedAssignment e assignment) = assignment := by
  rcases assignment with ⟨unit, citation, descriptor⟩
  change ({ unit := relabelSuppliedPhysicalUnit e
              (unrelabelSuppliedPhysicalUnit e unit),
            citation := citation,
            descriptor := descriptor } : SuppliedLocatedAssignment W) =
    { unit := unit, citation := citation, descriptor := descriptor }
  rw [relabelSuppliedPhysicalUnit_unrelabelSuppliedPhysicalUnit e unit]

/-- Relabel an ordered list of located assignments, preserving order and multiplicity. -/
def relabelSuppliedAssignments (e : V ≃ W)
    (assignments : List (SuppliedLocatedAssignment V)) :
    List (SuppliedLocatedAssignment W) :=
  assignments.map (relabelSuppliedLocatedAssignment e)

/-- Decode an ordered list of located assignments, preserving order and multiplicity. -/
def unrelabelSuppliedAssignments (e : V ≃ W)
    (assignments : List (SuppliedLocatedAssignment W)) :
    List (SuppliedLocatedAssignment V) :=
  assignments.map (unrelabelSuppliedLocatedAssignment e)

@[simp] theorem relabelSuppliedAssignments_length (e : V ≃ W)
    (assignments : List (SuppliedLocatedAssignment V)) :
    (relabelSuppliedAssignments e assignments).length = assignments.length := by
  simp [relabelSuppliedAssignments]

@[simp] theorem unrelabelSuppliedAssignments_length (e : V ≃ W)
    (assignments : List (SuppliedLocatedAssignment W)) :
    (unrelabelSuppliedAssignments e assignments).length = assignments.length := by
  simp [unrelabelSuppliedAssignments]

/-- Citation tokens are copied literally, in order and multiplicity. -/
theorem relabelSuppliedAssignments_citations (e : V ≃ W)
    (assignments : List (SuppliedLocatedAssignment V)) :
    (relabelSuppliedAssignments e assignments).map (fun assignment => assignment.citation) =
      assignments.map (fun assignment => assignment.citation) := by
  unfold relabelSuppliedAssignments
  rw [List.map_map]
  apply List.map_congr_left
  intro assignment _
  rfl

/-- Descriptors are copied literally, in order and multiplicity. -/
theorem relabelSuppliedAssignments_descriptors (e : V ≃ W)
    (assignments : List (SuppliedLocatedAssignment V)) :
    (relabelSuppliedAssignments e assignments).map (fun assignment => assignment.descriptor) =
      assignments.map (fun assignment => assignment.descriptor) := by
  unfold relabelSuppliedAssignments
  rw [List.map_map]
  apply List.map_congr_left
  intro assignment _
  rfl

/-- Decoding a relabelled list recovers the original list exactly. -/
theorem unrelabelSuppliedAssignments_relabelSuppliedAssignments
    (e : V ≃ W) (assignments : List (SuppliedLocatedAssignment V)) :
    unrelabelSuppliedAssignments e (relabelSuppliedAssignments e assignments) =
      assignments := by
  unfold unrelabelSuppliedAssignments relabelSuppliedAssignments
  rw [List.map_map]
  trans assignments.map id
  · apply List.map_congr_left
    intro assignment _
    exact unrelabelSuppliedLocatedAssignment_relabelSuppliedLocatedAssignment e assignment
  · exact List.map_id assignments

/-- Relabelling a decoded list recovers the original list exactly. -/
theorem relabelSuppliedAssignments_unrelabelSuppliedAssignments
    (e : V ≃ W) (assignments : List (SuppliedLocatedAssignment W)) :
    relabelSuppliedAssignments e (unrelabelSuppliedAssignments e assignments) =
      assignments := by
  unfold unrelabelSuppliedAssignments relabelSuppliedAssignments
  rw [List.map_map]
  trans assignments.map id
  · apply List.map_congr_left
    intro assignment _
    exact relabelSuppliedLocatedAssignment_unrelabelSuppliedLocatedAssignment e assignment
  · exact List.map_id assignments

end Assignments

/-! ## External detected units

`OfficialDetectedUnit` has exactly six fields.  `support` and `anchor?` carry vertices; the other
four are copied literally.  In particular `initialValues` are descriptor metadata, not physical
evidence, and are never reinterpreted. -/

section DetectedUnits

variable [DecidableEq V] [DecidableEq W]

/-- Relabel the vertex-bearing fields of an external detected unit and copy all metadata. -/
def relabelOfficialDetectedUnit (e : V ≃ W)
    (unit : OfficialDetectedUnit V) : OfficialDetectedUnit W where
  kind := unit.kind
  support := unit.support.image e
  anchor? := unit.anchor?.map e
  nodeKind? := unit.nodeKind?
  nodeRootDistance? := unit.nodeRootDistance?
  initialValues := unit.initialValues

/-- Decode the vertex-bearing fields of an external detected unit and copy all metadata. -/
def unrelabelOfficialDetectedUnit (e : V ≃ W)
    (unit : OfficialDetectedUnit W) : OfficialDetectedUnit V where
  kind := unit.kind
  support := unit.support.image e.symm
  anchor? := unit.anchor?.map e.symm
  nodeKind? := unit.nodeKind?
  nodeRootDistance? := unit.nodeRootDistance?
  initialValues := unit.initialValues

@[simp] theorem relabelOfficialDetectedUnit_kind (e : V ≃ W)
    (unit : OfficialDetectedUnit V) :
    (relabelOfficialDetectedUnit e unit).kind = unit.kind := rfl

@[simp] theorem relabelOfficialDetectedUnit_support (e : V ≃ W)
    (unit : OfficialDetectedUnit V) :
    (relabelOfficialDetectedUnit e unit).support = unit.support.image e := rfl

@[simp] theorem relabelOfficialDetectedUnit_anchor? (e : V ≃ W)
    (unit : OfficialDetectedUnit V) :
    (relabelOfficialDetectedUnit e unit).anchor? = unit.anchor?.map e := rfl

@[simp] theorem relabelOfficialDetectedUnit_nodeKind? (e : V ≃ W)
    (unit : OfficialDetectedUnit V) :
    (relabelOfficialDetectedUnit e unit).nodeKind? = unit.nodeKind? := rfl

@[simp] theorem relabelOfficialDetectedUnit_nodeRootDistance? (e : V ≃ W)
    (unit : OfficialDetectedUnit V) :
    (relabelOfficialDetectedUnit e unit).nodeRootDistance? = unit.nodeRootDistance? := rfl

@[simp] theorem relabelOfficialDetectedUnit_initialValues (e : V ≃ W)
    (unit : OfficialDetectedUnit V) :
    (relabelOfficialDetectedUnit e unit).initialValues = unit.initialValues := rfl

@[simp] theorem unrelabelOfficialDetectedUnit_kind (e : V ≃ W)
    (unit : OfficialDetectedUnit W) :
    (unrelabelOfficialDetectedUnit e unit).kind = unit.kind := rfl

@[simp] theorem unrelabelOfficialDetectedUnit_support (e : V ≃ W)
    (unit : OfficialDetectedUnit W) :
    (unrelabelOfficialDetectedUnit e unit).support = unit.support.image e.symm := rfl

@[simp] theorem unrelabelOfficialDetectedUnit_anchor? (e : V ≃ W)
    (unit : OfficialDetectedUnit W) :
    (unrelabelOfficialDetectedUnit e unit).anchor? = unit.anchor?.map e.symm := rfl

@[simp] theorem unrelabelOfficialDetectedUnit_nodeKind? (e : V ≃ W)
    (unit : OfficialDetectedUnit W) :
    (unrelabelOfficialDetectedUnit e unit).nodeKind? = unit.nodeKind? := rfl

@[simp] theorem unrelabelOfficialDetectedUnit_nodeRootDistance? (e : V ≃ W)
    (unit : OfficialDetectedUnit W) :
    (unrelabelOfficialDetectedUnit e unit).nodeRootDistance? = unit.nodeRootDistance? := rfl

@[simp] theorem unrelabelOfficialDetectedUnit_initialValues (e : V ≃ W)
    (unit : OfficialDetectedUnit W) :
    (unrelabelOfficialDetectedUnit e unit).initialValues = unit.initialValues := rfl

/-- Support cardinality is preserved: relabelling does not merge or drop detected vertices. -/
theorem relabelOfficialDetectedUnit_support_card (e : V ≃ W)
    (unit : OfficialDetectedUnit V) :
    (relabelOfficialDetectedUnit e unit).support.card = unit.support.card := by
  rw [relabelOfficialDetectedUnit_support]
  exact Finset.card_image_of_injective unit.support e.injective

/-- Exact support membership after relabelling. -/
theorem relabelOfficialDetectedUnit_support_mem_iff (e : V ≃ W)
    (unit : OfficialDetectedUnit V) (atom : W) :
    atom ∈ (relabelOfficialDetectedUnit e unit).support ↔
      e.symm atom ∈ unit.support := by
  rw [relabelOfficialDetectedUnit_support, Finset.mem_image]
  constructor
  · rintro ⟨original, member, rfl⟩
    simpa using member
  · intro member
    exact ⟨e.symm atom, member, by simp⟩

/-- The anchor slot is occupied exactly when the source anchor slot is occupied. -/
theorem relabelOfficialDetectedUnit_anchor?_isSome (e : V ≃ W)
    (unit : OfficialDetectedUnit V) :
    (relabelOfficialDetectedUnit e unit).anchor?.isSome = unit.anchor?.isSome := by
  rw [relabelOfficialDetectedUnit_anchor?]
  cases unit.anchor? <;> rfl

/-- Absence of an anchor is preserved and reflected. -/
theorem relabelOfficialDetectedUnit_anchor?_eq_none_iff (e : V ≃ W)
    (unit : OfficialDetectedUnit V) :
    (relabelOfficialDetectedUnit e unit).anchor? = none ↔ unit.anchor? = none := by
  rw [relabelOfficialDetectedUnit_anchor?]
  cases unit.anchor? <;> simp

/-- Full-record inverse of external-unit relabelling. -/
theorem unrelabelOfficialDetectedUnit_relabelOfficialDetectedUnit
    (e : V ≃ W) (unit : OfficialDetectedUnit V) :
    unrelabelOfficialDetectedUnit e (relabelOfficialDetectedUnit e unit) = unit := by
  cases unit with
  | mk kind support anchor? nodeKind? nodeRootDistance? initialValues =>
      simp only [relabelOfficialDetectedUnit, unrelabelOfficialDetectedUnit]
      rw [show (support.image e).image e.symm = support from by
        rw [Finset.image_image]
        simp]
      rw [show (anchor?.map e).map e.symm = anchor? from by
        rw [Option.map_map]
        simp]

/-- Full-record inverse of external-unit decoding. -/
theorem relabelOfficialDetectedUnit_unrelabelOfficialDetectedUnit
    (e : V ≃ W) (unit : OfficialDetectedUnit W) :
    relabelOfficialDetectedUnit e (unrelabelOfficialDetectedUnit e unit) = unit := by
  cases unit with
  | mk kind support anchor? nodeKind? nodeRootDistance? initialValues =>
      simp only [relabelOfficialDetectedUnit, unrelabelOfficialDetectedUnit]
      rw [show (support.image e.symm).image e = support from by
        rw [Finset.image_image]
        simp]
      rw [show (anchor?.map e.symm).map e = anchor? from by
        rw [Option.map_map]
        simp]

/-- The optional identity slot round-trips exactly, including absence versus presence. -/
theorem unrelabelExternalIdentity?_relabelExternalIdentity? (e : V ≃ W)
    (identity? : Option (OfficialDetectedUnit V)) :
    (identity?.map (relabelOfficialDetectedUnit e)).map
        (unrelabelOfficialDetectedUnit e) = identity? := by
  cases identity? with
  | none => rfl
  | some unit => simp [unrelabelOfficialDetectedUnit_relabelOfficialDetectedUnit e unit]

/-- The optional identity slot round-trips exactly in the other direction. -/
theorem relabelExternalIdentity?_unrelabelExternalIdentity? (e : V ≃ W)
    (identity? : Option (OfficialDetectedUnit W)) :
    (identity?.map (unrelabelOfficialDetectedUnit e)).map
        (relabelOfficialDetectedUnit e) = identity? := by
  cases identity? with
  | none => rfl
  | some unit => simp [relabelOfficialDetectedUnit_unrelabelOfficialDetectedUnit e unit]

end DetectedUnits

/-! ## Whole satellites -/

section Satellites

variable [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W]

/-- Relabel a whole supplied-citation satellite by one atom equivalence.

The graph is relabelled by the existing `relabelGraph`; the P-91 annotated name is copied
literally; the ordered assignment list is mapped in order; and the optional external identity is
mapped fieldwise.  No `V`-labelled source is stored in the result. -/
def relabelSuppliedSatellite (e : V ≃ W)
    (satellite : SuppliedCitationSatellite V BaseName Numbering Locant Prefix) :
    SuppliedCitationSatellite W BaseName Numbering Locant Prefix where
  graph := relabelGraph e satellite.graph
  annotatedName := satellite.annotatedName
  assignments := relabelSuppliedAssignments e satellite.assignments
  externalIdentity? := satellite.externalIdentity?.map (relabelOfficialDetectedUnit e)

/-- Decode a whole supplied-citation satellite using the inverse equivalence. -/
def unrelabelSuppliedSatellite (e : V ≃ W)
    (satellite : SuppliedCitationSatellite W BaseName Numbering Locant Prefix) :
    SuppliedCitationSatellite V BaseName Numbering Locant Prefix where
  graph := relabelGraph e.symm satellite.graph
  annotatedName := satellite.annotatedName
  assignments := unrelabelSuppliedAssignments e satellite.assignments
  externalIdentity? := satellite.externalIdentity?.map (unrelabelOfficialDetectedUnit e)

@[simp] theorem relabelSuppliedSatellite_graph (e : V ≃ W)
    (satellite : SuppliedCitationSatellite V BaseName Numbering Locant Prefix) :
    (relabelSuppliedSatellite e satellite).graph = relabelGraph e satellite.graph := rfl

@[simp] theorem relabelSuppliedSatellite_annotatedName (e : V ≃ W)
    (satellite : SuppliedCitationSatellite V BaseName Numbering Locant Prefix) :
    (relabelSuppliedSatellite e satellite).annotatedName = satellite.annotatedName := rfl

@[simp] theorem relabelSuppliedSatellite_assignments (e : V ≃ W)
    (satellite : SuppliedCitationSatellite V BaseName Numbering Locant Prefix) :
    (relabelSuppliedSatellite e satellite).assignments =
      relabelSuppliedAssignments e satellite.assignments := rfl

@[simp] theorem relabelSuppliedSatellite_externalIdentity? (e : V ≃ W)
    (satellite : SuppliedCitationSatellite V BaseName Numbering Locant Prefix) :
    (relabelSuppliedSatellite e satellite).externalIdentity? =
      satellite.externalIdentity?.map (relabelOfficialDetectedUnit e) := rfl

@[simp] theorem unrelabelSuppliedSatellite_graph (e : V ≃ W)
    (satellite : SuppliedCitationSatellite W BaseName Numbering Locant Prefix) :
    (unrelabelSuppliedSatellite e satellite).graph = relabelGraph e.symm satellite.graph := rfl

@[simp] theorem unrelabelSuppliedSatellite_annotatedName (e : V ≃ W)
    (satellite : SuppliedCitationSatellite W BaseName Numbering Locant Prefix) :
    (unrelabelSuppliedSatellite e satellite).annotatedName = satellite.annotatedName := rfl

@[simp] theorem unrelabelSuppliedSatellite_assignments (e : V ≃ W)
    (satellite : SuppliedCitationSatellite W BaseName Numbering Locant Prefix) :
    (unrelabelSuppliedSatellite e satellite).assignments =
      unrelabelSuppliedAssignments e satellite.assignments := rfl

@[simp] theorem unrelabelSuppliedSatellite_externalIdentity? (e : V ≃ W)
    (satellite : SuppliedCitationSatellite W BaseName Numbering Locant Prefix) :
    (unrelabelSuppliedSatellite e satellite).externalIdentity? =
      satellite.externalIdentity?.map (unrelabelOfficialDetectedUnit e) := rfl

/-- Full-record extensionality for supplied-citation satellites.  The graph, annotated name,
ordered assignment list and optional external identity determine the record. -/
theorem suppliedCitationSatellite_ext
    (first second : SuppliedCitationSatellite V BaseName Numbering Locant Prefix)
    (graph : first.graph = second.graph)
    (annotatedName : first.annotatedName = second.annotatedName)
    (assignments : first.assignments = second.assignments)
    (externalIdentity? : first.externalIdentity? = second.externalIdentity?) :
    first = second := by
  rcases first with ⟨firstGraph, firstName, firstAssignments, firstIdentity⟩
  rcases second with ⟨secondGraph, secondName, secondAssignments, secondIdentity⟩
  change firstGraph = secondGraph at graph
  change firstName = secondName at annotatedName
  change firstAssignments = secondAssignments at assignments
  change firstIdentity = secondIdentity at externalIdentity?
  subst graph
  subst annotatedName
  subst assignments
  subst externalIdentity?
  rfl

/-- Full-record inverse: decoding a relabelled satellite recovers the original satellite. -/
theorem unrelabelSuppliedSatellite_relabelSuppliedSatellite (e : V ≃ W)
    (satellite : SuppliedCitationSatellite V BaseName Numbering Locant Prefix) :
    unrelabelSuppliedSatellite e (relabelSuppliedSatellite e satellite) = satellite := by
  rcases satellite with ⟨graph, annotatedName, assignments, externalIdentity?⟩
  apply suppliedCitationSatellite_ext
  · exact relabelGraph_symm e graph
  · rfl
  · exact unrelabelSuppliedAssignments_relabelSuppliedAssignments e assignments
  · exact unrelabelExternalIdentity?_relabelExternalIdentity? e externalIdentity?

/-- Full-record inverse: relabelling a decoded satellite recovers the original satellite. -/
theorem relabelSuppliedSatellite_unrelabelSuppliedSatellite (e : V ≃ W)
    (satellite : SuppliedCitationSatellite W BaseName Numbering Locant Prefix) :
    relabelSuppliedSatellite e (unrelabelSuppliedSatellite e satellite) = satellite := by
  rcases satellite with ⟨graph, annotatedName, assignments, externalIdentity?⟩
  apply suppliedCitationSatellite_ext
  · exact relabelGraph_symm e.symm graph
  · rfl
  · exact relabelSuppliedAssignments_unrelabelSuppliedAssignments e assignments
  · exact relabelExternalIdentity?_unrelabelExternalIdentity? e externalIdentity?

/-! ### Compatibility with the existing graph encoding

Relabelling by an equivalence and then encoding at any enumeration is the same as encoding the
source at the composite enumeration.  This records that the graph channel uses the repository's
existing relabel/encoding API and does not introduce a second notion of atom identity. -/

/-- Atom lookup after graph relabelling: the encoded atom data is the source atom data at the
composite enumerated label. -/
theorem relabelGraph_encode_atomAt (e : V ≃ W)
    (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : W ≃ Fin (Fintype.card W))
    (index : Fin (Fintype.card W)) :
    listGet? ((relabelGraph e graph).encode enumeration).atoms index.val =
      some (graph.atomData (e.symm (enumeration.symm index))) := by
  rw [FiniteAtomInteractionHypergraph.encode_atomAt]
  rfl

end Satellites

/-! ## Explicit `Fin`-encoding

The codec below is the canonical use of the transport layer: choose an enumeration
`enumeration : V ≃ Fin n`, encode the whole satellite into `Fin n`, and decode using only that
enumeration and the encoded payload. -/

section FinEncoding

variable [DecidableEq V] [Fintype V]
variable {n : ℕ}

/-- Encode a whole satellite into `Fin n` using the given equivalence. -/
def encodeFin (enumeration : V ≃ Fin n)
    (satellite : SuppliedCitationSatellite V BaseName Numbering Locant Prefix) :
    SuppliedCitationSatellite (Fin n) BaseName Numbering Locant Prefix :=
  relabelSuppliedSatellite enumeration satellite

/-- Decode a whole satellite from `Fin n` using the inverse of the given equivalence.  No original
`V`-labelled satellite is consulted. -/
def decodeFin (enumeration : V ≃ Fin n)
    (satellite : SuppliedCitationSatellite (Fin n) BaseName Numbering Locant Prefix) :
    SuppliedCitationSatellite V BaseName Numbering Locant Prefix :=
  unrelabelSuppliedSatellite enumeration satellite

@[simp] theorem encodeFin_graph (enumeration : V ≃ Fin n)
    (satellite : SuppliedCitationSatellite V BaseName Numbering Locant Prefix) :
    (encodeFin enumeration satellite).graph =
      relabelGraph enumeration satellite.graph := rfl

@[simp] theorem encodeFin_annotatedName (enumeration : V ≃ Fin n)
    (satellite : SuppliedCitationSatellite V BaseName Numbering Locant Prefix) :
    (encodeFin enumeration satellite).annotatedName = satellite.annotatedName := rfl

@[simp] theorem encodeFin_assignments (enumeration : V ≃ Fin n)
    (satellite : SuppliedCitationSatellite V BaseName Numbering Locant Prefix) :
    (encodeFin enumeration satellite).assignments =
      relabelSuppliedAssignments enumeration satellite.assignments := rfl

@[simp] theorem encodeFin_externalIdentity? (enumeration : V ≃ Fin n)
    (satellite : SuppliedCitationSatellite V BaseName Numbering Locant Prefix) :
    (encodeFin enumeration satellite).externalIdentity? =
      satellite.externalIdentity?.map (relabelOfficialDetectedUnit enumeration) := rfl

@[simp] theorem decodeFin_graph (enumeration : V ≃ Fin n)
    (satellite : SuppliedCitationSatellite (Fin n) BaseName Numbering Locant Prefix) :
    (decodeFin enumeration satellite).graph =
      relabelGraph enumeration.symm satellite.graph := rfl

@[simp] theorem decodeFin_annotatedName (enumeration : V ≃ Fin n)
    (satellite : SuppliedCitationSatellite (Fin n) BaseName Numbering Locant Prefix) :
    (decodeFin enumeration satellite).annotatedName = satellite.annotatedName := rfl

@[simp] theorem decodeFin_assignments (enumeration : V ≃ Fin n)
    (satellite : SuppliedCitationSatellite (Fin n) BaseName Numbering Locant Prefix) :
    (decodeFin enumeration satellite).assignments =
      unrelabelSuppliedAssignments enumeration satellite.assignments := rfl

@[simp] theorem decodeFin_externalIdentity? (enumeration : V ≃ Fin n)
    (satellite : SuppliedCitationSatellite (Fin n) BaseName Numbering Locant Prefix) :
    (decodeFin enumeration satellite).externalIdentity? =
      satellite.externalIdentity?.map (unrelabelOfficialDetectedUnit enumeration) := rfl

/-- Decoding an encoded satellite recovers it exactly. -/
@[simp] theorem decodeFin_encodeFin (enumeration : V ≃ Fin n)
    (satellite : SuppliedCitationSatellite V BaseName Numbering Locant Prefix) :
    decodeFin enumeration (encodeFin enumeration satellite) = satellite :=
  unrelabelSuppliedSatellite_relabelSuppliedSatellite enumeration satellite

/-- Re-encoding a decoded payload recovers it exactly. -/
@[simp] theorem encodeFin_decodeFin (enumeration : V ≃ Fin n)
    (satellite : SuppliedCitationSatellite (Fin n) BaseName Numbering Locant Prefix) :
    encodeFin enumeration (decodeFin enumeration satellite) = satellite :=
  relabelSuppliedSatellite_unrelabelSuppliedSatellite enumeration satellite

/-- The explicit `Fin` encoding is injective. -/
theorem encodeFin_injective (enumeration : V ≃ Fin n) :
    Function.Injective
      (fun satellite : SuppliedCitationSatellite V BaseName Numbering Locant Prefix =>
        encodeFin enumeration satellite) := by
  intro first second equal
  calc
    first = decodeFin enumeration (encodeFin enumeration first) :=
      (decodeFin_encodeFin enumeration first).symm
    _ = decodeFin enumeration (encodeFin enumeration second) :=
      congrArg
        (fun satellite : SuppliedCitationSatellite (Fin n) BaseName Numbering Locant Prefix =>
          decodeFin enumeration satellite)
        equal
    _ = second := decodeFin_encodeFin enumeration second

/-- The explicit `Fin` encoding is bijective onto the encoded schema. -/
theorem encodeFin_bijective (enumeration : V ≃ Fin n) :
    Function.Bijective
      (fun satellite : SuppliedCitationSatellite V BaseName Numbering Locant Prefix =>
        encodeFin enumeration satellite) :=
  ⟨encodeFin_injective enumeration, fun encoded =>
    ⟨decodeFin enumeration encoded, encodeFin_decodeFin enumeration encoded⟩⟩

/-- The image of an arbitrary set of satellites under the `Fin` encoding. -/
def encodeFinSet (enumeration : V ≃ Fin n)
    (satellites : Set (SuppliedCitationSatellite V BaseName Numbering Locant Prefix)) :
    Set (SuppliedCitationSatellite (Fin n) BaseName Numbering Locant Prefix) :=
  encodeFin enumeration '' satellites

/-- Arbitrary-set round trip: decoding the encoded image of any set of satellites gives back
exactly that set.  Because the operation acts on whole records, graph, syntax, assignments and
external identity are recovered together. -/
theorem decodeFin_image_encodeFinSet (enumeration : V ≃ Fin n)
    (satellites : Set (SuppliedCitationSatellite V BaseName Numbering Locant Prefix)) :
    decodeFin enumeration '' encodeFinSet enumeration satellites = satellites := by
  rw [encodeFinSet, Set.image_image]
  have composed :
      (fun satellite : SuppliedCitationSatellite V BaseName Numbering Locant Prefix =>
        decodeFin enumeration (encodeFin enumeration satellite)) = id := by
    funext satellite
    exact decodeFin_encodeFin enumeration satellite
  change (fun satellite : SuppliedCitationSatellite V BaseName Numbering Locant Prefix =>
      decodeFin enumeration (encodeFin enumeration satellite)) '' satellites = satellites
  rw [composed, Set.image_id]

end FinEncoding

/-! ## Composition with the supplied-source adapter

The ingress adapter `adapt` turns a bounded raw source into a satellite over `V`; the codec above
then moves that satellite into `Fin n` and back without loss.  The composition recovers the raw
source exactly.  An explicit corollary records recovery of the external unit identity slot. -/

section SourceComposition

variable [DecidableEq V] [Fintype V]
variable {n : ℕ}

/-- Every bounded supplied source passes through the canonical satellite, is encoded into `Fin n`
and decoded, and is recovered exactly — graph context aside, which the raw source does not store. -/
theorem suppliedSource_encodeFin_decodeFin_adapt
    (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin n)
    (raw : RawSuppliedCitationSource V BaseName Numbering Locant Prefix)
    (bounded : ∀ assignment ∈ raw.assignments,
      P93AuthorityPhysicalUnit.BoundedIn n assignment.unit) :
    suppliedSource enumeration
      (decodeFin enumeration (encodeFin enumeration
        (adapt graph enumeration raw bounded))) = raw := by
  rw [decodeFin_encodeFin]
  exact suppliedSource_adapt graph enumeration raw bounded

/-- The external identity carried by the canonical satellite is exactly the relabelled raw
identity: support and anchor are mapped, while kind, node metadata and initial descriptor values
are copied. -/
theorem encodeFin_adapt_externalIdentity?
    (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin n)
    (raw : RawSuppliedCitationSource V BaseName Numbering Locant Prefix)
    (bounded : ∀ assignment ∈ raw.assignments,
      P93AuthorityPhysicalUnit.BoundedIn n assignment.unit) :
    (encodeFin enumeration (adapt graph enumeration raw bounded)).externalIdentity? =
      raw.externalIdentity?.map (relabelOfficialDetectedUnit enumeration) := by
  rw [encodeFin_externalIdentity?, adapt_externalIdentity?]

/-- Recovery of the optional external unit identity through the full transport composition. -/
theorem suppliedSource_encodeFin_decodeFin_adapt_externalIdentity?
    (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin n)
    (raw : RawSuppliedCitationSource V BaseName Numbering Locant Prefix)
    (bounded : ∀ assignment ∈ raw.assignments,
      P93AuthorityPhysicalUnit.BoundedIn n assignment.unit) :
    (suppliedSource enumeration
      (decodeFin enumeration (encodeFin enumeration
        (adapt graph enumeration raw bounded)))).externalIdentity? =
      raw.externalIdentity? := by
  rw [suppliedSource_encodeFin_decodeFin_adapt graph enumeration raw bounded]

end SourceComposition

end OrganicStereoSuppliedCitationTransport

end TetraStereo.OneCenter
