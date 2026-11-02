import TetraStereo.OneCenter.P91DescriptorSyntax
import TetraStereo.OneCenter.IUPACP93AuthorityConfigurationCarrier
import TetraStereo.OneCenter.OrganicStereoFiniteEncoding
import TetraStereo.OneCenter.OfficialNoncenterDetectors

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Ingress of externally supplied citation syntax and physical-unit associations

This module is an ingress/satellite bridge for data supplied from outside the
repository: a P-91 descriptor annotation together with P-93 located
assignments of physical stereochemical units to descriptor citations.

The two halves of the source record play different roles.

* The P-91 portion (`BlueBookP91.AnnotatedName`, hence base name, numbering,
  every `DescriptorCitation` with its optional locant, target, citation
  position and `parenthesizedAndHyphenated` flag, and the ordered citation
  list) is itself the intended output of the bridge.  It is therefore retained
  literally, including the order and multiplicity of citations.
* The P-93 portion contains atom-indexed physical units.  These are genuinely
  relabelled from the source's raw `Nat` atom indices to an arbitrary finite
  vertex type `V`, and decoded back.  Citation components (`value`, `primes`)
  are nomenclature data, not atom indices, so they are retained literally.
* The optional `OfficialDetectedUnit V` identity slot is external metadata.
  It is carried through unchanged, is allowed to be absent, and absence is
  distinct from presence of an empty identity.  Detector `initialValues` are
  not turned into physical evidence.

Nothing here asserts that a supplied descriptor is chemically correct, that a
citation is authorised, or that a list of constructors is exhaustive for
chemistry.  The only recovery claim is exact recovery of the supplied source
record.

## Scope of the relabelling result

Only the physical-unit atom references are relabelled.  In particular this
does *not* claim that an arbitrary relabelling preserves the policy-dependent
`P93AuthorityPhysicalUnit.ValidFor` predicate: its bond normalisation
`first < second` is not invariant under an arbitrary equivalence `V ≃ Fin n`.
Representation and boundedness are kept separate from that policy predicate.
-/

namespace OrganicStereoSuppliedCitationIngress

variable {V : Type*}
variable {n : ℕ}

/-! ## Relabelling finitely many atoms -/

section FiniteRelabel

/-- The raw atom index of `atom` under a chosen enumeration of `V`. -/
def encodeAtom (enumeration : V ≃ Fin n) (atom : V) : Nat :=
  (enumeration atom).val

/-- The atom of `V` with raw index `value`, provided `value` is in range. -/
def decodeAtom (enumeration : V ≃ Fin n) (value : Nat) (bound : value < n) : V :=
  enumeration.symm ⟨value, bound⟩

@[simp]
theorem encodeAtom_decodeAtom (enumeration : V ≃ Fin n) (value : Nat)
    (bound : value < n) :
    encodeAtom enumeration (decodeAtom enumeration value bound) = value := by
  simp [encodeAtom, decodeAtom]

theorem decodeAtom_encodeAtom (enumeration : V ≃ Fin n) (atom : V)
    (bound : encodeAtom enumeration atom < n) :
    decodeAtom enumeration (encodeAtom enumeration atom) bound = atom := by
  simp only [decodeAtom, encodeAtom]
  have finEq : (⟨(enumeration atom).val, bound⟩ : Fin n) = enumeration atom :=
    Fin.ext rfl
  rw [finEq, Equiv.symm_apply_apply]

theorem encodeAtom_lt (enumeration : V ≃ Fin n) (atom : V) :
    encodeAtom enumeration atom < n :=
  (enumeration atom).isLt

theorem encodeAtom_injective (enumeration : V ≃ Fin n) :
    Function.Injective (encodeAtom enumeration) := by
  intro first second equal
  exact enumeration.injective (Fin.ext equal)

/-! ### Ordered lists of atom indices (axis and helix paths) -/

/-- Relabel an ordered list of raw atom indices into `V`. -/
def relabelList (enumeration : V ≃ Fin n) (values : List Nat)
    (bounded : ∀ value ∈ values, value < n) : List V :=
  values.attach.map fun value =>
    decodeAtom enumeration value.1 (bounded value.1 value.2)

/-- Raw atom indices of an ordered list of atoms of `V`. -/
def unrelabelList (enumeration : V ≃ Fin n) (values : List V) : List Nat :=
  values.map (encodeAtom enumeration)

@[simp]
theorem relabelList_length (enumeration : V ≃ Fin n) (values : List Nat)
    (bounded : ∀ value ∈ values, value < n) :
    (relabelList enumeration values bounded).length = values.length := by
  simp [relabelList]

@[simp]
theorem unrelabelList_length (enumeration : V ≃ Fin n) (values : List V) :
    (unrelabelList enumeration values).length = values.length := by
  simp [unrelabelList]

theorem unrelabelList_bounded (enumeration : V ≃ Fin n) (values : List V) :
    ∀ value ∈ unrelabelList enumeration values, value < n := by
  intro value member
  rw [unrelabelList, List.mem_map] at member
  rcases member with ⟨atom, _atomMember, rfl⟩
  exact encodeAtom_lt enumeration atom

theorem unrelabelList_relabelList (enumeration : V ≃ Fin n) (values : List Nat)
    (bounded : ∀ value ∈ values, value < n) :
    unrelabelList enumeration (relabelList enumeration values bounded) = values := by
  unfold unrelabelList relabelList
  rw [List.map_map]
  trans values.attach.map Subtype.val
  · apply List.map_congr_left
    intro value _
    exact encodeAtom_decodeAtom enumeration value.1 (bounded value.1 value.2)
  · exact List.attach_map_subtype_val values

theorem relabelList_unrelabelList (enumeration : V ≃ Fin n) (values : List V) :
    relabelList enumeration (unrelabelList enumeration values)
        (unrelabelList_bounded enumeration values) = values := by
  unfold relabelList unrelabelList
  rw [List.attach_map, List.map_map]
  trans values.attach.map Subtype.val
  · apply List.map_congr_left
    intro value _
    exact decodeAtom_encodeAtom enumeration value.1 _
  · exact List.attach_map_subtype_val values

/-! ### Finite sets of atom indices (plane and polyhedron positions) -/

/-- Raw atom indices of a finite set of atoms of `V`. -/
def unrelabelFinset (enumeration : V ≃ Fin n) (values : Finset V) : Finset Nat :=
  values.image (encodeAtom enumeration)

@[simp]
theorem unrelabelFinset_bounded (enumeration : V ≃ Fin n) (values : Finset V) :
    ∀ value ∈ unrelabelFinset enumeration values, value < n := by
  intro value member
  rw [unrelabelFinset, Finset.mem_image] at member
  rcases member with ⟨atom, _atomMember, rfl⟩
  exact encodeAtom_lt enumeration atom

section FiniteFinsetRelabel

variable [DecidableEq V]

/-- Relabel a finite set of raw atom indices into `V`. -/
def relabelFinset (enumeration : V ≃ Fin n) (values : Finset Nat)
    (bounded : ∀ value ∈ values, value < n) : Finset V :=
  values.attach.image fun value =>
    decodeAtom enumeration value.1 (bounded value.1 value.2)

theorem unrelabelFinset_relabelFinset (enumeration : V ≃ Fin n) (values : Finset Nat)
    (bounded : ∀ value ∈ values, value < n) :
    unrelabelFinset enumeration (relabelFinset enumeration values bounded) = values := by
  ext value
  rw [unrelabelFinset, Finset.mem_image]
  constructor
  · rintro ⟨imageValue, imageMember, encodeEq⟩
    rw [relabelFinset, Finset.mem_image] at imageMember
    rcases imageMember with ⟨attached, _attachedMember, decodeEq⟩
    have valEq : attached.1 = value := by
      calc
        attached.1 =
            encodeAtom enumeration (decodeAtom enumeration attached.1
              (bounded attached.1 attached.2)) :=
          (encodeAtom_decodeAtom enumeration attached.1
            (bounded attached.1 attached.2)).symm
        _ = encodeAtom enumeration imageValue := by rw [decodeEq]
        _ = value := encodeEq
    simpa [valEq] using attached.2
  · intro valueMember
    refine ⟨decodeAtom enumeration value (bounded value valueMember), ?_,
      encodeAtom_decodeAtom enumeration value (bounded value valueMember)⟩
    exact Finset.mem_image_of_mem _
      (Finset.mem_attach values ⟨value, valueMember⟩)

theorem relabelFinset_unrelabelFinset (enumeration : V ≃ Fin n) (values : Finset V) :
    relabelFinset enumeration (unrelabelFinset enumeration values)
        (unrelabelFinset_bounded enumeration values) = values := by
  ext value
  rw [relabelFinset, Finset.mem_image]
  constructor
  · rintro ⟨attached, _attachedMember, decodeEq⟩
    have memImage : attached.1 ∈ unrelabelFinset enumeration values := attached.2
    change attached.1 ∈ values.image (encodeAtom enumeration) at memImage
    rw [Finset.mem_image] at memImage
    rcases memImage with ⟨atom, atomMember, encodeEq⟩
    have encodeAtomEq : encodeAtom enumeration atom =
        encodeAtom enumeration (decodeAtom enumeration attached.1
          ((unrelabelFinset_bounded enumeration values) attached.1 attached.2)) := by
      rw [encodeEq, encodeAtom_decodeAtom]
    have atomEq : atom = value := by
      rw [encodeAtom_injective enumeration encodeAtomEq]
      exact decodeEq
    simpa [atomEq] using atomMember
  · intro valueMember
    refine ⟨⟨encodeAtom enumeration value, ?_⟩, Finset.mem_attach _ _,
      decodeAtom_encodeAtom enumeration value _⟩
    exact Finset.mem_image_of_mem _ valueMember

theorem relabelFinset_card (enumeration : V ≃ Fin n) (values : Finset Nat)
    (bounded : ∀ value ∈ values, value < n) :
    (relabelFinset enumeration values bounded).card = values.card := by
  have cardEq := Finset.card_image_of_injOn
    (s := values.attach)
    (f := fun value : {x // x ∈ values} =>
      decodeAtom enumeration value.1 (bounded value.1 value.2)) ?_
  · simpa [relabelFinset] using cardEq
  · intro first _ second _ equal
    apply Subtype.ext
    have encoded := congrArg (encodeAtom enumeration) equal
    simpa [encodeAtom_decodeAtom] using encoded

end FiniteFinsetRelabel

end FiniteRelabel

/-! ## Physical units with atom references in `V` -/

namespace P93AuthorityPhysicalUnit

/-- The raw atom references of a P-93 physical unit all lie below `n`. -/
def BoundedIn (n : Nat) : P93AuthorityPhysicalUnit → Prop
  | .atomCenter center => center < n
  | .bond first second => first < n ∧ second < n
  | .axis path => ∀ atom ∈ path, atom < n
  | .plane members => ∀ atom ∈ members, atom < n
  | .helix path => ∀ atom ∈ path, atom < n
  | .polyhedron center positions => center < n ∧ ∀ atom ∈ positions, atom < n

end P93AuthorityPhysicalUnit

/-- A P-93 physical unit whose atom references are vertices of `V`.

The constructors and the list/`Finset` semantics of
`P93AuthorityPhysicalUnit` are retained one-for-one. -/
inductive SuppliedPhysicalUnit (V : Type*) where
  | atomCenter (center : V)
  | bond (first second : V)
  | axis (path : List V)
  | plane (members : Finset V)
  | helix (path : List V)
  | polyhedron (center : V) (positions : Finset V)

/-- Relabel a bounded raw physical unit into `V`. -/
def relabelUnit [DecidableEq V] (enumeration : V ≃ Fin n) :
    (unit : P93AuthorityPhysicalUnit) →
      P93AuthorityPhysicalUnit.BoundedIn n unit → SuppliedPhysicalUnit V
  | .atomCenter center, centerBounded =>
      .atomCenter (decodeAtom enumeration center centerBounded)
  | .bond first second, bounds =>
      .bond (decodeAtom enumeration first bounds.1)
        (decodeAtom enumeration second bounds.2)
  | .axis path, bounds =>
      .axis (relabelList enumeration path bounds)
  | .plane members, bounds =>
      .plane (relabelFinset enumeration members bounds)
  | .helix path, bounds =>
      .helix (relabelList enumeration path bounds)
  | .polyhedron center positions, bounds =>
      .polyhedron (decodeAtom enumeration center bounds.1)
        (relabelFinset enumeration positions bounds.2)

/-- Raw atom indices of a physical unit over `V`. -/
def unrelabelUnit (enumeration : V ≃ Fin n) :
    SuppliedPhysicalUnit V → P93AuthorityPhysicalUnit
  | .atomCenter center => .atomCenter (encodeAtom enumeration center)
  | .bond first second =>
      .bond (encodeAtom enumeration first) (encodeAtom enumeration second)
  | .axis path => .axis (unrelabelList enumeration path)
  | .plane members => .plane (unrelabelFinset enumeration members)
  | .helix path => .helix (unrelabelList enumeration path)
  | .polyhedron center positions =>
      .polyhedron (encodeAtom enumeration center)
        (unrelabelFinset enumeration positions)

/-- Every unit obtained by unrelabelling is in bounds. -/
def unrelabelUnitBounded (enumeration : V ≃ Fin n) :
    (unit : SuppliedPhysicalUnit V) →
      P93AuthorityPhysicalUnit.BoundedIn n (unrelabelUnit enumeration unit)
  | .atomCenter center => encodeAtom_lt enumeration center
  | .bond first second =>
      ⟨encodeAtom_lt enumeration first, encodeAtom_lt enumeration second⟩
  | .axis path => unrelabelList_bounded enumeration path
  | .plane members => unrelabelFinset_bounded enumeration members
  | .helix path => unrelabelList_bounded enumeration path
  | .polyhedron center positions =>
      ⟨encodeAtom_lt enumeration center,
        unrelabelFinset_bounded enumeration positions⟩

theorem unrelabelUnit_relabelUnit [DecidableEq V] (enumeration : V ≃ Fin n)
    (unit : P93AuthorityPhysicalUnit)
    (bound : P93AuthorityPhysicalUnit.BoundedIn n unit) :
    unrelabelUnit enumeration (relabelUnit enumeration unit bound) = unit := by
  cases unit with
  | atomCenter center =>
      simp [relabelUnit, unrelabelUnit, encodeAtom_decodeAtom]
  | bond first second =>
      simp [relabelUnit, unrelabelUnit, encodeAtom_decodeAtom]
  | axis path =>
      simp [relabelUnit, unrelabelUnit, unrelabelList_relabelList]
  | plane members =>
      simp [relabelUnit, unrelabelUnit, unrelabelFinset_relabelFinset]
  | helix path =>
      simp [relabelUnit, unrelabelUnit, unrelabelList_relabelList]
  | polyhedron center positions =>
      simp [relabelUnit, unrelabelUnit, unrelabelFinset_relabelFinset,
        encodeAtom_decodeAtom]

theorem relabelUnit_unrelabelUnit [DecidableEq V] (enumeration : V ≃ Fin n)
    (unit : SuppliedPhysicalUnit V) :
    relabelUnit enumeration (unrelabelUnit enumeration unit)
        (unrelabelUnitBounded enumeration unit) = unit := by
  cases unit with
  | atomCenter center =>
      simp [relabelUnit, unrelabelUnit, decodeAtom_encodeAtom]
  | bond first second =>
      simp [relabelUnit, unrelabelUnit, decodeAtom_encodeAtom]
  | axis path =>
      simp [relabelUnit, unrelabelUnit, relabelList_unrelabelList]
  | plane members =>
      simp [relabelUnit, unrelabelUnit, relabelFinset_unrelabelFinset]
  | helix path =>
      simp [relabelUnit, unrelabelUnit, relabelList_unrelabelList]
  | polyhedron center positions =>
      simp [relabelUnit, unrelabelUnit, relabelFinset_unrelabelFinset,
        decodeAtom_encodeAtom]

/-! ## Located assignments -/

/-- A located P-93 assignment with atom references in `V`.

The citation token and descriptor are source nomenclature data and are kept
literally. -/
structure SuppliedLocatedAssignment (V : Type*) where
  unit : SuppliedPhysicalUnit V
  citation : P93AuthorityCitationToken
  descriptor : BlueBookP91.Descriptor

/-- Relabel the physical unit of a located assignment, retaining the citation
token and descriptor literally. -/
def relabelAssignment [DecidableEq V] (enumeration : V ≃ Fin n)
    (assignment : P93AuthorityLocatedAssignment BlueBookP91.Descriptor)
    (bound : P93AuthorityPhysicalUnit.BoundedIn n assignment.unit) :
    SuppliedLocatedAssignment V where
  unit := relabelUnit enumeration assignment.unit bound
  citation := assignment.citation
  descriptor := assignment.descriptor

/-- Decode a located assignment to the raw P-93 carrier. -/
def unrelabelAssignment (enumeration : V ≃ Fin n)
    (assignment : SuppliedLocatedAssignment V) :
    P93AuthorityLocatedAssignment BlueBookP91.Descriptor where
  unit := unrelabelUnit enumeration assignment.unit
  citation := assignment.citation
  descriptor := assignment.descriptor

/-- Relabel an ordered list of bounded located assignments. -/
def relabelAssignments [DecidableEq V] (enumeration : V ≃ Fin n)
    (assignments : List (P93AuthorityLocatedAssignment BlueBookP91.Descriptor))
    (bounded : ∀ assignment ∈ assignments,
      P93AuthorityPhysicalUnit.BoundedIn n assignment.unit) :
    List (SuppliedLocatedAssignment V) :=
  assignments.attach.map fun assignment =>
    relabelAssignment enumeration assignment.1
      (bounded assignment.1 assignment.2)

/-- Decode an ordered list of located assignments. -/
def unrelabelAssignments (enumeration : V ≃ Fin n)
    (assignments : List (SuppliedLocatedAssignment V)) :
    List (P93AuthorityLocatedAssignment BlueBookP91.Descriptor) :=
  assignments.map (unrelabelAssignment enumeration)

@[simp]
theorem relabelAssignments_length [DecidableEq V] (enumeration : V ≃ Fin n)
    (assignments : List (P93AuthorityLocatedAssignment BlueBookP91.Descriptor))
    (bounded : ∀ assignment ∈ assignments,
      P93AuthorityPhysicalUnit.BoundedIn n assignment.unit) :
    (relabelAssignments enumeration assignments bounded).length =
      assignments.length := by
  simp [relabelAssignments]

@[simp]
theorem unrelabelAssignments_length (enumeration : V ≃ Fin n)
    (assignments : List (SuppliedLocatedAssignment V)) :
    (unrelabelAssignments enumeration assignments).length = assignments.length := by
  simp [unrelabelAssignments]

/-- Exact recovery of one located assignment. -/
theorem unrelabelAssignment_relabelAssignment [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (assignment : P93AuthorityLocatedAssignment BlueBookP91.Descriptor)
    (bound : P93AuthorityPhysicalUnit.BoundedIn n assignment.unit) :
    unrelabelAssignment enumeration
        (relabelAssignment enumeration assignment bound) = assignment := by
  rcases assignment with ⟨unit, citation, descriptor⟩
  simp [unrelabelAssignment, relabelAssignment, unrelabelUnit_relabelUnit]

/-- Exact recovery of the ordered assignment list. -/
theorem unrelabelAssignments_relabelAssignments [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (assignments : List (P93AuthorityLocatedAssignment BlueBookP91.Descriptor))
    (bounded : ∀ assignment ∈ assignments,
      P93AuthorityPhysicalUnit.BoundedIn n assignment.unit) :
    unrelabelAssignments enumeration
        (relabelAssignments enumeration assignments bounded) = assignments := by
  unfold unrelabelAssignments relabelAssignments
  rw [List.map_map]
  trans assignments.attach.map Subtype.val
  · apply List.map_congr_left
    intro assignment _
    exact unrelabelAssignment_relabelAssignment enumeration assignment.1
      (bounded assignment.1 assignment.2)
  · exact List.attach_map_subtype_val assignments

/-- A map of a relabelled assignment list is the map of the source list,
provided the two maps agree after relabelling.  This is the general form of
the order- and multiplicity-preserving projections below. -/
theorem relabelAssignments_map [DecidableEq V] (enumeration : V ≃ Fin n)
    (assignments : List (P93AuthorityLocatedAssignment BlueBookP91.Descriptor))
    (bounded : ∀ assignment ∈ assignments,
      P93AuthorityPhysicalUnit.BoundedIn n assignment.unit)
    {β : Type*} (suppliedMap : SuppliedLocatedAssignment V → β)
    (sourceMap : P93AuthorityLocatedAssignment BlueBookP91.Descriptor → β)
    (agree : ∀ assignment bound,
      suppliedMap (relabelAssignment enumeration assignment bound) =
        sourceMap assignment) :
    (relabelAssignments enumeration assignments bounded).map suppliedMap =
      assignments.map sourceMap := by
  unfold relabelAssignments
  rw [List.map_map]
  trans assignments.attach.map (fun assignment => sourceMap assignment.1)
  · apply List.map_congr_left
    intro assignment _
    exact agree assignment.1 (bounded assignment.1 assignment.2)
  · exact List.attach_map_val

/-- Citation tokens are retained literally, in order and multiplicity. -/
theorem relabelAssignments_citations [DecidableEq V] (enumeration : V ≃ Fin n)
    (assignments : List (P93AuthorityLocatedAssignment BlueBookP91.Descriptor))
    (bounded : ∀ assignment ∈ assignments,
      P93AuthorityPhysicalUnit.BoundedIn n assignment.unit) :
    (relabelAssignments enumeration assignments bounded).map
        (fun assignment => assignment.citation) =
      assignments.map (fun assignment => assignment.citation) :=
  relabelAssignments_map enumeration assignments bounded
    (fun assignment => assignment.citation)
    (fun assignment => assignment.citation) (by intro assignment _; rfl)

/-- Citation keys, including prime counts, are retained literally and in
order. -/
theorem relabelAssignments_citationKeys [DecidableEq V] (enumeration : V ≃ Fin n)
    (assignments : List (P93AuthorityLocatedAssignment BlueBookP91.Descriptor))
    (bounded : ∀ assignment ∈ assignments,
      P93AuthorityPhysicalUnit.BoundedIn n assignment.unit) :
    (relabelAssignments enumeration assignments bounded).map
        (fun assignment => assignment.citation.key) =
      assignments.map (fun assignment => assignment.citation.key) :=
  relabelAssignments_map enumeration assignments bounded
    (fun assignment => assignment.citation.key)
    (fun assignment => assignment.citation.key) (by intro assignment _; rfl)

/-- Citation components, including prime counts, are retained literally and in
order. -/
theorem relabelAssignments_citationComponents [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (assignments : List (P93AuthorityLocatedAssignment BlueBookP91.Descriptor))
    (bounded : ∀ assignment ∈ assignments,
      P93AuthorityPhysicalUnit.BoundedIn n assignment.unit) :
    (relabelAssignments enumeration assignments bounded).map
        (fun assignment => assignment.citation.components) =
      assignments.map (fun assignment => assignment.citation.components) :=
  relabelAssignments_map enumeration assignments bounded
    (fun assignment => assignment.citation.components)
    (fun assignment => assignment.citation.components) (by intro assignment _; rfl)

/-- Descriptors are retained literally, in order and multiplicity. -/
theorem relabelAssignments_descriptors [DecidableEq V] (enumeration : V ≃ Fin n)
    (assignments : List (P93AuthorityLocatedAssignment BlueBookP91.Descriptor))
    (bounded : ∀ assignment ∈ assignments,
      P93AuthorityPhysicalUnit.BoundedIn n assignment.unit) :
    (relabelAssignments enumeration assignments bounded).map
        (fun assignment => assignment.descriptor) =
      assignments.map (fun assignment => assignment.descriptor) :=
  relabelAssignments_map enumeration assignments bounded
    (fun assignment => assignment.descriptor)
    (fun assignment => assignment.descriptor) (by intro assignment _; rfl)

/-! ## External identity -/

/-- The canonical empty external identity of a given kind. -/
def emptyOfficialDetectedUnit (kind : OfficialStereochemicalUnitKind) :
    OfficialDetectedUnit V where
  kind := kind
  support := ∅

/-- Absence of an external identity is distinct from presence of an empty
identity. -/
theorem none_ne_some_empty (kind : OfficialStereochemicalUnitKind) :
    (none : Option (OfficialDetectedUnit V)) ≠
      some (emptyOfficialDetectedUnit (V := V) kind) := by
  intro equal
  cases equal

/-! ## The composable satellite and its source adapter -/

/-- An externally supplied P-91 annotation together with bounded P-93 located
assignments over the raw atom indices `Nat`. -/
structure RawSuppliedCitationSource (V : Type*)
    (BaseName Numbering Locant Prefix : Type*) where
  annotatedName : BlueBookP91.AnnotatedName BaseName Numbering Locant Prefix
  assignments : List (P93AuthorityLocatedAssignment BlueBookP91.Descriptor)
  externalIdentity? : Option (OfficialDetectedUnit V) := none

/-- A composable satellite over an arbitrary finite vertex type `V` and a
common interaction graph.

The annotated name and the ordered assignment list are the supplied source
data; the graph is the composition context and is not part of the source
recovery claim. -/
structure SuppliedCitationSatellite (V : Type*) [DecidableEq V] [Fintype V]
    (BaseName Numbering Locant Prefix : Type*) where
  graph : FiniteAtomInteractionHypergraph V
  annotatedName : BlueBookP91.AnnotatedName BaseName Numbering Locant Prefix
  assignments : List (SuppliedLocatedAssignment V)
  externalIdentity? : Option (OfficialDetectedUnit V) := none

section Satellite

variable [DecidableEq V] [Fintype V]
variable {BaseName Numbering Locant Prefix : Type*}

/-- Adapt a raw source into the satellite over `V`, using an explicit
enumeration `V ≃ Fin n` and explicit bounds on every raw physical unit. -/
def adapt (graph : FiniteAtomInteractionHypergraph V) (enumeration : V ≃ Fin n)
    (raw : RawSuppliedCitationSource V BaseName Numbering Locant Prefix)
    (bounded : ∀ assignment ∈ raw.assignments,
      P93AuthorityPhysicalUnit.BoundedIn n assignment.unit) :
    SuppliedCitationSatellite V BaseName Numbering Locant Prefix where
  graph := graph
  annotatedName := raw.annotatedName
  assignments := relabelAssignments enumeration raw.assignments bounded
  externalIdentity? := raw.externalIdentity?

/-- Recover the raw supplied source from the satellite.  The graph is
composition context and is dropped; annotated name, assignments and external
identity are decoded through the source projections. -/
def suppliedSource (enumeration : V ≃ Fin n)
    (satellite : SuppliedCitationSatellite V BaseName Numbering Locant Prefix) :
    RawSuppliedCitationSource V BaseName Numbering Locant Prefix where
  annotatedName := satellite.annotatedName
  assignments := unrelabelAssignments enumeration satellite.assignments
  externalIdentity? := satellite.externalIdentity?

/-- The adapter recovers the exact supplied source record, including ordered
citation/assignment multiplicity and the optional external identity. -/
@[simp]
theorem suppliedSource_adapt (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin n)
    (raw : RawSuppliedCitationSource V BaseName Numbering Locant Prefix)
    (bounded : ∀ assignment ∈ raw.assignments,
      P93AuthorityPhysicalUnit.BoundedIn n assignment.unit) :
    suppliedSource enumeration (adapt graph enumeration raw bounded) = raw := by
  rcases raw with ⟨annotatedName, assignments, externalIdentity?⟩
  rw [suppliedSource, adapt, unrelabelAssignments_relabelAssignments]

@[simp]
theorem adapt_annotatedName (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin n)
    (raw : RawSuppliedCitationSource V BaseName Numbering Locant Prefix)
    (bounded : ∀ assignment ∈ raw.assignments,
      P93AuthorityPhysicalUnit.BoundedIn n assignment.unit) :
    (adapt graph enumeration raw bounded).annotatedName = raw.annotatedName := rfl

@[simp]
theorem adapt_graph (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin n)
    (raw : RawSuppliedCitationSource V BaseName Numbering Locant Prefix)
    (bounded : ∀ assignment ∈ raw.assignments,
      P93AuthorityPhysicalUnit.BoundedIn n assignment.unit) :
    (adapt graph enumeration raw bounded).graph = graph := rfl

@[simp]
theorem adapt_externalIdentity? (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin n)
    (raw : RawSuppliedCitationSource V BaseName Numbering Locant Prefix)
    (bounded : ∀ assignment ∈ raw.assignments,
      P93AuthorityPhysicalUnit.BoundedIn n assignment.unit) :
    (adapt graph enumeration raw bounded).externalIdentity? =
      raw.externalIdentity? := rfl

/-- Every P-91 syntax field is retained literally by the adapter: base name,
numbering, and the ordered citations with descriptor, optional locant,
target, position and parenthesised-and-hyphenated flag. -/
theorem adapt_preservesP91Syntax (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin n)
    (raw : RawSuppliedCitationSource V BaseName Numbering Locant Prefix)
    (bounded : ∀ assignment ∈ raw.assignments,
      P93AuthorityPhysicalUnit.BoundedIn n assignment.unit) :
    (adapt graph enumeration raw bounded).annotatedName.baseName =
        raw.annotatedName.baseName ∧
    (adapt graph enumeration raw bounded).annotatedName.numbering =
        raw.annotatedName.numbering ∧
    (adapt graph enumeration raw bounded).annotatedName.citations.map
        (fun citation => citation.descriptor) =
      raw.annotatedName.citations.map (fun citation => citation.descriptor) ∧
    (adapt graph enumeration raw bounded).annotatedName.citations.map
        (fun citation => citation.locant) =
      raw.annotatedName.citations.map (fun citation => citation.locant) ∧
    (adapt graph enumeration raw bounded).annotatedName.citations.map
        (fun citation => citation.target) =
      raw.annotatedName.citations.map (fun citation => citation.target) ∧
    (adapt graph enumeration raw bounded).annotatedName.citations.map
        (fun citation => citation.position) =
      raw.annotatedName.citations.map (fun citation => citation.position) ∧
    (adapt graph enumeration raw bounded).annotatedName.citations.map
        (fun citation => citation.parenthesizedAndHyphenated) =
      raw.annotatedName.citations.map
        (fun citation => citation.parenthesizedAndHyphenated) := by
  simp [adapt]

/-- Updating external identity never changes physical assignments; detector
metadata is not physical evidence. -/
@[simp]
theorem externalIdentity_update_assignments
    (satellite : SuppliedCitationSatellite V BaseName Numbering Locant Prefix)
    (identity? : Option (OfficialDetectedUnit V)) :
    ({ satellite with externalIdentity? := identity? } :
        SuppliedCitationSatellite V BaseName Numbering Locant Prefix).assignments =
      satellite.assignments := rfl

/-- The satellite adapter distinguishes absence of external identity from a
present empty identity. -/
theorem adapt_none_ne_some_empty (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin n)
    (raw : RawSuppliedCitationSource V BaseName Numbering Locant Prefix)
    (bounded : ∀ assignment ∈ raw.assignments,
      P93AuthorityPhysicalUnit.BoundedIn n assignment.unit)
    (kind : OfficialStereochemicalUnitKind) :
    adapt graph enumeration { raw with externalIdentity? := none } bounded ≠
      adapt graph enumeration
        { raw with externalIdentity? := some (emptyOfficialDetectedUnit (V := V) kind) }
        bounded := by
  intro equal
  have externalEq := congrArg
    (fun satellite => satellite.externalIdentity?) equal
  simp [adapt] at externalEq

end Satellite

end OrganicStereoSuppliedCitationIngress

end TetraStereo.OneCenter
