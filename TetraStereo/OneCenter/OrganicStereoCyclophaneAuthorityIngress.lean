import TetraStereo.OneCenter.IUPACP93CyclophaneAuthorityCarrier
import TetraStereo.OneCenter.OrganicStereoP93PhysicalFrameIngress
import TetraStereo.OneCenter.OrganicStereoObservationCommonIndexBridge

set_option autoImplicit false

/-!
# Native source ingress for the cyclophane P-93 authority carrier

`IUPACP93CyclophaneAuthorityCarrier` stores a source-designated cyclophane system together with
three observation shapes: a plane observation over an ordered planar-frame record, a center
observation with two specification branches, and a double-bond observation whose descriptor is
optional.

This module gives that carrier a lossless native representation over an arbitrary finite atom type
`V` with an explicit enumeration `V ≃ Fin n`.

## What is relabelled

Only genuine molecular atom references are relabelled:

* `atomCarrier`, the atom sets of `phaneNodes`, every ordered `rings` list, and the **first**
  component (the atom cycle) of every `ringPhaneCycles` entry;
* the physical unit of every observation;
* the complete planar frame record (through the existing real
  `OrganicStereoP93PhysicalFrameIngress.NativePlanarFrame` codec);
* the physical `center` of every `RCTReferenceCandidate` and `RCTLocatedAssignment`.

## What is copied literally

* the **second** component of `ringPhaneCycles` is a list of indices into `phaneNodes`, not a list
  of molecular atoms; it is copied verbatim, as is `phaneRing` in the double-bond observation.
  An atom-cycle length is never substituted for a phane-node count;
* citation tokens and their components (values and prime counts) are nomenclature data, not atom
  indices;
* naming contexts, descriptors, `UnitKind`, `Bool` flags, sequence priorities, `RingSide` values,
  `MonocyclicSeniorLigandGeometry` and `CarbonDoubleBondContext` are copied literally;
* the optional double-bond descriptor keeps its exact `none`/`some` shape;
* `CyclophanePlaneReference` keeps its two `Prop`-valued fields literally; they are never turned
  into assumptions of the codec;
* the two branches of the center specification are kept as distinct constructors, and candidate
  order and multiplicity are preserved by the underlying list codecs.

## Bounds and validity

`CyclophaneSystemBoundedIn`, `PlaneObservationBoundedIn`, `CenterObservationBoundedIn` and
`DoubleBondObservationBoundedIn` are explicit hypotheses of the codec. Where the carrier's own
predicate supplies them they are *derived*: the system bounds come from
`P93AuthorityCyclophaneSystem.MechanicallyValidFor`, the unit bounds from
`P93CyclophaneUnitSupported` together with the bounded `atomCarrier`, the planar-frame bounds from
`P93AuthorityPlaneFrame.ValidFor`, and the candidate/assignment centers from the candidate
`ValidFor` predicates. No bound is assumed from an atom count.

## What is not claimed

Nothing here decides chemical admissibility, chooses a descriptor, or discharges the audited
`P93CyclophaneAuthorityPolicy` boundary. Validity is only *consumed*: after an exact decode the
original record's own `ValidFor` is recovered at the same source and policy. No claim is made that
`ValidFor` is invariant under an arbitrary renumbering of atom indices, and no list is collapsed to
a set.

No coordinate payload is invented: `P93AuthorityPlaneFrame` and the native `NativePlanarFrame`
carry only the indexed atom record. The plane `ValidFor` spatial-incidence witnesses and the
source's optional spatial channel are retained at the source level through the binding's actual
`spatial_eq`; the codec does not claim to recompute coordinates, a mean plane, or any output
geometry.
-/

namespace TetraStereo.OneCenter

namespace OrganicStereoCyclophaneAuthorityIngress

open TetraStereo.OneCenter.OrganicStereoSuppliedCitationIngress
open TetraStereo.OneCenter.OrganicStereoP93PhysicalFrameIngress
open BlueBookP93.Cyclic

variable {V : Type*}
variable {n : ℕ}
variable {policy : P93CyclophaneAuthorityPolicy}

/-! ## Re-exported unit bounds -/

/-- Explicit bound predicate on a physical unit. -/
abbrev UnitBoundedIn (n : ℕ) (unit : P93AuthorityPhysicalUnit) : Prop :=
  TetraStereo.OneCenter.OrganicStereoSuppliedCitationIngress.P93AuthorityPhysicalUnit.BoundedIn
    n unit

/-! ## The native cyclophane system -/

/-- Native mirror of `P93AuthorityCyclophaneSystem`.  The atom carrier, the phane-node atom sets,
the ordered rings and the atom cycles of `ringPhaneCycles` are native atoms; the phane-node index
lists are raw `Nat` indices into `phaneNodes` and are copied literally. -/
structure NativeCyclophaneSystem (V : Type*) where
  /-- Exact molecular atoms belonging to the cyclophane parent system. -/
  atomCarrier : List V
  /-- Atom carriers of the source-designated phane nomenclature nodes. -/
  phaneNodes : List (Finset V)
  /-- The ordered closed molecular rings. -/
  rings : List (List V)
  /-- For each molecular atom cycle, the matching cycle of indices into `phaneNodes`. -/
  ringPhaneCycles : List (List V × List Nat)
  deriving DecidableEq

/-- The atom references of a source system all lie below `n`.  The phane-node index lists inside
`ringPhaneCycles` are not atom references and therefore carry no bound. -/
structure CyclophaneSystemBoundedIn (n : ℕ)
    (system : P93AuthorityCyclophaneSystem) : Prop where
  atomCarrierBound : ∀ atom ∈ system.atomCarrier, atom < n
  phaneNodesBound : ∀ node ∈ system.phaneNodes, ∀ atom ∈ node, atom < n
  ringsBound : ∀ ring ∈ system.rings, ∀ atom ∈ ring, atom < n
  ringPhaneCyclesBound : ∀ mapping ∈ system.ringPhaneCycles, ∀ atom ∈ mapping.1, atom < n

/-- System bounds derived from the actual mechanical source predicate.  Every inclusion used here
is a conjunct of `MechanicallyValidFor`; the phane-node index lists are never reinterpreted as
atoms. -/
theorem cyclophaneSystemBoundedIn_of_mechanicallyValid
    (source : AuthoritativeChemicalInput) (system : P93AuthorityCyclophaneSystem)
    (valid : system.MechanicallyValidFor source) :
    CyclophaneSystemBoundedIn source.molecule.atomCount system := by
  rcases valid with
    ⟨_carrierLength, _carrierNodup, carrierBounded, _nodesLength, _nodesNodup, nodesCover,
      _carrierCover, _disjoint, _ringsNonempty, _ringsNodup, ringClosed, _ringCover,
      _cyclesNonempty, _cyclesNodup, cycleSound⟩
  refine
    { atomCarrierBound := carrierBounded
      phaneNodesBound := ?_
      ringsBound := ?_
      ringPhaneCyclesBound := ?_ }
  · intro node nodeMem atom atomMem
    exact carrierBounded atom ((nodesCover node nodeMem).2 atom atomMem)
  · intro ring ringMem atom atomMem
    exact carrierBounded atom ((ringClosed ring ringMem).2 atom atomMem)
  · intro mapping mappingMem atom atomMem
    exact carrierBounded atom
      ((ringClosed mapping.1 (cycleSound mapping mappingMem).1).2 atom atomMem)

/-- A physical unit supported by a bounded system is bounded.  The three unsupported constructors
are excluded by `P93CyclophaneUnitSupported` itself. -/
theorem unitBoundedIn_of_supported (n : ℕ) (system : P93AuthorityCyclophaneSystem)
    (bounded : CyclophaneSystemBoundedIn n system) (unit : P93AuthorityPhysicalUnit)
    (supported : P93CyclophaneUnitSupported system unit) :
    UnitBoundedIn n unit := by
  cases unit with
  | atomCenter center => exact bounded.atomCarrierBound center supported
  | bond first second =>
      exact ⟨bounded.atomCarrierBound first supported.1,
        bounded.atomCarrierBound second supported.2⟩
  | axis path => exact supported.elim
  | plane members =>
      exact fun atom atomMem => bounded.atomCarrierBound atom (supported atom atomMem)
  | helix path => exact supported.elim
  | polyhedron center positions => exact supported.elim

/-! ## List and finite-set inverses insensitive to the bound proof

The bound witnesses differ between a decoded native value and the canonical
`unrelabelFinset_bounded`/`unrelabelList_bounded` lemmas, so the round trips are stated for an
arbitrary bound proof.  The underlying element-level inverse
`decodeAtom_encodeAtom` already holds for an arbitrary bound. -/

theorem relabelList_unrelabelList_anyBound {n : ℕ} (enumeration : V ≃ Fin n)
    (values : List V)
    (bounded : ∀ value ∈ unrelabelList enumeration values, value < n) :
    relabelList enumeration (unrelabelList enumeration values) bounded = values := by
  unfold relabelList unrelabelList
  rw [List.attach_map, List.map_map]
  trans values.attach.map Subtype.val
  · apply List.map_congr_left
    intro value _
    exact decodeAtom_encodeAtom enumeration value.1 _
  · exact List.attach_map_subtype_val values

theorem relabelFinset_unrelabelFinset_anyBound {n : ℕ} [DecidableEq V]
    (enumeration : V ≃ Fin n) (values : Finset V)
    (bounded : ∀ value ∈ unrelabelFinset enumeration values, value < n) :
    relabelFinset enumeration (unrelabelFinset enumeration values) bounded = values := by
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
          (bounded attached.1 attached.2)) := by
      rw [encodeEq, encodeAtom_decodeAtom]
    have atomEq : atom = value := by
      rw [encodeAtom_injective enumeration encodeAtomEq]
      exact decodeEq
    simpa [atomEq] using atomMember
  · intro valueMember
    refine ⟨⟨encodeAtom enumeration value, ?_⟩, Finset.mem_attach _ _,
      decodeAtom_encodeAtom enumeration value _⟩
    exact Finset.mem_image_of_mem _ valueMember

/-! ## Bounds of decoded lists -/

theorem unrelabelFinsetList_bounded {n : ℕ} (enumeration : V ≃ Fin n)
    (nodes : List (Finset V)) :
    ∀ node ∈ nodes.map (unrelabelFinset enumeration), ∀ atom ∈ node, atom < n := by
  intro node nodeMem atom atomMem
  rw [List.mem_map] at nodeMem
  rcases nodeMem with ⟨native, _nativeMem, rfl⟩
  exact unrelabelFinset_bounded enumeration native atom atomMem

theorem unrelabelListList_bounded {n : ℕ} (enumeration : V ≃ Fin n)
    (rings : List (List V)) :
    ∀ ring ∈ rings.map (unrelabelList enumeration), ∀ atom ∈ ring, atom < n := by
  intro ring ringMem atom atomMem
  rw [List.mem_map] at ringMem
  rcases ringMem with ⟨native, _nativeMem, rfl⟩
  exact unrelabelList_bounded enumeration native atom atomMem

theorem unrelabelCycleList_bounded {n : ℕ} (enumeration : V ≃ Fin n)
    (cycles : List (List V × List Nat)) :
    ∀ mapping ∈ cycles.map (fun mapping => (unrelabelList enumeration mapping.1, mapping.2)),
      ∀ atom ∈ mapping.1, atom < n := by
  intro mapping mappingMem atom atomMem
  rw [List.mem_map] at mappingMem
  rcases mappingMem with ⟨native, _nativeMem, rfl⟩
  exact unrelabelList_bounded enumeration native.1 atom atomMem

/-! ## List-of-collections round trips -/

theorem relabelFinsetList_unrelabelFinsetList {n : ℕ} [DecidableEq V]
    (enumeration : V ≃ Fin n) (nodes : List (Finset V))
    (bounded : ∀ node ∈ nodes.map (unrelabelFinset enumeration), ∀ atom ∈ node, atom < n) :
    (nodes.map (unrelabelFinset enumeration)).attach.map
        (fun node => relabelFinset enumeration node.1 (bounded node.1 node.2)) = nodes := by
  rw [List.attach_map, List.map_map]
  trans nodes.attach.map Subtype.val
  · apply List.map_congr_left
    intro node _
    have boundHere : ∀ value ∈ unrelabelFinset enumeration node.1, value < n :=
      bounded (unrelabelFinset enumeration node.1) (List.mem_map_of_mem node.2)
    show relabelFinset enumeration (unrelabelFinset enumeration node.1) boundHere = node.1
    exact relabelFinset_unrelabelFinset_anyBound enumeration node.1 boundHere
  · exact List.attach_map_subtype_val nodes

theorem relabelListList_unrelabelListList {n : ℕ} (enumeration : V ≃ Fin n)
    (rings : List (List V))
    (bounded : ∀ ring ∈ rings.map (unrelabelList enumeration), ∀ atom ∈ ring, atom < n) :
    (rings.map (unrelabelList enumeration)).attach.map
        (fun ring => relabelList enumeration ring.1 (bounded ring.1 ring.2)) = rings := by
  rw [List.attach_map, List.map_map]
  trans rings.attach.map Subtype.val
  · apply List.map_congr_left
    intro ring _
    have boundHere : ∀ value ∈ unrelabelList enumeration ring.1, value < n :=
      bounded (unrelabelList enumeration ring.1) (List.mem_map_of_mem ring.2)
    show relabelList enumeration (unrelabelList enumeration ring.1) boundHere = ring.1
    exact relabelList_unrelabelList_anyBound enumeration ring.1 boundHere
  · exact List.attach_map_subtype_val rings

theorem relabelCycleList_unrelabelCycleList {n : ℕ} (enumeration : V ≃ Fin n)
    (cycles : List (List V × List Nat))
    (bounded : ∀ mapping ∈ cycles.map
        (fun mapping => (unrelabelList enumeration mapping.1, mapping.2)),
        ∀ atom ∈ mapping.1, atom < n) :
    (cycles.map (fun mapping => (unrelabelList enumeration mapping.1, mapping.2))).attach.map
        (fun mapping =>
          (relabelList enumeration mapping.1.1 (bounded mapping.1 mapping.2), mapping.1.2)) =
      cycles := by
  rw [List.attach_map, List.map_map]
  trans cycles.attach.map Subtype.val
  · apply List.map_congr_left
    intro mapping _
    have boundHere : ∀ value ∈ unrelabelList enumeration mapping.1.1, value < n :=
      bounded (unrelabelList enumeration mapping.1.1, mapping.1.2)
        (List.mem_map_of_mem mapping.2)
    show (relabelList enumeration (unrelabelList enumeration mapping.1.1) boundHere,
        mapping.1.2) = mapping.1
    exact Prod.ext (relabelList_unrelabelList_anyBound enumeration mapping.1.1 boundHere) rfl
  · exact List.attach_map_subtype_val cycles

/-! ## The system codec -/

/-- Relabel a bounded source system into the native payload. -/
def relabelSystem [DecidableEq V] {n : ℕ} (enumeration : V ≃ Fin n)
    (system : P93AuthorityCyclophaneSystem)
    (bounded : CyclophaneSystemBoundedIn n system) : NativeCyclophaneSystem V where
  atomCarrier := relabelList enumeration system.atomCarrier bounded.atomCarrierBound
  phaneNodes := system.phaneNodes.attach.map fun node =>
    relabelFinset enumeration node.1 (bounded.phaneNodesBound node.1 node.2)
  rings := system.rings.attach.map fun ring =>
    relabelList enumeration ring.1 (bounded.ringsBound ring.1 ring.2)
  ringPhaneCycles := system.ringPhaneCycles.attach.map fun mapping =>
    (relabelList enumeration mapping.1.1
      (bounded.ringPhaneCyclesBound mapping.1 mapping.2), mapping.1.2)

/-- Decode a native payload to the exact source system.  The phane-node index lists are returned
verbatim. -/
def decodeSystem [DecidableEq V] {n : ℕ} (enumeration : V ≃ Fin n)
    (native : NativeCyclophaneSystem V) : P93AuthorityCyclophaneSystem where
  atomCarrier := unrelabelList enumeration native.atomCarrier
  phaneNodes := native.phaneNodes.map (unrelabelFinset enumeration)
  rings := native.rings.map (unrelabelList enumeration)
  ringPhaneCycles := native.ringPhaneCycles.map fun mapping =>
    (unrelabelList enumeration mapping.1, mapping.2)

/-- Every decoded system satisfies the explicit bounds. -/
def decodeSystemBounded [DecidableEq V] {n : ℕ} (enumeration : V ≃ Fin n)
    (native : NativeCyclophaneSystem V) :
    CyclophaneSystemBoundedIn n (decodeSystem enumeration native) where
  atomCarrierBound := unrelabelList_bounded enumeration native.atomCarrier
  phaneNodesBound := unrelabelFinsetList_bounded enumeration native.phaneNodes
  ringsBound := unrelabelListList_bounded enumeration native.rings
  ringPhaneCyclesBound := unrelabelCycleList_bounded enumeration native.ringPhaneCycles

/-- Exact recovery of the source system, including the phane-node index lists. -/
theorem decodeSystem_relabelSystem [DecidableEq V] {n : ℕ} (enumeration : V ≃ Fin n)
    (system : P93AuthorityCyclophaneSystem)
    (bounded : CyclophaneSystemBoundedIn n system) :
    decodeSystem enumeration (relabelSystem enumeration system bounded) = system := by
  obtain ⟨atomCarrier, phaneNodes, rings, ringPhaneCycles⟩ := system
  simp only [relabelSystem, decodeSystem, List.map_map, Function.comp_def,
    unrelabelList_relabelList, unrelabelFinset_relabelFinset,
    List.attach_map_subtype_val]

/-- Relabelling a decoded native system returns the payload, for any accepted bound witness. -/
theorem relabelSystem_decodeSystem [DecidableEq V] {n : ℕ} (enumeration : V ≃ Fin n)
    (native : NativeCyclophaneSystem V)
    (bounded : CyclophaneSystemBoundedIn n (decodeSystem enumeration native)) :
    relabelSystem enumeration (decodeSystem enumeration native) bounded = native := by
  obtain ⟨atomCarrier, phaneNodes, rings, ringPhaneCycles⟩ := native
  have hAtoms := relabelList_unrelabelList_anyBound enumeration atomCarrier
    bounded.atomCarrierBound
  have hPhane := relabelFinsetList_unrelabelFinsetList enumeration phaneNodes
    bounded.phaneNodesBound
  have hRings := relabelListList_unrelabelListList enumeration rings bounded.ringsBound
  have hCycles := relabelCycleList_unrelabelCycleList enumeration ringPhaneCycles
    bounded.ringPhaneCyclesBound
  simp only [relabelSystem, decodeSystem]
  rw [hAtoms, hPhane, hRings, hCycles]

/-- Relabelling a decoded native system with the canonical decoded bounds returns the payload. -/
theorem relabelSystem_decodeSystem_bounded [DecidableEq V] {n : ℕ} (enumeration : V ≃ Fin n)
    (native : NativeCyclophaneSystem V) :
    relabelSystem enumeration (decodeSystem enumeration native)
        (decodeSystemBounded enumeration native) = native :=
  relabelSystem_decodeSystem enumeration native (decodeSystemBounded enumeration native)

/-! ## Relative-reference candidates and located assignments -/

/-- Native mirror of `P93CyclophaneRCTReferenceCandidate`.  `center` is a physical atom; the
citation, the suffix flag and the sequence priority are nomenclature data copied literally. -/
structure NativeCyclophaneRCTReferenceCandidate (V : Type*) where
  center : V
  citation : P93AuthorityCitationToken
  namedAsSuffix : Bool
  sequencePriority : Nat

/-- Native mirror of `P93CyclophaneRCTLocatedAssignment`. -/
structure NativeCyclophaneRCTLocatedAssignment (V : Type*) where
  center : V
  citation : P93AuthorityCitationToken
  side : RingSide
  descriptor : RCTDescriptor

/-- Relabel one reference candidate. -/
def relabelCandidate (enumeration : V ≃ Fin n)
    (candidate : P93CyclophaneRCTReferenceCandidate)
    (bounded : candidate.center < n) : NativeCyclophaneRCTReferenceCandidate V where
  center := decodeAtom enumeration candidate.center bounded
  citation := candidate.citation
  namedAsSuffix := candidate.namedAsSuffix
  sequencePriority := candidate.sequencePriority

/-- Decode one reference candidate. -/
def unrelabelCandidate (enumeration : V ≃ Fin n)
    (candidate : NativeCyclophaneRCTReferenceCandidate V) :
    P93CyclophaneRCTReferenceCandidate where
  center := encodeAtom enumeration candidate.center
  citation := candidate.citation
  namedAsSuffix := candidate.namedAsSuffix
  sequencePriority := candidate.sequencePriority

/-- Relabel one located assignment. -/
def relabelAssignment (enumeration : V ≃ Fin n)
    (assignment : P93CyclophaneRCTLocatedAssignment)
    (bounded : assignment.center < n) : NativeCyclophaneRCTLocatedAssignment V where
  center := decodeAtom enumeration assignment.center bounded
  citation := assignment.citation
  side := assignment.side
  descriptor := assignment.descriptor

/-- Decode one located assignment. -/
def unrelabelAssignment (enumeration : V ≃ Fin n)
    (assignment : NativeCyclophaneRCTLocatedAssignment V) :
    P93CyclophaneRCTLocatedAssignment where
  center := encodeAtom enumeration assignment.center
  citation := assignment.citation
  side := assignment.side
  descriptor := assignment.descriptor

theorem unrelabelCandidate_relabelCandidate (enumeration : V ≃ Fin n)
    (candidate : P93CyclophaneRCTReferenceCandidate) (bounded : candidate.center < n) :
    unrelabelCandidate enumeration (relabelCandidate enumeration candidate bounded) =
      candidate := by
  rcases candidate with ⟨center, citation, namedAsSuffix, sequencePriority⟩
  simp [relabelCandidate, unrelabelCandidate, encodeAtom_decodeAtom]

theorem relabelCandidate_unrelabelCandidate (enumeration : V ≃ Fin n)
    (candidate : NativeCyclophaneRCTReferenceCandidate V)
    (bounded : encodeAtom enumeration candidate.center < n) :
    relabelCandidate enumeration (unrelabelCandidate enumeration candidate) bounded =
      candidate := by
  rcases candidate with ⟨center, citation, namedAsSuffix, sequencePriority⟩
  simp [relabelCandidate, unrelabelCandidate, decodeAtom_encodeAtom]

theorem unrelabelAssignment_relabelAssignment (enumeration : V ≃ Fin n)
    (assignment : P93CyclophaneRCTLocatedAssignment) (bounded : assignment.center < n) :
    unrelabelAssignment enumeration (relabelAssignment enumeration assignment bounded) =
      assignment := by
  rcases assignment with ⟨center, citation, side, descriptor⟩
  simp [relabelAssignment, unrelabelAssignment, encodeAtom_decodeAtom]

theorem relabelAssignment_unrelabelAssignment (enumeration : V ≃ Fin n)
    (assignment : NativeCyclophaneRCTLocatedAssignment V)
    (bounded : encodeAtom enumeration assignment.center < n) :
    relabelAssignment enumeration (unrelabelAssignment enumeration assignment) bounded =
      assignment := by
  rcases assignment with ⟨center, citation, side, descriptor⟩
  simp [relabelAssignment, unrelabelAssignment, decodeAtom_encodeAtom]

/-! ### Ordered candidate and assignment lists -/

def relabelCandidates (enumeration : V ≃ Fin n)
    (candidates : List P93CyclophaneRCTReferenceCandidate)
    (bounded : ∀ candidate ∈ candidates, candidate.center < n) :
    List (NativeCyclophaneRCTReferenceCandidate V) :=
  candidates.attach.map fun candidate =>
    relabelCandidate enumeration candidate.1 (bounded candidate.1 candidate.2)

def unrelabelCandidates (enumeration : V ≃ Fin n)
    (candidates : List (NativeCyclophaneRCTReferenceCandidate V)) :
    List P93CyclophaneRCTReferenceCandidate :=
  candidates.map (unrelabelCandidate enumeration)

def unrelabelCandidatesBounded (enumeration : V ≃ Fin n)
    (candidates : List (NativeCyclophaneRCTReferenceCandidate V)) :
    ∀ candidate ∈ unrelabelCandidates enumeration candidates, candidate.center < n := by
  intro candidate member
  rw [unrelabelCandidates, List.mem_map] at member
  rcases member with ⟨native, _nativeMember, rfl⟩
  exact encodeAtom_lt enumeration native.center

def relabelAssignments (enumeration : V ≃ Fin n)
    (assignments : List P93CyclophaneRCTLocatedAssignment)
    (bounded : ∀ assignment ∈ assignments, assignment.center < n) :
    List (NativeCyclophaneRCTLocatedAssignment V) :=
  assignments.attach.map fun assignment =>
    relabelAssignment enumeration assignment.1 (bounded assignment.1 assignment.2)

def unrelabelAssignments (enumeration : V ≃ Fin n)
    (assignments : List (NativeCyclophaneRCTLocatedAssignment V)) :
    List P93CyclophaneRCTLocatedAssignment :=
  assignments.map (unrelabelAssignment enumeration)

def unrelabelAssignmentsBounded (enumeration : V ≃ Fin n)
    (assignments : List (NativeCyclophaneRCTLocatedAssignment V)) :
    ∀ assignment ∈ unrelabelAssignments enumeration assignments, assignment.center < n := by
  intro assignment member
  rw [unrelabelAssignments, List.mem_map] at member
  rcases member with ⟨native, _nativeMember, rfl⟩
  exact encodeAtom_lt enumeration native.center

@[simp] theorem relabelCandidates_length (enumeration : V ≃ Fin n)
    (candidates : List P93CyclophaneRCTReferenceCandidate)
    (bounded : ∀ candidate ∈ candidates, candidate.center < n) :
    (relabelCandidates enumeration candidates bounded).length = candidates.length := by
  simp [relabelCandidates]

@[simp] theorem unrelabelCandidates_length (enumeration : V ≃ Fin n)
    (candidates : List (NativeCyclophaneRCTReferenceCandidate V)) :
    (unrelabelCandidates enumeration candidates).length = candidates.length := by
  simp [unrelabelCandidates]

@[simp] theorem relabelAssignments_length (enumeration : V ≃ Fin n)
    (assignments : List P93CyclophaneRCTLocatedAssignment)
    (bounded : ∀ assignment ∈ assignments, assignment.center < n) :
    (relabelAssignments enumeration assignments bounded).length = assignments.length := by
  simp [relabelAssignments]

@[simp] theorem unrelabelAssignments_length (enumeration : V ≃ Fin n)
    (assignments : List (NativeCyclophaneRCTLocatedAssignment V)) :
    (unrelabelAssignments enumeration assignments).length = assignments.length := by
  simp [unrelabelAssignments]

theorem unrelabelCandidates_relabelCandidates (enumeration : V ≃ Fin n)
    (candidates : List P93CyclophaneRCTReferenceCandidate)
    (bounded : ∀ candidate ∈ candidates, candidate.center < n) :
    unrelabelCandidates enumeration (relabelCandidates enumeration candidates bounded) =
      candidates := by
  unfold unrelabelCandidates relabelCandidates
  rw [List.map_map]
  trans candidates.attach.map Subtype.val
  · apply List.map_congr_left
    intro candidate _
    exact unrelabelCandidate_relabelCandidate enumeration candidate.1
      (bounded candidate.1 candidate.2)
  · exact List.attach_map_subtype_val candidates

theorem relabelCandidates_unrelabelCandidates (enumeration : V ≃ Fin n)
    (candidates : List (NativeCyclophaneRCTReferenceCandidate V))
    (bounded : ∀ candidate ∈ unrelabelCandidates enumeration candidates,
      candidate.center < n) :
    relabelCandidates enumeration (unrelabelCandidates enumeration candidates) bounded =
      candidates := by
  unfold relabelCandidates unrelabelCandidates
  rw [List.attach_map, List.map_map]
  trans candidates.attach.map Subtype.val
  · apply List.map_congr_left
    intro candidate _
    have boundHere : encodeAtom enumeration candidate.1.center < n :=
      bounded (unrelabelCandidate enumeration candidate.1)
        (List.mem_map_of_mem candidate.2)
    show relabelCandidate enumeration (unrelabelCandidate enumeration candidate.1) boundHere =
      candidate.1
    exact relabelCandidate_unrelabelCandidate enumeration candidate.1 boundHere
  · exact List.attach_map_subtype_val candidates

theorem unrelabelAssignments_relabelAssignments (enumeration : V ≃ Fin n)
    (assignments : List P93CyclophaneRCTLocatedAssignment)
    (bounded : ∀ assignment ∈ assignments, assignment.center < n) :
    unrelabelAssignments enumeration (relabelAssignments enumeration assignments bounded) =
      assignments := by
  unfold unrelabelAssignments relabelAssignments
  rw [List.map_map]
  trans assignments.attach.map Subtype.val
  · apply List.map_congr_left
    intro assignment _
    exact unrelabelAssignment_relabelAssignment enumeration assignment.1
      (bounded assignment.1 assignment.2)
  · exact List.attach_map_subtype_val assignments

theorem relabelAssignments_unrelabelAssignments (enumeration : V ≃ Fin n)
    (assignments : List (NativeCyclophaneRCTLocatedAssignment V))
    (bounded : ∀ assignment ∈ unrelabelAssignments enumeration assignments,
      assignment.center < n) :
    relabelAssignments enumeration (unrelabelAssignments enumeration assignments) bounded =
      assignments := by
  unfold relabelAssignments unrelabelAssignments
  rw [List.attach_map, List.map_map]
  trans assignments.attach.map Subtype.val
  · apply List.map_congr_left
    intro assignment _
    have boundHere : encodeAtom enumeration assignment.1.center < n :=
      bounded (unrelabelAssignment enumeration assignment.1)
        (List.mem_map_of_mem assignment.2)
    show relabelAssignment enumeration (unrelabelAssignment enumeration assignment.1) boundHere =
      assignment.1
    exact relabelAssignment_unrelabelAssignment enumeration assignment.1 boundHere
  · exact List.attach_map_subtype_val assignments

/-! ## The two center-specification branches -/

/-- Native mirror of `P93CyclophaneCenterSpecification`.  Both branches are kept as distinct
constructors; the `cip` branch copies its context, kind and descriptor literally. -/
inductive NativeCyclophaneCenterSpecification (V : Type*) where
  | cip (context : BlueBookP93.Acyclic.NomenclatureContext)
      (kind : BlueBookP93.Acyclic.UnitKind)
      (descriptor : BlueBookP93.Acyclic.Descriptor)
  | relativeRCT (candidates : List (NativeCyclophaneRCTReferenceCandidate V))
      (selected : NativeCyclophaneRCTReferenceCandidate V)
      (referenceSide : RingSide)
      (assignments : List (NativeCyclophaneRCTLocatedAssignment V))

/-- Bounds for one center specification.  The `cip` branch has no atom reference of its own. -/
def CenterSpecificationBoundedIn (n : ℕ) :
    P93CyclophaneCenterSpecification → Prop
  | .cip _context _kind _descriptor => True
  | .relativeRCT candidates selected _referenceSide assignments =>
      (∀ candidate ∈ candidates, candidate.center < n) ∧
        selected.center < n ∧
        ∀ assignment ∈ assignments, assignment.center < n

def relabelCenterSpecification (enumeration : V ≃ Fin n) :
    (specification : P93CyclophaneCenterSpecification) →
      CenterSpecificationBoundedIn n specification →
        NativeCyclophaneCenterSpecification V
  | .cip context kind descriptor, _bounded => .cip context kind descriptor
  | .relativeRCT candidates selected referenceSide assignments, bounded =>
      .relativeRCT (relabelCandidates enumeration candidates bounded.1)
        (relabelCandidate enumeration selected bounded.2.1)
        referenceSide
        (relabelAssignments enumeration assignments bounded.2.2)

def decodeCenterSpecification (enumeration : V ≃ Fin n) :
    NativeCyclophaneCenterSpecification V → P93CyclophaneCenterSpecification
  | .cip context kind descriptor => .cip context kind descriptor
  | .relativeRCT candidates selected referenceSide assignments =>
      .relativeRCT (unrelabelCandidates enumeration candidates)
        (unrelabelCandidate enumeration selected)
        referenceSide
        (unrelabelAssignments enumeration assignments)

def decodeCenterSpecificationBounded (enumeration : V ≃ Fin n)
    (specification : NativeCyclophaneCenterSpecification V) :
    CenterSpecificationBoundedIn n (decodeCenterSpecification enumeration specification) := by
  cases specification with
  | cip context kind descriptor => exact trivial
  | relativeRCT candidates selected referenceSide assignments =>
      exact ⟨unrelabelCandidatesBounded enumeration candidates,
        encodeAtom_lt enumeration selected.center,
        unrelabelAssignmentsBounded enumeration assignments⟩

theorem decodeCenterSpecification_relabelCenterSpecification (enumeration : V ≃ Fin n)
    (specification : P93CyclophaneCenterSpecification)
    (bounded : CenterSpecificationBoundedIn n specification) :
    decodeCenterSpecification enumeration
        (relabelCenterSpecification enumeration specification bounded) = specification := by
  cases specification with
  | cip context kind descriptor => rfl
  | relativeRCT candidates selected referenceSide assignments =>
      simp [relabelCenterSpecification, decodeCenterSpecification,
        unrelabelCandidates_relabelCandidates,
        unrelabelCandidate_relabelCandidate,
        unrelabelAssignments_relabelAssignments]

theorem relabelCenterSpecification_decodeCenterSpecification (enumeration : V ≃ Fin n)
    (specification : NativeCyclophaneCenterSpecification V)
    (bounded : CenterSpecificationBoundedIn n
      (decodeCenterSpecification enumeration specification)) :
    relabelCenterSpecification enumeration
        (decodeCenterSpecification enumeration specification) bounded = specification := by
  cases specification with
  | cip context kind descriptor => rfl
  | relativeRCT candidates selected referenceSide assignments =>
      have candidateBound : ∀ candidate ∈ unrelabelCandidates enumeration candidates,
          candidate.center < n := bounded.1
      have selectedBound : (unrelabelCandidate enumeration selected).center < n := bounded.2.1
      have assignmentBound : ∀ assignment ∈ unrelabelAssignments enumeration assignments,
          assignment.center < n := bounded.2.2
      simp [relabelCenterSpecification, decodeCenterSpecification,
        relabelCandidates_unrelabelCandidates enumeration candidates candidateBound,
        relabelCandidate_unrelabelCandidate enumeration selected selectedBound,
        relabelAssignments_unrelabelAssignments enumeration assignments assignmentBound]

/-! ## The plane observation -/

/-- Native mirror of `P93CyclophanePlaneAuthorityObservation`.  The system, the physical unit and
the complete planar frame are native; the citation, the `Prop`-valued reference record, the naming
context and the descriptor are copied literally. -/
structure NativeCyclophanePlaneAuthorityObservation (V : Type*)
    (policy : P93CyclophaneAuthorityPolicy) where
  system : NativeCyclophaneSystem V
  unit : SuppliedPhysicalUnit V
  frame : NativePlanarFrame V
  citation : P93AuthorityCitationToken
  reference : CyclophanePlaneReference
  context : BlueBookP93.Acyclic.NomenclatureContext
  descriptor : CyclophanePlaneDescriptor

structure PlaneObservationBoundedIn (n : ℕ)
    (observation : P93CyclophanePlaneAuthorityObservation policy) : Prop where
  systemBound : CyclophaneSystemBoundedIn n observation.system
  unitBound : UnitBoundedIn n observation.unit
  frameBound : PlaneFrameBoundedIn n observation.frame

def relabelPlaneObservation [DecidableEq V] (enumeration : V ≃ Fin n)
    (observation : P93CyclophanePlaneAuthorityObservation policy)
    (bounded : PlaneObservationBoundedIn n observation) :
    NativeCyclophanePlaneAuthorityObservation V policy where
  system := relabelSystem enumeration observation.system bounded.systemBound
  unit := relabelUnit enumeration observation.unit bounded.unitBound
  frame := relabelPlane enumeration observation.frame bounded.frameBound
  citation := observation.citation
  reference := observation.reference
  context := observation.context
  descriptor := observation.descriptor

def decodePlaneObservation [DecidableEq V] (enumeration : V ≃ Fin n)
    (native : NativeCyclophanePlaneAuthorityObservation V policy) :
    P93CyclophanePlaneAuthorityObservation policy where
  system := decodeSystem enumeration native.system
  unit := unrelabelUnit enumeration native.unit
  frame := decodePlane enumeration native.frame
  citation := native.citation
  reference := native.reference
  context := native.context
  descriptor := native.descriptor

/-- The planar frame payload over `V` is recovered from its decoded source record. -/
theorem relabelPlane_decodePlane [DecidableEq V] (enumeration : V ≃ Fin n)
    (native : NativePlanarFrame V)
    (bounded : PlaneFrameBoundedIn n (decodePlane enumeration native)) :
    relabelPlane enumeration (decodePlane enumeration native) bounded = native := by
  obtain ⟨planeAtoms, pilotAtom, firstReference, secondReference, inPlaneBondAtom,
    outOfPlaneAtom, torsionRestricted, planeCannotBeSymmetryPlane⟩ := native
  have hPlaneAtoms : relabelList enumeration (unrelabelList enumeration planeAtoms)
      bounded.planeAtomsBound = planeAtoms :=
    relabelList_unrelabelList_anyBound enumeration planeAtoms bounded.planeAtomsBound
  have hPilot : decodeAtom enumeration (encodeAtom enumeration pilotAtom)
      bounded.pilotBound = pilotAtom := decodeAtom_encodeAtom enumeration pilotAtom _
  have hFirst : decodeAtom enumeration (encodeAtom enumeration firstReference)
      bounded.firstBound = firstReference := decodeAtom_encodeAtom enumeration firstReference _
  have hSecond : decodeAtom enumeration (encodeAtom enumeration secondReference)
      bounded.secondBound = secondReference :=
    decodeAtom_encodeAtom enumeration secondReference _
  have hInPlane : decodeAtom enumeration (encodeAtom enumeration inPlaneBondAtom)
      bounded.inPlaneBound = inPlaneBondAtom :=
    decodeAtom_encodeAtom enumeration inPlaneBondAtom _
  have hOutOfPlane : decodeAtom enumeration (encodeAtom enumeration outOfPlaneAtom)
      bounded.outOfPlaneBound = outOfPlaneAtom :=
    decodeAtom_encodeAtom enumeration outOfPlaneAtom _
  simp only [relabelPlane, decodePlane, hPlaneAtoms, hPilot, hFirst, hSecond, hInPlane,
    hOutOfPlane]

theorem decodePlaneObservation_relabelPlaneObservation [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (observation : P93CyclophanePlaneAuthorityObservation policy)
    (bounded : PlaneObservationBoundedIn n observation) :
    decodePlaneObservation enumeration
        (relabelPlaneObservation enumeration observation bounded) = observation := by
  obtain ⟨system, unit, frame, citation, reference, context, descriptor⟩ := observation
  simp [relabelPlaneObservation, decodePlaneObservation, decodeSystem_relabelSystem,
    unrelabelUnit_relabelUnit, decodePlane_relabelPlane]

theorem relabelPlaneObservation_decodePlaneObservation [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (native : NativeCyclophanePlaneAuthorityObservation V policy)
    (bounded : PlaneObservationBoundedIn n (decodePlaneObservation enumeration native)) :
    relabelPlaneObservation enumeration (decodePlaneObservation enumeration native) bounded =
      native := by
  obtain ⟨system, unit, frame, citation, reference, context, descriptor⟩ := native
  simp [relabelPlaneObservation, decodePlaneObservation, relabelSystem_decodeSystem,
    relabelUnit_unrelabelUnit, relabelPlane_decodePlane]

/-- Plane-observation bounds derived from the record's own `ValidFor`.  The system bounds come
from the mechanical source predicate, the unit bounds from `P93CyclophaneUnitSupported`, and the
frame bounds from the planar frame's own `ValidFor`, which is one conjunct of the observation
predicate. -/
theorem planeObservationBoundedIn_of_validFor (source : AuthoritativeChemicalInput)
    (observation : P93CyclophanePlaneAuthorityObservation policy)
    (valid : observation.ValidFor policy source) :
    PlaneObservationBoundedIn source.molecule.atomCount observation := by
  obtain ⟨systemValid, unitSupported, planeObserved, _rest⟩ := valid
  obtain ⟨members, _spatial, _high, _low, _highPoint, _lowPoint, _inPlanePoint,
    _outOfPlanePoint, _general, _unitEq, frameValid, _more⟩ := planeObserved
  have systemBound := cyclophaneSystemBoundedIn_of_mechanicallyValid source
    observation.system systemValid.1
  exact
    { systemBound := systemBound
      unitBound := unitBoundedIn_of_supported source.molecule.atomCount observation.system
        systemBound observation.unit unitSupported
      frameBound := planeFrameBoundedIn_of_validFor source members observation.frame frameValid }

/-! ## The center observation -/

/-- Native mirror of `P93CyclophaneCenterAuthorityObservation`. -/
structure NativeCyclophaneCenterAuthorityObservation (V : Type*)
    (policy : P93CyclophaneAuthorityPolicy) where
  system : NativeCyclophaneSystem V
  unit : SuppliedPhysicalUnit V
  citation : P93AuthorityCitationToken
  specification : NativeCyclophaneCenterSpecification V

structure CenterObservationBoundedIn (n : ℕ)
    (observation : P93CyclophaneCenterAuthorityObservation policy) : Prop where
  systemBound : CyclophaneSystemBoundedIn n observation.system
  unitBound : UnitBoundedIn n observation.unit
  specificationBound : CenterSpecificationBoundedIn n observation.specification

def relabelCenterObservation [DecidableEq V] (enumeration : V ≃ Fin n)
    (observation : P93CyclophaneCenterAuthorityObservation policy)
    (bounded : CenterObservationBoundedIn n observation) :
    NativeCyclophaneCenterAuthorityObservation V policy where
  system := relabelSystem enumeration observation.system bounded.systemBound
  unit := relabelUnit enumeration observation.unit bounded.unitBound
  citation := observation.citation
  specification := relabelCenterSpecification enumeration observation.specification
    bounded.specificationBound

def decodeCenterObservation [DecidableEq V] (enumeration : V ≃ Fin n)
    (native : NativeCyclophaneCenterAuthorityObservation V policy) :
    P93CyclophaneCenterAuthorityObservation policy where
  system := decodeSystem enumeration native.system
  unit := unrelabelUnit enumeration native.unit
  citation := native.citation
  specification := decodeCenterSpecification enumeration native.specification

theorem decodeCenterObservation_relabelCenterObservation [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (observation : P93CyclophaneCenterAuthorityObservation policy)
    (bounded : CenterObservationBoundedIn n observation) :
    decodeCenterObservation enumeration
        (relabelCenterObservation enumeration observation bounded) = observation := by
  obtain ⟨system, unit, citation, specification⟩ := observation
  simp [relabelCenterObservation, decodeCenterObservation, decodeSystem_relabelSystem,
    unrelabelUnit_relabelUnit, decodeCenterSpecification_relabelCenterSpecification]

theorem relabelCenterObservation_decodeCenterObservation [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (native : NativeCyclophaneCenterAuthorityObservation V policy)
    (bounded : CenterObservationBoundedIn n (decodeCenterObservation enumeration native)) :
    relabelCenterObservation enumeration (decodeCenterObservation enumeration native) bounded =
      native := by
  obtain ⟨system, unit, citation, specification⟩ := native
  simp [relabelCenterObservation, decodeCenterObservation, relabelSystem_decodeSystem,
    relabelUnit_unrelabelUnit, relabelCenterSpecification_decodeCenterSpecification]

/-- Center-observation bounds derived from the record's own `ValidFor`.  Candidate and assignment
centers are bounded because the carrier predicate proves each of them a member of `atomCarrier`,
which is itself bounded by `MechanicallyValidFor`.  The selected candidate is a member of the
candidate list by the reference rule. -/
theorem centerObservationBoundedIn_of_validFor (source : AuthoritativeChemicalInput)
    (observation : P93CyclophaneCenterAuthorityObservation policy)
    (valid : observation.ValidFor policy source) :
    CenterObservationBoundedIn source.molecule.atomCount observation := by
  obtain ⟨system, unit, citation, specification⟩ := observation
  obtain ⟨systemValid, _unitValid, unitSupported, _unitInSystem, _citationValid,
    _citationAuthorized, specificationValid⟩ := valid
  have systemBound := cyclophaneSystemBoundedIn_of_mechanicallyValid source system
    systemValid.1
  have unitBound := unitBoundedIn_of_supported source.molecule.atomCount system
    systemBound unit unitSupported
  refine
    { systemBound := systemBound
      unitBound := unitBound
      specificationBound := ?_ }
  cases specification with
  | cip context kind descriptor => exact trivial
  | relativeRCT candidates selected referenceSide assignments =>
      obtain ⟨_unitEq, _citationEq, _candidatesNe, _candidateCentersNodup,
        _candidateCitationsNodup, candidateValid, _coverage, uniqueReference,
        _sideNe, _sideObserved, _assignmentsNe, _assignmentCentersNodup,
        _assignmentCitationsNodup, _candidateCovered, assignmentSound⟩ := specificationValid
      refine ⟨?_, ?_, ?_⟩
      · intro candidate candidateMember
        exact systemBound.atomCarrierBound candidate.center
          (candidateValid candidate candidateMember).1
      · have selectedMember : selected ∈ candidates := uniqueReference.1.1
        exact systemBound.atomCarrierBound selected.center
          (candidateValid selected selectedMember).1
      · intro assignment assignmentMember
        obtain ⟨candidate, candidateMember, centerEq, _citationEq⟩ :=
          (assignmentSound assignment assignmentMember).1
        rw [centerEq]
        exact systemBound.atomCarrierBound candidate.center
          (candidateValid candidate candidateMember).1

/-! ## The double-bond observation -/

/-- Native mirror of `P93CyclophaneDoubleBondAuthorityObservation`.  `phaneRing` is a list of
indices into `phaneNodes`, not a list of atoms, and is copied verbatim; `descriptor?` keeps its
exact optional shape. -/
structure NativeCyclophaneDoubleBondAuthorityObservation (V : Type*)
    (policy : P93CyclophaneAuthorityPolicy) where
  system : NativeCyclophaneSystem V
  unit : SuppliedPhysicalUnit V
  ring : List V
  phaneRing : List Nat
  citation : P93AuthorityCitationToken
  geometry : MonocyclicSeniorLigandGeometry
  carbonContext : BlueBookP93.Acyclic.CarbonDoubleBondContext
  context : BlueBookP93.Acyclic.NomenclatureContext
  descriptor? : Option BlueBookP93.Acyclic.Descriptor

structure DoubleBondObservationBoundedIn (n : ℕ)
    (observation : P93CyclophaneDoubleBondAuthorityObservation policy) : Prop where
  systemBound : CyclophaneSystemBoundedIn n observation.system
  unitBound : UnitBoundedIn n observation.unit
  ringBound : ∀ atom ∈ observation.ring, atom < n

def relabelDoubleBondObservation [DecidableEq V] (enumeration : V ≃ Fin n)
    (observation : P93CyclophaneDoubleBondAuthorityObservation policy)
    (bounded : DoubleBondObservationBoundedIn n observation) :
    NativeCyclophaneDoubleBondAuthorityObservation V policy where
  system := relabelSystem enumeration observation.system bounded.systemBound
  unit := relabelUnit enumeration observation.unit bounded.unitBound
  ring := relabelList enumeration observation.ring bounded.ringBound
  phaneRing := observation.phaneRing
  citation := observation.citation
  geometry := observation.geometry
  carbonContext := observation.carbonContext
  context := observation.context
  descriptor? := observation.descriptor?

def decodeDoubleBondObservation [DecidableEq V] (enumeration : V ≃ Fin n)
    (native : NativeCyclophaneDoubleBondAuthorityObservation V policy) :
    P93CyclophaneDoubleBondAuthorityObservation policy where
  system := decodeSystem enumeration native.system
  unit := unrelabelUnit enumeration native.unit
  ring := unrelabelList enumeration native.ring
  phaneRing := native.phaneRing
  citation := native.citation
  geometry := native.geometry
  carbonContext := native.carbonContext
  context := native.context
  descriptor? := native.descriptor?

theorem decodeDoubleBondObservation_relabelDoubleBondObservation [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (observation : P93CyclophaneDoubleBondAuthorityObservation policy)
    (bounded : DoubleBondObservationBoundedIn n observation) :
    decodeDoubleBondObservation enumeration
        (relabelDoubleBondObservation enumeration observation bounded) = observation := by
  obtain ⟨system, unit, ring, phaneRing, citation, geometry, carbonContext, context,
    descriptor?⟩ := observation
  simp [relabelDoubleBondObservation, decodeDoubleBondObservation,
    decodeSystem_relabelSystem, unrelabelUnit_relabelUnit, unrelabelList_relabelList]

theorem relabelDoubleBondObservation_decodeDoubleBondObservation [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (native : NativeCyclophaneDoubleBondAuthorityObservation V policy)
    (bounded : DoubleBondObservationBoundedIn n
      (decodeDoubleBondObservation enumeration native)) :
    relabelDoubleBondObservation enumeration
        (decodeDoubleBondObservation enumeration native) bounded = native := by
  obtain ⟨system, unit, ring, phaneRing, citation, geometry, carbonContext, context,
    descriptor?⟩ := native
  have hRing : relabelList enumeration (unrelabelList enumeration ring) bounded.ringBound =
      ring := relabelList_unrelabelList_anyBound enumeration ring bounded.ringBound
  simp [relabelDoubleBondObservation, decodeDoubleBondObservation,
    relabelSystem_decodeSystem, relabelUnit_unrelabelUnit, hRing]

/-- Double-bond observation bounds derived from the record's own `ValidFor`.  The ring atoms are
bounded because `ValidFor` places the ring in `system.rings`, whose atoms `MechanicallyValidFor`
includes in `atomCarrier`. -/
theorem doubleBondObservationBoundedIn_of_validFor (source : AuthoritativeChemicalInput)
    (observation : P93CyclophaneDoubleBondAuthorityObservation policy)
    (valid : observation.ValidFor policy source) :
    DoubleBondObservationBoundedIn source.molecule.atomCount observation := by
  obtain ⟨system, unit, ring, phaneRing, citation, geometry, carbonContext, context,
    descriptor?⟩ := observation
  obtain ⟨systemValid, _unitValid, unitSupported, _bondEndpoints, ringMember, _cycleMember,
    _rest⟩ := valid
  have systemBound := cyclophaneSystemBoundedIn_of_mechanicallyValid source system
    systemValid.1
  refine
    { systemBound := systemBound
      unitBound := unitBoundedIn_of_supported source.molecule.atomCount system systemBound
        unit unitSupported
      ringBound := ?_ }
  intro atom atomMember
  exact systemBound.ringsBound ring ringMember atom atomMember

/-! ## The tagged observation sum

The carrier distinguishes exactly three observation shapes.  The tag is kept as an inductive
constructor, so a plane observation can never be decoded as a center or double-bond observation. -/

inductive NativeCyclophaneAuthorityObservation (V : Type*)
    (policy : P93CyclophaneAuthorityPolicy) where
  | plane (observation : NativeCyclophanePlaneAuthorityObservation V policy)
  | center (observation : NativeCyclophaneCenterAuthorityObservation V policy)
  | doubleBond (observation : NativeCyclophaneDoubleBondAuthorityObservation V policy)

/-- The source-side tagged sum: exactly the three pre-existing carrier records. -/
inductive SourceCyclophaneAuthorityObservation (policy : P93CyclophaneAuthorityPolicy) where
  | plane (observation : P93CyclophanePlaneAuthorityObservation policy)
  | center (observation : P93CyclophaneCenterAuthorityObservation policy)
  | doubleBond (observation : P93CyclophaneDoubleBondAuthorityObservation policy)

/-- Explicit bounds for a tagged source observation. -/
def SourceCyclophaneAuthorityObservation.BoundedIn (n : ℕ) :
    SourceCyclophaneAuthorityObservation policy → Prop
  | .plane observation => PlaneObservationBoundedIn n observation
  | .center observation => CenterObservationBoundedIn n observation
  | .doubleBond observation => DoubleBondObservationBoundedIn n observation

/-- Bounds of a decoded planar frame: every reference is the encoding of a native label. -/
def decodePlaneFrameBounded [DecidableEq V] (enumeration : V ≃ Fin n)
    (native : NativePlanarFrame V) :
    PlaneFrameBoundedIn n (decodePlane enumeration native) where
  pilotBound := encodeAtom_lt enumeration native.pilotAtom
  firstBound := encodeAtom_lt enumeration native.firstReference
  secondBound := encodeAtom_lt enumeration native.secondReference
  inPlaneBound := encodeAtom_lt enumeration native.inPlaneBondAtom
  outOfPlaneBound := encodeAtom_lt enumeration native.outOfPlaneAtom
  planeAtomsBound := unrelabelList_bounded enumeration native.planeAtoms

/-- Relabel a bounded tagged observation. -/
def relabelObservation [DecidableEq V] (enumeration : V ≃ Fin n) :
    (observation : SourceCyclophaneAuthorityObservation policy) →
      observation.BoundedIn n → NativeCyclophaneAuthorityObservation V policy
  | .plane observation, bounded =>
      .plane (relabelPlaneObservation enumeration observation bounded)
  | .center observation, bounded =>
      .center (relabelCenterObservation enumeration observation bounded)
  | .doubleBond observation, bounded =>
      .doubleBond (relabelDoubleBondObservation enumeration observation bounded)

/-- Decode a tagged observation to the exact pre-existing carrier record. -/
def unrelabelObservation [DecidableEq V] (enumeration : V ≃ Fin n) :
    NativeCyclophaneAuthorityObservation V policy → SourceCyclophaneAuthorityObservation policy
  | .plane observation => .plane (decodePlaneObservation enumeration observation)
  | .center observation => .center (decodeCenterObservation enumeration observation)
  | .doubleBond observation => .doubleBond (decodeDoubleBondObservation enumeration observation)

/-- Exact recovery of every pre-existing cyclophane observation record, constructor by
constructor.  No original record is stored as a payload. -/
theorem unrelabelObservation_relabelObservation [DecidableEq V] (enumeration : V ≃ Fin n)
    (observation : SourceCyclophaneAuthorityObservation policy)
    (bounded : observation.BoundedIn n) :
    unrelabelObservation enumeration (relabelObservation enumeration observation bounded) =
      observation := by
  cases observation with
  | plane observation =>
      simp [relabelObservation, unrelabelObservation,
        decodePlaneObservation_relabelPlaneObservation]
  | center observation =>
      simp [relabelObservation, unrelabelObservation,
        decodeCenterObservation_relabelCenterObservation]
  | doubleBond observation =>
      simp [relabelObservation, unrelabelObservation,
        decodeDoubleBondObservation_relabelDoubleBondObservation]

/-- Bounds of a decoded tagged observation. -/
def unrelabelObservationBounded [DecidableEq V] (enumeration : V ≃ Fin n) :
    (observation : NativeCyclophaneAuthorityObservation V policy) →
      (unrelabelObservation enumeration observation).BoundedIn n
  | .plane observation =>
      { systemBound := decodeSystemBounded enumeration observation.system
        unitBound := unrelabelUnitBounded enumeration observation.unit
        frameBound := decodePlaneFrameBounded enumeration observation.frame }
  | .center observation =>
      { systemBound := decodeSystemBounded enumeration observation.system
        unitBound := unrelabelUnitBounded enumeration observation.unit
        specificationBound :=
          decodeCenterSpecificationBounded enumeration observation.specification }
  | .doubleBond observation =>
      { systemBound := decodeSystemBounded enumeration observation.system
        unitBound := unrelabelUnitBounded enumeration observation.unit
        ringBound := unrelabelList_bounded enumeration observation.ring }

/-- Relabelling a decoded tagged observation returns the native observation. -/
theorem relabelObservation_unrelabelObservation [DecidableEq V] (enumeration : V ≃ Fin n)
    (observation : NativeCyclophaneAuthorityObservation V policy) :
    relabelObservation enumeration (unrelabelObservation enumeration observation)
        (unrelabelObservationBounded enumeration observation) = observation := by
  cases observation with
  | plane observation =>
      simp [relabelObservation, unrelabelObservation,
        relabelPlaneObservation_decodePlaneObservation]
  | center observation =>
      simp [relabelObservation, unrelabelObservation,
        relabelCenterObservation_decodeCenterObservation]
  | doubleBond observation =>
      simp [relabelObservation, unrelabelObservation,
        relabelDoubleBondObservation_decodeDoubleBondObservation]

/-! ## Direct `ValidFor`-only ingress for every variant -/

/-- Plane ingress which needs no explicit bound: the bound is derived from the record's own
`ValidFor`, and the enumeration is exactly the source atom-count enumeration. -/
def ofSourcePlaneObservation [DecidableEq V] (source : AuthoritativeChemicalInput)
    (enumeration : V ≃ Fin source.molecule.atomCount)
    (observation : P93CyclophanePlaneAuthorityObservation policy)
    (valid : observation.ValidFor policy source) :
    NativeCyclophanePlaneAuthorityObservation V policy :=
  relabelPlaneObservation enumeration observation
    (planeObservationBoundedIn_of_validFor source observation valid)

/-- Exact recovery of a plane observation from `ValidFor` alone. -/
theorem decodePlaneObservation_ofSourcePlaneObservation [DecidableEq V]
    (source : AuthoritativeChemicalInput)
    (enumeration : V ≃ Fin source.molecule.atomCount)
    (observation : P93CyclophanePlaneAuthorityObservation policy)
    (valid : observation.ValidFor policy source) :
    decodePlaneObservation enumeration
        (ofSourcePlaneObservation source enumeration observation valid) = observation :=
  decodePlaneObservation_relabelPlaneObservation enumeration observation
    (planeObservationBoundedIn_of_validFor source observation valid)

/-- Center ingress which needs no explicit bound. -/
def ofSourceCenterObservation [DecidableEq V] (source : AuthoritativeChemicalInput)
    (enumeration : V ≃ Fin source.molecule.atomCount)
    (observation : P93CyclophaneCenterAuthorityObservation policy)
    (valid : observation.ValidFor policy source) :
    NativeCyclophaneCenterAuthorityObservation V policy :=
  relabelCenterObservation enumeration observation
    (centerObservationBoundedIn_of_validFor source observation valid)

/-- Exact recovery of a center observation from `ValidFor` alone. -/
theorem decodeCenterObservation_ofSourceCenterObservation [DecidableEq V]
    (source : AuthoritativeChemicalInput)
    (enumeration : V ≃ Fin source.molecule.atomCount)
    (observation : P93CyclophaneCenterAuthorityObservation policy)
    (valid : observation.ValidFor policy source) :
    decodeCenterObservation enumeration
        (ofSourceCenterObservation source enumeration observation valid) = observation :=
  decodeCenterObservation_relabelCenterObservation enumeration observation
    (centerObservationBoundedIn_of_validFor source observation valid)

/-- Double-bond ingress which needs no explicit bound. -/
def ofSourceDoubleBondObservation [DecidableEq V] (source : AuthoritativeChemicalInput)
    (enumeration : V ≃ Fin source.molecule.atomCount)
    (observation : P93CyclophaneDoubleBondAuthorityObservation policy)
    (valid : observation.ValidFor policy source) :
    NativeCyclophaneDoubleBondAuthorityObservation V policy :=
  relabelDoubleBondObservation enumeration observation
    (doubleBondObservationBoundedIn_of_validFor source observation valid)

/-- Exact recovery of a double-bond observation from `ValidFor` alone, including the optional
descriptor's exact shape. -/
theorem decodeDoubleBondObservation_ofSourceDoubleBondObservation [DecidableEq V]
    (source : AuthoritativeChemicalInput)
    (enumeration : V ≃ Fin source.molecule.atomCount)
    (observation : P93CyclophaneDoubleBondAuthorityObservation policy)
    (valid : observation.ValidFor policy source) :
    decodeDoubleBondObservation enumeration
        (ofSourceDoubleBondObservation source enumeration observation valid) = observation :=
  decodeDoubleBondObservation_relabelDoubleBondObservation enumeration observation
    (doubleBondObservationBoundedIn_of_validFor source observation valid)

/-! ## Existing validity predicates, consumed at the same source and policy -/

/-- The existing `ValidFor` of each pre-existing record, dispatched on the tag. -/
def SourceCyclophaneAuthorityObservation.ValidFor
    (source : AuthoritativeChemicalInput) :
    SourceCyclophaneAuthorityObservation policy → Prop
  | .plane observation => observation.ValidFor policy source
  | .center observation => observation.ValidFor policy source
  | .doubleBond observation => observation.ValidFor policy source

/-- Bounds derived from the actual `ValidFor` of a tagged source observation.  No spatial
well-formedness or atom-count hypothesis is needed: each variant's own predicate already bounds
its atom references. -/
theorem SourceCyclophaneAuthorityObservation.boundedIn_of_validFor
    (source : AuthoritativeChemicalInput)
    (observation : SourceCyclophaneAuthorityObservation policy)
    (valid : observation.ValidFor source) :
    observation.BoundedIn source.molecule.atomCount := by
  cases observation with
  | plane observation => exact planeObservationBoundedIn_of_validFor source observation valid
  | center observation => exact centerObservationBoundedIn_of_validFor source observation valid
  | doubleBond observation =>
      exact doubleBondObservationBoundedIn_of_validFor source observation valid

/-- **Validity transport through the exact decode.**  For every tagged observation, the decoded
record's `ValidFor` at the same `source` and `policy` is equivalent to the original record's
`ValidFor`.  The equivalence is the record equality, not an invariance claim about an arbitrary
renumbering. -/
theorem validFor_unrelabelObservation_relabelObservation_iff [DecidableEq V]
    (enumeration : V ≃ Fin n) (source : AuthoritativeChemicalInput)
    (observation : SourceCyclophaneAuthorityObservation policy)
    (bounded : observation.BoundedIn n) :
    (unrelabelObservation enumeration
        (relabelObservation enumeration observation bounded)).ValidFor source ↔
      observation.ValidFor source := by
  rw [unrelabelObservation_relabelObservation]

/-- Forward validity preservation at the same source and policy. -/
theorem validFor_of_relabelObservation [DecidableEq V] (enumeration : V ≃ Fin n)
    (source : AuthoritativeChemicalInput)
    (observation : SourceCyclophaneAuthorityObservation policy)
    (bounded : observation.BoundedIn n)
    (valid : observation.ValidFor source) :
    (unrelabelObservation enumeration
        (relabelObservation enumeration observation bounded)).ValidFor source :=
  (validFor_unrelabelObservation_relabelObservation_iff enumeration source observation
    bounded).mpr valid

/-- Validity transport for a decoded native observation through a full native round trip. -/
theorem validFor_unrelabelObservation_roundtrip_iff [DecidableEq V]
    (enumeration : V ≃ Fin n) (source : AuthoritativeChemicalInput)
    (observation : NativeCyclophaneAuthorityObservation V policy) :
    (unrelabelObservation enumeration
        (relabelObservation enumeration (unrelabelObservation enumeration observation)
          (unrelabelObservationBounded enumeration observation))).ValidFor source ↔
      (unrelabelObservation enumeration observation).ValidFor source := by
  rw [relabelObservation_unrelabelObservation]

/-- Tagged ingress which needs only the observation and its own `ValidFor`. -/
def SourceCyclophaneAuthorityObservation.ofSource [DecidableEq V]
    (source : AuthoritativeChemicalInput)
    (enumeration : V ≃ Fin source.molecule.atomCount)
    (observation : SourceCyclophaneAuthorityObservation policy)
    (valid : observation.ValidFor source) :
    NativeCyclophaneAuthorityObservation V policy :=
  relabelObservation enumeration observation
    (SourceCyclophaneAuthorityObservation.boundedIn_of_validFor source observation valid)

/-- Exact recovery of a tagged observation from its own `ValidFor` alone. -/
theorem unrelabelObservation_ofSource [DecidableEq V]
    (source : AuthoritativeChemicalInput)
    (enumeration : V ≃ Fin source.molecule.atomCount)
    (observation : SourceCyclophaneAuthorityObservation policy)
    (valid : observation.ValidFor source) :
    unrelabelObservation enumeration
        (SourceCyclophaneAuthorityObservation.ofSource source enumeration observation valid) =
      observation :=
  unrelabelObservation_relabelObservation enumeration observation
    (SourceCyclophaneAuthorityObservation.boundedIn_of_validFor source observation valid)

/-- Validity of the decoded tagged ingress at the original source and policy. -/
theorem validFor_unrelabelObservation_ofSource [DecidableEq V]
    (source : AuthoritativeChemicalInput)
    (enumeration : V ≃ Fin source.molecule.atomCount)
    (observation : SourceCyclophaneAuthorityObservation policy)
    (valid : observation.ValidFor source) :
    (unrelabelObservation enumeration
        (SourceCyclophaneAuthorityObservation.ofSource source enumeration observation valid)
      ).ValidFor source :=
  (validFor_unrelabelObservation_relabelObservation_iff enumeration source observation
    (SourceCyclophaneAuthorityObservation.boundedIn_of_validFor source observation
      valid)).mpr valid

/-! ## Ordered heterogeneous lists -/

def relabelObservationList [DecidableEq V] (enumeration : V ≃ Fin n)
    (observations : List (SourceCyclophaneAuthorityObservation policy))
    (bounded : ∀ observation ∈ observations, observation.BoundedIn n) :
    List (NativeCyclophaneAuthorityObservation V policy) :=
  observations.attach.map fun observation =>
    relabelObservation enumeration observation.1 (bounded observation.1 observation.2)

def unrelabelObservationList [DecidableEq V] (enumeration : V ≃ Fin n)
    (observations : List (NativeCyclophaneAuthorityObservation V policy)) :
    List (SourceCyclophaneAuthorityObservation policy) :=
  observations.map (unrelabelObservation enumeration)

def unrelabelObservationListBounded [DecidableEq V] (enumeration : V ≃ Fin n)
    (observations : List (NativeCyclophaneAuthorityObservation V policy)) :
    ∀ observation ∈ unrelabelObservationList enumeration observations,
      observation.BoundedIn n := by
  intro observation member
  rw [unrelabelObservationList, List.mem_map] at member
  rcases member with ⟨presented, _presentedMember, rfl⟩
  exact unrelabelObservationBounded enumeration presented

@[simp] theorem relabelObservationList_length [DecidableEq V] (enumeration : V ≃ Fin n)
    (observations : List (SourceCyclophaneAuthorityObservation policy))
    (bounded : ∀ observation ∈ observations, observation.BoundedIn n) :
    (relabelObservationList enumeration observations bounded).length =
      observations.length := by
  simp [relabelObservationList]

@[simp] theorem unrelabelObservationList_length [DecidableEq V] (enumeration : V ≃ Fin n)
    (observations : List (NativeCyclophaneAuthorityObservation V policy)) :
    (unrelabelObservationList enumeration observations).length = observations.length := by
  simp [unrelabelObservationList]

/-- Exact recovery of the ordered heterogeneous list, including order, multiplicity and each
concrete record shape. -/
theorem unrelabelObservationList_relabelObservationList [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (observations : List (SourceCyclophaneAuthorityObservation policy))
    (bounded : ∀ observation ∈ observations, observation.BoundedIn n) :
    unrelabelObservationList enumeration
        (relabelObservationList enumeration observations bounded) = observations := by
  unfold unrelabelObservationList relabelObservationList
  rw [List.map_map]
  trans observations.attach.map Subtype.val
  · apply List.map_congr_left
    intro observation _
    exact unrelabelObservation_relabelObservation enumeration observation.1
      (bounded observation.1 observation.2)
  · exact List.attach_map_subtype_val observations

/-- Relabelling a decoded heterogeneous list returns the native list. -/
theorem relabelObservationList_unrelabelObservationList [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (observations : List (NativeCyclophaneAuthorityObservation V policy)) :
    relabelObservationList enumeration (unrelabelObservationList enumeration observations)
        (unrelabelObservationListBounded enumeration observations) = observations := by
  unfold relabelObservationList unrelabelObservationList
  rw [List.attach_map, List.map_map]
  trans observations.attach.map Subtype.val
  · apply List.map_congr_left
    intro observation _
    exact relabelObservation_unrelabelObservation enumeration observation.1
  · exact List.attach_map_subtype_val observations

/-! ## Correlated sets of observations

A `Set` records no order or multiplicity, so this section is separate from the ordered-list codec
above.  The bound is correlated with membership: each element comes with its own proof. -/

def relabelObservationSet [DecidableEq V] (enumeration : V ≃ Fin n)
    (observations : Set (SourceCyclophaneAuthorityObservation policy))
    (bounded : ∀ observation ∈ observations, observation.BoundedIn n) :
    Set (NativeCyclophaneAuthorityObservation V policy) :=
  fun presented =>
    ∃ observation, ∃ member : observation ∈ observations,
      relabelObservation enumeration observation (bounded observation member) = presented

def unrelabelObservationSet [DecidableEq V] (enumeration : V ≃ Fin n)
    (observations : Set (NativeCyclophaneAuthorityObservation V policy)) :
    Set (SourceCyclophaneAuthorityObservation policy) :=
  fun recovered =>
    ∃ presented ∈ observations,
      unrelabelObservation enumeration presented = recovered

def unrelabelObservationSetBounded [DecidableEq V] (enumeration : V ≃ Fin n)
    (observations : Set (NativeCyclophaneAuthorityObservation V policy)) :
    ∀ observation ∈ unrelabelObservationSet enumeration observations,
      observation.BoundedIn n := by
  rintro recovered ⟨presented, _presentedMember, rfl⟩
  exact unrelabelObservationBounded enumeration presented

theorem unrelabelObservationSet_relabelObservationSet [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (observations : Set (SourceCyclophaneAuthorityObservation policy))
    (bounded : ∀ observation ∈ observations, observation.BoundedIn n) :
    unrelabelObservationSet enumeration
        (relabelObservationSet enumeration observations bounded) = observations := by
  ext recovered
  constructor
  · rintro ⟨presented, ⟨observation, member, relabelEq⟩, decodeEq⟩
    rw [← relabelEq] at decodeEq
    rw [unrelabelObservation_relabelObservation] at decodeEq
    rw [← decodeEq]
    exact member
  · intro member
    exact ⟨relabelObservation enumeration recovered (bounded recovered member),
      ⟨recovered, member, rfl⟩,
      unrelabelObservation_relabelObservation enumeration recovered (bounded recovered member)⟩

/-- Relabelling does not inspect the proof of boundedness. -/
theorem relabelObservation_bound_irrel [DecidableEq V] (enumeration : V ≃ Fin n)
    (observation : SourceCyclophaneAuthorityObservation policy)
    (first second : observation.BoundedIn n) :
    relabelObservation enumeration observation first =
      relabelObservation enumeration observation second := by
  cases observation <;> rfl

/-- Relabelling respects equality of the underlying source observation, independently of how the
two boundedness proofs were obtained. -/
theorem relabelObservation_congr [DecidableEq V] (enumeration : V ≃ Fin n)
    {first second : SourceCyclophaneAuthorityObservation policy} (h : first = second)
    (firstBounded : first.BoundedIn n) (secondBounded : second.BoundedIn n) :
    relabelObservation enumeration first firstBounded =
      relabelObservation enumeration second secondBounded := by
  cases h
  exact relabelObservation_bound_irrel enumeration _ firstBounded secondBounded

/-- The correlated-set inverse on the native side. -/
theorem relabelObservationSet_unrelabelObservationSet [DecidableEq V]
    (enumeration : V ≃ Fin n)
    (observations : Set (NativeCyclophaneAuthorityObservation V policy)) :
    relabelObservationSet enumeration (unrelabelObservationSet enumeration observations)
        (unrelabelObservationSetBounded enumeration observations) = observations := by
  ext presented
  constructor
  · rintro ⟨observation, ⟨presented₀, presentedMember, decodeEq⟩, relabelEq⟩
    have obsEq : unrelabelObservation enumeration presented = observation := by
      have := congrArg (unrelabelObservation enumeration) relabelEq.symm
      rwa [unrelabelObservation_relabelObservation] at this
    have decodeEq' : unrelabelObservation enumeration presented₀ =
        unrelabelObservation enumeration presented := by
      rw [decodeEq, ← obsEq]
    have key : relabelObservation enumeration (unrelabelObservation enumeration presented₀)
        (unrelabelObservationBounded enumeration presented₀) = presented := by
      calc
        relabelObservation enumeration (unrelabelObservation enumeration presented₀)
            (unrelabelObservationBounded enumeration presented₀) =
          relabelObservation enumeration (unrelabelObservation enumeration presented)
            (unrelabelObservationBounded enumeration presented) :=
          relabelObservation_congr enumeration decodeEq' _ _
        _ = presented := relabelObservation_unrelabelObservation enumeration presented
    have presentedEq : presented = presented₀ := by
      rw [← key, relabelObservation_unrelabelObservation]
    simpa [presentedEq] using presentedMember
  · intro member
    exact ⟨unrelabelObservation enumeration presented,
      ⟨presented, member, rfl⟩,
      relabelObservation_unrelabelObservation enumeration presented⟩

/-- **Correlated validity for a set.**  A native observation belongs to the image of a set exactly
when its decoded record is one of the source observations, so its `ValidFor` at the same source
and policy is exactly the validity of that source observation. -/
theorem validFor_mem_relabelObservationSet_iff [DecidableEq V] (enumeration : V ≃ Fin n)
    (source : AuthoritativeChemicalInput)
    (observations : Set (SourceCyclophaneAuthorityObservation policy))
    (bounded : ∀ observation ∈ observations, observation.BoundedIn n)
    (presented : NativeCyclophaneAuthorityObservation V policy)
    (member : presented ∈ relabelObservationSet enumeration observations bounded) :
    (unrelabelObservation enumeration presented).ValidFor source ↔
      ∃ observation, ∃ observationMember : observation ∈ observations,
        relabelObservation enumeration observation
            (bounded observation observationMember) = presented ∧
          observation.ValidFor source := by
  constructor
  · intro valid
    rcases member with ⟨observation, observationMember, relabelEq⟩
    refine ⟨observation, observationMember, relabelEq, ?_⟩
    rw [← relabelEq] at valid
    rwa [unrelabelObservation_relabelObservation] at valid
  · rintro ⟨observation, observationMember, relabelEq, valid⟩
    rw [← relabelEq]
    rwa [unrelabelObservation_relabelObservation]

/-! ## Shared source context and the composable satellite -/

/-- The common source binding: the existing molecule-codec binding from
`OrganicStereoP93PhysicalFrameIngress`.  It ties a shared finite graph, coordinate channel and
diagram channel to the authoritative input by actual equalities, not by an atom count. -/
abbrev CyclophaneSourceBinding (V : Type*) [DecidableEq V] [Fintype V] :=
  OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V

/-- Bounds of a tagged observation derived from its validity and the exact source binding. -/
theorem SourceCyclophaneAuthorityObservation.boundedIn_of_validFor_binding
    [DecidableEq V] [Fintype V]
    (binding : CyclophaneSourceBinding V)
    (observation : SourceCyclophaneAuthorityObservation policy)
    (valid : observation.ValidFor binding.source) :
    observation.BoundedIn (Fintype.card V) := by
  have bounded := SourceCyclophaneAuthorityObservation.boundedIn_of_validFor binding.source
    observation valid
  rwa [binding.atomCount_eq] at bounded

/-- A raw cyclophane observation source: the exact source binding plus an ordered list of
`Nat`-indexed carrier observations, each valid at the bound source. -/
structure RawCyclophaneAuthorityObservationSource (V : Type*) [DecidableEq V] [Fintype V]
    (policy : P93CyclophaneAuthorityPolicy) where
  binding : CyclophaneSourceBinding V
  observations : List (SourceCyclophaneAuthorityObservation policy)
  valid : ∀ observation ∈ observations, observation.ValidFor binding.source

/-- The composable native satellite.  It carries the same graph/spatial/diagram context as the
existing molecule codec and the ordered list of native observations.  No original observation and
no original `AuthoritativeChemicalInput` is stored here. -/
structure CyclophaneAuthorityObservationSatellite (V : Type*) [DecidableEq V] [Fintype V]
    (policy : P93CyclophaneAuthorityPolicy) where
  graph : FiniteAtomInteractionHypergraph V
  spatial? : Option (V → CartesianPoint3) := none
  diagram? : Option (OrganicDiagramSource V) := none
  observations : List (NativeCyclophaneAuthorityObservation V policy)

namespace CyclophaneAuthorityObservationSatellite

variable [DecidableEq V] [Fintype V]

/-- The shared finite source, with observations intentionally excluded. -/
def toFiniteSource (satellite : CyclophaneAuthorityObservationSatellite V policy) :
    OrganicFiniteSource V where
  graph := satellite.graph
  spatial? := satellite.spatial?
  diagram? := satellite.diagram?

end CyclophaneAuthorityObservationSatellite

/-- Adapt a raw source into the satellite: keep the exact shared finite source and relabel every
observation, deriving its bounds from its actual `ValidFor`. -/
def adapt [DecidableEq V] [Fintype V]
    (raw : RawCyclophaneAuthorityObservationSource V policy) :
    CyclophaneAuthorityObservationSatellite V policy where
  graph := raw.binding.shared.graph
  spatial? := raw.binding.shared.spatial?
  diagram? := raw.binding.shared.diagram?
  observations := raw.observations.attach.map fun observation =>
    relabelObservation raw.binding.enumeration observation.1
      (SourceCyclophaneAuthorityObservation.boundedIn_of_validFor_binding raw.binding
        observation.1 (raw.valid observation.1 observation.2))

@[simp] theorem adapt_graph [DecidableEq V] [Fintype V]
    (raw : RawCyclophaneAuthorityObservationSource V policy) :
    (adapt raw).graph = raw.binding.shared.graph := rfl

@[simp] theorem adapt_spatial? [DecidableEq V] [Fintype V]
    (raw : RawCyclophaneAuthorityObservationSource V policy) :
    (adapt raw).spatial? = raw.binding.shared.spatial? := rfl

@[simp] theorem adapt_diagram? [DecidableEq V] [Fintype V]
    (raw : RawCyclophaneAuthorityObservationSource V policy) :
    (adapt raw).diagram? = raw.binding.shared.diagram? := rfl

/-- The recovered source record: the exact authoritative input and the decoded observation list. -/
@[ext] structure RecoveredCyclophaneAuthorityObservationSource
    (policy : P93CyclophaneAuthorityPolicy) where
  source : AuthoritativeChemicalInput
  observations : List (SourceCyclophaneAuthorityObservation policy)

/-- Decode a satellite into the recovered source record.  The authoritative input is the exact
encode of the shared finite source; observations are decoded with the same enumeration. -/
def suppliedSource [DecidableEq V] [Fintype V]
    (enumeration : V ≃ Fin (Fintype.card V))
    (satellite : CyclophaneAuthorityObservationSatellite V policy) :
    RecoveredCyclophaneAuthorityObservationSource policy where
  source := satellite.toFiniteSource.encode enumeration
  observations := unrelabelObservationList enumeration satellite.observations

/-- **Exact full source recovery.**  Adapting a raw source and decoding it returns the exact
authoritative input (through the binding's actual source equality) and the exact ordered list of
pre-existing cyclophane observation records. -/
theorem suppliedSource_adapt [DecidableEq V] [Fintype V]
    (raw : RawCyclophaneAuthorityObservationSource V policy) :
    suppliedSource raw.binding.enumeration (adapt raw) =
      { source := raw.binding.source, observations := raw.observations } := by
  apply RecoveredCyclophaneAuthorityObservationSource.ext
  · exact raw.binding.encode_shared
  · change unrelabelObservationList raw.binding.enumeration (adapt raw).observations =
      raw.observations
    rw [show (adapt raw).observations = raw.observations.attach.map (fun observation =>
        relabelObservation raw.binding.enumeration observation.1
          (SourceCyclophaneAuthorityObservation.boundedIn_of_validFor_binding raw.binding
            observation.1 (raw.valid observation.1 observation.2))) from rfl]
    exact unrelabelObservationList_relabelObservationList raw.binding.enumeration
      raw.observations (fun observation member =>
        SourceCyclophaneAuthorityObservation.boundedIn_of_validFor_binding raw.binding
          observation (raw.valid observation member))

/-- The recovered authoritative input is exactly the bound source. -/
theorem suppliedSource_adapt_source [DecidableEq V] [Fintype V]
    (raw : RawCyclophaneAuthorityObservationSource V policy) :
    (suppliedSource raw.binding.enumeration (adapt raw)).source = raw.binding.source :=
  congrArg RecoveredCyclophaneAuthorityObservationSource.source (suppliedSource_adapt raw)

/-- The recovered ordered observation list is exactly the raw list. -/
theorem suppliedSource_adapt_observations [DecidableEq V] [Fintype V]
    (raw : RawCyclophaneAuthorityObservationSource V policy) :
    (suppliedSource raw.binding.enumeration (adapt raw)).observations = raw.observations :=
  congrArg RecoveredCyclophaneAuthorityObservationSource.observations (suppliedSource_adapt raw)

/-- The satellite graph encodes to exactly the source molecule (the binding's graph equality). -/
theorem adapt_graph_encode [DecidableEq V] [Fintype V]
    (raw : RawCyclophaneAuthorityObservationSource V policy) :
    (adapt raw).graph.encode raw.binding.enumeration = raw.binding.source.molecule :=
  raw.binding.graph_eq

/-- The satellite spatial channel encodes to exactly the source spatial channel. -/
theorem adapt_spatial_encode [DecidableEq V] [Fintype V]
    (raw : RawCyclophaneAuthorityObservationSource V policy) :
    OrganicFiniteSource.encodeSpatial? raw.binding.enumeration (adapt raw).spatial? =
      raw.binding.source.spatial? :=
  raw.binding.spatial_eq

/-- The satellite diagram channel encodes to exactly the source diagram channel. -/
theorem adapt_diagram_encode [DecidableEq V] [Fintype V]
    (raw : RawCyclophaneAuthorityObservationSource V policy) :
    (adapt raw).diagram?.map (OrganicDiagramSource.encodeDiagram raw.binding.enumeration) =
      raw.binding.source.diagram? :=
  raw.binding.diagram_eq

/-- Validity is preserved for the whole recovered list at the same source and policy. -/
theorem suppliedSource_adapt_validFor [DecidableEq V] [Fintype V]
    (raw : RawCyclophaneAuthorityObservationSource V policy)
    (observation : SourceCyclophaneAuthorityObservation policy)
    (member : observation ∈
      (suppliedSource raw.binding.enumeration (adapt raw)).observations) :
    observation.ValidFor raw.binding.source := by
  have listEq : (suppliedSource raw.binding.enumeration (adapt raw)).observations =
      raw.observations := by
    simpa using congrArg RecoveredCyclophaneAuthorityObservationSource.observations
      (suppliedSource_adapt raw)
  have sourceMember : observation ∈ raw.observations := by
    rw [← listEq]
    exact member
  exact raw.valid observation sourceMember

/-! ## Concrete certified-source adapter -/

/-- The concrete binding of a certified authoritative input to its exact finite ingress source,
reusing the existing molecule codec's certified binding. -/
def certifiedBinding (certified : CertifiedAuthoritativeChemicalInput) :
    CyclophaneSourceBinding (Fin certified.input.molecule.atomCount) :=
  OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding.ofCertified certified

/-- Adapt a certified source together with an ordered list of valid carrier observations. -/
def adaptCertified (certified : CertifiedAuthoritativeChemicalInput)
    (observations : List (SourceCyclophaneAuthorityObservation policy))
    (valid : ∀ observation ∈ observations,
      observation.ValidFor certified.input) :
    CyclophaneAuthorityObservationSatellite (Fin certified.input.molecule.atomCount) policy :=
  adapt { binding := certifiedBinding certified
          observations := observations
          valid := valid }

/-- **Concrete exact recovery from a certified source.** -/
theorem suppliedSource_adaptCertified
    (certified : CertifiedAuthoritativeChemicalInput)
    (observations : List (SourceCyclophaneAuthorityObservation policy))
    (valid : ∀ observation ∈ observations,
      observation.ValidFor certified.input) :
    suppliedSource (identityEnumeration certified.input.molecule.atomCount)
        (adaptCertified certified observations valid) =
      { source := certified.input, observations := observations } :=
  suppliedSource_adapt
    { binding := certifiedBinding certified
      observations := observations
      valid := valid }

/-! ## Common enumeration compatibility

The codec's enumeration is the same map used by the accepted common-index bridge.  The two facts
below record that encoding a common index returns the source index number and that encoding a
native label and taking its common index returns the original label.  They are stated both for a
certified source (through `OrganicStereoObservationCommonIndexBridge.commonIndexEquiv`) and for a
`PhysicalFrameSourceBinding` (through its derived count equality).
-/

open OrganicStereoObservationCommonIndexBridge

/-- Encoding the common index of a certified source returns the source atom number. -/
theorem encodeAtom_commonIndexEquiv [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V) (enumeration : V ≃ Fin (Fintype.card V))
    (certified : CertifiedAuthoritativeChemicalInput)
    (h : certified.input.molecule = graph.encode enumeration)
    (index : SourceAtomIndex certified) :
    encodeAtom enumeration (commonIndexEquiv graph enumeration certified h index) =
      index.val := by
  show (enumeration (commonIndexEquiv graph enumeration certified h index)).val = index.val
  exact congrArg Fin.val
    (enumeration_commonIndexEquiv graph enumeration certified h index)

/-- The source atom index of a native label, for a certified source whose molecule is the common
graph encoding. -/
def sourceIndexOfAtom [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V) (enumeration : V ≃ Fin (Fintype.card V))
    (certified : CertifiedAuthoritativeChemicalInput)
    (h : certified.input.molecule = graph.encode enumeration) (atom : V) :
    SourceAtomIndex certified :=
  ⟨encodeAtom enumeration atom, by
    rw [source_atomCount_eq_encoded graph enumeration certified h]
    exact encodeAtom_lt enumeration atom⟩

/-- The common index of the encoded native label is the original native label. -/
theorem commonIndexEquiv_sourceIndexOfAtom [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V) (enumeration : V ≃ Fin (Fintype.card V))
    (certified : CertifiedAuthoritativeChemicalInput)
    (h : certified.input.molecule = graph.encode enumeration) (atom : V) :
    commonIndexEquiv graph enumeration certified h
        (sourceIndexOfAtom graph enumeration certified h atom) = atom := by
  have castEq : finCongr (source_atomCount_eq_encoded graph enumeration certified h)
      (sourceIndexOfAtom graph enumeration certified h atom) = enumeration atom := by
    apply Fin.ext
    simp [sourceIndexOfAtom, encodeAtom]
  simp only [commonIndexEquiv, Equiv.trans_apply]
  rw [castEq, Equiv.symm_apply_apply]

/-- The common index bijection derived from a physical-frame source binding.  It is the same
construction as `commonIndexEquiv`, with the source count equality supplied by the binding. -/
def commonIndexEquivOfBinding [DecidableEq V] [Fintype V]
    (binding : CyclophaneSourceBinding V) :
    Fin binding.source.molecule.atomCount ≃ V :=
  (finCongr binding.atomCount_eq).trans binding.enumeration.symm

/-- The binding's atom number at a native label. -/
def encodeAtomBindingIndex [DecidableEq V] [Fintype V]
    (binding : CyclophaneSourceBinding V) (atom : V) :
    Fin binding.source.molecule.atomCount :=
  ⟨encodeAtom binding.enumeration atom, by
    rw [binding.atomCount_eq]
    exact encodeAtom_lt binding.enumeration atom⟩

/-- Encoding a binding common index returns the source atom number. -/
@[simp] theorem encodeAtom_commonIndexEquivOfBinding [DecidableEq V] [Fintype V]
    (binding : CyclophaneSourceBinding V)
    (index : Fin binding.source.molecule.atomCount) :
    encodeAtom binding.enumeration (commonIndexEquivOfBinding binding index) = index.val := by
  simp [commonIndexEquivOfBinding, encodeAtom]

/-- The binding common index of a native label is the original native label. -/
@[simp] theorem commonIndexEquivOfBinding_encodeAtomBindingIndex
    [DecidableEq V] [Fintype V]
    (binding : CyclophaneSourceBinding V) (atom : V) :
    commonIndexEquivOfBinding binding (encodeAtomBindingIndex binding atom) = atom := by
  simp [commonIndexEquivOfBinding, encodeAtomBindingIndex, encodeAtom]



assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCyclophaneAuthorityIngress.decodeSystem_relabelSystem
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCyclophaneAuthorityIngress.relabelSystem_decodeSystem
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCyclophaneAuthorityIngress.unrelabelObservation_relabelObservation
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCyclophaneAuthorityIngress.relabelObservation_unrelabelObservation
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCyclophaneAuthorityIngress.validFor_unrelabelObservation_relabelObservation_iff
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCyclophaneAuthorityIngress.unrelabelObservation_ofSource
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCyclophaneAuthorityIngress.unrelabelObservationList_relabelObservationList
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCyclophaneAuthorityIngress.relabelObservationSet_unrelabelObservationSet
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCyclophaneAuthorityIngress.suppliedSource_adapt
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoCyclophaneAuthorityIngress.suppliedSource_adaptCertified

end OrganicStereoCyclophaneAuthorityIngress

end TetraStereo.OneCenter

-- Authoritative root deliverable: this module is the one compiled by the registered checker.
