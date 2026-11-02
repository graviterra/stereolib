import TetraStereo.OneCenter.IUPACP93AuthorityConfigurationCarrier
import TetraStereo.OneCenter.OrganicStereoSuppliedCitationIngress
import TetraStereo.OneCenter.OrganicStereoAuthoritativeSourceBridge

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace OrganicStereoP93PhysicalFrameIngress

open TetraStereo.OneCenter.OrganicStereoSuppliedCitationIngress
open BlueBookP94.CoordinateRing

/-!
# Concrete physical-frame ingress for the P-93 authority carrier

The P-93 authority carrier (`IUPACP93AuthorityConfigurationCarrier`) stores three *source frame*
records:

* `P93AuthorityHelixFrame` — an ordered helix traversal with front/back references, a supplied
  sense and the descriptor built from it;
* `P93AuthorityPlaneFrame` — the complete `IndexedPlanarDerivedTetrahedronObservation`, including
  the ordered planar traversal, the pilot/reference roles, the out-of-plane bond and both
  applicability Booleans;
* `P93AuthorityPolyhedralFrame` — the complete `IndexedPolyhedralGeometryObservation` together with
  the *coordinate* fields `spatial`, `centerPoint` and `positionPoints`.

The metadata-only `FrameAnnotation` channel is deliberately not used here.  It retains the
polyhedral record and the ordered ligand identifiers but it has no place for `spatial`,
`centerPoint` or `positionPoints`; those fields are exactly what the polyhedral `ValidFor`
predicate constrains through `SpatialPointAt` and `SpatialPointsAt`.  This module therefore builds
the missing concrete adapter directly from the carrier frames.

## What is transported, and what is not

One native tagged payload `PhysicalFrame V` carries all three cases over an arbitrary finite atom
type `V` with an explicit enumeration `V ≃ Fin n`:

* every ordered atom reference (helix path, plane traversal, ligand list), with order and
  multiplicity preserved literally because the payload uses lists rather than finite sets;
* the supplied descriptors, senses, applicability Booleans and the complete
  `IndexedPolyhedralGeometryObservation`;
* **not** the polyhedral coordinate fields.  Those are recovered by an explicit decoder that reads
  the native payload *plus* the shared rational coordinate configuration.  The decoder contains no
  hidden copy of the original frame.

The geometry-role lists inside `RedBookIR9.ConfigurationPositionObservation` are position ordinals
selected by the geometry rule, not atom identifiers.  They are copied literally through both
directions and are never relabelled or encoded as atoms.  The same holds for `recognition`,
`geometry`, `absoluteOrientation` and `priming`.

## Source binding

A `PhysicalFrameSourceBinding` ties an arbitrary `AuthoritativeChemicalInput` to a shared
`OrganicFiniteSource V` by three *actual equalities*: the encoded graph equals the source
molecule, the encoded spatial channel equals `source.spatial?`, and the encoded diagram channel
equals `source.diagram?`.  Atom-count agreement is then a consequence of the bridge theorem
`FiniteAtomInteractionHypergraph.encode_atomCount`, never an assumption.  The concrete certified
instance uses `OrganicStereoAuthoritativeSourceBridge`'s exact ingress and exact round trip; no
second reconstruction of the source is introduced.

## Scope

Nothing here decides chemical admissibility, selects a descriptor, or discharges the audited
`P93AuthorityPhysicalObservationPolicy` boundary.  `ValidFor` is only *consumed*: the recovery
theorems preserve an existing source validity under an exact decode.  In particular the
`Nat`-ordered constraints inside `ValidFor` (canonical path orientation, bond order `first <
second`, ordered `Nodup`) are **not** transported through an arbitrary relabelling: relabelling is
a representation change only, and every recovery theorem returns the original `Nat`-indexed
source frame.  No exhaustiveness or all-organic completeness claim is made for these three frame
constructors.
-/

/-! ## Coordinate reconstruction from an explicit shared configuration -/

/-- Harmless total default used only when a coordinate is absent.  Every recovery theorem in this
file is stated under actual `SpatialPointAt`/`SpatialPointsAt` evidence, so the default is never
observed in a recovered frame. -/
def defaultCartesianPoint : CartesianPoint3 := ⟨0, 0, 0⟩

/-- Exact indexed coordinate lookup in a shared spatial configuration. -/
def coordinateAt (spatial : SpatialConfiguration) (atom : ℕ) : CartesianPoint3 :=
  (spatial.positions[atom]?).getD defaultCartesianPoint

/-- Exact ordered coordinate lookup for a list of atom indices. -/
def coordinateList (spatial : SpatialConfiguration) (atoms : List ℕ) : List CartesianPoint3 :=
  atoms.map (coordinateAt spatial)

/-- A genuine indexed coordinate is recovered by the total lookup. -/
theorem coordinateAt_eq_of_spatialPointAt {spatial : SpatialConfiguration} {atom : ℕ}
    {point : CartesianPoint3} (observed : SpatialPointAt spatial atom point) :
    coordinateAt spatial atom = point := by
  unfold coordinateAt
  unfold SpatialPointAt at observed
  rw [observed]
  rfl

/-- An atom with a coordinate is in range of the stored position list. -/
theorem lt_length_of_spatialPointAt {spatial : SpatialConfiguration} {atom : ℕ}
    {point : CartesianPoint3} (observed : SpatialPointAt spatial atom point) :
    atom < spatial.positions.length := by
  unfold SpatialPointAt at observed
  exact (List.getElem?_eq_some_iff.mp observed).1

/-- Every atom of an ordered collection with coordinates is in range. -/
theorem spatialPointsAt_mem_lt (spatial : SpatialConfiguration) {atoms : List ℕ}
    {points : List CartesianPoint3} (related₀ : SpatialPointsAt spatial atoms points) :
    ∀ atom ∈ atoms, atom < spatial.positions.length := by
  unfold SpatialPointsAt at related₀
  induction related₀ with
  | nil =>
      intro atom member
      simp at member
  | cons head _tail ih =>
      intro atom member
      rcases List.mem_cons.mp member with rfl | rest
      · exact lt_length_of_spatialPointAt head
      · exact ih atom rest

/-- An ordered coordinate collection is recovered entry by entry from the shared configuration.
The list is not rebuilt from an unordered set: order and multiplicity are those of `atoms`. -/
theorem coordinateList_eq_of_spatialPointsAt (spatial : SpatialConfiguration) {atoms : List ℕ}
    {points : List CartesianPoint3} (related₀ : SpatialPointsAt spatial atoms points) :
    coordinateList spatial atoms = points := by
  unfold SpatialPointsAt at related₀
  induction related₀ with
  | nil => rfl
  | cons head _tail ih =>
      simp only [coordinateList, List.map_cons, coordinateAt_eq_of_spatialPointAt head]
      rw [← ih]
      rfl

/-! ## The native tagged payload -/

/-- Ordered helical frame over an arbitrary atom type.  `sense` and `descriptor` are copied
literally; no descriptor is derived. -/
structure NativeHelixFrame (V : Type*) where
  helixPath : List V
  frontReference : V
  backReference : V
  sense : StereoSense
  descriptor : HelicalDescriptor
  deriving DecidableEq, Repr

/-- Ordered planar frame over an arbitrary atom type, mirroring the complete
`IndexedPlanarDerivedTetrahedronObservation`, including both physical applicability Booleans. -/
structure NativePlanarFrame (V : Type*) where
  planeAtoms : List V
  pilotAtom : V
  firstReference : V
  secondReference : V
  inPlaneBondAtom : V
  outOfPlaneAtom : V
  torsionRestricted : Bool
  planeCannotBeSymmetryPlane : Bool
  deriving DecidableEq, Repr

/-- The atom-identified part of a polyhedral source frame.  The coordinate fields `spatial`,
`centerPoint` and `positionPoints` are intentionally absent: they are recovered from the shared
coordinate representation by `decodePolyhedral`.  `configurationPositions` carries geometry-role
ordinals which are *not* atom labels and are copied verbatim. -/
structure NativePolyhedralFrame (V : Type*) where
  center : V
  geometry : PolyhedralGeometry
  recognition : RedBookIR9.GeometryRecognitionObservation
  ligands : List V
  configurationPositions : RedBookIR9.ConfigurationPositionObservation
  absoluteOrientation : RedBookIR9.AbsoluteOrientationObservation
  priming : IndexedPolyhedralPrimingObservation := .repeatedPolydentateLigands
  deriving DecidableEq, Repr

/-- One native tagged physical-frame payload.  Exactly one of the three carrier frame shapes is
carried; the tag is the only sum introduction. -/
inductive PhysicalFrame (V : Type*) where
  | helix (frame : NativeHelixFrame V)
  | plane (frame : NativePlanarFrame V)
  | polyhedral (frame : NativePolyhedralFrame V)
  deriving DecidableEq, Repr

/-! ## The source-side tagged frame and explicit bounds -/

/-- A source frame tagged together with the exact source identity data its `ValidFor` predicate is
stated at.  The `Nat` fields here are the raw source identity (`path`, planar `members`, polyhedral
center/ligand set/geometry); they are never relabelled.  Geometry-role positions remain inside
`frame.record.configurationPositions` and are not part of this identity. -/
inductive SourcePhysicalFrame where
  | helix (path : List ℕ) (frame : P93AuthorityHelixFrame)
  | plane (members : Finset ℕ) (frame : P93AuthorityPlaneFrame)
  | polyhedral (center : ℕ) (ligands : Finset ℕ) (geometry : BlueBookP93.Geometry)
      (frame : P93AuthorityPolyhedralFrame)

/-- Bounds on the helix record references. -/
structure HelixFrameBoundedIn (n : ℕ) (frame : P93AuthorityHelixFrame) : Prop where
  frontBound : frame.record.frontReference < n
  backBound : frame.record.backReference < n
  pathBound : ∀ atom ∈ frame.record.helixPath, atom < n

/-- Bounds on every planar record reference, including the ordered traversal. -/
structure PlaneFrameBoundedIn (n : ℕ) (frame : P93AuthorityPlaneFrame) : Prop where
  pilotBound : frame.record.pilotAtom < n
  firstBound : frame.record.firstReference < n
  secondBound : frame.record.secondReference < n
  inPlaneBound : frame.record.inPlaneBondAtom < n
  outOfPlaneBound : frame.record.outOfPlaneAtom < n
  planeAtomsBound : ∀ atom ∈ frame.record.planeAtoms, atom < n

/-- Bounds on the polyhedral center and ordered ligand list. -/
structure PolyhedralFrameBoundedIn (n : ℕ) (frame : P93AuthorityPolyhedralFrame) : Prop where
  centerBound : frame.record.center < n
  ligandsBound : ∀ atom ∈ frame.record.ligands, atom < n

namespace SourcePhysicalFrame

/-- The carrier `ValidFor` predicate, dispatched on the tag.  This is consumed, never produced. -/
def ValidFor (source : AuthoritativeChemicalInput) : SourcePhysicalFrame → Prop
  | .helix path frame => frame.ValidFor source path
  | .plane members frame => frame.ValidFor source members
  | .polyhedral center ligands geometry frame =>
      frame.ValidFor source center ligands geometry

/-- The atom references of the carried frame record all lie below `n`.  Only the payload atoms are
bounded; the source identity data stays in its original `Nat` space. -/
def BoundedIn (n : ℕ) : SourcePhysicalFrame → Prop
  | .helix _ frame => HelixFrameBoundedIn n frame
  | .plane _ frame => PlaneFrameBoundedIn n frame
  | .polyhedral _ _ _ frame => PolyhedralFrameBoundedIn n frame

end SourcePhysicalFrame

/-! ## Bounds proved from source validity

The helix and plane `ValidFor` predicates already contain `P93AuthorityAtomsBounded`.  The
polyhedral predicate constrains its atoms only through actual coordinate incidence, so its bounds
are derived from `SpatialPointAt`/`SpatialPointsAt` together with the certified spatial-length
fact.  None of these bounds is assumed. -/

theorem helixFrameBoundedIn_of_validFor (source : AuthoritativeChemicalInput)
    (path : List ℕ) (frame : P93AuthorityHelixFrame)
    (valid : frame.ValidFor source path) :
    HelixFrameBoundedIn source.molecule.atomCount frame := by
  rcases valid with ⟨pathEq, _descriptor, _length, bounded, _canonical, _connected, _rest⟩
  exact
    { frontBound := bounded frame.record.frontReference (by simp)
      backBound := bounded frame.record.backReference (by simp)
      pathBound := fun atom member => bounded atom (by
        rw [← pathEq]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member)) }

theorem planeFrameBoundedIn_of_validFor (source : AuthoritativeChemicalInput)
    (members : Finset ℕ) (frame : P93AuthorityPlaneFrame)
    (valid : frame.ValidFor source members) :
    PlaneFrameBoundedIn source.molecule.atomCount frame := by
  rcases valid with
    ⟨_setEq, _length, _nodup, bounded, _pilotMem, _firstMem, _secondMem, _inPlaneMem,
      _outOfPlaneMem, _traversalNodup, _pilotFirst, _pilotSecond, _pilotInPlane,
      _inPlaneOutOfPlane, _restricted, _noSymmetry, _spatiallyResolved⟩
  exact
    { pilotBound := bounded frame.record.pilotAtom (by simp)
      firstBound := bounded frame.record.firstReference (by simp)
      secondBound := bounded frame.record.secondReference (by simp)
      inPlaneBound := bounded frame.record.inPlaneBondAtom (by simp)
      outOfPlaneBound := bounded frame.record.outOfPlaneAtom (by simp)
      planeAtomsBound := fun atom member => bounded atom (by simp [member]) }

theorem polyhedralFrameBoundedIn_of_validFor (source : AuthoritativeChemicalInput)
    (center : ℕ) (ligands : Finset ℕ) (geometry : BlueBookP93.Geometry)
    (frame : P93AuthorityPolyhedralFrame)
    (valid : frame.ValidFor source center ligands geometry)
    (spatialWellFormed : source.SpatialIndicesWellFormed) :
    PolyhedralFrameBoundedIn source.molecule.atomCount frame := by
  rcases valid with
    ⟨centerEq, _ligandSetEq, _ligandNodup, _geometryEq, _recognized, sourceSpatial,
      centerPointAt, positionsAt, _arity, _incidence, _roles, _orientation⟩
  have fits := spatialFits_of_wf source spatialWellFormed frame.spatial sourceSpatial
  refine ⟨?_, ?_⟩
  · rw [centerEq]
    exact fits ▸ lt_length_of_spatialPointAt centerPointAt
  · intro atom member
    exact fits ▸ spatialPointsAt_mem_lt frame.spatial positionsAt atom member

/-! ## Relabelling into the native payload -/

/-- Relabel one helix frame.  The ordered traversal is relabelled position by position, so order
and multiplicity are preserved. -/
def relabelHelix {V : Type*} [DecidableEq V] {n : ℕ} (e : V ≃ Fin n)
    (frame : P93AuthorityHelixFrame) (bounded : HelixFrameBoundedIn n frame) :
    NativeHelixFrame V where
  helixPath := relabelList e frame.record.helixPath bounded.pathBound
  frontReference := decodeAtom e frame.record.frontReference bounded.frontBound
  backReference := decodeAtom e frame.record.backReference bounded.backBound
  sense := frame.record.sense
  descriptor := frame.descriptor

/-- Relabel one planar frame, retaining the complete ordered observation. -/
def relabelPlane {V : Type*} [DecidableEq V] {n : ℕ} (e : V ≃ Fin n)
    (frame : P93AuthorityPlaneFrame) (bounded : PlaneFrameBoundedIn n frame) :
    NativePlanarFrame V where
  planeAtoms := relabelList e frame.record.planeAtoms bounded.planeAtomsBound
  pilotAtom := decodeAtom e frame.record.pilotAtom bounded.pilotBound
  firstReference := decodeAtom e frame.record.firstReference bounded.firstBound
  secondReference := decodeAtom e frame.record.secondReference bounded.secondBound
  inPlaneBondAtom := decodeAtom e frame.record.inPlaneBondAtom bounded.inPlaneBound
  outOfPlaneAtom := decodeAtom e frame.record.outOfPlaneAtom bounded.outOfPlaneBound
  torsionRestricted := frame.record.torsionRestricted
  planeCannotBeSymmetryPlane := frame.record.planeCannotBeSymmetryPlane

/-- Relabel the atom-identified part of one polyhedral frame.  `geometry`, `recognition`,
`configurationPositions`, `absoluteOrientation` and `priming` are copied literally: the
geometry-position ordinals selected by the observation are not atom labels. -/
def relabelPolyhedral {V : Type*} [DecidableEq V] {n : ℕ} (e : V ≃ Fin n)
    (frame : P93AuthorityPolyhedralFrame) (bounded : PolyhedralFrameBoundedIn n frame) :
    NativePolyhedralFrame V where
  center := decodeAtom e frame.record.center bounded.centerBound
  geometry := frame.record.geometry
  recognition := frame.record.recognition
  ligands := relabelList e frame.record.ligands bounded.ligandsBound
  configurationPositions := frame.record.configurationPositions
  absoluteOrientation := frame.record.absoluteOrientation
  priming := frame.record.priming

/-- Relabel a tagged source frame into the native payload. -/
def relabelFrame {V : Type*} [DecidableEq V] {n : ℕ} (e : V ≃ Fin n) :
    (frame : SourcePhysicalFrame) → frame.BoundedIn n → PhysicalFrame V
  | .helix _ frame, bounded => .helix (relabelHelix e frame bounded)
  | .plane _ frame, bounded => .plane (relabelPlane e frame bounded)
  | .polyhedral _ _ _ frame, bounded => .polyhedral (relabelPolyhedral e frame bounded)

/-! ## Decoding, including true polyhedral point reconstruction -/

/-- Recover the complete `IndexedPolyhedralGeometryObservation` from the native payload.  The
geometry-role fields are copied literally. -/
def decodePolyhedralObservation {V : Type*} [DecidableEq V] {n : ℕ} (e : V ≃ Fin n)
    (native : NativePolyhedralFrame V) : IndexedPolyhedralGeometryObservation where
  center := encodeAtom e native.center
  geometry := native.geometry
  recognition := native.recognition
  ligands := unrelabelList e native.ligands
  configurationPositions := native.configurationPositions
  absoluteOrientation := native.absoluteOrientation
  priming := native.priming

/-- Decode one polyhedral frame.  The shared spatial configuration is the sole source of
`spatial`, `centerPoint` and `positionPoints`; the native payload supplies no coordinate and no
copy of the original frame.  The points are true indexed lookups, one per ordered ligand. -/
def decodePolyhedral {V : Type*} [DecidableEq V] {n : ℕ} (e : V ≃ Fin n)
    (spatial : SpatialConfiguration) (native : NativePolyhedralFrame V) :
    P93AuthorityPolyhedralFrame where
  record := decodePolyhedralObservation e native
  spatial := spatial
  centerPoint := coordinateAt spatial (encodeAtom e native.center)
  positionPoints := coordinateList spatial (unrelabelList e native.ligands)

/-- Decode one helix frame. -/
def decodeHelix {V : Type*} [DecidableEq V] {n : ℕ} (e : V ≃ Fin n)
    (native : NativeHelixFrame V) : P93AuthorityHelixFrame where
  record :=
    { helixPath := unrelabelList e native.helixPath
      frontReference := encodeAtom e native.frontReference
      backReference := encodeAtom e native.backReference
      sense := native.sense }
  descriptor := native.descriptor

/-- Decode one planar frame, retaining every ordered reference and applicability field. -/
def decodePlane {V : Type*} [DecidableEq V] {n : ℕ} (e : V ≃ Fin n)
    (native : NativePlanarFrame V) : P93AuthorityPlaneFrame where
  record :=
    { planeAtoms := unrelabelList e native.planeAtoms
      pilotAtom := encodeAtom e native.pilotAtom
      firstReference := encodeAtom e native.firstReference
      secondReference := encodeAtom e native.secondReference
      inPlaneBondAtom := encodeAtom e native.inPlaneBondAtom
      outOfPlaneAtom := encodeAtom e native.outOfPlaneAtom
      torsionRestricted := native.torsionRestricted
      planeCannotBeSymmetryPlane := native.planeCannotBeSymmetryPlane }

/-- Decode one tagged native payload.  The source identity data of the tagged frame is recomputed
from the recovered record: the helix path and plane traversal from the ordered list, the planar
member set and the polyhedral ligand set from the recovered list's `toFinset`.  This is why the
whole-set recovery is a consequence of the list inverse rather than a separate assumption. -/
def decodeFrame {V : Type*} [DecidableEq V] {n : ℕ} (e : V ≃ Fin n)
    (spatial : SpatialConfiguration) : PhysicalFrame V → SourcePhysicalFrame
  | .helix native => .helix (unrelabelList e native.helixPath) (decodeHelix e native)
  | .plane native =>
      .plane (unrelabelList e native.planeAtoms).toFinset (decodePlane e native)
  | .polyhedral native =>
      .polyhedral (encodeAtom e native.center) (unrelabelList e native.ligands).toFinset
        (BlueBookP93.geometryOfProduction native.geometry)
        (decodePolyhedral e spatial native)

/-! ## Exact recovery of the observation and the coordinate fields -/

/-- The complete polyhedral observation is recovered exactly from the native payload. -/
theorem decodePolyhedralObservation_relabelPolyhedral {V : Type*} [DecidableEq V] {n : ℕ}
    (e : V ≃ Fin n) (frame : P93AuthorityPolyhedralFrame)
    (bounded : PolyhedralFrameBoundedIn n frame) :
    decodePolyhedralObservation e (relabelPolyhedral e frame bounded) = frame.record := by
  obtain ⟨record, _spatial, _centerPoint, _positionPoints⟩ := frame
  obtain ⟨center, geometry, recognition, ligands, configurationPositions,
    absoluteOrientation, priming⟩ := record
  simp [decodePolyhedralObservation, relabelPolyhedral, encodeAtom_decodeAtom,
    unrelabelList_relabelList]

/-- Helix frame recovery. -/
theorem decodeHelix_relabelHelix {V : Type*} [DecidableEq V] {n : ℕ}
    (e : V ≃ Fin n) (frame : P93AuthorityHelixFrame)
    (bounded : HelixFrameBoundedIn n frame) :
    decodeHelix e (relabelHelix e frame bounded) = frame := by
  obtain ⟨record, descriptor⟩ := frame
  obtain ⟨helixPath, frontReference, backReference, sense⟩ := record
  simp [decodeHelix, relabelHelix, encodeAtom_decodeAtom, unrelabelList_relabelList]

/-- Planar frame recovery, including both ordered references and both applicability Booleans. -/
theorem decodePlane_relabelPlane {V : Type*} [DecidableEq V] {n : ℕ}
    (e : V ≃ Fin n) (frame : P93AuthorityPlaneFrame)
    (bounded : PlaneFrameBoundedIn n frame) :
    decodePlane e (relabelPlane e frame bounded) = frame := by
  obtain ⟨record⟩ := frame
  obtain ⟨planeAtoms, pilotAtom, firstReference, secondReference, inPlaneBondAtom,
    outOfPlaneAtom, torsionRestricted, planeCannotBeSymmetryPlane⟩ := record
  simp [decodePlane, relabelPlane, encodeAtom_decodeAtom, unrelabelList_relabelList]

/-- **True polyhedral point reconstruction.**  Given a shared spatial configuration in which the
frame center and every ordered ligand have their actual coordinates, decoding the relabelled native
payload returns the original frame: the center point is the indexed lookup at the center atom and
the position list is the ordered indexed lookup of the ligand list.  The decoder receives only the
native payload and the shared configuration. -/
theorem decodePolyhedral_relabelPolyhedral {V : Type*} [DecidableEq V] {n : ℕ}
    (e : V ≃ Fin n) (frame : P93AuthorityPolyhedralFrame)
    (bounded : PolyhedralFrameBoundedIn n frame)
    (centerPointAt : SpatialPointAt frame.spatial frame.record.center frame.centerPoint)
    (positionsAt : SpatialPointsAt frame.spatial frame.record.ligands frame.positionPoints) :
    decodePolyhedral e frame.spatial (relabelPolyhedral e frame bounded) = frame := by
  obtain ⟨record, frameSpatial, frameCenter, framePositions⟩ := frame
  obtain ⟨center, geometry, recognition, ligands, configurationPositions,
    absoluteOrientation, priming⟩ := record
  have frameCenterPointAt : SpatialPointAt frameSpatial center frameCenter := by
    exact centerPointAt
  have framePositionsAt : SpatialPointsAt frameSpatial ligands framePositions := by
    exact positionsAt
  simp [decodePolyhedral, relabelPolyhedral, decodePolyhedralObservation,
    encodeAtom_decodeAtom, unrelabelList_relabelList,
    coordinateAt_eq_of_spatialPointAt frameCenterPointAt,
    coordinateList_eq_of_spatialPointsAt frameSpatial framePositionsAt]

/-- Polyhedral recovery from source validity: `ValidFor` supplies the shared spatial equality and
both coordinate incidence facts. -/
theorem decodePolyhedral_relabelPolyhedral_of_validFor {V : Type*} [DecidableEq V] {n : ℕ}
    (e : V ≃ Fin n) (source : AuthoritativeChemicalInput)
    (center : ℕ) (ligands : Finset ℕ) (geometry : BlueBookP93.Geometry)
    (frame : P93AuthorityPolyhedralFrame)
    (valid : frame.ValidFor source center ligands geometry)
    (bounded : PolyhedralFrameBoundedIn n frame) :
    decodePolyhedral e frame.spatial (relabelPolyhedral e frame bounded) = frame := by
  rcases valid with
    ⟨centerEq, _ligandSetEq, _ligandNodup, _geometryEq, _recognized, _sourceSpatial,
      centerPointAt, positionsAt, _arity, _incidence, _roles, _orientation⟩
  have centerPointAt' : SpatialPointAt frame.spatial frame.record.center frame.centerPoint := by
    rw [centerEq]
    exact centerPointAt
  exact decodePolyhedral_relabelPolyhedral e frame bounded centerPointAt' positionsAt

/-! ## Whole-set recovery follows the actual list inverse -/

/-- The recovered planar member set is the source member set: it is the `toFinset` of the exactly
recovered ordered traversal, and `ValidFor` identifies that traversal's set with the source set. -/
theorem decodedPlane_members {V : Type*} [DecidableEq V] {n : ℕ}
    (e : V ≃ Fin n) (source : AuthoritativeChemicalInput) (members : Finset ℕ)
    (frame : P93AuthorityPlaneFrame) (valid : frame.ValidFor source members)
    (bounded : PlaneFrameBoundedIn n frame) :
    (unrelabelList e (relabelList e frame.record.planeAtoms bounded.planeAtomsBound)).toFinset =
      members := by
  rw [unrelabelList_relabelList]
  exact valid.1

/-- The recovered polyhedral ligand set is the source ligand set, again as a consequence of the
exact ordered-list inverse. -/
theorem decodedPolyhedral_ligands {V : Type*} [DecidableEq V] {n : ℕ}
    (e : V ≃ Fin n) (source : AuthoritativeChemicalInput) (center : ℕ)
    (ligands : Finset ℕ) (geometry : BlueBookP93.Geometry)
    (frame : P93AuthorityPolyhedralFrame)
    (valid : frame.ValidFor source center ligands geometry)
    (bounded : PolyhedralFrameBoundedIn n frame) :
    (unrelabelList e (relabelList e frame.record.ligands bounded.ligandsBound)).toFinset =
      ligands := by
  rw [unrelabelList_relabelList]
  exact valid.2.1

/-! ## Exact frame recovery under source validity -/

/-- The native payload of a helix frame recovers the exact tagged source frame. -/
theorem decodeFrame_relabelFrame_helix {V : Type*} [DecidableEq V] {n : ℕ}
    (e : V ≃ Fin n) (source : AuthoritativeChemicalInput) (spatial : SpatialConfiguration)
    (path : List ℕ) (frame : P93AuthorityHelixFrame)
    (valid : frame.ValidFor source path) (bounded : HelixFrameBoundedIn n frame) :
    decodeFrame e spatial (.helix (relabelHelix e frame bounded)) = .helix path frame := by
  rcases valid with
    ⟨pathEq, _descriptor, _length, _atomsBounded, _canonical, _connected, _rest⟩
  have frameEq : decodeHelix e (relabelHelix e frame bounded) = frame :=
    decodeHelix_relabelHelix e frame bounded
  have listEq : unrelabelList e (relabelList e frame.record.helixPath bounded.pathBound) =
      frame.record.helixPath := unrelabelList_relabelList e _ _
  have decodeEq : decodeFrame e spatial (.helix (relabelHelix e frame bounded)) =
      .helix (unrelabelList e (relabelList e frame.record.helixPath bounded.pathBound))
        (decodeHelix e (relabelHelix e frame bounded)) := rfl
  rw [decodeEq, listEq, pathEq, frameEq]

/-- The native payload of a planar frame recovers the exact tagged source frame. -/
theorem decodeFrame_relabelFrame_plane {V : Type*} [DecidableEq V] {n : ℕ}
    (e : V ≃ Fin n) (source : AuthoritativeChemicalInput) (spatial : SpatialConfiguration)
    (members : Finset ℕ) (frame : P93AuthorityPlaneFrame)
    (valid : frame.ValidFor source members) (bounded : PlaneFrameBoundedIn n frame) :
    decodeFrame e spatial (.plane (relabelPlane e frame bounded)) = .plane members frame := by
  rcases valid with
    ⟨setEq, _length, _nodup, _atomsBounded, _pilotMem, _firstMem, _secondMem, _inPlaneMem,
      _outOfPlaneMem, _traversalNodup, _pilotFirst, _pilotSecond, _pilotInPlane,
      _inPlaneOutOfPlane, _restricted, _noSymmetry, _spatiallyResolved⟩
  have frameEq : decodePlane e (relabelPlane e frame bounded) = frame :=
    decodePlane_relabelPlane e frame bounded
  have listEq : unrelabelList e (relabelList e frame.record.planeAtoms bounded.planeAtomsBound) =
      frame.record.planeAtoms := unrelabelList_relabelList e _ _
  have decodeEq : decodeFrame e spatial (.plane (relabelPlane e frame bounded)) =
      .plane (unrelabelList e
          (relabelList e frame.record.planeAtoms bounded.planeAtomsBound)).toFinset
        (decodePlane e (relabelPlane e frame bounded)) := rfl
  rw [decodeEq, listEq, setEq, frameEq]

/-- The native payload of a polyhedral frame recovers the exact tagged source frame whenever the
shared coordinate configuration is the source's own configuration.  The decoder is given only the
payload, the source, and the shared configuration; the source coordinate is used to identify the
configuration, not to inject points into the payload. -/
theorem decodeFrame_relabelFrame_polyhedral {V : Type*} [DecidableEq V] {n : ℕ}
    (e : V ≃ Fin n) (source : AuthoritativeChemicalInput)
    (spatial : SpatialConfiguration) (center : ℕ) (ligands : Finset ℕ)
    (geometry : BlueBookP93.Geometry) (frame : P93AuthorityPolyhedralFrame)
    (valid : frame.ValidFor source center ligands geometry)
    (bounded : PolyhedralFrameBoundedIn n frame)
    (spatialObserved : source.spatial? = some spatial) :
    decodeFrame e spatial
        (relabelFrame e (.polyhedral center ligands geometry frame) bounded) =
      .polyhedral center ligands geometry frame := by
  rcases valid with
    ⟨centerEq, ligandSetEq, _ligandNodup, geometryEq, _recognized, sourceSpatial,
      centerPointAt, positionsAt, _arity, _incidence, _roles, _orientation⟩
  have spatialEq : spatial = frame.spatial := by
    rw [spatialObserved] at sourceSpatial
    exact Option.some.inj sourceSpatial
  have centerPointAt' : SpatialPointAt frame.spatial frame.record.center frame.centerPoint := by
    rw [centerEq]
    exact centerPointAt
  have frameEq : decodePolyhedral e spatial (relabelPolyhedral e frame bounded) = frame := by
    rw [spatialEq]
    exact decodePolyhedral_relabelPolyhedral e frame bounded centerPointAt' positionsAt
  have listEq : unrelabelList e (relabelList e frame.record.ligands bounded.ligandsBound) =
      frame.record.ligands := unrelabelList_relabelList e _ _
  have decodeEq' : decodeFrame e spatial
        (relabelFrame e (.polyhedral center ligands geometry frame) bounded) =
      SourcePhysicalFrame.polyhedral
        (encodeAtom e (decodeAtom e frame.record.center bounded.centerBound))
        (unrelabelList e (relabelList e frame.record.ligands bounded.ligandsBound)).toFinset
        (BlueBookP93.geometryOfProduction frame.record.geometry)
        (decodePolyhedral e spatial (relabelPolyhedral e frame bounded)) := rfl
  rw [decodeEq', encodeAtom_decodeAtom, centerEq, listEq, ligandSetEq, geometryEq.symm, frameEq]

/-- Exact frame recovery from `ValidFor` alone: the shared configuration is the source's own
spatial channel, which `ValidFor` identifies for a polyhedral frame.  For helix and plane frames
the shared configuration is irrelevant to the payload. -/
theorem decodeFrame_relabelFrame_of_validFor {V : Type*} [DecidableEq V] {n : ℕ}
    (e : V ≃ Fin n) (source : AuthoritativeChemicalInput)
    (spatial : SpatialConfiguration) (frame : SourcePhysicalFrame)
    (valid : frame.ValidFor source) (bounded : frame.BoundedIn n)
    (spatialObserved : source.spatial? = some spatial) :
    decodeFrame e spatial (relabelFrame e frame bounded) = frame := by
  cases frame with
  | helix path frame =>
      exact decodeFrame_relabelFrame_helix e source spatial path frame valid bounded
  | plane members frame =>
      exact decodeFrame_relabelFrame_plane e source spatial members frame valid bounded
  | polyhedral center ligands geometry frame =>
      exact decodeFrame_relabelFrame_polyhedral e source spatial center ligands geometry frame
        valid bounded spatialObserved

/-! ## Field preservation: geometry metadata and role positions -/

/-- The polyhedral geometry metadata is copied literally into the native payload.  In particular
`configurationPositions` and `absoluteOrientation` are not relabelled as atoms. -/
theorem relabelPolyhedral_geometryMetadata {V : Type*} [DecidableEq V] {n : ℕ}
    (e : V ≃ Fin n) (frame : P93AuthorityPolyhedralFrame)
    (bounded : PolyhedralFrameBoundedIn n frame) :
    (relabelPolyhedral e frame bounded).geometry = frame.record.geometry ∧
      (relabelPolyhedral e frame bounded).recognition = frame.record.recognition ∧
      (relabelPolyhedral e frame bounded).configurationPositions =
        frame.record.configurationPositions ∧
      (relabelPolyhedral e frame bounded).absoluteOrientation =
        frame.record.absoluteOrientation ∧
      (relabelPolyhedral e frame bounded).priming = frame.record.priming := by
  simp [relabelPolyhedral]

/-- The geometry-role observation is copied literally on the way back as well. -/
theorem decodePolyhedralObservation_configurationPositions {V : Type*} [DecidableEq V] {n : ℕ}
    (e : V ≃ Fin n) (native : NativePolyhedralFrame V) :
    (decodePolyhedralObservation e native).configurationPositions =
      native.configurationPositions := rfl

/-- The absolute-orientation observation is copied literally on the way back as well. -/
theorem decodePolyhedralObservation_absoluteOrientation {V : Type*} [DecidableEq V] {n : ℕ}
    (e : V ≃ Fin n) (native : NativePolyhedralFrame V) :
    (decodePolyhedralObservation e native).absoluteOrientation =
      native.absoluteOrientation := rfl

/-- The geometry-recognition observation is copied literally on the way back as well. -/
theorem decodePolyhedralObservation_recognition {V : Type*} [DecidableEq V] {n : ℕ}
    (e : V ≃ Fin n) (native : NativePolyhedralFrame V) :
    (decodePolyhedralObservation e native).recognition = native.recognition := rfl

/-- The ordered helix traversal is relabelled position by position; its length, and therefore its
multiplicity structure, is unchanged. -/
theorem relabelHelix_helixPath_length {V : Type*} [DecidableEq V] {n : ℕ}
    (e : V ≃ Fin n) (frame : P93AuthorityHelixFrame)
    (bounded : HelixFrameBoundedIn n frame) :
    (relabelHelix e frame bounded).helixPath.length = frame.record.helixPath.length := by
  simp [relabelHelix]

/-- The ordered planar traversal has the same length after relabelling. -/
theorem relabelPlane_planeAtoms_length {V : Type*} [DecidableEq V] {n : ℕ}
    (e : V ≃ Fin n) (frame : P93AuthorityPlaneFrame)
    (bounded : PlaneFrameBoundedIn n frame) :
    (relabelPlane e frame bounded).planeAtoms.length = frame.record.planeAtoms.length := by
  simp [relabelPlane]

/-- The ordered polyhedral ligand list has the same length after relabelling. -/
theorem relabelPolyhedral_ligands_length {V : Type*} [DecidableEq V] {n : ℕ}
    (e : V ≃ Fin n) (frame : P93AuthorityPolyhedralFrame)
    (bounded : PolyhedralFrameBoundedIn n frame) :
    (relabelPolyhedral e frame bounded).ligands.length = frame.record.ligands.length := by
  simp [relabelPolyhedral]

/-! ## The composable satellite and its source binding -/

/-- A source binding ties an authoritative input to an explicitly shared finite source by three
*actual equalities*.  The shared graph, coordinate channel and drawing channel are not required to
be a canonical reconstruction; they are required to encode to exactly the stored source. -/
structure PhysicalFrameSourceBinding (V : Type*) [DecidableEq V] [Fintype V] where
  source : AuthoritativeChemicalInput
  shared : OrganicFiniteSource V
  enumeration : V ≃ Fin (Fintype.card V)
  graph_eq : shared.graph.encode enumeration = source.molecule
  spatial_eq : OrganicFiniteSource.encodeSpatial? enumeration shared.spatial? = source.spatial?
  diagram_eq : shared.diagram?.map (OrganicDiagramSource.encodeDiagram enumeration) =
    source.diagram?
  spatial_wellFormed : source.SpatialIndicesWellFormed

namespace PhysicalFrameSourceBinding

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The shared finite source encodes to exactly the stored authoritative input, including both
optional evidence channels.  This is a real equality, not a cardinality comparison. -/
theorem encode_shared (binding : PhysicalFrameSourceBinding V) :
    binding.shared.encode binding.enumeration = binding.source := by
  apply authoritativeInput_ext
  · exact binding.graph_eq
  · exact binding.spatial_eq
  · exact binding.diagram_eq

/-- Atom-count agreement is a consequence of the graph equality and the exact encoder, not an
input assumption. -/
theorem atomCount_eq (binding : PhysicalFrameSourceBinding V) :
    binding.source.molecule.atomCount = Fintype.card V := by
  rw [← binding.graph_eq]
  exact FiniteAtomInteractionHypergraph.encode_atomCount binding.shared.graph
    binding.enumeration

end PhysicalFrameSourceBinding

/-- A raw physical-frame source: one explicit source binding and an ordered list of tagged carrier
frames, each certified valid against the bound source. -/
structure RawPhysicalFrameSource (V : Type*) [DecidableEq V] [Fintype V] where
  binding : PhysicalFrameSourceBinding V
  frames : List SourcePhysicalFrame
  valid : ∀ frame ∈ frames, frame.ValidFor binding.source

/-- The composable satellite channel.  The graph and both optional evidence channels are one
independent finite source; `frames` is the ordered native payload list.  No original frame and no
original `AuthoritativeChemicalInput` is stored here. -/
structure PhysicalFrameSatellite (V : Type*) [DecidableEq V] [Fintype V] where
  graph : FiniteAtomInteractionHypergraph V
  spatial? : Option (V → CartesianPoint3) := none
  diagram? : Option (OrganicDiagramSource V) := none
  frames : List (PhysicalFrame V)

namespace PhysicalFrameSatellite

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The satellite's shared finite source, with the frames intentionally excluded. -/
def toFiniteSource (satellite : PhysicalFrameSatellite V) : OrganicFiniteSource V where
  graph := satellite.graph
  spatial? := satellite.spatial?
  diagram? := satellite.diagram?

/-- The shared rational coordinate configuration encoded from the satellite.  Absence of the
channel produces an empty configuration; the recovery theorems never rely on that case for a
polyhedral frame, because `ValidFor` supplies a present coordinate channel. -/
def sharedSpatial? (satellite : PhysicalFrameSatellite V)
    (e : V ≃ Fin (Fintype.card V)) : Option SpatialConfiguration :=
  OrganicFiniteSource.encodeSpatial? e satellite.spatial?

/-- The total spatial configuration handed to the frame decoder. -/
def spatialConfiguration (satellite : PhysicalFrameSatellite V)
    (e : V ≃ Fin (Fintype.card V)) : SpatialConfiguration :=
  (satellite.sharedSpatial? e).getD { positions := [] }

end PhysicalFrameSatellite

/-- Bounds for a tagged source frame, derived from its source validity and the binding.  The
polyhedral case uses the certified spatial-length fact and actual coordinate incidence. -/
theorem SourcePhysicalFrame.boundedIn_of_validFor {V : Type*} [DecidableEq V] [Fintype V]
    (binding : PhysicalFrameSourceBinding V) (frame : SourcePhysicalFrame)
    (valid : frame.ValidFor binding.source) :
    frame.BoundedIn (Fintype.card V) := by
  cases frame with
  | helix path frame =>
      have bounded := helixFrameBoundedIn_of_validFor binding.source path frame valid
      rw [binding.atomCount_eq] at bounded
      exact bounded
  | plane members frame =>
      have bounded := planeFrameBoundedIn_of_validFor binding.source members frame valid
      rw [binding.atomCount_eq] at bounded
      exact bounded
  | polyhedral center ligands geometry frame =>
      have bounded := polyhedralFrameBoundedIn_of_validFor binding.source center ligands
        geometry frame valid binding.spatial_wellFormed
      rw [binding.atomCount_eq] at bounded
      exact bounded

/-- Adapt a raw source into the satellite: the shared finite source is retained verbatim, and each
validated carrier frame is relabelled into the native payload.  Bounds are derived, never assumed. -/
def adapt {V : Type*} [DecidableEq V] [Fintype V]
    (raw : RawPhysicalFrameSource V) : PhysicalFrameSatellite V where
  graph := raw.binding.shared.graph
  spatial? := raw.binding.shared.spatial?
  diagram? := raw.binding.shared.diagram?
  frames := raw.frames.attach.map fun frame =>
    relabelFrame raw.binding.enumeration frame.1
      (SourcePhysicalFrame.boundedIn_of_validFor raw.binding frame.1
        (raw.valid frame.1 frame.2))

@[simp] theorem adapt_graph {V : Type*} [DecidableEq V] [Fintype V]
    (raw : RawPhysicalFrameSource V) : (adapt raw).graph = raw.binding.shared.graph := rfl

@[simp] theorem adapt_spatial? {V : Type*} [DecidableEq V] [Fintype V]
    (raw : RawPhysicalFrameSource V) :
    (adapt raw).spatial? = raw.binding.shared.spatial? := rfl

@[simp] theorem adapt_diagram? {V : Type*} [DecidableEq V] [Fintype V]
    (raw : RawPhysicalFrameSource V) :
    (adapt raw).diagram? = raw.binding.shared.diagram? := rfl

@[simp] theorem adapt_frames {V : Type*} [DecidableEq V] [Fintype V]
    (raw : RawPhysicalFrameSource V) :
    (adapt raw).frames = raw.frames.attach.map (fun frame =>
      relabelFrame raw.binding.enumeration frame.1
        (SourcePhysicalFrame.boundedIn_of_validFor raw.binding frame.1
          (raw.valid frame.1 frame.2))) := rfl

/-- The satellite's shared configuration is exactly any spatial configuration actually stored in
the source.  This is where the bridge's exact spatial encode/decode round trip is reused. -/
theorem PhysicalFrameSatellite.spatialConfiguration_adapt {V : Type*} [DecidableEq V] [Fintype V]
    (binding : PhysicalFrameSourceBinding V) (frames : List SourcePhysicalFrame)
    (valid : ∀ frame ∈ frames, frame.ValidFor binding.source)
    (spatial : SpatialConfiguration)
    (observed : binding.source.spatial? = some spatial) :
    (adapt ⟨binding, frames, valid⟩).spatialConfiguration binding.enumeration = spatial := by
  unfold PhysicalFrameSatellite.spatialConfiguration PhysicalFrameSatellite.sharedSpatial?
  change (OrganicFiniteSource.encodeSpatial? binding.enumeration
    binding.shared.spatial?).getD { positions := [] } = spatial
  rw [binding.spatial_eq, observed]
  rfl

/-! ## The decoder, the ordered list wrapper and exact source recovery -/

/-- The recovered source record: the exact authoritative input together with the ordered list of
tagged source frames. -/
@[ext] structure RecoveredPhysicalFrameSource where
  source : AuthoritativeChemicalInput
  frames : List SourcePhysicalFrame

/-- Decode a satellite into the recovered source record.  The authoritative input is the exact
encode of the shared finite source; the frames are decoded one by one with the explicit enumeration
and the satellite's shared coordinate configuration. -/
def suppliedSource {V : Type*} [DecidableEq V] [Fintype V]
    (e : V ≃ Fin (Fintype.card V)) (satellite : PhysicalFrameSatellite V) :
    RecoveredPhysicalFrameSource where
  source := satellite.toFiniteSource.encode e
  frames := satellite.frames.map (decodeFrame e (satellite.spatialConfiguration e))

/-- The ordered frame list is recovered exactly, including order, multiplicity and every carried
atom reference. -/
theorem decodedFrames_adapt {V : Type*} [DecidableEq V] [Fintype V]
    (raw : RawPhysicalFrameSource V) :
    (adapt raw).frames.map
        (decodeFrame raw.binding.enumeration
          ((adapt raw).spatialConfiguration raw.binding.enumeration)) =
      raw.frames := by
  obtain ⟨binding, frames, valid⟩ := raw
  rw [adapt_frames, List.map_map]
  refine Eq.trans ?_ (List.attach_map_subtype_val frames)
  apply List.map_congr_left
  intro frame _
  obtain ⟨frame, member⟩ := frame
  have bounded : frame.BoundedIn (Fintype.card V) :=
    SourcePhysicalFrame.boundedIn_of_validFor binding frame (valid frame member)
  cases frame with
  | helix path helixFrame =>
      exact decodeFrame_relabelFrame_helix binding.enumeration binding.source
        ((adapt ⟨binding, frames, valid⟩).spatialConfiguration binding.enumeration)
        path helixFrame (valid (.helix path helixFrame) member) bounded
  | plane members planeFrame =>
      exact decodeFrame_relabelFrame_plane binding.enumeration binding.source
        ((adapt ⟨binding, frames, valid⟩).spatialConfiguration binding.enumeration)
        members planeFrame (valid (.plane members planeFrame) member) bounded
  | polyhedral center ligands geometry polyFrame =>
      rcases (valid (.polyhedral center ligands geometry polyFrame) member) with
        ⟨_centerEq, _ligandSetEq, _ligandNodup, _geometryEq, _recognized, sourceSpatial,
          _centerPointAt, _positionsAt, _arity, _incidence, _roles, _orientation⟩
      have spatialEq : (adapt ⟨binding, frames, valid⟩).spatialConfiguration
            binding.enumeration = polyFrame.spatial :=
        PhysicalFrameSatellite.spatialConfiguration_adapt binding frames valid
          polyFrame.spatial sourceSpatial
      have spatialObserved : binding.source.spatial? =
          some ((adapt ⟨binding, frames, valid⟩).spatialConfiguration binding.enumeration) := by
        rw [spatialEq]
        exact sourceSpatial
      exact decodeFrame_relabelFrame_polyhedral binding.enumeration binding.source
        ((adapt ⟨binding, frames, valid⟩).spatialConfiguration binding.enumeration)
        center ligands geometry polyFrame
        (valid (.polyhedral center ligands geometry polyFrame) member) bounded spatialObserved

/-- **Exact full source recovery.**  Adapting a raw source into the satellite and decoding it
returns the exact authoritative input and the exact ordered frame list.  The source equality is
the genuine encode equality of the binding; the frame equality is the exact native inverse,
including true polyhedral point reconstruction from the shared coordinates. -/
theorem suppliedSource_adapt {V : Type*} [DecidableEq V] [Fintype V]
    (raw : RawPhysicalFrameSource V) :
    suppliedSource raw.binding.enumeration (adapt raw) =
      { source := raw.binding.source, frames := raw.frames } := by
  apply RecoveredPhysicalFrameSource.ext
  · exact raw.binding.encode_shared
  · simp only [suppliedSource]
    exact decodedFrames_adapt raw

/-! ## Concrete certified-source adapter

`OrganicStereoAuthoritativeSourceBridge`'s exact ingress supplies the shared finite source for any
certified input, and its exact round trip supplies all three binding equalities.  This is the
concrete instantiation of the abstract binding, with no extra reconstruction. -/

/-- The concrete binding of a certified authoritative input to its exact finite ingress source. -/
def PhysicalFrameSourceBinding.ofCertified (certified : CertifiedAuthoritativeChemicalInput) :
    PhysicalFrameSourceBinding (Fin certified.input.molecule.atomCount) where
  source := certified.input
  shared := certified.decode
  enumeration := identityEnumeration certified.input.molecule.atomCount
  graph_eq := CertifiedAuthoritativeChemicalInput.encode_decode_molecule certified
  spatial_eq := CertifiedAuthoritativeChemicalInput.encode_decode_spatial? certified
  diagram_eq := CertifiedAuthoritativeChemicalInput.encode_decode_diagram? certified
  spatial_wellFormed := certified.structurallyWellFormed.2.1

/-- Adapt a certified source together with an ordered list of validated carrier frames. -/
def adaptCertified (certified : CertifiedAuthoritativeChemicalInput)
    (frames : List SourcePhysicalFrame)
    (valid : ∀ frame ∈ frames, frame.ValidFor certified.input) :
    PhysicalFrameSatellite (Fin certified.input.molecule.atomCount) :=
  adapt { binding := PhysicalFrameSourceBinding.ofCertified certified
          frames := frames
          valid := valid }

/-- The certified adapter's shared configuration is any spatial configuration actually stored in
the source. -/
theorem adaptCertified_spatialConfiguration
    (certified : CertifiedAuthoritativeChemicalInput)
    (frames : List SourcePhysicalFrame)
    (valid : ∀ frame ∈ frames, frame.ValidFor certified.input)
    (spatial : SpatialConfiguration)
    (observed : certified.input.spatial? = some spatial) :
    (adaptCertified certified frames valid).spatialConfiguration
        (identityEnumeration certified.input.molecule.atomCount) = spatial :=
  PhysicalFrameSatellite.spatialConfiguration_adapt _ frames valid spatial observed

/-- **Concrete exact recovery from a certified source.**  Decoding the adapted satellite returns the
exact certified authoritative input and the exact ordered carrier frame list. -/
theorem suppliedSource_adaptCertified
    (certified : CertifiedAuthoritativeChemicalInput)
    (frames : List SourcePhysicalFrame)
    (valid : ∀ frame ∈ frames, frame.ValidFor certified.input) :
    suppliedSource (identityEnumeration certified.input.molecule.atomCount)
        (adaptCertified certified frames valid) =
      { source := certified.input, frames := frames } :=
  suppliedSource_adapt
    { binding := PhysicalFrameSourceBinding.ofCertified certified
      frames := frames
      valid := valid }

/-! ## Inverse on the native side -/

/-- Every decoded payload satisfies the explicit bounds at the same enumeration arity. -/
theorem decodeFrame_bounded {V : Type*} [DecidableEq V] {n : ℕ} (e : V ≃ Fin n)
    (spatial : SpatialConfiguration) (native : PhysicalFrame V) :
    (decodeFrame e spatial native).BoundedIn n := by
  cases native with
  | helix native =>
      exact
        { frontBound := encodeAtom_lt e native.frontReference
          backBound := encodeAtom_lt e native.backReference
          pathBound := fun atom member =>
            unrelabelList_bounded e native.helixPath atom member }
  | plane native =>
      exact
        { pilotBound := encodeAtom_lt e native.pilotAtom
          firstBound := encodeAtom_lt e native.firstReference
          secondBound := encodeAtom_lt e native.secondReference
          inPlaneBound := encodeAtom_lt e native.inPlaneBondAtom
          outOfPlaneBound := encodeAtom_lt e native.outOfPlaneAtom
          planeAtomsBound := fun atom member =>
            unrelabelList_bounded e native.planeAtoms atom member }
  | polyhedral native =>
      exact
        { centerBound := encodeAtom_lt e native.center
          ligandsBound := fun atom member =>
            unrelabelList_bounded e native.ligands atom member }

/-- Relabelling a decoded native payload returns the payload.  This is a representation inverse and
requires no source validity or coordinate incidence: the polyhedral coordinate fields are simply
not part of the native payload. -/
theorem relabelFrame_decodeFrame {V : Type*} [DecidableEq V] {n : ℕ}
    (e : V ≃ Fin n) (spatial : SpatialConfiguration) (native : PhysicalFrame V) :
    relabelFrame e (decodeFrame e spatial native) (decodeFrame_bounded e spatial native) =
      native := by
  cases native with
  | helix native =>
      obtain ⟨helixPath, frontReference, backReference, sense, descriptor⟩ := native
      simp [decodeFrame, relabelFrame, decodeHelix, relabelHelix,
        relabelList_unrelabelList, decodeAtom_encodeAtom]
  | plane native =>
      obtain ⟨planeAtoms, pilotAtom, firstReference, secondReference, inPlaneBondAtom,
        outOfPlaneAtom, torsionRestricted, planeCannotBeSymmetryPlane⟩ := native
      simp [decodeFrame, relabelFrame, decodePlane, relabelPlane,
        relabelList_unrelabelList, decodeAtom_encodeAtom]
  | polyhedral native =>
      obtain ⟨center, geometry, recognition, ligands, configurationPositions,
        absoluteOrientation, priming⟩ := native
      simp [decodeFrame, relabelFrame, decodePolyhedral, relabelPolyhedral,
        decodePolyhedralObservation, relabelList_unrelabelList, decodeAtom_encodeAtom]

end OrganicStereoP93PhysicalFrameIngress

end TetraStereo.OneCenter
