import Mathlib.Data.Finset.Image
import TetraStereo.OneCenter.OrganicStereoFiniteClassicalDescription
import TetraStereo.OneCenter.OrganicStereoP93PhysicalFrameIngress

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace TetraStereo.OneCenter

namespace OrganicStereoP93PhysicalFrameTransport

open TetraStereo.OneCenter.OrganicStereoP93PhysicalFrameIngress
open TetraStereo.OneCenter.OrganicStereoSuppliedCitationIngress

/-!
# Native `V ≃ W` transport for the P-93 physical-frame satellite

`OrganicStereoP93PhysicalFrameIngress` defines a native tagged payload `PhysicalFrame V` and a
composable satellite `PhysicalFrameSatellite V`.  Its relabelling operation `relabelFrame` adapts a
*raw `Nat`-indexed* `SourcePhysicalFrame` into the native payload at one chosen enumeration; it is
not a native-to-native operation.

This module supplies the missing representation layer: one actual equivalence `e : V ≃ W` is used
for every atom reference of a native frame and of a whole satellite at once.

* Every native atom reference is mapped by `e`: the helix front/back references and ordered helix
  path, the planar pilot/reference/in-plane/out-of-plane atoms and ordered traversal, and the
  polyhedral centre and ordered ligand list.  `List.map` preserves order and multiplicity
  literally; the two-sided inverse theorems show that nothing is merged, sorted or dropped.
* The shared graph channel is relabelled with the repository's existing
  `FiniteAtomInteractionHypergraph.relabelGraph` (whose inverse is `relabelGraph_symm`).  The
  optional coordinate channel and the optional drawing channel are moved fieldwise and are proved
  compatible with the existing encoders `OrganicFiniteSource.encodeSpatial?` and
  `OrganicDiagramSource.encodeDiagram`.
* Descriptor/sense/applicability fields, polyhedral geometry metadata, the geometry-role
  `configurationPositions`, `recognition`, `absoluteOrientation`, `priming`, drawing bond
  styles/scopes and atom parity tokens are copied **literally**.  Geometry-role ordinals and
  printed/naming metadata are not atom labels and are never mapped through `e`.
* The ordered frame list of a satellite is mapped in order and multiplicity.

The native transport is a genuine record-level codec: `transportFrame`/`untransportFrame` and
`transportSatellite`/`untransportSatellite` are fieldwise definitions with no stored copy of the
original payload, and both inverse laws are proved as full equalities.  Arbitrary-set and finite-set
recovery follow from those inverses, not from assumed inverses.

## Enumeration transport and the physical source

The physical source recovered by `suppliedSource` is `Nat`-indexed.  Its canonical predicates (the
`first < second` bond normalisation, ordered `Nodup`, path orientation, the `Nat` identity data of a
`SourcePhysicalFrame`) are *not* invariant under an arbitrary re-numbering of the atom labels.  We
therefore do not claim that an arbitrary pair of enumerations of `V` and `W` recovers the same
`Nat` source.  Instead, for an enumeration `eV : V ≃ Fin (Fintype.card V)` we transport it to the
*corresponding* enumeration `transportEnumeration e eV : W ≃ Fin (Fintype.card W)`, whose indices
agree with `eV` along `e`.  At that enumeration the entire recovered `suppliedSource` is proved
invariant: the recovered source record and the ordered `SourcePhysicalFrame` list are exactly the
same, including the reconstructed polyhedral `centerPoint` and ordered `positionPoints`.

## Scope

This is lossless representation transport only.  It does not assert chemical admissibility, does
not discharge any P-93 policy boundary, and does not claim invariance of source-indexed `Nat`
predicates under arbitrary re-numbering.  It is intended to enable a later `MixedSource` canonical
transport: the same fieldwise codec can be composed with the canonical enumeration of a mixed
source without exposing a second notion of atom identity.
-/

/-! ## Corresponding finite enumerations

Given `e : V ≃ W` and an enumeration of `V`, the enumeration of `W` used below assigns to `e v` the
same raw index that the original enumeration assigns to `v`.  This is the only enumeration at which
the `Nat`-indexed physical source is claimed to be invariant. -/

variable {V W : Type*}

/-- The canonical index equivalence induced by a finite-type equivalence.  It preserves the
underlying `Nat` value of every index in both directions. -/
def cardEquiv (e : V ≃ W) [Fintype V] [Fintype W] :
    Fin (Fintype.card V) ≃ Fin (Fintype.card W) where
  toFun index :=
    ⟨index.val, (Fintype.card_congr e) ▸ index.isLt⟩
  invFun index :=
    ⟨index.val, (Fintype.card_congr e).symm ▸ index.isLt⟩
  left_inv _ := Fin.ext rfl
  right_inv _ := Fin.ext rfl

@[simp] theorem cardEquiv_apply_val (e : V ≃ W) [Fintype V] [Fintype W]
    (index : Fin (Fintype.card V)) :
    (cardEquiv e index).val = index.val := rfl

@[simp] theorem cardEquiv_symm_apply_val (e : V ≃ W) [Fintype V] [Fintype W]
    (index : Fin (Fintype.card W)) :
    ((cardEquiv e).symm index).val = index.val := rfl

/-- The enumeration of `W` corresponding to an enumeration of `V` along `e`. -/
def transportEnumeration (e : V ≃ W) [Fintype V] [Fintype W]
    (enumeration : V ≃ Fin (Fintype.card V)) : W ≃ Fin (Fintype.card W) :=
  (e.symm.trans enumeration).trans (cardEquiv e)

/-- At a transported atom, the corresponding enumeration assigns exactly the same index. -/
@[simp] theorem transportEnumeration_apply (e : V ≃ W) [Fintype V] [Fintype W]
    (enumeration : V ≃ Fin (Fintype.card V)) (atom : V) :
    transportEnumeration e enumeration (e atom) = cardEquiv e (enumeration atom) := by
  simp [transportEnumeration]

/-- The raw index of a transported atom is the raw index the original enumeration gave it. -/
@[simp] theorem transportEnumeration_apply_val (e : V ≃ W) [Fintype V] [Fintype W]
    (enumeration : V ≃ Fin (Fintype.card V)) (atom : V) :
    ((transportEnumeration e enumeration) (e atom)).val = (enumeration atom).val := by
  rw [transportEnumeration_apply]
  rfl

/-- The inverse transported enumeration maps an index back through the inverse equivalence. -/
@[simp] theorem transportEnumeration_symm_apply (e : V ≃ W) [Fintype V] [Fintype W]
    (enumeration : V ≃ Fin (Fintype.card V)) (index : Fin (Fintype.card W)) :
    (transportEnumeration e enumeration).symm index =
      e (enumeration.symm ((cardEquiv e).symm index)) := by
  simp [transportEnumeration]

/-- Pulling an index back through the transported enumeration and then through `e` gives exactly
the original enumeration applied to the cast index. -/
theorem e_symm_transportEnumeration_symm (e : V ≃ W) [Fintype V] [Fintype W]
    (enumeration : V ≃ Fin (Fintype.card V)) (index : Fin (Fintype.card W)) :
    e.symm ((transportEnumeration e enumeration).symm index) =
      enumeration.symm (Fin.cast (Fintype.card_congr e).symm index) := by
  rw [transportEnumeration_symm_apply]
  have hidx : (cardEquiv e).symm index =
      Fin.cast (Fintype.card_congr e).symm index := Fin.ext rfl
  rw [hidx]
  simp

/-- The existing atom encoder commutes with the corresponding enumeration. -/
@[simp] theorem encodeAtom_transportEnumeration (e : V ≃ W) [Fintype V] [Fintype W]
    (enumeration : V ≃ Fin (Fintype.card V)) (atom : V) :
    encodeAtom (transportEnumeration e enumeration) (e atom) = encodeAtom enumeration atom := by
  simp [encodeAtom]

/-- Ordered lists of atoms encode identically at corresponding enumerations. -/
@[simp] theorem unrelabelList_map (e : V ≃ W) [Fintype V] [Fintype W]
    (enumeration : V ≃ Fin (Fintype.card V)) (atoms : List V) :
    unrelabelList (transportEnumeration e enumeration) (atoms.map e) =
      unrelabelList enumeration atoms := by
  unfold unrelabelList
  rw [List.map_map]
  apply List.map_congr_left
  intro atom _
  exact encodeAtom_transportEnumeration e enumeration atom

/-! ## Native frame transport -/

section NativeFrames

variable [DecidableEq V] [DecidableEq W]

/-- Map every atom reference of a native helix frame by one equivalence.  The supplied sense and
descriptor are copied literally. -/
def transportHelix (e : V ≃ W) (frame : NativeHelixFrame V) : NativeHelixFrame W where
  helixPath := frame.helixPath.map e
  frontReference := e frame.frontReference
  backReference := e frame.backReference
  sense := frame.sense
  descriptor := frame.descriptor

/-- Map every atom reference of a native planar frame by one equivalence.  Both applicability
Booleans are copied literally. -/
def transportPlane (e : V ≃ W) (frame : NativePlanarFrame V) : NativePlanarFrame W where
  planeAtoms := frame.planeAtoms.map e
  pilotAtom := e frame.pilotAtom
  firstReference := e frame.firstReference
  secondReference := e frame.secondReference
  inPlaneBondAtom := e frame.inPlaneBondAtom
  outOfPlaneAtom := e frame.outOfPlaneAtom
  torsionRestricted := frame.torsionRestricted
  planeCannotBeSymmetryPlane := frame.planeCannotBeSymmetryPlane

/-- Map the atom-identified part of a native polyhedral frame by one equivalence.

`geometry`, `recognition`, `configurationPositions`, `absoluteOrientation` and `priming` are
copied literally: those fields are geometry-role metadata and naming/geometry observations, not
atom labels.  In particular the geometry-position ordinals are never mapped through `e`. -/
def transportPolyhedral (e : V ≃ W) (frame : NativePolyhedralFrame V) :
    NativePolyhedralFrame W where
  center := e frame.center
  geometry := frame.geometry
  recognition := frame.recognition
  ligands := frame.ligands.map e
  configurationPositions := frame.configurationPositions
  absoluteOrientation := frame.absoluteOrientation
  priming := frame.priming

/-- Map every atom reference of a tagged native payload by one equivalence.  The tag is preserved
and no original payload is stored. -/
def transportFrame (e : V ≃ W) : PhysicalFrame V → PhysicalFrame W
  | .helix frame => .helix (transportHelix e frame)
  | .plane frame => .plane (transportPlane e frame)
  | .polyhedral frame => .polyhedral (transportPolyhedral e frame)

/-- Decode every atom reference of a native helix frame using the inverse equivalence. -/
def untransportHelix (e : V ≃ W) (frame : NativeHelixFrame W) : NativeHelixFrame V where
  helixPath := frame.helixPath.map e.symm
  frontReference := e.symm frame.frontReference
  backReference := e.symm frame.backReference
  sense := frame.sense
  descriptor := frame.descriptor

/-- Decode every atom reference of a native planar frame using the inverse equivalence. -/
def untransportPlane (e : V ≃ W) (frame : NativePlanarFrame W) : NativePlanarFrame V where
  planeAtoms := frame.planeAtoms.map e.symm
  pilotAtom := e.symm frame.pilotAtom
  firstReference := e.symm frame.firstReference
  secondReference := e.symm frame.secondReference
  inPlaneBondAtom := e.symm frame.inPlaneBondAtom
  outOfPlaneAtom := e.symm frame.outOfPlaneAtom
  torsionRestricted := frame.torsionRestricted
  planeCannotBeSymmetryPlane := frame.planeCannotBeSymmetryPlane

/-- Decode the atom-identified part of a native polyhedral frame using the inverse equivalence. -/
def untransportPolyhedral (e : V ≃ W) (frame : NativePolyhedralFrame W) :
    NativePolyhedralFrame V where
  center := e.symm frame.center
  geometry := frame.geometry
  recognition := frame.recognition
  ligands := frame.ligands.map e.symm
  configurationPositions := frame.configurationPositions
  absoluteOrientation := frame.absoluteOrientation
  priming := frame.priming

/-- Decode a tagged native payload using the inverse equivalence. -/
def untransportFrame (e : V ≃ W) : PhysicalFrame W → PhysicalFrame V
  | .helix frame => .helix (untransportHelix e frame)
  | .plane frame => .plane (untransportPlane e frame)
  | .polyhedral frame => .polyhedral (untransportPolyhedral e frame)

/-! ### Field equations and order/multiplicity preservation -/

@[simp] theorem transportHelix_helixPath (e : V ≃ W) (frame : NativeHelixFrame V) :
    (transportHelix e frame).helixPath = frame.helixPath.map e := rfl

@[simp] theorem transportHelix_frontReference (e : V ≃ W) (frame : NativeHelixFrame V) :
    (transportHelix e frame).frontReference = e frame.frontReference := rfl

@[simp] theorem transportHelix_backReference (e : V ≃ W) (frame : NativeHelixFrame V) :
    (transportHelix e frame).backReference = e frame.backReference := rfl

@[simp] theorem transportHelix_sense (e : V ≃ W) (frame : NativeHelixFrame V) :
    (transportHelix e frame).sense = frame.sense := rfl

@[simp] theorem transportHelix_descriptor (e : V ≃ W) (frame : NativeHelixFrame V) :
    (transportHelix e frame).descriptor = frame.descriptor := rfl

@[simp] theorem transportPlane_planeAtoms (e : V ≃ W) (frame : NativePlanarFrame V) :
    (transportPlane e frame).planeAtoms = frame.planeAtoms.map e := rfl

@[simp] theorem transportPlane_pilotAtom (e : V ≃ W) (frame : NativePlanarFrame V) :
    (transportPlane e frame).pilotAtom = e frame.pilotAtom := rfl

@[simp] theorem transportPlane_firstReference (e : V ≃ W) (frame : NativePlanarFrame V) :
    (transportPlane e frame).firstReference = e frame.firstReference := rfl

@[simp] theorem transportPlane_secondReference (e : V ≃ W) (frame : NativePlanarFrame V) :
    (transportPlane e frame).secondReference = e frame.secondReference := rfl

@[simp] theorem transportPlane_inPlaneBondAtom (e : V ≃ W) (frame : NativePlanarFrame V) :
    (transportPlane e frame).inPlaneBondAtom = e frame.inPlaneBondAtom := rfl

@[simp] theorem transportPlane_outOfPlaneAtom (e : V ≃ W) (frame : NativePlanarFrame V) :
    (transportPlane e frame).outOfPlaneAtom = e frame.outOfPlaneAtom := rfl

@[simp] theorem transportPlane_torsionRestricted (e : V ≃ W) (frame : NativePlanarFrame V) :
    (transportPlane e frame).torsionRestricted = frame.torsionRestricted := rfl

@[simp] theorem transportPlane_planeCannotBeSymmetryPlane (e : V ≃ W)
    (frame : NativePlanarFrame V) :
    (transportPlane e frame).planeCannotBeSymmetryPlane =
      frame.planeCannotBeSymmetryPlane := rfl

@[simp] theorem transportPolyhedral_center (e : V ≃ W) (frame : NativePolyhedralFrame V) :
    (transportPolyhedral e frame).center = e frame.center := rfl

@[simp] theorem transportPolyhedral_ligands (e : V ≃ W) (frame : NativePolyhedralFrame V) :
    (transportPolyhedral e frame).ligands = frame.ligands.map e := rfl

@[simp] theorem transportPolyhedral_geometry (e : V ≃ W) (frame : NativePolyhedralFrame V) :
    (transportPolyhedral e frame).geometry = frame.geometry := rfl

@[simp] theorem transportPolyhedral_recognition (e : V ≃ W) (frame : NativePolyhedralFrame V) :
    (transportPolyhedral e frame).recognition = frame.recognition := rfl

/-- Geometry-role position ordinals are metadata, not atom labels.  They are transported
literally and are never renumbered. -/
@[simp] theorem transportPolyhedral_configurationPositions (e : V ≃ W)
    (frame : NativePolyhedralFrame V) :
    (transportPolyhedral e frame).configurationPositions = frame.configurationPositions := rfl

@[simp] theorem transportPolyhedral_absoluteOrientation (e : V ≃ W)
    (frame : NativePolyhedralFrame V) :
    (transportPolyhedral e frame).absoluteOrientation = frame.absoluteOrientation := rfl

@[simp] theorem transportPolyhedral_priming (e : V ≃ W) (frame : NativePolyhedralFrame V) :
    (transportPolyhedral e frame).priming = frame.priming := rfl

/-- The ordered helix traversal keeps its length. -/
@[simp] theorem transportHelix_helixPath_length (e : V ≃ W) (frame : NativeHelixFrame V) :
    (transportHelix e frame).helixPath.length = frame.helixPath.length := by
  simp

/-- The ordered planar traversal keeps its length. -/
@[simp] theorem transportPlane_planeAtoms_length (e : V ≃ W) (frame : NativePlanarFrame V) :
    (transportPlane e frame).planeAtoms.length = frame.planeAtoms.length := by
  simp

/-- The ordered polyhedral ligand list keeps its length. -/
@[simp] theorem transportPolyhedral_ligands_length (e : V ≃ W)
    (frame : NativePolyhedralFrame V) :
    (transportPolyhedral e frame).ligands.length = frame.ligands.length := by
  simp

/-- Duplicate-freeness of the helix traversal is preserved and reflected: mapping by an
equivalence neither creates nor removes repetitions. -/
theorem transportHelix_helixPath_nodup_iff (e : V ≃ W) (frame : NativeHelixFrame V) :
    (transportHelix e frame).helixPath.Nodup ↔ frame.helixPath.Nodup :=
  List.nodup_map_iff e.injective

/-- Duplicate-freeness of the planar traversal is preserved and reflected. -/
theorem transportPlane_planeAtoms_nodup_iff (e : V ≃ W) (frame : NativePlanarFrame V) :
    (transportPlane e frame).planeAtoms.Nodup ↔ frame.planeAtoms.Nodup :=
  List.nodup_map_iff e.injective

/-- Duplicate-freeness of the polyhedral ligand list is preserved and reflected. -/
theorem transportPolyhedral_ligands_nodup_iff (e : V ≃ W)
    (frame : NativePolyhedralFrame V) :
    (transportPolyhedral e frame).ligands.Nodup ↔ frame.ligands.Nodup :=
  List.nodup_map_iff e.injective

/-- The helix path is moved position by position; its exact list structure is a `map`. -/
theorem transportHelix_path_eq (e : V ≃ W) (frame : NativeHelixFrame V) :
    (transportHelix e frame).helixPath = frame.helixPath.map e := rfl

/-- The planar traversal is moved position by position. -/
theorem transportPlane_atoms_eq (e : V ≃ W) (frame : NativePlanarFrame V) :
    (transportPlane e frame).planeAtoms = frame.planeAtoms.map e := rfl

/-- The polyhedral ligand list is moved position by position. -/
theorem transportPolyhedral_ligands_eq (e : V ≃ W) (frame : NativePolyhedralFrame V) :
    (transportPolyhedral e frame).ligands = frame.ligands.map e := rfl

/-! ### Two-sided native inverses -/

theorem untransportHelix_transportHelix (e : V ≃ W) (frame : NativeHelixFrame V) :
    untransportHelix e (transportHelix e frame) = frame := by
  obtain ⟨helixPath, frontReference, backReference, sense, descriptor⟩ := frame
  simp [transportHelix, untransportHelix]

theorem transportHelix_untransportHelix (e : V ≃ W) (frame : NativeHelixFrame W) :
    transportHelix e (untransportHelix e frame) = frame := by
  obtain ⟨helixPath, frontReference, backReference, sense, descriptor⟩ := frame
  simp [transportHelix, untransportHelix]

theorem untransportPlane_transportPlane (e : V ≃ W) (frame : NativePlanarFrame V) :
    untransportPlane e (transportPlane e frame) = frame := by
  obtain ⟨planeAtoms, pilotAtom, firstReference, secondReference, inPlaneBondAtom,
    outOfPlaneAtom, torsionRestricted, planeCannotBeSymmetryPlane⟩ := frame
  simp [transportPlane, untransportPlane]

theorem transportPlane_untransportPlane (e : V ≃ W) (frame : NativePlanarFrame W) :
    transportPlane e (untransportPlane e frame) = frame := by
  obtain ⟨planeAtoms, pilotAtom, firstReference, secondReference, inPlaneBondAtom,
    outOfPlaneAtom, torsionRestricted, planeCannotBeSymmetryPlane⟩ := frame
  simp [transportPlane, untransportPlane]

theorem untransportPolyhedral_transportPolyhedral (e : V ≃ W)
    (frame : NativePolyhedralFrame V) :
    untransportPolyhedral e (transportPolyhedral e frame) = frame := by
  obtain ⟨center, geometry, recognition, ligands, configurationPositions,
    absoluteOrientation, priming⟩ := frame
  simp [transportPolyhedral, untransportPolyhedral]

theorem transportPolyhedral_untransportPolyhedral (e : V ≃ W)
    (frame : NativePolyhedralFrame W) :
    transportPolyhedral e (untransportPolyhedral e frame) = frame := by
  obtain ⟨center, geometry, recognition, ligands, configurationPositions,
    absoluteOrientation, priming⟩ := frame
  simp [transportPolyhedral, untransportPolyhedral]

/-- Decoding a transported native payload recovers the exact original payload. -/
theorem untransportFrame_transportFrame (e : V ≃ W) (frame : PhysicalFrame V) :
    untransportFrame e (transportFrame e frame) = frame := by
  cases frame with
  | helix frame =>
      simp [transportFrame, untransportFrame, untransportHelix_transportHelix]
  | plane frame =>
      simp [transportFrame, untransportFrame, untransportPlane_transportPlane]
  | polyhedral frame =>
      simp [transportFrame, untransportFrame, untransportPolyhedral_transportPolyhedral]

/-- Re-transporting a decoded native payload recovers the exact original payload. -/
theorem transportFrame_untransportFrame (e : V ≃ W) (frame : PhysicalFrame W) :
    transportFrame e (untransportFrame e frame) = frame := by
  cases frame with
  | helix frame =>
      simp [transportFrame, untransportFrame, transportHelix_untransportHelix]
  | plane frame =>
      simp [transportFrame, untransportFrame, transportPlane_untransportPlane]
  | polyhedral frame =>
      simp [transportFrame, untransportFrame, transportPolyhedral_untransportPolyhedral]

/-- Native transport is injective. -/
theorem transportFrame_injective (e : V ≃ W) :
    Function.Injective (transportFrame e) := by
  intro first second equal
  calc
    first = untransportFrame e (transportFrame e first) :=
      (untransportFrame_transportFrame e first).symm
    _ = untransportFrame e (transportFrame e second) := by rw [equal]
    _ = second := untransportFrame_transportFrame e second

/-- Native transport is bijective. -/
theorem transportFrame_bijective (e : V ≃ W) :
    Function.Bijective (transportFrame e) :=
  ⟨transportFrame_injective e, fun target =>
    ⟨untransportFrame e target, transportFrame_untransportFrame e target⟩⟩

/-- An arbitrary set of native payloads is recovered exactly by transporting and undoing. -/
theorem untransportFrame_image_transportFrameSet (e : V ≃ W)
    (frames : Set (PhysicalFrame V)) :
    untransportFrame e '' (transportFrame e '' frames) = frames := by
  rw [Set.image_image]
  have composed : (fun frame : PhysicalFrame V => untransportFrame e (transportFrame e frame)) =
      id := by
    funext frame
    exact untransportFrame_transportFrame e frame
  change (fun frame : PhysicalFrame V => untransportFrame e (transportFrame e frame)) ''
    frames = frames
  rw [composed, Set.image_id]

/-- An arbitrary finite set of native payloads is recovered exactly. -/
theorem untransportFrame_image_finset (e : V ≃ W) (frames : Finset (PhysicalFrame V)) :
    (frames.image (transportFrame e)).image (untransportFrame e) = frames := by
  rw [Finset.image_image]
  have composed : (fun frame : PhysicalFrame V => untransportFrame e (transportFrame e frame)) =
      id := by
    funext frame
    exact untransportFrame_transportFrame e frame
  change frames.image
    (fun frame : PhysicalFrame V => untransportFrame e (transportFrame e frame)) = frames
  rw [composed, Finset.image_id]

/-- List membership after transport is exactly membership of the transported-back payload. -/
theorem mem_transportFrames_iff (e : V ≃ W) (frames : List (PhysicalFrame V))
    (native : PhysicalFrame W) :
    native ∈ frames.map (transportFrame e) ↔ untransportFrame e native ∈ frames := by
  rw [List.mem_map]
  constructor
  · rintro ⟨original, member, rfl⟩
    simpa [untransportFrame_transportFrame] using member
  · intro member
    exact ⟨untransportFrame e native, member,
      transportFrame_untransportFrame e native⟩

end NativeFrames

/-! ## Optional coordinate and drawing channels -/

section Channels

variable [DecidableEq V] [DecidableEq W]

/-- Move a total rational coordinate function across the equivalence. -/
def transportSpatialFunction (e : V ≃ W) (positions : V → CartesianPoint3) :
    W → CartesianPoint3 :=
  fun atom => positions (e.symm atom)

/-- Move a total rational coordinate function back across the equivalence. -/
def untransportSpatialFunction (e : V ≃ W) (positions : W → CartesianPoint3) :
    V → CartesianPoint3 :=
  fun atom => positions (e atom)

/-- Transport the optional spatial channel; absence is preserved as absence. -/
def transportSpatial? (e : V ≃ W) :
    Option (V → CartesianPoint3) → Option (W → CartesianPoint3)
  | none => none
  | some positions => some (transportSpatialFunction e positions)

/-- Decode the optional spatial channel; absence is preserved as absence. -/
def untransportSpatial? (e : V ≃ W) :
    Option (W → CartesianPoint3) → Option (V → CartesianPoint3)
  | none => none
  | some positions => some (untransportSpatialFunction e positions)

@[simp] theorem transportSpatial?_none (e : V ≃ W) :
    transportSpatial? e none = none := rfl

@[simp] theorem transportSpatial?_some (e : V ≃ W) (positions : V → CartesianPoint3) :
    transportSpatial? e (some positions) =
      some (fun atom : W => positions (e.symm atom)) := rfl

@[simp] theorem untransportSpatial?_none (e : V ≃ W) :
    untransportSpatial? e none = none := rfl

@[simp] theorem untransportSpatial?_some (e : V ≃ W) (positions : W → CartesianPoint3) :
    untransportSpatial? e (some positions) =
      some (fun atom : V => positions (e atom)) := rfl

theorem untransportSpatial?_transportSpatial? (e : V ≃ W)
    (positions? : Option (V → CartesianPoint3)) :
    untransportSpatial? e (transportSpatial? e positions?) = positions? := by
  cases positions? with
  | none => rfl
  | some positions => simp [transportSpatialFunction, untransportSpatialFunction]

theorem transportSpatial?_untransportSpatial? (e : V ≃ W)
    (positions? : Option (W → CartesianPoint3)) :
    transportSpatial? e (untransportSpatial? e positions?) = positions? := by
  cases positions? with
  | none => rfl
  | some positions => simp [transportSpatialFunction, untransportSpatialFunction]

/-- Extensionality for the single-field spatial configuration. -/
theorem spatialConfiguration_ext {first second : SpatialConfiguration}
    (positions : first.positions = second.positions) : first = second := by
  cases first
  cases second
  simp_all

/-- The existing all-or-nothing spatial encoder commutes with transport at the corresponding
enumeration. -/
theorem encodeSpatial?_transportSpatial? (e : V ≃ W) [Fintype V] [Fintype W]
    (enumeration : V ≃ Fin (Fintype.card V))
    (positions? : Option (V → CartesianPoint3)) :
    OrganicFiniteSource.encodeSpatial? (transportEnumeration e enumeration)
        (transportSpatial? e positions?) =
      OrganicFiniteSource.encodeSpatial? enumeration positions? := by
  cases positions? with
  | none => rfl
  | some positions =>
      simp only [transportSpatial?_some, OrganicFiniteSource.encodeSpatial?_some]
      apply congrArg some
      apply spatialConfiguration_ext
      rw [List.ofFn_congr (Fintype.card_congr e)
        (fun index : Fin (Fintype.card V) => positions (enumeration.symm index))]
      rw [List.ofFn_inj]
      funext index
      rw [e_symm_transportEnumeration_symm]

/-! ### Drawing channel -/

/-- Transport one source bond annotation: endpoints move with `e`, while style and scope are
printed/naming metadata and are copied literally. -/
def transportDiagramBond (e : V ≃ W) (bond : SourceDiagramBond V) :
    SourceDiagramBond W where
  source := e bond.source
  target := e bond.target
  style := bond.style
  scope := bond.scope

/-- Decode one source bond annotation using the inverse equivalence. -/
def untransportDiagramBond (e : V ≃ W) (bond : SourceDiagramBond W) :
    SourceDiagramBond V where
  source := e.symm bond.source
  target := e.symm bond.target
  style := bond.style
  scope := bond.scope

/-- Transport one atom-parity annotation: the atom moves with `e`, while the parity token and the
scope (including any group number) are copied literally. -/
def transportDiagramAtom (e : V ≃ W) (atom : SourceDiagramAtom V) :
    SourceDiagramAtom W where
  atom := e atom.atom
  parity := atom.parity
  scope := atom.scope

/-- Decode one atom-parity annotation using the inverse equivalence. -/
def untransportDiagramAtom (e : V ≃ W) (atom : SourceDiagramAtom W) :
    SourceDiagramAtom V where
  atom := e.symm atom.atom
  parity := atom.parity
  scope := atom.scope

@[simp] theorem transportDiagramBond_style (e : V ≃ W) (bond : SourceDiagramBond V) :
    (transportDiagramBond e bond).style = bond.style := rfl

/-- The bond scope, including any relative/racemic group number, is printed metadata, not an atom
label. -/
@[simp] theorem transportDiagramBond_scope (e : V ≃ W) (bond : SourceDiagramBond V) :
    (transportDiagramBond e bond).scope = bond.scope := rfl

@[simp] theorem transportDiagramAtom_parity (e : V ≃ W) (atom : SourceDiagramAtom V) :
    (transportDiagramAtom e atom).parity = atom.parity := rfl

/-- The configuration scope of an atom annotation is printed metadata, not an atom label. -/
@[simp] theorem transportDiagramAtom_scope (e : V ≃ W) (atom : SourceDiagramAtom V) :
    (transportDiagramAtom e atom).scope = atom.scope := rfl

/-- Transport an optional two-dimensional position function. -/
def transportPositions2? (e : V ≃ W) :
    Option (V → CartesianPoint2) → Option (W → CartesianPoint2)
  | none => none
  | some positions => some fun atom => positions (e.symm atom)

/-- Decode an optional two-dimensional position function. -/
def untransportPositions2? (e : V ≃ W) :
    Option (W → CartesianPoint2) → Option (V → CartesianPoint2)
  | none => none
  | some positions => some fun atom => positions (e atom)

@[simp] theorem transportPositions2?_none (e : V ≃ W) :
    transportPositions2? e none = none := rfl

@[simp] theorem transportPositions2?_some (e : V ≃ W) (positions : V → CartesianPoint2) :
    transportPositions2? e (some positions) =
      some (fun atom : W => positions (e.symm atom)) := rfl

@[simp] theorem untransportPositions2?_none (e : V ≃ W) :
    untransportPositions2? e none = none := rfl

@[simp] theorem untransportPositions2?_some (e : V ≃ W) (positions : W → CartesianPoint2) :
    untransportPositions2? e (some positions) =
      some (fun atom : V => positions (e atom)) := rfl

/-- Transport a whole source drawing channel.  Positions and atom references move; bond style,
parity and scope metadata are copied literally. -/
def transportDiagram (e : V ≃ W) (source : OrganicDiagramSource V) :
    OrganicDiagramSource W where
  positions? := transportPositions2? e source.positions?
  bonds := source.bonds.map (transportDiagramBond e)
  atomConfigurations := source.atomConfigurations.map (transportDiagramAtom e)

/-- Decode a whole source drawing channel. -/
def untransportDiagram (e : V ≃ W) (source : OrganicDiagramSource W) :
    OrganicDiagramSource V where
  positions? := untransportPositions2? e source.positions?
  bonds := source.bonds.map (untransportDiagramBond e)
  atomConfigurations := source.atomConfigurations.map (untransportDiagramAtom e)

/-- Extensionality for the drawing channel. -/
theorem organicDiagramSource_ext {first second : OrganicDiagramSource V}
    (positions : first.positions? = second.positions?)
    (bonds : first.bonds = second.bonds)
    (atomConfigurations : first.atomConfigurations = second.atomConfigurations) :
    first = second := by
  cases first
  cases second
  simp_all

theorem untransportDiagram_transportDiagram (e : V ≃ W)
    (source : OrganicDiagramSource V) :
    untransportDiagram e (transportDiagram e source) = source := by
  obtain ⟨positions?, bonds, atomConfigurations⟩ := source
  apply organicDiagramSource_ext
  · cases positions? with
    | none => rfl
    | some positions =>
        simp only [transportDiagram, untransportDiagram, transportPositions2?,
          untransportPositions2?]
        congr 1
        funext atom
        simp
  · simp only [transportDiagram, untransportDiagram]
    rw [List.map_map]
    trans bonds.map id
    · apply List.map_congr_left
      rintro ⟨source, target, style, scope⟩ _
      simp [transportDiagramBond, untransportDiagramBond]
    · exact List.map_id bonds
  · simp only [transportDiagram, untransportDiagram]
    rw [List.map_map]
    trans atomConfigurations.map id
    · apply List.map_congr_left
      rintro ⟨atom, parity, scope⟩ _
      simp [transportDiagramAtom, untransportDiagramAtom]
    · exact List.map_id atomConfigurations

theorem transportDiagram_untransportDiagram (e : V ≃ W)
    (source : OrganicDiagramSource W) :
    transportDiagram e (untransportDiagram e source) = source := by
  obtain ⟨positions?, bonds, atomConfigurations⟩ := source
  apply organicDiagramSource_ext
  · cases positions? with
    | none => rfl
    | some positions =>
        simp only [transportDiagram, untransportDiagram, transportPositions2?,
          untransportPositions2?]
        congr 1
        funext atom
        simp
  · simp only [transportDiagram, untransportDiagram]
    rw [List.map_map]
    trans bonds.map id
    · apply List.map_congr_left
      rintro ⟨source, target, style, scope⟩ _
      simp [transportDiagramBond, untransportDiagramBond]
    · exact List.map_id bonds
  · simp only [transportDiagram, untransportDiagram]
    rw [List.map_map]
    trans atomConfigurations.map id
    · apply List.map_congr_left
      rintro ⟨atom, parity, scope⟩ _
      simp [transportDiagramAtom, untransportDiagramAtom]
    · exact List.map_id atomConfigurations

theorem untransportDiagram?_transportDiagram? (e : V ≃ W)
    (source? : Option (OrganicDiagramSource V)) :
    (source?.map (transportDiagram e)).map (untransportDiagram e) = source? := by
  cases source? with
  | none => rfl
  | some source => simp [untransportDiagram_transportDiagram e source]

theorem transportDiagram?_untransportDiagram? (e : V ≃ W)
    (source? : Option (OrganicDiagramSource W)) :
    (source?.map (untransportDiagram e)).map (transportDiagram e) = source? := by
  cases source? with
  | none => rfl
  | some source => simp [transportDiagram_untransportDiagram e source]

/-- The existing position encoder commutes with transport at the corresponding enumeration. -/
theorem encodePositions?_transportPositions? (e : V ≃ W) [Fintype V] [Fintype W]
    (enumeration : V ≃ Fin (Fintype.card V))
    (positions? : Option (V → CartesianPoint2)) :
    OrganicDiagramSource.encodePositions? (transportEnumeration e enumeration)
        (transportPositions2? e positions?) =
      OrganicDiagramSource.encodePositions? enumeration positions? := by
  cases positions? with
  | none => rfl
  | some positions =>
      simp only [transportPositions2?_some, OrganicDiagramSource.encodePositions?_some]
      congr 1
      rw [List.ofFn_congr (Fintype.card_congr e)
        (fun index : Fin (Fintype.card V) => positions (enumeration.symm index))]
      rw [List.ofFn_inj]
      funext index
      rw [e_symm_transportEnumeration_symm]

/-- A transported bond encodes to exactly the same `Nat` bond at the corresponding enumeration. -/
theorem encodeBond_transportDiagramBond (e : V ≃ W) [Fintype V] [Fintype W]
    (enumeration : V ≃ Fin (Fintype.card V)) (bond : SourceDiagramBond V) :
    OrganicDiagramSource.encodeBond (transportEnumeration e enumeration)
        (transportDiagramBond e bond) =
      OrganicDiagramSource.encodeBond enumeration bond := by
  obtain ⟨source, target, style, scope⟩ := bond
  simp [OrganicDiagramSource.encodeBond, transportDiagramBond]

/-- A transported atom annotation encodes to exactly the same `Nat` annotation. -/
theorem encodeAtomConfiguration_transportDiagramAtom (e : V ≃ W) [Fintype V] [Fintype W]
    (enumeration : V ≃ Fin (Fintype.card V)) (atom : SourceDiagramAtom V) :
    OrganicDiagramSource.encodeAtomConfiguration (transportEnumeration e enumeration)
        (transportDiagramAtom e atom) =
      OrganicDiagramSource.encodeAtomConfiguration enumeration atom := by
  obtain ⟨atom, parity, scope⟩ := atom
  simp [OrganicDiagramSource.encodeAtomConfiguration, transportDiagramAtom]

/-- Extensionality for the encoded drawing configuration. -/
theorem diagramConfiguration_ext {first second : DiagramConfiguration}
    (atomPositions : first.atomPositions? = second.atomPositions?)
    (bonds : first.bonds = second.bonds)
    (atomConfigurations : first.atomConfigurations = second.atomConfigurations) :
    first = second := by
  cases first
  cases second
  simp_all

/-- The existing drawing encoder commutes with transport of the drawing channel at the
corresponding enumeration. -/
theorem encodeDiagram_transportDiagram (e : V ≃ W) [Fintype V] [Fintype W]
    (enumeration : V ≃ Fin (Fintype.card V)) (source : OrganicDiagramSource V) :
    OrganicDiagramSource.encodeDiagram (transportEnumeration e enumeration)
        (transportDiagram e source) =
      OrganicDiagramSource.encodeDiagram enumeration source := by
  obtain ⟨positions?, bonds, atomConfigurations⟩ := source
  apply diagramConfiguration_ext
  · exact encodePositions?_transportPositions? e enumeration positions?
  · simp only [transportDiagram, OrganicDiagramSource.encodeDiagram]
    rw [List.map_map]
    apply List.map_congr_left
    intro bond _
    exact encodeBond_transportDiagramBond e enumeration bond
  · simp only [transportDiagram, OrganicDiagramSource.encodeDiagram]
    rw [List.map_map]
    apply List.map_congr_left
    intro atom _
    exact encodeAtomConfiguration_transportDiagramAtom e enumeration atom

end Channels

/-! ## Whole-satellite transport -/

section Satellites

variable [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W]

/-- Transport a whole physical-frame satellite by one equivalence.  The shared graph uses the
existing `relabelGraph`; both optional evidence channels move fieldwise; the ordered frame list is
mapped in order and multiplicity.  Nothing from the original satellite is stored. -/
def transportSatellite (e : V ≃ W) (satellite : PhysicalFrameSatellite V) :
    PhysicalFrameSatellite W where
  graph := relabelGraph e satellite.graph
  spatial? := transportSpatial? e satellite.spatial?
  diagram? := satellite.diagram?.map (transportDiagram e)
  frames := satellite.frames.map (transportFrame e)

/-- Decode a whole physical-frame satellite using the inverse equivalence. -/
def untransportSatellite (e : V ≃ W) (satellite : PhysicalFrameSatellite W) :
    PhysicalFrameSatellite V where
  graph := relabelGraph e.symm satellite.graph
  spatial? := untransportSpatial? e satellite.spatial?
  diagram? := satellite.diagram?.map (untransportDiagram e)
  frames := satellite.frames.map (untransportFrame e)

@[simp] theorem transportSatellite_graph (e : V ≃ W)
    (satellite : PhysicalFrameSatellite V) :
    (transportSatellite e satellite).graph = relabelGraph e satellite.graph := rfl

@[simp] theorem transportSatellite_spatial? (e : V ≃ W)
    (satellite : PhysicalFrameSatellite V) :
    (transportSatellite e satellite).spatial? =
      transportSpatial? e satellite.spatial? := rfl

@[simp] theorem transportSatellite_diagram? (e : V ≃ W)
    (satellite : PhysicalFrameSatellite V) :
    (transportSatellite e satellite).diagram? =
      satellite.diagram?.map (transportDiagram e) := rfl

@[simp] theorem transportSatellite_frames (e : V ≃ W)
    (satellite : PhysicalFrameSatellite V) :
    (transportSatellite e satellite).frames =
      satellite.frames.map (transportFrame e) := rfl

@[simp] theorem untransportSatellite_graph (e : V ≃ W)
    (satellite : PhysicalFrameSatellite W) :
    (untransportSatellite e satellite).graph = relabelGraph e.symm satellite.graph := rfl

@[simp] theorem untransportSatellite_spatial? (e : V ≃ W)
    (satellite : PhysicalFrameSatellite W) :
    (untransportSatellite e satellite).spatial? =
      untransportSpatial? e satellite.spatial? := rfl

@[simp] theorem untransportSatellite_diagram? (e : V ≃ W)
    (satellite : PhysicalFrameSatellite W) :
    (untransportSatellite e satellite).diagram? =
      satellite.diagram?.map (untransportDiagram e) := rfl

@[simp] theorem untransportSatellite_frames (e : V ≃ W)
    (satellite : PhysicalFrameSatellite W) :
    (untransportSatellite e satellite).frames =
      satellite.frames.map (untransportFrame e) := rfl

/-- Extensionality for the physical-frame satellite. -/
theorem physicalFrameSatellite_ext {first second : PhysicalFrameSatellite V}
    (graph : first.graph = second.graph)
    (spatial : first.spatial? = second.spatial?)
    (diagram : first.diagram? = second.diagram?)
    (frames : first.frames = second.frames) : first = second := by
  cases first
  cases second
  simp_all

/-- Full-record inverse: decoding a transported satellite recovers the original satellite. -/
theorem untransportSatellite_transportSatellite (e : V ≃ W)
    (satellite : PhysicalFrameSatellite V) :
    untransportSatellite e (transportSatellite e satellite) = satellite := by
  obtain ⟨graph, spatial?, diagram?, frames⟩ := satellite
  apply physicalFrameSatellite_ext
  · exact relabelGraph_symm e graph
  · exact untransportSpatial?_transportSpatial? e spatial?
  · exact untransportDiagram?_transportDiagram? e diagram?
  · simp only [transportSatellite, untransportSatellite]
    rw [List.map_map]
    trans frames.map id
    · apply List.map_congr_left
      intro frame _
      exact untransportFrame_transportFrame e frame
    · exact List.map_id frames

/-- Full-record inverse: re-transporting a decoded satellite recovers the original satellite. -/
theorem transportSatellite_untransportSatellite (e : V ≃ W)
    (satellite : PhysicalFrameSatellite W) :
    transportSatellite e (untransportSatellite e satellite) = satellite := by
  obtain ⟨graph, spatial?, diagram?, frames⟩ := satellite
  apply physicalFrameSatellite_ext
  · simpa using relabelGraph_symm e.symm graph
  · exact transportSpatial?_untransportSpatial? e spatial?
  · exact transportDiagram?_untransportDiagram? e diagram?
  · simp only [transportSatellite, untransportSatellite]
    rw [List.map_map]
    trans frames.map id
    · apply List.map_congr_left
      intro frame _
      exact transportFrame_untransportFrame e frame
    · exact List.map_id frames

/-- Satellite transport is injective. -/
theorem transportSatellite_injective (e : V ≃ W) :
    Function.Injective (transportSatellite e) := by
  intro first second equal
  calc
    first = untransportSatellite e (transportSatellite e first) :=
      (untransportSatellite_transportSatellite e first).symm
    _ = untransportSatellite e (transportSatellite e second) := by rw [equal]
    _ = second := untransportSatellite_transportSatellite e second

/-- Satellite transport is bijective. -/
theorem transportSatellite_bijective (e : V ≃ W) :
    Function.Bijective (transportSatellite e) :=
  ⟨transportSatellite_injective e, fun target =>
    ⟨untransportSatellite e target, transportSatellite_untransportSatellite e target⟩⟩

/-- An arbitrary set of satellites is recovered exactly by transporting and undoing. -/
theorem untransportSatellite_image_transportSatelliteSet (e : V ≃ W)
    (satellites : Set (PhysicalFrameSatellite V)) :
    untransportSatellite e '' (transportSatellite e '' satellites) = satellites := by
  rw [Set.image_image]
  have composed :
      (fun satellite : PhysicalFrameSatellite V =>
        untransportSatellite e (transportSatellite e satellite)) = id := by
    funext satellite
    exact untransportSatellite_transportSatellite e satellite
  change (fun satellite : PhysicalFrameSatellite V =>
      untransportSatellite e (transportSatellite e satellite)) '' satellites = satellites
  rw [composed, Set.image_id]

/-- An arbitrary finite set of satellites is recovered exactly.  The two `DecidableEq` instances
are exactly those required by the `Finset.image` API; no equality decision on functions is
constructed here. -/
theorem untransportSatellite_image_finset (e : V ≃ W)
    [DecidableEq (PhysicalFrameSatellite V)] [DecidableEq (PhysicalFrameSatellite W)]
    (satellites : Finset (PhysicalFrameSatellite V)) :
    (satellites.image (transportSatellite e)).image (untransportSatellite e) = satellites := by
  rw [Finset.image_image]
  have composed :
      (fun satellite : PhysicalFrameSatellite V =>
        untransportSatellite e (transportSatellite e satellite)) = id := by
    funext satellite
    exact untransportSatellite_transportSatellite e satellite
  change satellites.image
    (fun satellite : PhysicalFrameSatellite V =>
      untransportSatellite e (transportSatellite e satellite)) = satellites
  rw [composed, Finset.image_id]

end Satellites

/-! ## Compatibility with the actual P-93 decoder

The decoder `decodeFrame` is reused unchanged.  Transporting a native payload and then decoding at
the corresponding enumeration gives exactly the same `Nat`-indexed source frame.  In particular the
reconstructed polyhedral `centerPoint` (an indexed coordinate lookup at the centre atom) and the
ordered `positionPoints` (indexed lookups at the ordered ligand list) commute with transport. -/

section Decoder

variable [DecidableEq V] [DecidableEq W] [Fintype V] [Fintype W]

/-- Exact coordinate lookup commutes with transport at the corresponding enumeration. -/
theorem coordinateAt_transport (e : V ≃ W) (enumeration : V ≃ Fin (Fintype.card V))
    (spatial : SpatialConfiguration) (atom : V) :
    coordinateAt spatial (encodeAtom (transportEnumeration e enumeration) (e atom)) =
      coordinateAt spatial (encodeAtom enumeration atom) := by
  rw [encodeAtom_transportEnumeration]

/-- Exact ordered coordinate lookup commutes with transport at the corresponding enumeration. -/
theorem coordinateList_transport (e : V ≃ W) (enumeration : V ≃ Fin (Fintype.card V))
    (spatial : SpatialConfiguration) (atoms : List V) :
    coordinateList spatial
        (unrelabelList (transportEnumeration e enumeration) (atoms.map e)) =
      coordinateList spatial (unrelabelList enumeration atoms) := by
  rw [unrelabelList_map]

theorem decodeHelix_transportHelix (e : V ≃ W) (enumeration : V ≃ Fin (Fintype.card V))
    (native : NativeHelixFrame V) :
    decodeHelix (transportEnumeration e enumeration) (transportHelix e native) =
      decodeHelix enumeration native := by
  obtain ⟨helixPath, frontReference, backReference, sense, descriptor⟩ := native
  simp [decodeHelix, transportHelix]

theorem decodePlane_transportPlane (e : V ≃ W) (enumeration : V ≃ Fin (Fintype.card V))
    (native : NativePlanarFrame V) :
    decodePlane (transportEnumeration e enumeration) (transportPlane e native) =
      decodePlane enumeration native := by
  obtain ⟨planeAtoms, pilotAtom, firstReference, secondReference, inPlaneBondAtom,
    outOfPlaneAtom, torsionRestricted, planeCannotBeSymmetryPlane⟩ := native
  simp [decodePlane, transportPlane]

theorem decodePolyhedralObservation_transportPolyhedral (e : V ≃ W)
    (enumeration : V ≃ Fin (Fintype.card V)) (native : NativePolyhedralFrame V) :
    decodePolyhedralObservation (transportEnumeration e enumeration)
        (transportPolyhedral e native) =
      decodePolyhedralObservation enumeration native := by
  obtain ⟨center, geometry, recognition, ligands, configurationPositions,
    absoluteOrientation, priming⟩ := native
  simp [decodePolyhedralObservation, transportPolyhedral]

/-- **Reconstructed polyhedral frame commutes with transport.**  The centre point and the ordered
position points are recovered from the same shared coordinate configuration, at the same raw
indices, so the reconstructed polyhedral frame is exactly the original one. -/
theorem decodePolyhedral_transportPolyhedral (e : V ≃ W)
    (enumeration : V ≃ Fin (Fintype.card V)) (spatial : SpatialConfiguration)
    (native : NativePolyhedralFrame V) :
    decodePolyhedral (transportEnumeration e enumeration) spatial
        (transportPolyhedral e native) =
      decodePolyhedral enumeration spatial native := by
  obtain ⟨center, geometry, recognition, ligands, configurationPositions,
    absoluteOrientation, priming⟩ := native
  simp [decodePolyhedral, decodePolyhedralObservation, transportPolyhedral,
    coordinateAt_transport, coordinateList_transport]

/-- The reconstructed polyhedral `centerPoint` commutes with transport. -/
theorem decodePolyhedral_centerPoint_transport (e : V ≃ W)
    (enumeration : V ≃ Fin (Fintype.card V)) (spatial : SpatialConfiguration)
    (native : NativePolyhedralFrame V) :
    (decodePolyhedral (transportEnumeration e enumeration) spatial
        (transportPolyhedral e native)).centerPoint =
      (decodePolyhedral enumeration spatial native).centerPoint := by
  rw [decodePolyhedral_transportPolyhedral]

/-- The reconstructed ordered polyhedral `positionPoints` commute with transport. -/
theorem decodePolyhedral_positionPoints_transport (e : V ≃ W)
    (enumeration : V ≃ Fin (Fintype.card V)) (spatial : SpatialConfiguration)
    (native : NativePolyhedralFrame V) :
    (decodePolyhedral (transportEnumeration e enumeration) spatial
        (transportPolyhedral e native)).positionPoints =
      (decodePolyhedral enumeration spatial native).positionPoints := by
  rw [decodePolyhedral_transportPolyhedral]

/-- The reconstructed polyhedral observation record commutes with transport. -/
theorem decodePolyhedral_record_transport (e : V ≃ W)
    (enumeration : V ≃ Fin (Fintype.card V)) (native : NativePolyhedralFrame V) :
    (decodePolyhedralObservation (transportEnumeration e enumeration)
        (transportPolyhedral e native)) =
      (decodePolyhedralObservation enumeration native) :=
  decodePolyhedralObservation_transportPolyhedral e enumeration native

/-- **The actual P-93 decoder commutes with native transport.**  Transporting any native payload
and decoding it at the corresponding enumeration yields exactly the same `Nat`-indexed
`SourcePhysicalFrame`.  No bounds, source validity or original payload are used. -/
@[simp] theorem decodeFrame_transportFrame (e : V ≃ W)
    (enumeration : V ≃ Fin (Fintype.card V)) (spatial : SpatialConfiguration)
    (native : PhysicalFrame V) :
    decodeFrame (transportEnumeration e enumeration) spatial (transportFrame e native) =
      decodeFrame enumeration spatial native := by
  cases native with
  | helix native =>
      simp [transportFrame, decodeFrame, decodeHelix_transportHelix]
  | plane native =>
      simp [transportFrame, decodeFrame, decodePlane_transportPlane]
  | polyhedral native =>
      simp [transportFrame, decodeFrame, decodePolyhedral_transportPolyhedral,
        unrelabelList_map]

end Decoder

/-! ## The recovered physical source is invariant

The shared finite source of a satellite is encoded with the existing source encoder.  At the
corresponding enumeration the encoded `AuthoritativeChemicalInput` and the ordered decoded frame
list are both invariant, so `suppliedSource` returns exactly the same physical source. -/

section SourceInvariance

variable [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W]

/-- Extensionality for `SemanticMolecule`. -/
theorem semanticMolecule_ext {first second : SemanticMolecule}
    (atoms : first.atoms = second.atoms)
    (interactions : first.interactions = second.interactions) : first = second := by
  cases first
  cases second
  simp_all

/-- Encoding one relabelled hyperedge at the corresponding enumeration is exactly encoding the
source hyperedge at the original enumeration. -/
theorem encodeInteraction_relabelInteractionEdge (e : V ≃ W)
    (enumeration : V ≃ Fin (Fintype.card V))
    (edge : List V × SemanticInteractionKind) :
    FiniteAtomInteractionHypergraph.encodeInteraction
        (transportEnumeration e enumeration) (relabelInteractionEdge e edge) =
      FiniteAtomInteractionHypergraph.encodeInteraction enumeration edge := by
  obtain ⟨participants, kind⟩ := edge
  have hmap :
      (participants.map e).map
          (fun atom => (transportEnumeration e enumeration atom).val) =
        participants.map (fun atom => (enumeration atom).val) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro atom _
    exact transportEnumeration_apply_val e enumeration atom
  simp [FiniteAtomInteractionHypergraph.encodeInteraction, relabelInteractionEdge, hmap]

/-- The graph channel encodes identically after relabelling at the corresponding enumeration. -/
theorem encode_relabelGraph_transportEnumeration (e : V ≃ W)
    (enumeration : V ≃ Fin (Fintype.card V))
    (graph : FiniteAtomInteractionHypergraph V) :
    (relabelGraph e graph).encode (transportEnumeration e enumeration) =
      graph.encode enumeration := by
  have hcard : Fintype.card V = Fintype.card W := Fintype.card_congr e
  apply semanticMolecule_ext
  · unfold FiniteAtomInteractionHypergraph.encode
    simp only [relabelGraph]
    rw [List.ofFn_congr hcard
      (fun index : Fin (Fintype.card V) => graph.atomData (enumeration.symm index))]
    rw [List.ofFn_inj]
    funext index
    rw [e_symm_transportEnumeration_symm]
  · unfold FiniteAtomInteractionHypergraph.encode
    simp only [relabelGraph, List.map_map]
    apply List.map_congr_left
    intro edge _
    exact encodeInteraction_relabelInteractionEdge e enumeration edge

/-- The shared finite source (graph plus both optional evidence channels) encodes identically
after satellite transport at the corresponding enumeration. -/
theorem encode_toFiniteSource_transportSatellite (e : V ≃ W)
    (enumeration : V ≃ Fin (Fintype.card V))
    (satellite : PhysicalFrameSatellite V) :
    (transportSatellite e satellite).toFiniteSource.encode
        (transportEnumeration e enumeration) =
      satellite.toFiniteSource.encode enumeration := by
  apply authoritativeInput_ext
  · simpa [PhysicalFrameSatellite.toFiniteSource, transportSatellite] using
      encode_relabelGraph_transportEnumeration e enumeration satellite.graph
  · simpa [PhysicalFrameSatellite.toFiniteSource, transportSatellite] using
      encodeSpatial?_transportSpatial? e enumeration satellite.spatial?
  · cases hd : satellite.diagram? with
    | none => simp [PhysicalFrameSatellite.toFiniteSource, transportSatellite, hd]
    | some source =>
        simp [PhysicalFrameSatellite.toFiniteSource, transportSatellite, hd,
          encodeDiagram_transportDiagram e enumeration source]

/-- The shared spatial configuration of a satellite is invariant under transport at the
corresponding enumeration. -/
theorem sharedSpatial?_transportSatellite (e : V ≃ W)
    (enumeration : V ≃ Fin (Fintype.card V))
    (satellite : PhysicalFrameSatellite V) :
    (transportSatellite e satellite).sharedSpatial?
        (transportEnumeration e enumeration) =
      satellite.sharedSpatial? enumeration := by
  unfold PhysicalFrameSatellite.sharedSpatial?
  exact encodeSpatial?_transportSpatial? e enumeration satellite.spatial?

/-- The total spatial configuration handed to the decoder is invariant under transport. -/
theorem spatialConfiguration_transportSatellite (e : V ≃ W)
    (enumeration : V ≃ Fin (Fintype.card V))
    (satellite : PhysicalFrameSatellite V) :
    (transportSatellite e satellite).spatialConfiguration
        (transportEnumeration e enumeration) =
      satellite.spatialConfiguration enumeration := by
  unfold PhysicalFrameSatellite.spatialConfiguration
  rw [sharedSpatial?_transportSatellite]

/-- **Whole-source invariance.**  At the corresponding enumeration, transporting a satellite and
recovering its source returns exactly the same `AuthoritativeChemicalInput` and the exact same
ordered `SourcePhysicalFrame` list as recovering the original satellite.  The physical source is
not renumbered, re-normalised or otherwise altered by the representation change. -/
theorem suppliedSource_transportSatellite (e : V ≃ W)
    (enumeration : V ≃ Fin (Fintype.card V))
    (satellite : PhysicalFrameSatellite V) :
    OrganicStereoP93PhysicalFrameIngress.suppliedSource
        (transportEnumeration e enumeration) (transportSatellite e satellite) =
      OrganicStereoP93PhysicalFrameIngress.suppliedSource enumeration satellite := by
  apply RecoveredPhysicalFrameSource.ext
  · exact encode_toFiniteSource_transportSatellite e enumeration satellite
  · simp only [OrganicStereoP93PhysicalFrameIngress.suppliedSource]
    rw [spatialConfiguration_transportSatellite]
    rw [show (transportSatellite e satellite).frames =
        satellite.frames.map (transportFrame e) from rfl]
    rw [List.map_map]
    apply List.map_congr_left
    intro native _
    exact decodeFrame_transportFrame e enumeration
      (satellite.spatialConfiguration enumeration) native

/-- Concrete source recovery through transport: adapting a raw source, transporting the satellite
along an equivalence and decoding at the corresponding enumeration returns the original
authoritative input and the original ordered frame list. -/
theorem suppliedSource_transportSatellite_adapt (e : V ≃ W)
    (raw : RawPhysicalFrameSource V) :
    OrganicStereoP93PhysicalFrameIngress.suppliedSource
        (transportEnumeration e raw.binding.enumeration)
        (transportSatellite e (adapt raw)) =
      { source := raw.binding.source, frames := raw.frames } := by
  rw [suppliedSource_transportSatellite,
    OrganicStereoP93PhysicalFrameIngress.suppliedSource_adapt]

/-- The same invariance stated for the ordered frame list alone. -/
theorem suppliedSource_frames_transportSatellite (e : V ≃ W)
    (enumeration : V ≃ Fin (Fintype.card V))
    (satellite : PhysicalFrameSatellite V) :
    (OrganicStereoP93PhysicalFrameIngress.suppliedSource
        (transportEnumeration e enumeration)
        (transportSatellite e satellite)).frames =
      (OrganicStereoP93PhysicalFrameIngress.suppliedSource enumeration satellite).frames := by
  rw [suppliedSource_transportSatellite]

/-- The same invariance stated for the recovered authoritative input alone. -/
theorem suppliedSource_source_transportSatellite (e : V ≃ W)
    (enumeration : V ≃ Fin (Fintype.card V))
    (satellite : PhysicalFrameSatellite V) :
    (OrganicStereoP93PhysicalFrameIngress.suppliedSource
        (transportEnumeration e enumeration)
        (transportSatellite e satellite)).source =
      (OrganicStereoP93PhysicalFrameIngress.suppliedSource enumeration satellite).source := by
  rw [suppliedSource_transportSatellite]

end SourceInvariance

end OrganicStereoP93PhysicalFrameTransport

end TetraStereo.OneCenter
