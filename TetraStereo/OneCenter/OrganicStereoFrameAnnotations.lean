import TetraStereo.OneCenter.StereochemicalElements
import TetraStereo.OneCenter.AuthoritativeChemicalInput
import TetraStereo.OneCenter.GeometryAnnotatedCIPAnalysis
import TetraStereo.OneCenter.CIPObservedPlanarSpatialConformance
import TetraStereo.OneCenter.P94CoordinateRingGeometry
import TetraStereo.OneCenter.OrganicStereoIndependentElectronicEncoding
import TetraStereo.OneCenter.OrganicStereoPhysicalPlaneEvidence
import TetraStereo.OneCenter.OrganicStereoAxialFrameEncoding

set_option autoImplicit false

namespace TetraStereo.OneCenter

open OrganicStereoAxialFrameEncoding
open BlueBookP94
open OrganicStereoElectronicSites
open OrganicStereoIndependentElectronicEncoding

/-!
# Independent finite atom-reference frame annotations

A molecular geometry observation does not by itself retain the ordered atom references, pilot
atoms, reference atoms, torsion participants or helix/ring traversals that the caller used to
*describe* the unit.  Two callers can therefore supply the same unordered support while meaning
different ordered frames.  This module provides one small, concrete annotation channel for
exactly that retained source data.

The channel is **source annotation retention**, not a classifier and not a physical realization
proof:

* no field is a desired `R/S`, `P/M`, `E/Z` or polyhedral descriptor, and no ranking is derived
  from the stored high/low labels;
* `AxialReferenceRoles.suppliedHighLow` records only that the caller supplied high/low labels.
  `orderedIncidencePair` records only the order in which endpoint incidences were listed;
* atom references are carried as an ordered `List`, never as an unordered `Finset`;
* P-94 torsion participants retain their actual `atom` / `lonePair` / `duplicateAtom` identity,
  the selected axis is an ordered path, and the supplied torsion angle (when present) is copied
  literally;
* polyhedral `configurationPositions` are geometry *positions*, not atom identifiers, and an
  oriented exact plane is carried as plane metadata; neither is relabelled as an atom.

The public sum `FrameAnnotation V` covers one-center annotations, axial units, planar units,
helical units, alkene units, polyhedral frames, P-94 torsion reference frames and ordered ring
traversals.  For the four `StereochemicalElements` families the structure fields coincide with
the existing unit records; the richer planar/helical/polyhedral shapes follow the indexed
observation records used by `GeometryAnnotatedCIPAnalysis` and
`CIPObservedPlanarSpatialConformance`.

Every atom reference is transported by one common equivalence `V ≃ W`, and
`relabelFrameAnnotation_symm` proves exact inverse recovery.  The adapters from `Nat`-indexed
observations require explicit bounds against a real source atom count; an out-of-range index
cannot be converted, so no invalid atom is fabricated.  The source-level axial adapter takes the
existing `SourceIndexedAxialFrame.Bounded` evidence, and the P-94 adapter takes the existing
`P94ConformationUnit.ParticipantBounded` evidence.
-/

/-! ## Reference-role conventions -/

/-- How the caller supplied the four ordered axial reference slots.

`suppliedHighLow` records that the caller's labels were supplied as high/low annotations.
`orderedIncidencePair` records only the order of the listed endpoint incidences.  Neither
constructor asserts a CIP priority or a derived ranking. -/
inductive AxialReferenceRoles where
  | suppliedHighLow
  | orderedIncidencePair
  deriving DecidableEq, Repr

/-- How the caller supplied the planar reference slots.

`suppliedHighLow` records the existing `PlanarUnit` high/low labels.  `orderedReferencePair`
records only an ordered pair of reference atoms, as in the indexed planar observation.  Neither
constructor asserts a CIP priority or a derived ranking. -/
inductive PlaneReferenceRoles where
  | suppliedHighLow
  | orderedReferencePair
  deriving DecidableEq, Repr

/-! ## Concrete frame records -/

/-- Ordered one-center frame: the central atom and the caller's ordered ligand list.  The list is
retained verbatim, including repetitions; no distinctness, arity or priority claim is built in. -/
structure CenterFrame (V : Type*) where
  center : V
  ligandOrder : List V
  deriving DecidableEq, Repr

/-- Ordered axial frame.  The four reference slots preserve the caller's order exactly.  The
optional `sense?` is a supplied annotation, not a computed descriptor. -/
structure AxialFrame (V : Type*) where
  axisStart : V
  axisEnd : V
  startFirst : V
  startSecond : V
  endFirst : V
  endSecond : V
  roles : AxialReferenceRoles := .orderedIncidencePair
  sense? : Option StereoSense := none
  deriving DecidableEq, Repr

/-- Ordered planar frame.  `planeAtoms` is the caller's traversal, not an unordered member set.
The pilot and reference roles are distinct fields.  The richer indexed planar-derived-tetrahedron
observation is represented by the optional `inPlaneBondAtom?`, `outOfPlaneAtom?` and applicability
fields; an oriented exact plane, when the caller supplied one, is retained in `exactPlane?`.
All of these are copied literally and no side or descriptor is derived. -/
structure PlanarFrame (V : Type*) where
  planeAtoms : List V
  pilotAtom : V
  firstReference : V
  secondReference : V
  inPlaneBondAtom? : Option V := none
  outOfPlaneAtom? : Option V := none
  torsionRestricted? : Option Bool := none
  planeCannotBeSymmetryPlane? : Option Bool := none
  exactPlane? : Option BlueBookP94.CoordinateRing.ExactPlane := none
  roles : PlaneReferenceRoles := .orderedReferencePair
  sense? : Option StereoSense := none
  deriving DecidableEq, Repr

/-- Ordered helical frame.  `helixPath` is the caller's ordered path; `sense?` is only a supplied
annotation. -/
structure HelicalFrame (V : Type*) where
  helixPath : List V
  frontReference : V
  backReference : V
  sense? : Option StereoSense := none
  deriving DecidableEq, Repr

/-- Polyhedral geometry and position-role metadata.  `configurationPositions` chooses geometry
positions (the `Nat`s routed by `ConfigurationPositionObservation.positionsFor?`); those `Nat`s are
**not** atom identifiers and must not be relabelled as atoms.  `geometry`, `recognition`,
`absoluteOrientation` and `priming` are likewise supplied, qualitative observations. -/
structure PolyhedralGeometryMetadata where
  geometry : PolyhedralGeometry
  recognition : RedBookIR9.GeometryRecognitionObservation
  configurationPositions : RedBookIR9.ConfigurationPositionObservation
  absoluteOrientation : RedBookIR9.AbsoluteOrientationObservation
  priming : IndexedPolyhedralPrimingObservation := .repeatedPolydentateLigands
  deriving DecidableEq, Repr

/-- Ordered polyhedral frame: the center and the ordered ligand references are atom identifiers;
all geometry and position-role data lives in `metadata` and is not atom-labelled. -/
structure PolyhedralFrame (V : Type*) where
  center : V
  ligandOrder : List V
  metadata : PolyhedralGeometryMetadata
  deriving DecidableEq, Repr

/-- An explicitly selected individual electronic or CIP-reference site over independent atom
labels.  `inventory` is the supplied per-owner multiplicity record; `slot` is a genuine `Nat` slot
with a proof that it is below the supplied count at `owner` and `kind`.  Thus two lone pairs at
one owner with different slots are different references.  No slot is derived from geometry, and
an unslotted legacy participant is never assigned a default slot. -/
structure SelectedElectronicSite (V : Type*) where
  inventory : IndependentSiteCounts V
  owner : V
  kind : SiteKind
  slot : Nat
  slotBound : slot < (inventory.counts owner).count kind

namespace SelectedElectronicSite

variable {V : Type*}

/-- The slot is a real slot of the supplied inventory at the selected owner and kind. -/
theorem slot_isLt (site : SelectedElectronicSite V) :
    site.slot < (site.inventory.counts site.owner).count site.kind :=
  site.slotBound

/-- Extensionality for selected sites.  It is stated explicitly because the final `slotBound`
field is proof-dependent: equal owner, kind, slot and inventory force the whole site to be equal.
The numeric slot is compared here, not weakened to owner/kind. -/
theorem ext_of_fields {first second : SelectedElectronicSite V}
    (inventory : first.inventory = second.inventory)
    (owner : first.owner = second.owner)
    (kind : first.kind = second.kind)
    (slot : first.slot = second.slot) : first = second := by
  obtain ⟨firstInventory, firstOwner, firstKind, firstSlot, firstBound⟩ := first
  obtain ⟨secondInventory, secondOwner, secondKind, secondSlot, secondBound⟩ := second
  dsimp only at inventory owner kind slot
  cases inventory
  cases owner
  cases kind
  cases slot
  exact congrArg (SelectedElectronicSite.mk firstInventory firstOwner firstKind firstSlot)
    (Subsingleton.elim firstBound secondBound)

/-- Visible binding between a selected site and a supplied common inventory.  This is an explicit
predicate; it does not silently identify the stored inventory with any Domain field.  A joint
constructor must establish it when the same inventory is supplied to both sides. -/
def MatchesInventory (site : SelectedElectronicSite V)
    (inventory : IndependentSiteCounts V) : Prop :=
  site.inventory = inventory

/-- The legacy owner projected from one torsion participant: the ordinary atom, the owner of a
lone pair, or the original atom of a virtual duplicate. -/
def participantOwner : TorsionParticipant V → V
  | .atom atom => atom
  | .lonePair center => center
  | .duplicateAtom original => original

/-- The site kind forced by a legacy participant, when the participant is a site-like reference.
An ordinary `.atom` participant forces no electronic kind. -/
def participantSiteKind? : TorsionParticipant V → Option SiteKind
  | .atom _ => none
  | .lonePair _ => some (.electronic .lonePair)
  | .duplicateAtom _ => some (.cipReference .virtualDuplicate)

/-- Compatibility between an explicitly selected site and a legacy participant.  The selected
owner must be the participant's owner, and when the legacy participant pins a site kind the
selected kind must be that kind.  This is what lets a caller choose either of two lone pairs at
one atom while remaining compatible with the legacy `lonePair` record. -/
def CompatibleWith (site : SelectedElectronicSite V) (participant : TorsionParticipant V) :
    Prop :=
  site.owner = participantOwner participant ∧
    ∀ kind, participantSiteKind? participant = some kind → site.kind = kind

/-- Compatibility with an ordinary atom only fixes the owner; it does not invent an electronic
kind. -/
@[simp] theorem compatibleWith_atom_iff (site : SelectedElectronicSite V) (atom : V) :
    site.CompatibleWith (.atom atom) ↔ site.owner = atom := by
  simp [CompatibleWith, participantOwner, participantSiteKind?]

/-- Compatibility with a lone-pair participant fixes both the owner and the lone-pair kind. -/
@[simp] theorem compatibleWith_lonePair_iff (site : SelectedElectronicSite V) (center : V) :
    site.CompatibleWith (.lonePair center) ↔
      site.owner = center ∧ site.kind = .electronic .lonePair := by
  simp [CompatibleWith, participantOwner, participantSiteKind?]

/-- Compatibility with a duplicate participant fixes both the original atom and the virtual
duplicate kind. -/
@[simp] theorem compatibleWith_duplicateAtom_iff (site : SelectedElectronicSite V)
    (original : V) :
    site.CompatibleWith (.duplicateAtom original) ↔
      site.owner = original ∧ site.kind = .cipReference .virtualDuplicate := by
  simp [CompatibleWith, participantOwner, participantSiteKind?]

end SelectedElectronicSite

/-- P-94 torsion reference frame.  `axisPath` is the selected oriented axis path `A-...-B`;
`front` and `rear` retain the actual participant identity (`atom`, `lonePair` phantom, or
`duplicateAtom` original) in their ordered roles.  `angle?` is the supplied torsion angle when
one was supplied.  The optional `frontSite?`/`rearSite?` carry explicitly selected counted site
identities; absent options mean the legacy participant alone was supplied, and no slot is
invented.  Nothing here derives a conformation descriptor. -/
structure TorsionReferenceFrame (V : Type*) where
  axisPath : List V
  front : TorsionParticipant V
  rear : TorsionParticipant V
  angle? : Option TorsionAngle := none
  frontSite? : Option (SelectedElectronicSite V) := none
  rearSite? : Option (SelectedElectronicSite V) := none

namespace TorsionReferenceFrame

variable {V : Type*}

/-- A frame is valid when every supplied site is compatible with the legacy participant in its
role.  Absent selections are valid and are not silently replaced by slots. -/
def Valid (frame : TorsionReferenceFrame V) : Prop :=
  (∀ site, frame.frontSite? = some site → site.CompatibleWith frame.front) ∧
    ∀ site, frame.rearSite? = some site → site.CompatibleWith frame.rear

end TorsionReferenceFrame

/-- Ordered ring traversal: exactly the caller's ordered ring-atom sequence.  It is a list, so
traversal order and multiplicity are retained; no cyclicity or closure proof is asserted here. -/
structure RingTraversalFrame (V : Type*) where
  ringAtoms : List V
  deriving DecidableEq, Repr

/-- One selected source substituent attachment retained inside a real ring-plane frame.

`ringPosition` is the actual selected ring atom reference (the ring atom to which the substituent
is attached), carried as the caller's atom label so it is transported by the same equivalence as
every other atom reference.  `interactionIndex` is the occurrence index of the actual source
interaction inside the common source molecule's interaction list; it is retained literally by
relabelling because atom labels do not index the common source graph.  The index is data: together
with the common source molecule it determines the interaction by an actual list lookup.  No
default index or fabricated occurrence is built in; a frame simply omits the whole attachment when
the source interaction was not supplied. -/
structure RealRingPlaneAttachment (V : Type*) where
  ringPosition : V
  interactionIndex : Nat
  deriving DecidableEq, Repr

/-- An actual supplied real ring-plane reference.  The field `plane` is the existing
`PhysicalPlaneEvidence.ReferencePlane`: a real origin together with an oriented nonzero real
normal, retained literally.  `ringAtoms` is the caller's ordered ring support and the two
substituent fields are ordered real atom references.  Physical coplanarity is deliberately not a
field: it remains the separate `CoplanarRingEvidence` object, so this annotation records the
chosen plane and support without asserting or deriving coplanarity from atom geometry.  No
rational approximation of the plane is introduced.

The two optional attachment references retain the *selected* `SourceRingSubstituentAttachment`
data that the ring support and the two substituent positions do not determine: the chosen ring
position of each attachment and the actual occurrence index of its source interaction.  They
default to `none`, so a legacy `PhysicalRingPlaneObservation` adapter and every existing record
literal keep their previous meaning.  Attachment presence is not a classification and the frame
still does not assert coplanarity or any descriptor. -/
structure RealRingPlaneFrame (V : Type*) where
  plane : PhysicalPlaneEvidence.ReferencePlane
  ringAtoms : List V
  firstSubstituent : V
  secondSubstituent : V
  /-- The selected source attachment of the first substituent, when one was supplied. -/
  firstAttachment? : Option (RealRingPlaneAttachment V) := none
  /-- The selected source attachment of the second substituent, when one was supplied. -/
  secondAttachment? : Option (RealRingPlaneAttachment V) := none

/-! ## The annotation channel -/

/-- One compact source frame annotation.  Each constructor retains the caller's ordered atom
references and reference roles.  The `alkene` constructor carries the existing `AlkeneUnit`
verbatim, including its supplied high/low labels; `polyhedral` keeps geometry positions separate
from atom identifiers; `torsionReference` keeps participant identity and the supplied angle. -/
inductive FrameAnnotation (V : Type*) where
  | center (frame : CenterFrame V)
  | axial (frame : AxialFrame V)
  | planar (frame : PlanarFrame V)
  | helical (frame : HelicalFrame V)
  | alkene (unit : AlkeneUnit V)
  | polyhedral (frame : PolyhedralFrame V)
  | torsionReference (frame : TorsionReferenceFrame V)
  | ringTraversal (frame : RingTraversalFrame V)
  | realRingPlane (frame : RealRingPlaneFrame V)

/-- The atom references retained by one torsion participant: an ordinary atom, the center owning a
lone-pair phantom, or the original atom of a multiple-bond duplicate.  The participant constructor
itself is retained in `TorsionReferenceFrame`; this projection only exposes the atom label. -/
def torsionParticipantRefs {V : Type*} : TorsionParticipant V → List V
  | .atom atom => [atom]
  | .lonePair center => [center]
  | .duplicateAtom original => [original]

namespace FrameAnnotation

variable {V : Type*}

/-- The ordered list of every atom reference retained by the annotation.  This is a list, not a
finite set: repeated references and their positions are meaningful.  For polyhedral annotations
this contains the center and the ordered ligand identifiers but never the geometry positions;
for torsion annotations it contains the axis path followed by the front and rear participant
references; for a real ring plane it contains the ring support, both substituents, and the
selected ring position of each supplied source attachment (the interaction occurrence index is
not an atom reference and is therefore not listed here). -/
def atomRefs : FrameAnnotation V → List V
  | .center frame => frame.center :: frame.ligandOrder
  | .axial frame =>
      [frame.axisStart, frame.axisEnd, frame.startFirst, frame.startSecond,
        frame.endFirst, frame.endSecond]
  | .planar frame =>
      frame.planeAtoms ++ [frame.pilotAtom, frame.firstReference, frame.secondReference] ++
        frame.inPlaneBondAtom?.toList ++ frame.outOfPlaneAtom?.toList
  | .helical frame => frame.helixPath ++ [frame.frontReference, frame.backReference]
  | .alkene unit =>
      [unit.leftAtom, unit.rightAtom, unit.leftHigh, unit.leftLow,
        unit.rightHigh, unit.rightLow]
  | .polyhedral frame => frame.center :: frame.ligandOrder
  | .torsionReference frame =>
      frame.axisPath ++ torsionParticipantRefs frame.front ++
        torsionParticipantRefs frame.rear ++
        (frame.frontSite?.map SelectedElectronicSite.owner).toList ++
        (frame.rearSite?.map SelectedElectronicSite.owner).toList
  | .ringTraversal frame => frame.ringAtoms
  | .realRingPlane frame =>
      frame.ringAtoms ++ [frame.firstSubstituent, frame.secondSubstituent] ++
        (frame.firstAttachment?.map RealRingPlaneAttachment.ringPosition).toList ++
        (frame.secondAttachment?.map RealRingPlaneAttachment.ringPosition).toList

/-- The ordered planar traversal, when this is a planar annotation; otherwise `none`. -/
def planeAtoms? : FrameAnnotation V → Option (List V)
  | .planar frame => some frame.planeAtoms
  | _ => none

/-- The ordered helix path, when this is a helical annotation; otherwise `none`. -/
def helixPath? : FrameAnnotation V → Option (List V)
  | .helical frame => some frame.helixPath
  | _ => none

/-- The ordered selected torsion axis path, when this is a torsion annotation. -/
def torsionAxisPath? : FrameAnnotation V → Option (List V)
  | .torsionReference frame => some frame.axisPath
  | _ => none

/-- The ordered ring traversal, when this is a ring-traversal or real-ring-plane annotation;
otherwise `none`. -/
def ringAtoms? : FrameAnnotation V → Option (List V)
  | .ringTraversal frame => some frame.ringAtoms
  | .realRingPlane frame => some frame.ringAtoms
  | _ => none

/-- The supplied real reference plane, when this is a real-ring-plane annotation; otherwise
`none`.  This is the actual real `ReferencePlane`, not a rational approximation. -/
def realPlane? : FrameAnnotation V →
    Option PhysicalPlaneEvidence.ReferencePlane
  | .realRingPlane frame => some frame.plane
  | _ => none

/-- The whole real ring-plane record, when this is a real-ring-plane annotation. -/
def realRingPlaneFrame? : FrameAnnotation V → Option (RealRingPlaneFrame V)
  | .realRingPlane frame => some frame
  | _ => none

/-- The first substituent reference of a real-ring-plane annotation. -/
def realRingPlaneFirstSubstituent? : FrameAnnotation V → Option V
  | .realRingPlane frame => some frame.firstSubstituent
  | _ => none

/-- The second substituent reference of a real-ring-plane annotation. -/
def realRingPlaneSecondSubstituent? : FrameAnnotation V → Option V
  | .realRingPlane frame => some frame.secondSubstituent
  | _ => none

/-- The selected source attachment of the first substituent, when supplied.  Absence means no
source attachment reference was supplied; no occurrence index is invented. -/
def realRingPlaneFirstAttachment? :
    FrameAnnotation V → Option (RealRingPlaneAttachment V)
  | .realRingPlane frame => frame.firstAttachment?
  | _ => none

/-- The selected source attachment of the second substituent, when supplied.  Absence means no
source attachment reference was supplied; no occurrence index is invented. -/
def realRingPlaneSecondAttachment? :
    FrameAnnotation V → Option (RealRingPlaneAttachment V)
  | .realRingPlane frame => frame.secondAttachment?
  | _ => none

/-- The polyhedral geometry/position-role metadata, when present. -/
def polyhedralMetadata? : FrameAnnotation V → Option PolyhedralGeometryMetadata
  | .polyhedral frame => some frame.metadata
  | _ => none

/-- The supplied polyhedral configuration-position observation, when present.  These are position
roles, not atom identifiers. -/
def positionRoleObservation? :
    FrameAnnotation V → Option RedBookIR9.ConfigurationPositionObservation
  | .polyhedral frame => some frame.metadata.configurationPositions
  | _ => none

/-- The supplied oriented exact plane, when present.  It is plane geometry, not an atom
reference. -/
def exactPlane? : FrameAnnotation V → Option BlueBookP94.CoordinateRing.ExactPlane
  | .planar frame => frame.exactPlane?
  | _ => none

/-- The supplied torsion angle, when present. -/
def torsionAngle? : FrameAnnotation V → Option TorsionAngle
  | .torsionReference frame => frame.angle?
  | _ => none

/-- The explicitly selected front site identity, when supplied.  Absence means the legacy
participant alone was supplied; no default slot is manufactured. -/
def frontSite? : FrameAnnotation V → Option (SelectedElectronicSite V)
  | .torsionReference frame => frame.frontSite?
  | _ => none

/-- The explicitly selected rear site identity, when supplied.  Absence means the legacy
participant alone was supplied; no default slot is manufactured. -/
def rearSite? : FrameAnnotation V → Option (SelectedElectronicSite V)
  | .torsionReference frame => frame.rearSite?
  | _ => none

end FrameAnnotation

/-! ## Fieldwise atom transport -/

/-- Relabel every atom reference of a center frame; order and multiplicity are preserved. -/
def relabelCenterFrame {V W : Type*} (e : V ≃ W) (frame : CenterFrame V) :
    CenterFrame W where
  center := e frame.center
  ligandOrder := frame.ligandOrder.map e

/-- Relabel every atom reference of an axial frame.  The supplied role convention and sense
annotation are copied literally. -/
def relabelAxialFrame {V W : Type*} (e : V ≃ W) (frame : AxialFrame V) :
    AxialFrame W where
  axisStart := e frame.axisStart
  axisEnd := e frame.axisEnd
  startFirst := e frame.startFirst
  startSecond := e frame.startSecond
  endFirst := e frame.endFirst
  endSecond := e frame.endSecond
  roles := frame.roles
  sense? := frame.sense?

/-- Relabel every atom identifier of a planar frame.  The ordered traversal is mapped in order,
optional atom references are mapped when present, and every Boolean/role/plane metadata field is
copied literally. -/
def relabelPlanarFrame {V W : Type*} (e : V ≃ W) (frame : PlanarFrame V) :
    PlanarFrame W where
  planeAtoms := frame.planeAtoms.map e
  pilotAtom := e frame.pilotAtom
  firstReference := e frame.firstReference
  secondReference := e frame.secondReference
  inPlaneBondAtom? := frame.inPlaneBondAtom?.map e
  outOfPlaneAtom? := frame.outOfPlaneAtom?.map e
  torsionRestricted? := frame.torsionRestricted?
  planeCannotBeSymmetryPlane? := frame.planeCannotBeSymmetryPlane?
  exactPlane? := frame.exactPlane?
  roles := frame.roles
  sense? := frame.sense?

/-- Relabel the ordered helix path and its two terminal references. -/
def relabelHelicalFrame {V W : Type*} (e : V ≃ W) (frame : HelicalFrame V) :
    HelicalFrame W where
  helixPath := frame.helixPath.map e
  frontReference := e frame.frontReference
  backReference := e frame.backReference
  sense? := frame.sense?

/-- Relabel the six atom references of an existing `AlkeneUnit`. -/
def relabelAlkeneUnit {V W : Type*} (e : V ≃ W) (unit : AlkeneUnit V) :
    AlkeneUnit W where
  leftAtom := e unit.leftAtom
  rightAtom := e unit.rightAtom
  leftHigh := e unit.leftHigh
  leftLow := e unit.leftLow
  rightHigh := e unit.rightHigh
  rightLow := e unit.rightLow

/-- Relabel the center and ordered ligand identifiers of a polyhedral frame.  The geometry and
position-role metadata is copied literally, so geometry positions are not confused with atoms. -/
def relabelPolyhedralFrame {V W : Type*} (e : V ≃ W) (frame : PolyhedralFrame V) :
    PolyhedralFrame W where
  center := e frame.center
  ligandOrder := frame.ligandOrder.map e
  metadata := frame.metadata

/-- Relabel one P-94 torsion participant, retaining its `atom` / `lonePair` / `duplicateAtom`
constructor and mapping only the atom label. -/
def relabelTorsionParticipant {V W : Type*} (e : V ≃ W) :
    TorsionParticipant V → TorsionParticipant W
  | .atom atom => .atom (e atom)
  | .lonePair center => .lonePair (e center)
  | .duplicateAtom original => .duplicateAtom (e original)

/-- Relabel one explicitly selected site: the owner is mapped by `e`, the supplied inventory is
pulled back along `e`, and the kind and numeric slot are retained literally.  The slot bound is
transported because the pulled-back inventory gives the same count at the mapped owner. -/
def relabelSelectedElectronicSite {V W : Type*} (e : V ≃ W)
    (site : SelectedElectronicSite V) : SelectedElectronicSite W where
  inventory := { counts := fun owner => site.inventory.counts (e.symm owner) }
  owner := e site.owner
  kind := site.kind
  slot := site.slot
  slotBound := by
    show site.slot < (site.inventory.counts (e.symm (e site.owner))).count site.kind
    simpa using site.slotBound

/-- Relabel the ordered torsion axis path and the two participant labels.  The participant
variants, the supplied angle and the selected site kind/slot data are copied literally; only
owners are mapped, and the inventories are transported coherently. -/
def relabelTorsionReferenceFrame {V W : Type*} (e : V ≃ W)
    (frame : TorsionReferenceFrame V) : TorsionReferenceFrame W where
  axisPath := frame.axisPath.map e
  front := relabelTorsionParticipant e frame.front
  rear := relabelTorsionParticipant e frame.rear
  angle? := frame.angle?
  frontSite? := frame.frontSite?.map (relabelSelectedElectronicSite e)
  rearSite? := frame.rearSite?.map (relabelSelectedElectronicSite e)

/-- Relabel an ordered ring traversal in place. -/
def relabelRingTraversalFrame {V W : Type*} (e : V ≃ W)
    (frame : RingTraversalFrame V) : RingTraversalFrame W where
  ringAtoms := frame.ringAtoms.map e

/-- Relabel one retained source attachment: the selected ring atom reference is mapped by `e`,
while the actual source interaction occurrence index is retained literally because it indexes the
common source molecule, not the atom-label type. -/
def relabelRealRingPlaneAttachment {V W : Type*} (e : V ≃ W)
    (attachment : RealRingPlaneAttachment V) : RealRingPlaneAttachment W where
  ringPosition := e attachment.ringPosition
  interactionIndex := attachment.interactionIndex

/-- Relabel one real ring-plane frame: atom references (including both optional attachment
ring-position references) are mapped by `e`, the actual interaction occurrence indices are kept,
and the supplied real reference plane is copied literally (no rational approximation). -/
def relabelRealRingPlaneFrame {V W : Type*} (e : V ≃ W)
    (frame : RealRingPlaneFrame V) : RealRingPlaneFrame W where
  plane := frame.plane
  ringAtoms := frame.ringAtoms.map e
  firstSubstituent := e frame.firstSubstituent
  secondSubstituent := e frame.secondSubstituent
  firstAttachment? := frame.firstAttachment?.map (relabelRealRingPlaneAttachment e)
  secondAttachment? := frame.secondAttachment?.map (relabelRealRingPlaneAttachment e)

/-- Fieldwise transport of one annotation by one common atom equivalence.  Constructors, list
order, optional presence, participant identity, reference roles, senses, angles and polyhedral
metadata are all preserved. -/
def relabelFrameAnnotation {V W : Type*} (e : V ≃ W) :
    FrameAnnotation V → FrameAnnotation W
  | .center frame => .center (relabelCenterFrame e frame)
  | .axial frame => .axial (relabelAxialFrame e frame)
  | .planar frame => .planar (relabelPlanarFrame e frame)
  | .helical frame => .helical (relabelHelicalFrame e frame)
  | .alkene unit => .alkene (relabelAlkeneUnit e unit)
  | .polyhedral frame => .polyhedral (relabelPolyhedralFrame e frame)
  | .torsionReference frame =>
      .torsionReference (relabelTorsionReferenceFrame e frame)
  | .ringTraversal frame => .ringTraversal (relabelRingTraversalFrame e frame)
  | .realRingPlane frame => .realRingPlane (relabelRealRingPlaneFrame e frame)

/-! ## Field and list recovery -/

@[simp] theorem relabelCenterFrame_symm {V W : Type*} (e : V ≃ W)
    (frame : CenterFrame V) :
    relabelCenterFrame e.symm (relabelCenterFrame e frame) = frame := by
  cases frame
  simp [relabelCenterFrame, List.map_map, Function.comp_def]

@[simp] theorem relabelAxialFrame_symm {V W : Type*} (e : V ≃ W)
    (frame : AxialFrame V) :
    relabelAxialFrame e.symm (relabelAxialFrame e frame) = frame := by
  cases frame
  simp [relabelAxialFrame]

@[simp] theorem relabelPlanarFrame_symm {V W : Type*} (e : V ≃ W)
    (frame : PlanarFrame V) :
    relabelPlanarFrame e.symm (relabelPlanarFrame e frame) = frame := by
  cases frame
  simp [relabelPlanarFrame, List.map_map, Function.comp_def]

@[simp] theorem relabelHelicalFrame_symm {V W : Type*} (e : V ≃ W)
    (frame : HelicalFrame V) :
    relabelHelicalFrame e.symm (relabelHelicalFrame e frame) = frame := by
  cases frame
  simp [relabelHelicalFrame, List.map_map, Function.comp_def]

@[simp] theorem relabelAlkeneUnit_symm {V W : Type*} (e : V ≃ W)
    (unit : AlkeneUnit V) :
    relabelAlkeneUnit e.symm (relabelAlkeneUnit e unit) = unit := by
  cases unit
  simp [relabelAlkeneUnit]

@[simp] theorem relabelPolyhedralFrame_symm {V W : Type*} (e : V ≃ W)
    (frame : PolyhedralFrame V) :
    relabelPolyhedralFrame e.symm (relabelPolyhedralFrame e frame) = frame := by
  cases frame
  simp [relabelPolyhedralFrame, List.map_map, Function.comp_def]

@[simp] theorem relabelTorsionParticipant_symm {V W : Type*} (e : V ≃ W)
    (participant : TorsionParticipant V) :
    relabelTorsionParticipant e.symm (relabelTorsionParticipant e participant) =
      participant := by
  cases participant <;> simp [relabelTorsionParticipant]

/-- The participant atom-reference projection commutes with transport and preserves the ordered
role list.  It is placed before the whole-annotation proof so that proof can use it for an
arbitrary participant variable. -/
@[simp] theorem torsionParticipantRefs_relabel {V W : Type*} (e : V ≃ W)
    (participant : TorsionParticipant V) :
    torsionParticipantRefs (relabelTorsionParticipant e participant) =
      (torsionParticipantRefs participant).map e := by
  cases participant <;> simp [torsionParticipantRefs, relabelTorsionParticipant]

/-- A selected-site owner is mapped by the common equivalence; kind and slot are untouched. -/
@[simp] theorem relabelSelectedElectronicSite_owner {V W : Type*} (e : V ≃ W)
    (site : SelectedElectronicSite V) :
    (relabelSelectedElectronicSite e site).owner = e site.owner := rfl

@[simp] theorem relabelSelectedElectronicSite_kind {V W : Type*} (e : V ≃ W)
    (site : SelectedElectronicSite V) :
    (relabelSelectedElectronicSite e site).kind = site.kind := rfl

/-- The numeric slot is retained literally, so slot identity is not collapsed to owner/kind. -/
@[simp] theorem relabelSelectedElectronicSite_slot {V W : Type*} (e : V ≃ W)
    (site : SelectedElectronicSite V) :
    (relabelSelectedElectronicSite e site).slot = site.slot := rfl

@[simp] theorem relabelSelectedElectronicSite_inventory_counts {V W : Type*}
    (e : V ≃ W) (site : SelectedElectronicSite V) (owner : W) :
    (relabelSelectedElectronicSite e site).inventory.counts owner =
      site.inventory.counts (e.symm owner) := rfl

/-- The stored inventory is transported by the same equivalence `e`, not left implicit: at a
mapped owner it is the source inventory at the inverse image.  Consequently a visible
`MatchesInventory` binding to a common supplied inventory is preserved by transport. -/
theorem SelectedElectronicSite.matchesInventory_relabel {V W : Type*} (e : V ≃ W)
    (site : SelectedElectronicSite V) (inventory : IndependentSiteCounts V)
    (compatibleCounts : site.MatchesInventory inventory) :
    (relabelSelectedElectronicSite e site).MatchesInventory
      { counts := fun owner => inventory.counts (e.symm owner) } := by
  simp only [SelectedElectronicSite.MatchesInventory, relabelSelectedElectronicSite]
    at compatibleCounts ⊢
  rw [compatibleCounts]

/-- The slot bound is transported along the same equivalence and inventory pullback. -/
@[simp] theorem relabelSelectedElectronicSite_slotBound {V W : Type*} (e : V ≃ W)
    (site : SelectedElectronicSite V) :
    (relabelSelectedElectronicSite e site).slot <
      ((relabelSelectedElectronicSite e site).inventory.counts
        (relabelSelectedElectronicSite e site).owner).count
          (relabelSelectedElectronicSite e site).kind :=
  (relabelSelectedElectronicSite e site).slotBound

/-- Inverse recovery for a selected site: owner, inventory, kind and exact numeric slot all
return unchanged. -/
@[simp] theorem relabelSelectedElectronicSite_symm {V W : Type*} (e : V ≃ W)
    (site : SelectedElectronicSite V) :
    relabelSelectedElectronicSite e.symm (relabelSelectedElectronicSite e site) = site := by
  cases site with
  | mk inventory owner kind slot slotBound =>
      refine SelectedElectronicSite.ext_of_fields ?_ ?_ ?_ ?_
      · cases inventory with
        | mk values =>
            simp [relabelSelectedElectronicSite]
      · simp
      · rfl
      · rfl

@[simp] theorem relabelTorsionReferenceFrame_symm {V W : Type*} (e : V ≃ W)
    (frame : TorsionReferenceFrame V) :
    relabelTorsionReferenceFrame e.symm (relabelTorsionReferenceFrame e frame) = frame := by
  cases frame
  simp [relabelTorsionReferenceFrame, List.map_map, Function.comp_def]

@[simp] theorem relabelRingTraversalFrame_symm {V W : Type*} (e : V ≃ W)
    (frame : RingTraversalFrame V) :
    relabelRingTraversalFrame e.symm (relabelRingTraversalFrame e frame) = frame := by
  cases frame
  simp [relabelRingTraversalFrame]

/-- Inverse recovery for one retained source attachment: the ring-position reference returns
unchanged and the actual interaction occurrence index is literally the same. -/
@[simp] theorem relabelRealRingPlaneAttachment_symm {V W : Type*} (e : V ≃ W)
    (attachment : RealRingPlaneAttachment V) :
    relabelRealRingPlaneAttachment e.symm (relabelRealRingPlaneAttachment e attachment) =
      attachment := by
  cases attachment
  simp [relabelRealRingPlaneAttachment]

@[simp] theorem relabelRealRingPlaneFrame_symm {V W : Type*} (e : V ≃ W)
    (frame : RealRingPlaneFrame V) :
    relabelRealRingPlaneFrame e.symm (relabelRealRingPlaneFrame e frame) = frame := by
  cases frame
  simp [relabelRealRingPlaneFrame, relabelRealRingPlaneAttachment, List.map_map,
    Function.comp_def]

/-- Inverse recovery for the whole annotation channel: transporting by `e` and then by `e.symm`
returns the original annotation, including every field, list order, participant identity and
metadata item. -/
@[simp] theorem relabelFrameAnnotation_symm {V W : Type*} (e : V ≃ W)
    (annotation : FrameAnnotation V) :
    relabelFrameAnnotation e.symm (relabelFrameAnnotation e annotation) = annotation := by
  cases annotation <;> simp [relabelFrameAnnotation]

/-- Transport is injective: two annotations with the same transport were already equal. -/
theorem relabelFrameAnnotation_injective {V W : Type*} (e : V ≃ W) :
    Function.Injective (relabelFrameAnnotation (V := V) (W := W) e) := by
  intro first second equal
  calc
    first = relabelFrameAnnotation e.symm (relabelFrameAnnotation e first) :=
      (relabelFrameAnnotation_symm e first).symm
    _ = relabelFrameAnnotation e.symm (relabelFrameAnnotation e second) := by rw [equal]
    _ = second := relabelFrameAnnotation_symm e second

/-- The ordered atom-reference list is transported exactly elementwise.  In particular, order,
multiplicity and optional-reference presence are retained; the result is not an unordered
support. -/
@[simp] theorem atomRefs_relabelFrameAnnotation {V W : Type*} (e : V ≃ W)
    (annotation : FrameAnnotation V) :
    (relabelFrameAnnotation e annotation).atomRefs = annotation.atomRefs.map e := by
  cases annotation with
  | center frame => rfl
  | axial frame => rfl
  | planar frame =>
      (first | rfl | simp [FrameAnnotation.atomRefs, relabelFrameAnnotation,
        relabelPlanarFrame, Option.toList_map])
  | helical frame =>
      (first | rfl | simp [FrameAnnotation.atomRefs, relabelFrameAnnotation,
        relabelHelicalFrame])
  | alkene unit => rfl
  | polyhedral frame => rfl
  | torsionReference frame =>
      obtain ⟨axisPath, front, rear, angle, frontSite, rearSite⟩ := frame
      cases frontSite <;> cases rearSite <;>
        (first | rfl | simp [FrameAnnotation.atomRefs, relabelFrameAnnotation,
          relabelTorsionReferenceFrame])
  | ringTraversal frame => rfl
  | realRingPlane frame =>
      obtain ⟨plane, ringAtoms, firstSubstituent, secondSubstituent,
        firstAttachment, secondAttachment⟩ := frame
      cases firstAttachment <;> cases secondAttachment <;>
        (first | rfl | simp [FrameAnnotation.atomRefs, relabelFrameAnnotation,
          relabelRealRingPlaneFrame, relabelRealRingPlaneAttachment])

/-- The exact ordered planar traversal is recovered as the mapped source traversal. -/
@[simp] theorem planeAtoms?_relabelFrameAnnotation {V W : Type*} (e : V ≃ W)
    (annotation : FrameAnnotation V) :
    (relabelFrameAnnotation e annotation).planeAtoms? =
      annotation.planeAtoms?.map (List.map e) := by
  cases annotation <;> rfl

/-- The exact ordered helix path is recovered as the mapped source path. -/
@[simp] theorem helixPath?_relabelFrameAnnotation {V W : Type*} (e : V ≃ W)
    (annotation : FrameAnnotation V) :
    (relabelFrameAnnotation e annotation).helixPath? =
      annotation.helixPath?.map (List.map e) := by
  cases annotation <;> rfl

/-- The exact ordered torsion axis path is recovered as the mapped source path. -/
@[simp] theorem torsionAxisPath?_relabelFrameAnnotation {V W : Type*} (e : V ≃ W)
    (annotation : FrameAnnotation V) :
    (relabelFrameAnnotation e annotation).torsionAxisPath? =
      annotation.torsionAxisPath?.map (List.map e) := by
  cases annotation <;> rfl

/-- The exact ordered ring traversal is recovered as the mapped source traversal. -/
@[simp] theorem ringAtoms?_relabelFrameAnnotation {V W : Type*} (e : V ≃ W)
    (annotation : FrameAnnotation V) :
    (relabelFrameAnnotation e annotation).ringAtoms? =
      annotation.ringAtoms?.map (List.map e) := by
  cases annotation <;> rfl

/-- The actual real reference plane is retained literally by atom relabelling, with no rational
approximation and no derived coplanarity. -/
@[simp] theorem realPlane?_relabelFrameAnnotation {V W : Type*} (e : V ≃ W)
    (annotation : FrameAnnotation V) :
    (relabelFrameAnnotation e annotation).realPlane? = annotation.realPlane? := by
  cases annotation <;> rfl

/-- The whole real ring-plane record is transported fieldwise; in particular both optional
attachment references are retained, with their occurrence indices unchanged. -/
@[simp] theorem realRingPlaneFrame?_relabelFrameAnnotation {V W : Type*} (e : V ≃ W)
    (annotation : FrameAnnotation V) :
    (relabelFrameAnnotation e annotation).realRingPlaneFrame? =
      annotation.realRingPlaneFrame?.map (relabelRealRingPlaneFrame e) := by
  cases annotation <;> rfl

/-- The first substituent reference is transported by the same atom equivalence. -/
@[simp] theorem realRingPlaneFirstSubstituent?_relabelFrameAnnotation {V W : Type*}
    (e : V ≃ W) (annotation : FrameAnnotation V) :
    (relabelFrameAnnotation e annotation).realRingPlaneFirstSubstituent? =
      annotation.realRingPlaneFirstSubstituent?.map e := by
  cases annotation <;> rfl

/-- The second substituent reference is transported by the same atom equivalence. -/
@[simp] theorem realRingPlaneSecondSubstituent?_relabelFrameAnnotation {V W : Type*}
    (e : V ≃ W) (annotation : FrameAnnotation V) :
    (relabelFrameAnnotation e annotation).realRingPlaneSecondSubstituent? =
      annotation.realRingPlaneSecondSubstituent?.map e := by
  cases annotation <;> rfl

/-- The first selected source attachment is transported with its ring position mapped and its
actual interaction occurrence index retained literally. -/
@[simp] theorem realRingPlaneFirstAttachment?_relabelFrameAnnotation {V W : Type*}
    (e : V ≃ W) (annotation : FrameAnnotation V) :
    (relabelFrameAnnotation e annotation).realRingPlaneFirstAttachment? =
      annotation.realRingPlaneFirstAttachment?.map (relabelRealRingPlaneAttachment e) := by
  cases annotation <;> rfl

/-- The second selected source attachment is transported with its ring position mapped and its
actual interaction occurrence index retained literally. -/
@[simp] theorem realRingPlaneSecondAttachment?_relabelFrameAnnotation {V W : Type*}
    (e : V ≃ W) (annotation : FrameAnnotation V) :
    (relabelFrameAnnotation e annotation).realRingPlaneSecondAttachment? =
      annotation.realRingPlaneSecondAttachment?.map (relabelRealRingPlaneAttachment e) := by
  cases annotation <;> rfl

/-- Polyhedral geometry and position-role metadata is independent of atom labelling and is
recovered literally. -/
@[simp] theorem polyhedralMetadata?_relabelFrameAnnotation {V W : Type*} (e : V ≃ W)
    (annotation : FrameAnnotation V) :
    (relabelFrameAnnotation e annotation).polyhedralMetadata? =
      annotation.polyhedralMetadata? := by
  cases annotation <;> rfl

/-- Geometry positions are not atom identifiers: the supplied polyhedral position observation is
unchanged by every atom equivalence. -/
@[simp] theorem positionRoleObservation?_relabelFrameAnnotation {V W : Type*} (e : V ≃ W)
    (annotation : FrameAnnotation V) :
    (relabelFrameAnnotation e annotation).positionRoleObservation? =
      annotation.positionRoleObservation? := by
  cases annotation <;> rfl

/-- A supplied oriented exact plane is retained literally by atom relabelling. -/
@[simp] theorem exactPlane?_relabelFrameAnnotation {V W : Type*} (e : V ≃ W)
    (annotation : FrameAnnotation V) :
    (relabelFrameAnnotation e annotation).exactPlane? = annotation.exactPlane? := by
  cases annotation <;> rfl

/-- A supplied torsion angle is retained literally by atom relabelling. -/
@[simp] theorem torsionAngle?_relabelFrameAnnotation {V W : Type*} (e : V ≃ W)
    (annotation : FrameAnnotation V) :
    (relabelFrameAnnotation e annotation).torsionAngle? = annotation.torsionAngle? := by
  cases annotation <;> rfl

/-- The explicitly selected front site is transported by the same equivalence as every atom
reference, and absence is preserved. -/
@[simp] theorem frontSite?_relabelFrameAnnotation {V W : Type*} (e : V ≃ W)
    (annotation : FrameAnnotation V) :
    (relabelFrameAnnotation e annotation).frontSite? =
      annotation.frontSite?.map (relabelSelectedElectronicSite e) := by
  cases annotation <;> rfl

/-- The explicitly selected rear site is transported by the same equivalence as every atom
reference, and absence is preserved. -/
@[simp] theorem rearSite?_relabelFrameAnnotation {V W : Type*} (e : V ≃ W)
    (annotation : FrameAnnotation V) :
    (relabelFrameAnnotation e annotation).rearSite? =
      annotation.rearSite?.map (relabelSelectedElectronicSite e) := by
  cases annotation <;> rfl

/-! ### Selected-site recovery and compatibility -/

/-- The legacy owner projection commutes with participant transport. -/
@[simp] theorem participantOwner_relabelTorsionParticipant {V W : Type*} (e : V ≃ W)
    (participant : TorsionParticipant V) :
    SelectedElectronicSite.participantOwner
        (relabelTorsionParticipant e participant) =
      e (SelectedElectronicSite.participantOwner participant) := by
  cases participant <;>
    simp [relabelTorsionParticipant, SelectedElectronicSite.participantOwner]

/-- The site kind pinned by a legacy participant is independent of atom labelling. -/
@[simp] theorem participantSiteKind?_relabelTorsionParticipant {V W : Type*} (e : V ≃ W)
    (participant : TorsionParticipant V) :
    SelectedElectronicSite.participantSiteKind?
        (relabelTorsionParticipant e participant) =
      SelectedElectronicSite.participantSiteKind? participant := by
  cases participant <;>
    simp [relabelTorsionParticipant, SelectedElectronicSite.participantSiteKind?]

/-- Compatibility with the legacy participant is preserved by transport: the owner is mapped and
the pinned kind is unchanged. -/
theorem SelectedElectronicSite.compatibleWith_relabel {V W : Type*} (e : V ≃ W)
    (site : SelectedElectronicSite V) (participant : TorsionParticipant V)
    (compatible : site.CompatibleWith participant) :
    (relabelSelectedElectronicSite e site).CompatibleWith
      (relabelTorsionParticipant e participant) := by
  simp only [SelectedElectronicSite.CompatibleWith] at compatible
  rcases compatible with ⟨owner_eq, kind_condition⟩
  simp only [SelectedElectronicSite.CompatibleWith]
  constructor
  · simp [owner_eq]
  · intro kind member
    have sourceMember :
        SelectedElectronicSite.participantSiteKind? participant = some kind := by
      rw [participantSiteKind?_relabelTorsionParticipant e participant] at member
      exact member
    have pinned := kind_condition kind sourceMember
    simpa using pinned

/-- Validity of a torsion reference frame is preserved by transport.  In particular, a selected
slot remains a genuine slot of the transported inventory and stays compatible with the mapped
legacy participant. -/
theorem TorsionReferenceFrame.valid_relabel {V W : Type*} (e : V ≃ W)
    (frame : TorsionReferenceFrame V) (valid : frame.Valid) :
    (relabelTorsionReferenceFrame e frame).Valid := by
  simp only [TorsionReferenceFrame.Valid] at valid ⊢
  rcases valid with ⟨frontValid, rearValid⟩
  constructor
  · intro site member
    change frame.frontSite?.map (relabelSelectedElectronicSite e) = some site at member
    rw [Option.map_eq_some_iff] at member
    rcases member with ⟨sourceSite, sourceMember, rfl⟩
    exact SelectedElectronicSite.compatibleWith_relabel e sourceSite frame.front
      (frontValid sourceSite sourceMember)
  · intro site member
    change frame.rearSite?.map (relabelSelectedElectronicSite e) = some site at member
    rw [Option.map_eq_some_iff] at member
    rcases member with ⟨sourceSite, sourceMember, rfl⟩
    exact SelectedElectronicSite.compatibleWith_relabel e sourceSite frame.rear
      (rearValid sourceSite sourceMember)

/-- A frame with no explicitly selected sites is valid: legacy unslotted input needs no invented
slot. -/
theorem torsionReferenceFrame_valid_of_sites_none {V : Type*}
    (frame : TorsionReferenceFrame V)
    (frontNone : frame.frontSite? = none) (rearNone : frame.rearSite? = none) :
    frame.Valid := by
  simp only [TorsionReferenceFrame.Valid]
  constructor
  · intro site member
    simp [frontNone] at member
  · intro site member
    simp [rearNone] at member

/-! ### Individual field recovery -/

@[simp] theorem relabelAxialFrame_roles {V W : Type*} (e : V ≃ W)
    (frame : AxialFrame V) :
    (relabelAxialFrame e frame).roles = frame.roles := rfl

@[simp] theorem relabelAxialFrame_sense? {V W : Type*} (e : V ≃ W)
    (frame : AxialFrame V) :
    (relabelAxialFrame e frame).sense? = frame.sense? := rfl

@[simp] theorem relabelPlanarFrame_roles {V W : Type*} (e : V ≃ W)
    (frame : PlanarFrame V) :
    (relabelPlanarFrame e frame).roles = frame.roles := rfl

@[simp] theorem relabelPlanarFrame_torsionRestricted? {V W : Type*} (e : V ≃ W)
    (frame : PlanarFrame V) :
    (relabelPlanarFrame e frame).torsionRestricted? = frame.torsionRestricted? := rfl

@[simp] theorem relabelPlanarFrame_planeCannotBeSymmetryPlane? {V W : Type*} (e : V ≃ W)
    (frame : PlanarFrame V) :
    (relabelPlanarFrame e frame).planeCannotBeSymmetryPlane? =
      frame.planeCannotBeSymmetryPlane? := rfl

@[simp] theorem relabelPlanarFrame_exactPlane? {V W : Type*} (e : V ≃ W)
    (frame : PlanarFrame V) :
    (relabelPlanarFrame e frame).exactPlane? = frame.exactPlane? := rfl

@[simp] theorem relabelPlanarFrame_sense? {V W : Type*} (e : V ≃ W)
    (frame : PlanarFrame V) :
    (relabelPlanarFrame e frame).sense? = frame.sense? := rfl

@[simp] theorem relabelHelicalFrame_sense? {V W : Type*} (e : V ≃ W)
    (frame : HelicalFrame V) :
    (relabelHelicalFrame e frame).sense? = frame.sense? := rfl

@[simp] theorem relabelPolyhedralFrame_metadata {V W : Type*} (e : V ≃ W)
    (frame : PolyhedralFrame V) :
    (relabelPolyhedralFrame e frame).metadata = frame.metadata := rfl

@[simp] theorem relabelTorsionReferenceFrame_front {V W : Type*} (e : V ≃ W)
    (frame : TorsionReferenceFrame V) :
    (relabelTorsionReferenceFrame e frame).front =
      relabelTorsionParticipant e frame.front := rfl

@[simp] theorem relabelTorsionReferenceFrame_rear {V W : Type*} (e : V ≃ W)
    (frame : TorsionReferenceFrame V) :
    (relabelTorsionReferenceFrame e frame).rear =
      relabelTorsionParticipant e frame.rear := rfl

@[simp] theorem relabelTorsionReferenceFrame_angle? {V W : Type*} (e : V ≃ W)
    (frame : TorsionReferenceFrame V) :
    (relabelTorsionReferenceFrame e frame).angle? = frame.angle? := rfl

@[simp] theorem relabelTorsionReferenceFrame_frontSite? {V W : Type*} (e : V ≃ W)
    (frame : TorsionReferenceFrame V) :
    (relabelTorsionReferenceFrame e frame).frontSite? =
      frame.frontSite?.map (relabelSelectedElectronicSite e) := rfl

@[simp] theorem relabelTorsionReferenceFrame_rearSite? {V W : Type*} (e : V ≃ W)
    (frame : TorsionReferenceFrame V) :
    (relabelTorsionReferenceFrame e frame).rearSite? =
      frame.rearSite?.map (relabelSelectedElectronicSite e) := rfl

@[simp] theorem relabelRealRingPlaneFrame_plane {V W : Type*} (e : V ≃ W)
    (frame : RealRingPlaneFrame V) :
    (relabelRealRingPlaneFrame e frame).plane = frame.plane := rfl

@[simp] theorem relabelRealRingPlaneFrame_ringAtoms {V W : Type*} (e : V ≃ W)
    (frame : RealRingPlaneFrame V) :
    (relabelRealRingPlaneFrame e frame).ringAtoms = frame.ringAtoms.map e := rfl

@[simp] theorem relabelRealRingPlaneFrame_firstSubstituent {V W : Type*} (e : V ≃ W)
    (frame : RealRingPlaneFrame V) :
    (relabelRealRingPlaneFrame e frame).firstSubstituent = e frame.firstSubstituent := rfl

@[simp] theorem relabelRealRingPlaneFrame_secondSubstituent {V W : Type*} (e : V ≃ W)
    (frame : RealRingPlaneFrame V) :
    (relabelRealRingPlaneFrame e frame).secondSubstituent = e frame.secondSubstituent := rfl

@[simp] theorem relabelRealRingPlaneFrame_firstAttachment? {V W : Type*} (e : V ≃ W)
    (frame : RealRingPlaneFrame V) :
    (relabelRealRingPlaneFrame e frame).firstAttachment? =
      frame.firstAttachment?.map (relabelRealRingPlaneAttachment e) := rfl

@[simp] theorem relabelRealRingPlaneFrame_secondAttachment? {V W : Type*} (e : V ≃ W)
    (frame : RealRingPlaneFrame V) :
    (relabelRealRingPlaneFrame e frame).secondAttachment? =
      frame.secondAttachment?.map (relabelRealRingPlaneAttachment e) := rfl

@[simp] theorem relabelRealRingPlaneAttachment_ringPosition {V W : Type*} (e : V ≃ W)
    (attachment : RealRingPlaneAttachment V) :
    (relabelRealRingPlaneAttachment e attachment).ringPosition =
      e attachment.ringPosition := rfl

/-- The actual source interaction occurrence index is independent of the atom labelling. -/
@[simp] theorem relabelRealRingPlaneAttachment_interactionIndex {V W : Type*} (e : V ≃ W)
    (attachment : RealRingPlaneAttachment V) :
    (relabelRealRingPlaneAttachment e attachment).interactionIndex =
      attachment.interactionIndex := rfl

/-! ## Source-indexed adapters

The indexed observations use `Nat` atom positions.  The adapters below convert one such position
only through an explicit proof that it is below the real source atom count.  The conversion is
implemented with `Fin`, so an out-of-range index has no inhabitant and cannot be fabricated. -/

section SourceIndexing

variable {V : Type*} {n : Nat}

/-- The atom label assigned to one source position `index`, given a proof that the position is a
real atom of the source (`index < n`). -/
def sourceAtomOfIndex (e : V ≃ Fin n) (index : Nat) (bound : index < n) : V :=
  e.symm ⟨index, bound⟩

/-- The transported atom maps back to exactly the checked source position. -/
@[simp] theorem sourceAtomOfIndex_apply (e : V ≃ Fin n) (index : Nat)
    (bound : index < n) :
    e (sourceAtomOfIndex e index bound) = ⟨index, bound⟩ := by
  simp [sourceAtomOfIndex]

/-- In particular, the transported atom denotes the same numeric source position. -/
@[simp] theorem sourceAtomOfIndex_val (e : V ≃ Fin n) (index : Nat)
    (bound : index < n) :
    (e (sourceAtomOfIndex e index bound)).val = index := by
  simp [sourceAtomOfIndex]

/-- The transported atom is a real atom of the source: its position is below `n`. -/
theorem sourceAtomOfIndex_bound (e : V ≃ Fin n) (index : Nat)
    (bound : index < n) :
    (e (sourceAtomOfIndex e index bound)).val < n := by
  simpa [sourceAtomOfIndex] using bound

/-- Convert an ordered list of source positions.  Every member must carry its own bound; the order
and multiplicity of the source list are preserved. -/
def sourceAtomListOfIndices (e : V ≃ Fin n) (indices : List Nat)
    (bounded : ∀ index ∈ indices, index < n) : List V :=
  match indices with
  | [] => []
  | index :: rest =>
      sourceAtomOfIndex e index (bounded index (by simp)) ::
        sourceAtomListOfIndices e rest
          (fun other member => bounded other (by simp [member]))

/-- Converting an ordered source-position list preserves its length. -/
@[simp] theorem sourceAtomListOfIndices_length (e : V ≃ Fin n)
    (indices : List Nat) (bounded : ∀ index ∈ indices, index < n) :
    (sourceAtomListOfIndices e indices bounded).length = indices.length := by
  revert bounded
  induction indices with
  | nil =>
      intro bounded
      rfl
  | cons index rest inductionHypothesis =>
      intro bounded
      simp [sourceAtomListOfIndices,
        inductionHypothesis (fun other member => bounded other (by simp [member]))]

/-- Mapping the converted list back through `e` recovers exactly the original source positions.
This is the no-fabrication guarantee: every produced atom is one of the supplied, bounded source
positions, in the same order. -/
theorem map_sourceAtomListOfIndices (e : V ≃ Fin n) (indices : List Nat)
    (bounded : ∀ index ∈ indices, index < n) :
    (sourceAtomListOfIndices e indices bounded).map (fun atom => (e atom).val) =
      indices := by
  revert bounded
  induction indices with
  | nil =>
      intro bounded
      rfl
  | cons index rest inductionHypothesis =>
      intro bounded
      simp [sourceAtomListOfIndices,
        inductionHypothesis (fun other member => bounded other (by simp [member]))]

end SourceIndexing

/-! ### Bounds for indexed observations -/

/-- Every atom position named by one indexed axial observation is a real atom of a source with
`n` atoms. -/
def IndexedAxialSourceBounded (n : Nat)
    (record : IndexedAxialGeometryObservation) : Prop :=
  record.axisStart < n ∧ record.axisEnd < n ∧
    record.startFirst < n ∧ record.startSecond < n ∧
    record.endFirst < n ∧ record.endSecond < n

/-- Every atom position named by one legacy indexed planar observation is a real atom. -/
def IndexedPlanarSourceBounded (n : Nat)
    (record : IndexedPlanarGeometryObservation) : Prop :=
  (∀ atom ∈ record.planeAtoms, atom < n) ∧
    record.pilotAtom < n ∧ record.firstReference < n ∧ record.secondReference < n

/-- Every atom position named by one indexed planar-derived-tetrahedron observation is a real
atom.  The two Boolean applicability fields are not atom positions. -/
def IndexedPlanarDerivedSourceBounded (n : Nat)
    (record : IndexedPlanarDerivedTetrahedronObservation) : Prop :=
  (∀ atom ∈ record.planeAtoms, atom < n) ∧
    record.pilotAtom < n ∧ record.firstReference < n ∧ record.secondReference < n ∧
    record.inPlaneBondAtom < n ∧ record.outOfPlaneAtom < n

/-- Every atom position named by one indexed helical observation is a real atom. -/
def IndexedHelicalSourceBounded (n : Nat)
    (record : IndexedHelicalGeometryObservation) : Prop :=
  (∀ atom ∈ record.helixPath, atom < n) ∧
    record.frontReference < n ∧ record.backReference < n

/-- Every atom position named by one indexed polyhedral observation is a real atom.  The
`configurationPositions` observation is deliberately absent: it names geometry positions bounded
by the coordination number, not atom identifiers. -/
def IndexedPolyhedralSourceBounded (n : Nat)
    (record : IndexedPolyhedralGeometryObservation) : Prop :=
  record.center < n ∧ ∀ atom ∈ record.ligands, atom < n

/-- Every atom label of one P-94 torsion participant is a real atom of a source with `n` atoms.
The three participant constructors are bounded through the existing
`P94ConformationUnit.ParticipantBounded` relation. -/
def TorsionParticipantSourceBounded (n : Nat) (participant : TorsionParticipant Nat) : Prop :=
  P94ConformationUnit.ParticipantBounded participant n

/-- Every member of an ordered P-94 axis path is a real atom. -/
def TorsionAxisPathSourceBounded (n : Nat) (path : List Nat) : Prop :=
  ∀ atom ∈ path, atom < n

/-! ### Unit-record adapters -/

section Adapters

variable {V : Type*} {n : Nat}

/-- Adapt an existing `AxialUnit`.  The supplied high/low labels are stored as the ordered
`startFirst`/`startSecond`/`endFirst`/`endSecond` slots, and the role marker records that they
were caller-supplied labels.  No ranking is derived. -/
def axialUnitToFrame (unit : AxialUnit V) : FrameAnnotation V :=
  .axial
    { axisStart := unit.axisStart
      axisEnd := unit.axisEnd
      startFirst := unit.startHigh
      startSecond := unit.startLow
      endFirst := unit.endHigh
      endSecond := unit.endLow
      roles := .suppliedHighLow
      sense? := none }

/-- Adapt an existing `PlanarUnit`, preserving the ordered plane traversal, the pilot atom and the
supplied high/low reference labels. -/
def planarUnitToFrame (unit : PlanarUnit V) : FrameAnnotation V :=
  .planar
    { planeAtoms := unit.planeAtoms
      pilotAtom := unit.pilotAtom
      firstReference := unit.highReference
      secondReference := unit.lowReference
      roles := .suppliedHighLow }

/-- Adapt an existing `HelicalUnit`, preserving the ordered helix path and the two references. -/
def helicalUnitToFrame (unit : HelicalUnit V) : FrameAnnotation V :=
  .helical
    { helixPath := unit.helixPath
      frontReference := unit.frontReference
      backReference := unit.backReference
      sense? := none }

/-- Adapt an existing `AlkeneUnit` verbatim. -/
def alkeneUnitToFrame (unit : AlkeneUnit V) : FrameAnnotation V :=
  .alkene unit

/-! ### Indexed-observation adapters -/

/-- Adapt one bounded indexed axial observation.  The listed incidence order is retained;
`sense` is stored only as a supplied annotation. -/
def indexedAxialToFrame (e : V ≃ Fin n) (record : IndexedAxialGeometryObservation)
    (bounded : IndexedAxialSourceBounded n record) : FrameAnnotation V :=
  .axial
    { axisStart := sourceAtomOfIndex e record.axisStart bounded.1
      axisEnd := sourceAtomOfIndex e record.axisEnd bounded.2.1
      startFirst := sourceAtomOfIndex e record.startFirst bounded.2.2.1
      startSecond := sourceAtomOfIndex e record.startSecond bounded.2.2.2.1
      endFirst := sourceAtomOfIndex e record.endFirst bounded.2.2.2.2.1
      endSecond := sourceAtomOfIndex e record.endSecond bounded.2.2.2.2.2
      roles := .orderedIncidencePair
      sense? := some record.sense }

/-- Adapt one bounded legacy indexed planar observation.  The richer planar-derived fields are
absent, exactly as in the source record. -/
def indexedPlanarToFrame (e : V ≃ Fin n) (record : IndexedPlanarGeometryObservation)
    (bounded : IndexedPlanarSourceBounded n record) : FrameAnnotation V :=
  .planar
    { planeAtoms := sourceAtomListOfIndices e record.planeAtoms bounded.1
      pilotAtom := sourceAtomOfIndex e record.pilotAtom bounded.2.1
      firstReference := sourceAtomOfIndex e record.firstReference bounded.2.2.1
      secondReference := sourceAtomOfIndex e record.secondReference bounded.2.2.2
      roles := .orderedReferencePair
      sense? := some record.sense }

/-- Adapt one bounded indexed planar-derived-tetrahedron observation.  All source roles are
retained: the ordered plane traversal, pilot, the two ordered references, the in-plane bond atom,
the out-of-plane atom, both applicability Booleans and, when the caller supplies it, the oriented
exact plane.  The plane, like the Booleans, is copied literally; no side or descriptor is
derived. -/
def indexedPlanarDerivedToFrame (e : V ≃ Fin n)
    (record : IndexedPlanarDerivedTetrahedronObservation)
    (bounded : IndexedPlanarDerivedSourceBounded n record)
    (exactPlane? : Option BlueBookP94.CoordinateRing.ExactPlane := none) :
    FrameAnnotation V :=
  .planar
    { planeAtoms := sourceAtomListOfIndices e record.planeAtoms bounded.1
      pilotAtom := sourceAtomOfIndex e record.pilotAtom bounded.2.1
      firstReference := sourceAtomOfIndex e record.firstReference bounded.2.2.1
      secondReference := sourceAtomOfIndex e record.secondReference bounded.2.2.2.1
      inPlaneBondAtom? :=
        some (sourceAtomOfIndex e record.inPlaneBondAtom bounded.2.2.2.2.1)
      outOfPlaneAtom? :=
        some (sourceAtomOfIndex e record.outOfPlaneAtom bounded.2.2.2.2.2)
      torsionRestricted? := some record.torsionRestricted
      planeCannotBeSymmetryPlane? := some record.planeCannotBeSymmetryPlane
      exactPlane? := exactPlane?
      roles := .orderedReferencePair }

/-- Adapt one bounded indexed helical observation.  The ordered helix path and both terminal
references are retained, and the supplied sense is stored as an annotation. -/
def indexedHelicalToFrame (e : V ≃ Fin n) (record : IndexedHelicalGeometryObservation)
    (bounded : IndexedHelicalSourceBounded n record) : FrameAnnotation V :=
  .helical
    { helixPath := sourceAtomListOfIndices e record.helixPath bounded.1
      frontReference := sourceAtomOfIndex e record.frontReference bounded.2.1
      backReference := sourceAtomOfIndex e record.backReference bounded.2.2
      sense? := some record.sense }

/-- Adapt one bounded indexed polyhedral observation.  Atom identifiers (center and ordered
ligands) are converted; every geometry and position-role observation is copied literally, so
geometry positions never become atoms. -/
def indexedPolyhedralToFrame (e : V ≃ Fin n)
    (record : IndexedPolyhedralGeometryObservation)
    (bounded : IndexedPolyhedralSourceBounded n record) : FrameAnnotation V :=
  .polyhedral
    { center := sourceAtomOfIndex e record.center bounded.1
      ligandOrder := sourceAtomListOfIndices e record.ligands bounded.2
      metadata :=
        { geometry := record.geometry
          recognition := record.recognition
          configurationPositions := record.configurationPositions
          absoluteOrientation := record.absoluteOrientation
          priming := record.priming } }

/-- Convert one bounded source torsion participant, retaining its variant. -/
def sourceTorsionParticipant (e : V ≃ Fin n) (participant : TorsionParticipant Nat)
    (bounded : TorsionParticipantSourceBounded n participant) : TorsionParticipant V :=
  match participant with
  | .atom atom => .atom (sourceAtomOfIndex e atom bounded)
  | .lonePair center => .lonePair (sourceAtomOfIndex e center bounded)
  | .duplicateAtom original => .duplicateAtom (sourceAtomOfIndex e original bounded)

/-- Adapt an actual independently supplied site identity into a selected-site reference.  The
supplied inventory is copied, and owner, kind and the exact numeric slot are retained. -/
def selectedSiteOfIndependent {V : Type*} [DecidableEq V] [Fintype V]
    (siteCounts : IndependentSiteCounts V)
    (identity : IndependentSiteIdentity siteCounts) : SelectedElectronicSite V where
  inventory := siteCounts
  owner := identity.owner
  kind := identity.kind
  slot := identity.slot.val
  slotBound := identity.slot.isLt

@[simp] theorem selectedSiteOfIndependent_owner {V : Type*} [DecidableEq V] [Fintype V]
    (siteCounts : IndependentSiteCounts V)
    (identity : IndependentSiteIdentity siteCounts) :
    (selectedSiteOfIndependent siteCounts identity).owner = identity.owner := rfl

@[simp] theorem selectedSiteOfIndependent_kind {V : Type*} [DecidableEq V] [Fintype V]
    (siteCounts : IndependentSiteCounts V)
    (identity : IndependentSiteIdentity siteCounts) :
    (selectedSiteOfIndependent siteCounts identity).kind = identity.kind := rfl

/-- The exact numeric slot is recovered, not merely the owner and kind. -/
@[simp] theorem selectedSiteOfIndependent_slot {V : Type*} [DecidableEq V] [Fintype V]
    (siteCounts : IndependentSiteCounts V)
    (identity : IndependentSiteIdentity siteCounts) :
    (selectedSiteOfIndependent siteCounts identity).slot = identity.slot.val := rfl

@[simp] theorem selectedSiteOfIndependent_inventory {V : Type*} [DecidableEq V] [Fintype V]
    (siteCounts : IndependentSiteCounts V)
    (identity : IndependentSiteIdentity siteCounts) :
    (selectedSiteOfIndependent siteCounts identity).inventory = siteCounts := rfl

/-- The actual independent-site adapter establishes the visible inventory binding explicitly. -/
@[simp] theorem selectedSiteOfIndependent_matchesInventory {V : Type*} [DecidableEq V] [Fintype V]
    (siteCounts : IndependentSiteCounts V)
    (identity : IndependentSiteIdentity siteCounts) :
    (selectedSiteOfIndependent siteCounts identity).MatchesInventory siteCounts := rfl

/-- Genuine identity recovery: selected-site references built from actual independent site
identities are equal exactly when the identities are equal.  Because the numeric slot is part of
the recovered identity, choosing one of two lone pairs at the same owner is not collapsed to an
owner/kind pair. -/
theorem selectedSiteOfIndependent_injective {V : Type*} [DecidableEq V] [Fintype V]
    (siteCounts : IndependentSiteCounts V) :
    Function.Injective (selectedSiteOfIndependent siteCounts) := by
  intro first second equal
  have ownerEq := congrArg SelectedElectronicSite.owner equal
  have kindEq := congrArg SelectedElectronicSite.kind equal
  have slotEq := congrArg SelectedElectronicSite.slot equal
  cases first with
  | mk owner kind slot =>
      cases second with
      | mk owner' kind' slot' =>
          simp only [selectedSiteOfIndependent] at ownerEq kindEq slotEq
          cases ownerEq
          cases kindEq
          cases Fin.ext slotEq
          rfl

/-- The P-94 torsion reference frame underlying the annotation adapters.  The selected ordered
axis path and the two participant identities are retained, the selected frame's supplied torsion
angle is copied literally, and explicitly selected counted sites are attached when supplied.
Bounds are the existing P-94 participant-boundedness and a path bound against the real source
atom count. -/
def p94TorsionReferenceFrame (e : V ≃ Fin n) (record : P94TorsionEvidence)
    (pathBounded : TorsionAxisPathSourceBounded n record.unit.atoms)
    (frontBounded : TorsionParticipantSourceBounded n record.frame.front)
    (rearBounded : TorsionParticipantSourceBounded n record.frame.rear)
    (frontSite? : Option (SelectedElectronicSite V) := none)
    (rearSite? : Option (SelectedElectronicSite V) := none) :
    TorsionReferenceFrame V where
  axisPath := sourceAtomListOfIndices e record.unit.atoms pathBounded
  front := sourceTorsionParticipant e record.frame.front frontBounded
  rear := sourceTorsionParticipant e record.frame.rear rearBounded
  angle? := some record.frame.angle
  frontSite? := frontSite?
  rearSite? := rearSite?

/-- Adapt the current P-94 torsion-evidence shape.  This legacy adapter leaves the explicit site
selection absent: the participant identity is retained, but no slot is invented. -/
def p94TorsionEvidenceToFrame (e : V ≃ Fin n) (record : P94TorsionEvidence)
    (pathBounded : TorsionAxisPathSourceBounded n record.unit.atoms)
    (frontBounded : TorsionParticipantSourceBounded n record.frame.front)
    (rearBounded : TorsionParticipantSourceBounded n record.frame.rear) :
    FrameAnnotation V :=
  .torsionReference
    (p94TorsionReferenceFrame e record pathBounded frontBounded rearBounded)

/-- Adapt the current P-94 torsion-evidence shape with explicit counted-site selections.  This
distinguishes, for example, two lone pairs at the same owner by slot.  The caller-supplied
compatibility evidence is checked by `p94TorsionEvidenceToFrameWithSites_valid`, which proves the
underlying frame valid; no validity proof is manufactured inside the annotation. -/
def p94TorsionEvidenceToFrameWithSites (e : V ≃ Fin n) (record : P94TorsionEvidence)
    (pathBounded : TorsionAxisPathSourceBounded n record.unit.atoms)
    (frontBounded : TorsionParticipantSourceBounded n record.frame.front)
    (rearBounded : TorsionParticipantSourceBounded n record.frame.rear)
    (frontSite? : Option (SelectedElectronicSite V))
    (rearSite? : Option (SelectedElectronicSite V)) :
    FrameAnnotation V :=
  .torsionReference
    (p94TorsionReferenceFrame e record pathBounded frontBounded rearBounded
      frontSite? rearSite?)

/-- The with-sites P-94 adapter produces a valid torsion reference frame: every supplied site is
checked against the selected legacy participant. -/
theorem p94TorsionEvidenceToFrameWithSites_valid (e : V ≃ Fin n)
    (record : P94TorsionEvidence)
    (pathBounded : TorsionAxisPathSourceBounded n record.unit.atoms)
    (frontBounded : TorsionParticipantSourceBounded n record.frame.front)
    (rearBounded : TorsionParticipantSourceBounded n record.frame.rear)
    (frontSite? : Option (SelectedElectronicSite V))
    (rearSite? : Option (SelectedElectronicSite V))
    (frontCompatible : ∀ site, frontSite? = some site →
      site.CompatibleWith
        (sourceTorsionParticipant e record.frame.front frontBounded))
    (rearCompatible : ∀ site, rearSite? = some site →
      site.CompatibleWith
        (sourceTorsionParticipant e record.frame.rear rearBounded)) :
    (p94TorsionReferenceFrame e record pathBounded frontBounded rearBounded
      frontSite? rearSite?).Valid := by
  simp only [TorsionReferenceFrame.Valid]
  constructor
  · intro site member
    exact frontCompatible site member
  · intro site member
    exact rearCompatible site member

/-- The legacy P-94 adapter leaves the front selection absent; it does not invent slot zero. -/
@[simp] theorem p94TorsionEvidenceToFrame_frontSite?_none (e : V ≃ Fin n)
    (record : P94TorsionEvidence)
    (pathBounded : TorsionAxisPathSourceBounded n record.unit.atoms)
    (frontBounded : TorsionParticipantSourceBounded n record.frame.front)
    (rearBounded : TorsionParticipantSourceBounded n record.frame.rear) :
    (p94TorsionEvidenceToFrame (V := V) e record pathBounded frontBounded
      rearBounded).frontSite? = none := rfl

/-- The legacy P-94 adapter leaves the rear selection absent; it does not invent slot zero. -/
@[simp] theorem p94TorsionEvidenceToFrame_rearSite?_none (e : V ≃ Fin n)
    (record : P94TorsionEvidence)
    (pathBounded : TorsionAxisPathSourceBounded n record.unit.atoms)
    (frontBounded : TorsionParticipantSourceBounded n record.frame.front)
    (rearBounded : TorsionParticipantSourceBounded n record.frame.rear) :
    (p94TorsionEvidenceToFrame (V := V) e record pathBounded frontBounded
      rearBounded).rearSite? = none := rfl

/-- Adapt one bounded P-94 conformation unit's ordered ring traversal. -/
def p94ConformationUnitToRingTraversal (e : V ≃ Fin n)
    (unit : P94ConformationUnit) (bounded : TorsionAxisPathSourceBounded n unit.atoms) :
    FrameAnnotation V :=
  .ringTraversal { ringAtoms := sourceAtomListOfIndices e unit.atoms bounded }

/-- Adapt an existing physical ring-plane observation.  The actual real reference plane is copied
literally; the ordered ring support and the two substituted positions are mapped from source
`Fin molecule.atomCount` indices by `e.symm`, so no out-of-range atom can be fabricated.  The
separate `CoplanarRingEvidence` is neither assumed nor folded into the annotation: the chosen
plane and the physical coplanarity claim stay distinct. -/
def physicalRingPlaneObservationToFrame {molecule : SemanticMolecule}
    (e : V ≃ Fin molecule.atomCount)
    (observation : PhysicalPlaneEvidence.PhysicalRingPlaneObservation molecule) :
    FrameAnnotation V :=
  .realRingPlane
    { plane := observation.plane
      ringAtoms := observation.ringAtoms.map e.symm
      firstSubstituent := e.symm observation.firstSubstituent
      secondSubstituent := e.symm observation.secondSubstituent
      firstAttachment? := none
      secondAttachment? := none }

/-- The real ring-plane adapter retains the supplied real plane literally. -/
@[simp] theorem physicalRingPlaneObservationToFrame_realPlane? {molecule : SemanticMolecule}
    (e : V ≃ Fin molecule.atomCount)
    (observation : PhysicalPlaneEvidence.PhysicalRingPlaneObservation molecule) :
    (physicalRingPlaneObservationToFrame (V := V) e observation).realPlane? =
      some observation.plane := rfl

/-- The real ring-plane adapter retains the ordered ring support, mapped from source indices. -/
@[simp] theorem physicalRingPlaneObservationToFrame_ringAtoms? {molecule : SemanticMolecule}
    (e : V ≃ Fin molecule.atomCount)
    (observation : PhysicalPlaneEvidence.PhysicalRingPlaneObservation molecule) :
    (physicalRingPlaneObservationToFrame (V := V) e observation).ringAtoms? =
      some (observation.ringAtoms.map e.symm) := rfl

/-- Mapping the adapted ordered ring support back through the same equivalence recovers exactly
the original source-indexed support, in order. -/
theorem map_physicalRingPlaneObservation_ringAtoms {molecule : SemanticMolecule}
    (e : V ≃ Fin molecule.atomCount)
    (observation : PhysicalPlaneEvidence.PhysicalRingPlaneObservation molecule) :
    (observation.ringAtoms.map e.symm).map e = observation.ringAtoms := by
  rw [List.map_map]
  simp [Function.comp_def]

/-- The legacy physical ring-plane adapter leaves the first source attachment absent.  It does not
invent a ring position or an interaction occurrence. -/
@[simp] theorem physicalRingPlaneObservationToFrame_firstAttachment?_none
    {molecule : SemanticMolecule} (e : V ≃ Fin molecule.atomCount)
    (observation : PhysicalPlaneEvidence.PhysicalRingPlaneObservation molecule) :
    (physicalRingPlaneObservationToFrame (V := V) e observation).realRingPlaneFirstAttachment? =
      none := rfl

/-- The legacy physical ring-plane adapter leaves the second source attachment absent.  It does
not invent a ring position or an interaction occurrence. -/
@[simp] theorem physicalRingPlaneObservationToFrame_secondAttachment?_none
    {molecule : SemanticMolecule} (e : V ≃ Fin molecule.atomCount)
    (observation : PhysicalPlaneEvidence.PhysicalRingPlaneObservation molecule) :
    (physicalRingPlaneObservationToFrame (V := V) e observation).realRingPlaneSecondAttachment? =
      none := rfl

/-! ### Actual source interaction occurrences

The source interaction occurrence index retained by a `RealRingPlaneAttachment` is chosen from the
actual `interaction_mem` witness against the common source molecule.  The choice is a genuine
position of the common interaction list: the bound is a theorem derived from the membership
proof, never a stored assumption, and the lookup at that position is the original interaction. -/

section SourceInteractionOccurrence

/-- The actual occurrence index of a source interaction in the common molecule's interaction
list.  It is obtained from the supplied membership proof, so it denotes a real occurrence; no
position is fabricated and no repeated occurrence is removed. -/
noncomputable def sourceInteractionIndex {molecule : SemanticMolecule}
    (interaction : SemanticInteraction) (member : interaction ∈ molecule.interactions) : Nat :=
  (List.mem_iff_getElem.mp member).choose

/-- The chosen occurrence index is a real position of the common interaction list.  The bound is
derived from the input membership proof, not assumed. -/
theorem sourceInteractionIndex_lt {molecule : SemanticMolecule}
    (interaction : SemanticInteraction) (member : interaction ∈ molecule.interactions) :
    sourceInteractionIndex interaction member < molecule.interactions.length :=
  (List.mem_iff_getElem.mp member).choose_spec.choose

/-- Looking up the chosen occurrence index returns exactly the interaction supplied by the
membership witness. -/
theorem sourceInteractionIndex_get {molecule : SemanticMolecule}
    (interaction : SemanticInteraction) (member : interaction ∈ molecule.interactions) :
    molecule.interactions[sourceInteractionIndex interaction member]'
      (sourceInteractionIndex_lt interaction member) = interaction :=
  (List.mem_iff_getElem.mp member).choose_spec.choose_spec

end SourceInteractionOccurrence

/-- The actual real ring-plane record of a closed-ring observation, retaining both selected
source attachments.  Factored out so that the legacy `physicalRingPlaneObservationToFrame` API
keeps its signature while the closed-ring adapter is a thin wrapper. -/
noncomputable def physicalClosedRingObservationToRealRingPlaneFrame {molecule : SemanticMolecule}
    (e : V ≃ Fin molecule.atomCount)
    (observation : PhysicalPlaneEvidence.PhysicalClosedRingObservation molecule) :
    RealRingPlaneFrame V :=
  { plane := observation.observation.plane
    ringAtoms := observation.observation.ringAtoms.map e.symm
    firstSubstituent := e.symm observation.observation.firstSubstituent
    secondSubstituent := e.symm observation.observation.secondSubstituent
    firstAttachment? := some
      { ringPosition := e.symm observation.firstAttachment.ringPosition
        interactionIndex := sourceInteractionIndex observation.firstAttachment.interaction
          observation.firstAttachment.interaction_mem }
    secondAttachment? := some
      { ringPosition := e.symm observation.secondAttachment.ringPosition
        interactionIndex := sourceInteractionIndex observation.secondAttachment.interaction
          observation.secondAttachment.interaction_mem } }

/-- Adapt an existing physical closed-ring observation.  The actual real plane, ordered ring
support, both substituents, both selected attachment ring positions and both actual source
interaction occurrence indices are retained.  Each occurrence index is chosen from the actual
`interaction_mem` witness (via `List.mem_iff_getElem`), so it is a real occurrence in the common
source graph; no preimage is assumed, no occurrence is fabricated and no duplicate is dropped. -/
noncomputable def physicalClosedRingObservationToFrame {molecule : SemanticMolecule}
    (e : V ≃ Fin molecule.atomCount)
    (observation : PhysicalPlaneEvidence.PhysicalClosedRingObservation molecule) :
    FrameAnnotation V :=
  .realRingPlane (physicalClosedRingObservationToRealRingPlaneFrame e observation)

/-- The closed-ring adapter retains the supplied real plane literally. -/
@[simp] theorem physicalClosedRingObservationToFrame_realPlane? {molecule : SemanticMolecule}
    (e : V ≃ Fin molecule.atomCount)
    (observation : PhysicalPlaneEvidence.PhysicalClosedRingObservation molecule) :
    (physicalClosedRingObservationToFrame (V := V) e observation).realPlane? =
      some observation.observation.plane := rfl

/-- The closed-ring adapter retains the ordered ring support, mapped from source indices. -/
@[simp] theorem physicalClosedRingObservationToFrame_ringAtoms? {molecule : SemanticMolecule}
    (e : V ≃ Fin molecule.atomCount)
    (observation : PhysicalPlaneEvidence.PhysicalClosedRingObservation molecule) :
    (physicalClosedRingObservationToFrame (V := V) e observation).ringAtoms? =
      some (observation.observation.ringAtoms.map e.symm) := rfl

/-- The closed-ring adapter retains the first substituent reference. -/
@[simp] theorem physicalClosedRingObservationToFrame_firstSubstituent?
    {molecule : SemanticMolecule} (e : V ≃ Fin molecule.atomCount)
    (observation : PhysicalPlaneEvidence.PhysicalClosedRingObservation molecule) :
    (physicalClosedRingObservationToFrame (V := V) e observation).realRingPlaneFirstSubstituent? =
      some (e.symm observation.observation.firstSubstituent) := rfl

/-- The closed-ring adapter retains the second substituent reference. -/
@[simp] theorem physicalClosedRingObservationToFrame_secondSubstituent?
    {molecule : SemanticMolecule} (e : V ≃ Fin molecule.atomCount)
    (observation : PhysicalPlaneEvidence.PhysicalClosedRingObservation molecule) :
    (physicalClosedRingObservationToFrame (V := V) e observation).realRingPlaneSecondSubstituent? =
      some (e.symm observation.observation.secondSubstituent) := rfl

/-- The closed-ring adapter retains the first selected attachment: its ring position and the
actual occurrence index of its source interaction. -/
@[simp] theorem physicalClosedRingObservationToFrame_firstAttachment?
    {molecule : SemanticMolecule} (e : V ≃ Fin molecule.atomCount)
    (observation : PhysicalPlaneEvidence.PhysicalClosedRingObservation molecule) :
    (physicalClosedRingObservationToFrame (V := V) e observation).realRingPlaneFirstAttachment? =
      some
        { ringPosition := e.symm observation.firstAttachment.ringPosition
          interactionIndex := sourceInteractionIndex observation.firstAttachment.interaction
            observation.firstAttachment.interaction_mem } := rfl

/-- The closed-ring adapter retains the second selected attachment: its ring position and the
actual occurrence index of its source interaction. -/
@[simp] theorem physicalClosedRingObservationToFrame_secondAttachment?
    {molecule : SemanticMolecule} (e : V ≃ Fin molecule.atomCount)
    (observation : PhysicalPlaneEvidence.PhysicalClosedRingObservation molecule) :
    (physicalClosedRingObservationToFrame (V := V) e observation).realRingPlaneSecondAttachment? =
      some
        { ringPosition := e.symm observation.secondAttachment.ringPosition
          interactionIndex := sourceInteractionIndex observation.secondAttachment.interaction
            observation.secondAttachment.interaction_mem } := rfl

/-- The first stored occurrence index is a real position in the common source interaction list;
the bound is derived from the observation's actual membership witness. -/
theorem physicalClosedRingObservationToFrame_firstAttachment_interactionIndex_lt
    {molecule : SemanticMolecule} (_e : V ≃ Fin molecule.atomCount)
    (observation : PhysicalPlaneEvidence.PhysicalClosedRingObservation molecule) :
    sourceInteractionIndex observation.firstAttachment.interaction
        observation.firstAttachment.interaction_mem <
      molecule.interactions.length :=
  sourceInteractionIndex_lt _ _

/-- Looking up the first stored occurrence index returns exactly the original source
interaction. -/
theorem physicalClosedRingObservationToFrame_firstAttachment_lookup
    {molecule : SemanticMolecule} (_e : V ≃ Fin molecule.atomCount)
    (observation : PhysicalPlaneEvidence.PhysicalClosedRingObservation molecule) :
    molecule.interactions[
        sourceInteractionIndex observation.firstAttachment.interaction
          observation.firstAttachment.interaction_mem]'
        (sourceInteractionIndex_lt _ _) =
      observation.firstAttachment.interaction :=
  sourceInteractionIndex_get _ _

/-- The second stored occurrence index is a real position in the common source interaction list;
the bound is derived from the observation's actual membership witness. -/
theorem physicalClosedRingObservationToFrame_secondAttachment_interactionIndex_lt
    {molecule : SemanticMolecule} (_e : V ≃ Fin molecule.atomCount)
    (observation : PhysicalPlaneEvidence.PhysicalClosedRingObservation molecule) :
    sourceInteractionIndex observation.secondAttachment.interaction
        observation.secondAttachment.interaction_mem <
      molecule.interactions.length :=
  sourceInteractionIndex_lt _ _

/-- Looking up the second stored occurrence index returns exactly the original source
interaction. -/
theorem physicalClosedRingObservationToFrame_secondAttachment_lookup
    {molecule : SemanticMolecule} (_e : V ≃ Fin molecule.atomCount)
    (observation : PhysicalPlaneEvidence.PhysicalClosedRingObservation molecule) :
    molecule.interactions[
        sourceInteractionIndex observation.secondAttachment.interaction
          observation.secondAttachment.interaction_mem]'
        (sourceInteractionIndex_lt _ _) =
      observation.secondAttachment.interaction :=
  sourceInteractionIndex_get _ _

/-- Exact first selected ring-position recovery: mapping the retained attachment ring position
back through the same equivalence returns the observation's selected ring position. -/
@[simp] theorem physicalClosedRingObservationToFrame_firstAttachment_ringPosition
    {molecule : SemanticMolecule} (e : V ≃ Fin molecule.atomCount)
    (observation : PhysicalPlaneEvidence.PhysicalClosedRingObservation molecule) :
    (physicalClosedRingObservationToFrame (V := V) e observation).realRingPlaneFirstAttachment?.map
        (fun attachment => e attachment.ringPosition) =
      some observation.firstAttachment.ringPosition := by
  change some (e (e.symm observation.firstAttachment.ringPosition)) =
    some observation.firstAttachment.ringPosition
  simp

/-- Exact second selected ring-position recovery: mapping the retained attachment ring position
back through the same equivalence returns the observation's selected ring position. -/
@[simp] theorem physicalClosedRingObservationToFrame_secondAttachment_ringPosition
    {molecule : SemanticMolecule} (e : V ≃ Fin molecule.atomCount)
    (observation : PhysicalPlaneEvidence.PhysicalClosedRingObservation molecule) :
    (physicalClosedRingObservationToFrame (V := V) e observation).realRingPlaneSecondAttachment?.map
        (fun attachment => e attachment.ringPosition) =
      some observation.secondAttachment.ringPosition := by
  change some (e (e.symm observation.secondAttachment.ringPosition)) =
    some observation.secondAttachment.ringPosition
  simp

/-- Full generic data recovery from the closed-ring adapter: the real plane, ordered ring support
and both substituent references are exactly the mapped observation fields. -/
theorem physicalClosedRingObservationToFrame_genericRecovery
    {molecule : SemanticMolecule} (e : V ≃ Fin molecule.atomCount)
    (observation : PhysicalPlaneEvidence.PhysicalClosedRingObservation molecule) :
    (physicalClosedRingObservationToFrame (V := V) e observation).realPlane? =
        some observation.observation.plane ∧
      (physicalClosedRingObservationToFrame (V := V) e observation).ringAtoms? =
        some (observation.observation.ringAtoms.map e.symm) ∧
      (physicalClosedRingObservationToFrame (V := V) e observation).realRingPlaneFirstSubstituent? =
        some (e.symm observation.observation.firstSubstituent) ∧
      (physicalClosedRingObservationToFrame (V := V) e observation).realRingPlaneSecondSubstituent? =
        some (e.symm observation.observation.secondSubstituent) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### Decoding from an actual frame and the common source state

The decoder below reads a `RealRingPlaneFrame` together with the common source molecule and the
common conformation.  It stores no original-observation payload: all retained physical data comes
from the frame, while the certificate supplies only propositional source-graph facts. -/

namespace RealRingPlaneFrame

/-- Validity of one retained source attachment relative to a common source molecule and atom
correspondence.  Every fact is about the frame and the common source graph; no original
observation is referenced.  The occurrence bound is kept separate because
`RealRingPlaneAttachment` stores the index as data. -/
structure SourceAttachmentValid {molecule : SemanticMolecule} {V : Type*}
    (e : V ≃ Fin molecule.atomCount) (ringAtoms : List V)
    (attachment : RealRingPlaneAttachment V) (substituent : V) : Prop where
  ringPosition_mem : e attachment.ringPosition ∈ ringAtoms.map e
  substituent_not_ring : e substituent ∉ ringAtoms.map e
  interactionIndex_lt : attachment.interactionIndex < molecule.interactions.length
  interaction_isRingBond :
    PhysicalPlaneEvidence.IsRingBond
      (molecule.interactions[attachment.interactionIndex]'interactionIndex_lt).kind
  binaryParticipants :
    PhysicalPlaneEvidence.HasBinaryParticipants
      (e attachment.ringPosition).val (e substituent).val
      (molecule.interactions[attachment.interactionIndex]'interactionIndex_lt)

/-- Explicit frame-validity certificate for decoding a complete
`PhysicalClosedRingObservation` from a `RealRingPlaneFrame` and the common source molecule.

It supplies only the propositional facts that the frame does not retain as data: an actual source
closed ring agreeing with the frame's ordered support, distinctness and non-ring placement of the
two substituents, and validity of both optional attachment references.  The two attachment
records named here are the frame's actual optional values (witnessed by the equality fields), so
the selected ring position and occurrence index are read from the frame, not fabricated.  No
equality with any original observation is assumed. -/
structure ClosedRingCertificate {molecule : SemanticMolecule} {V : Type*}
    (e : V ≃ Fin molecule.atomCount) (frame : RealRingPlaneFrame V) where
  ring : PhysicalPlaneEvidence.SourceClosedRing molecule
  ring_matches : ring.ringAtoms = frame.ringAtoms.map e
  substituents_distinct : e frame.firstSubstituent ≠ e frame.secondSubstituent
  firstSubstituent_not_ring : e frame.firstSubstituent ∉ frame.ringAtoms.map e
  secondSubstituent_not_ring : e frame.secondSubstituent ∉ frame.ringAtoms.map e
  firstAttachment : RealRingPlaneAttachment V
  firstAttachment_eq : frame.firstAttachment? = some firstAttachment
  firstAttachmentValid :
    SourceAttachmentValid e frame.ringAtoms firstAttachment frame.firstSubstituent
  secondAttachment : RealRingPlaneAttachment V
  secondAttachment_eq : frame.secondAttachment? = some secondAttachment
  secondAttachmentValid :
    SourceAttachmentValid e frame.ringAtoms secondAttachment frame.secondSubstituent

/-- Decode a complete physical closed-ring observation from an actual real ring-plane frame, the
common source molecule and the common conformation, under the explicit frame-validity
certificate.  Both attachment interactions are the actual lookups at the frame's retained
occurrence indices. -/
def toPhysicalClosedRingObservation {molecule : SemanticMolecule} {V : Type*}
    (e : V ≃ Fin molecule.atomCount)
    (conformation : MolecularConformation (Fin molecule.atomCount))
    (frame : RealRingPlaneFrame V)
    (certificate : ClosedRingCertificate e frame) :
    PhysicalPlaneEvidence.PhysicalClosedRingObservation molecule where
  observation :=
    { conformation := conformation
      plane := frame.plane
      ringAtoms := frame.ringAtoms.map e
      ringAtoms_nodup := by
        rw [← certificate.ring_matches]
        exact certificate.ring.nodup
      ringAtoms_nonempty := by
        rw [← certificate.ring_matches]
        exact List.ne_nil_of_length_pos
          (Nat.lt_of_lt_of_le (by decide : 0 < 3) certificate.ring.length_ge_three)
      firstSubstituent := e frame.firstSubstituent
      secondSubstituent := e frame.secondSubstituent
      substituents_distinct := certificate.substituents_distinct
      firstSubstituent_not_ring := certificate.firstSubstituent_not_ring
      secondSubstituent_not_ring := certificate.secondSubstituent_not_ring }
  ring := certificate.ring
  ring_matches := certificate.ring_matches
  firstAttachment :=
    { ringPosition := e certificate.firstAttachment.ringPosition
      ringPosition_mem := by
        rw [certificate.ring_matches]
        exact certificate.firstAttachmentValid.ringPosition_mem
      substituent_not_ring := by
        show e frame.firstSubstituent ∉ certificate.ring.ringAtoms
        rw [certificate.ring_matches]
        exact certificate.firstAttachmentValid.substituent_not_ring
      interaction :=
        molecule.interactions[certificate.firstAttachment.interactionIndex]'
          certificate.firstAttachmentValid.interactionIndex_lt
      interaction_mem := List.getElem_mem _
      interaction_isRingBond := certificate.firstAttachmentValid.interaction_isRingBond
      binaryParticipants := certificate.firstAttachmentValid.binaryParticipants }
  secondAttachment :=
    { ringPosition := e certificate.secondAttachment.ringPosition
      ringPosition_mem := by
        rw [certificate.ring_matches]
        exact certificate.secondAttachmentValid.ringPosition_mem
      substituent_not_ring := by
        show e frame.secondSubstituent ∉ certificate.ring.ringAtoms
        rw [certificate.ring_matches]
        exact certificate.secondAttachmentValid.substituent_not_ring
      interaction :=
        molecule.interactions[certificate.secondAttachment.interactionIndex]'
          certificate.secondAttachmentValid.interactionIndex_lt
      interaction_mem := List.getElem_mem _
      interaction_isRingBond := certificate.secondAttachmentValid.interaction_isRingBond
      binaryParticipants := certificate.secondAttachmentValid.binaryParticipants }

/-- The decoded conformation is exactly the supplied common conformation. -/
@[simp] theorem toPhysicalClosedRingObservation_conformation {molecule : SemanticMolecule}
    {V : Type*} (e : V ≃ Fin molecule.atomCount)
    (conformation : MolecularConformation (Fin molecule.atomCount))
    (frame : RealRingPlaneFrame V) (certificate : ClosedRingCertificate e frame) :
    (toPhysicalClosedRingObservation e conformation frame certificate).observation.conformation =
      conformation := rfl

/-- The decoded real reference plane is exactly the frame's retained plane. -/
@[simp] theorem toPhysicalClosedRingObservation_plane {molecule : SemanticMolecule}
    {V : Type*} (e : V ≃ Fin molecule.atomCount)
    (conformation : MolecularConformation (Fin molecule.atomCount))
    (frame : RealRingPlaneFrame V) (certificate : ClosedRingCertificate e frame) :
    (toPhysicalClosedRingObservation e conformation frame certificate).observation.plane =
      frame.plane := rfl

/-- The decoded ordered ring support is exactly the frame's ordered support mapped by `e`. -/
@[simp] theorem toPhysicalClosedRingObservation_ringAtoms {molecule : SemanticMolecule}
    {V : Type*} (e : V ≃ Fin molecule.atomCount)
    (conformation : MolecularConformation (Fin molecule.atomCount))
    (frame : RealRingPlaneFrame V) (certificate : ClosedRingCertificate e frame) :
    (toPhysicalClosedRingObservation e conformation frame certificate).observation.ringAtoms =
      frame.ringAtoms.map e := rfl

/-- The decoded first substituent is exactly the frame's reference mapped by `e`. -/
@[simp] theorem toPhysicalClosedRingObservation_firstSubstituent
    {molecule : SemanticMolecule} {V : Type*} (e : V ≃ Fin molecule.atomCount)
    (conformation : MolecularConformation (Fin molecule.atomCount))
    (frame : RealRingPlaneFrame V) (certificate : ClosedRingCertificate e frame) :
    (toPhysicalClosedRingObservation e conformation frame certificate).observation.firstSubstituent =
      e frame.firstSubstituent := rfl

/-- The decoded second substituent is exactly the frame's reference mapped by `e`. -/
@[simp] theorem toPhysicalClosedRingObservation_secondSubstituent
    {molecule : SemanticMolecule} {V : Type*} (e : V ≃ Fin molecule.atomCount)
    (conformation : MolecularConformation (Fin molecule.atomCount))
    (frame : RealRingPlaneFrame V) (certificate : ClosedRingCertificate e frame) :
    (toPhysicalClosedRingObservation e conformation frame certificate).observation.secondSubstituent =
      e frame.secondSubstituent := rfl

/-- The decoded source closed ring is exactly the certificate's actual source ring. -/
@[simp] theorem toPhysicalClosedRingObservation_ring {molecule : SemanticMolecule}
    {V : Type*} (e : V ≃ Fin molecule.atomCount)
    (conformation : MolecularConformation (Fin molecule.atomCount))
    (frame : RealRingPlaneFrame V) (certificate : ClosedRingCertificate e frame) :
    (toPhysicalClosedRingObservation e conformation frame certificate).ring =
      certificate.ring := rfl

/-- Exact selected first ring-position recovery from the frame's retained attachment. -/
@[simp] theorem toPhysicalClosedRingObservation_firstAttachment_ringPosition
    {molecule : SemanticMolecule} {V : Type*} (e : V ≃ Fin molecule.atomCount)
    (conformation : MolecularConformation (Fin molecule.atomCount))
    (frame : RealRingPlaneFrame V) (certificate : ClosedRingCertificate e frame) :
    (toPhysicalClosedRingObservation e conformation frame certificate).firstAttachment.ringPosition =
      e certificate.firstAttachment.ringPosition := rfl

/-- Exact selected first interaction lookup recovery: the decoded interaction is the actual
lookup at the frame's retained occurrence index. -/
@[simp] theorem toPhysicalClosedRingObservation_firstAttachment_interaction
    {molecule : SemanticMolecule} {V : Type*} (e : V ≃ Fin molecule.atomCount)
    (conformation : MolecularConformation (Fin molecule.atomCount))
    (frame : RealRingPlaneFrame V) (certificate : ClosedRingCertificate e frame) :
    (toPhysicalClosedRingObservation e conformation frame certificate).firstAttachment.interaction =
      molecule.interactions[certificate.firstAttachment.interactionIndex]'
        certificate.firstAttachmentValid.interactionIndex_lt := rfl

/-- Exact selected second ring-position recovery from the frame's retained attachment. -/
@[simp] theorem toPhysicalClosedRingObservation_secondAttachment_ringPosition
    {molecule : SemanticMolecule} {V : Type*} (e : V ≃ Fin molecule.atomCount)
    (conformation : MolecularConformation (Fin molecule.atomCount))
    (frame : RealRingPlaneFrame V) (certificate : ClosedRingCertificate e frame) :
    (toPhysicalClosedRingObservation e conformation frame certificate).secondAttachment.ringPosition =
      e certificate.secondAttachment.ringPosition := rfl

/-- Exact selected second interaction lookup recovery: the decoded interaction is the actual
lookup at the frame's retained occurrence index. -/
@[simp] theorem toPhysicalClosedRingObservation_secondAttachment_interaction
    {molecule : SemanticMolecule} {V : Type*} (e : V ≃ Fin molecule.atomCount)
    (conformation : MolecularConformation (Fin molecule.atomCount))
    (frame : RealRingPlaneFrame V) (certificate : ClosedRingCertificate e frame) :
    (toPhysicalClosedRingObservation e conformation frame certificate).secondAttachment.interaction =
      molecule.interactions[certificate.secondAttachment.interactionIndex]'
        certificate.secondAttachmentValid.interactionIndex_lt := rfl

end RealRingPlaneFrame

/-- The certificate induced by an actual closed-ring observation for its adapter frame.  It is
constructed from the observation's own source ring and attachment witnesses, never assumed; the
frame itself retains no observation payload. -/
noncomputable def physicalClosedRingObservationToFrameCertificate {molecule : SemanticMolecule}
    (e : V ≃ Fin molecule.atomCount)
    (observation : PhysicalPlaneEvidence.PhysicalClosedRingObservation molecule) :
    RealRingPlaneFrame.ClosedRingCertificate e
      (physicalClosedRingObservationToRealRingPlaneFrame e observation) where
  ring := observation.ring
  ring_matches := by
    show observation.ring.ringAtoms =
      (observation.observation.ringAtoms.map e.symm).map e
    rw [observation.ring_matches, List.map_map]
    simp [Function.comp_def]
  substituents_distinct := by
    show e (e.symm observation.observation.firstSubstituent) ≠
      e (e.symm observation.observation.secondSubstituent)
    simpa using observation.observation.substituents_distinct
  firstSubstituent_not_ring := by
    show e (e.symm observation.observation.firstSubstituent) ∉
      (observation.observation.ringAtoms.map e.symm).map e
    rw [List.map_map]
    simpa [Function.comp_def] using observation.observation.firstSubstituent_not_ring
  secondSubstituent_not_ring := by
    show e (e.symm observation.observation.secondSubstituent) ∉
      (observation.observation.ringAtoms.map e.symm).map e
    rw [List.map_map]
    simpa [Function.comp_def] using observation.observation.secondSubstituent_not_ring
  firstAttachment :=
    { ringPosition := e.symm observation.firstAttachment.ringPosition
      interactionIndex := sourceInteractionIndex observation.firstAttachment.interaction
        observation.firstAttachment.interaction_mem }
  firstAttachment_eq := rfl
  firstAttachmentValid :=
    { ringPosition_mem := by
        show e (e.symm observation.firstAttachment.ringPosition) ∈
          (observation.observation.ringAtoms.map e.symm).map e
        rw [List.map_map]
        simpa [Function.comp_def] using
          observation.firstAttachment_ringPosition_mem_observation
      substituent_not_ring := by
        show e (e.symm observation.observation.firstSubstituent) ∉
          (observation.observation.ringAtoms.map e.symm).map e
        rw [List.map_map]
        simpa [Function.comp_def] using observation.observation.firstSubstituent_not_ring
      interactionIndex_lt := sourceInteractionIndex_lt _ _
      interaction_isRingBond := by
        rw [sourceInteractionIndex_get]
        exact observation.firstAttachment.interaction_isRingBond
      binaryParticipants := by
        rw [sourceInteractionIndex_get]
        simpa [physicalClosedRingObservationToRealRingPlaneFrame] using
          observation.firstAttachment.binaryParticipants }
  secondAttachment :=
    { ringPosition := e.symm observation.secondAttachment.ringPosition
      interactionIndex := sourceInteractionIndex observation.secondAttachment.interaction
        observation.secondAttachment.interaction_mem }
  secondAttachment_eq := rfl
  secondAttachmentValid :=
    { ringPosition_mem := by
        show e (e.symm observation.secondAttachment.ringPosition) ∈
          (observation.observation.ringAtoms.map e.symm).map e
        rw [List.map_map]
        simpa [Function.comp_def] using
          observation.secondAttachment_ringPosition_mem_observation
      substituent_not_ring := by
        show e (e.symm observation.observation.secondSubstituent) ∉
          (observation.observation.ringAtoms.map e.symm).map e
        rw [List.map_map]
        simpa [Function.comp_def] using observation.observation.secondSubstituent_not_ring
      interactionIndex_lt := sourceInteractionIndex_lt _ _
      interaction_isRingBond := by
        rw [sourceInteractionIndex_get]
        exact observation.secondAttachment.interaction_isRingBond
      binaryParticipants := by
        rw [sourceInteractionIndex_get]
        simpa [physicalClosedRingObservationToRealRingPlaneFrame] using
          observation.secondAttachment.binaryParticipants }

/-- Fieldwise round-trip: decoding the adapter frame under its induced certificate returns the
observation's own selected ring positions and actual interactions, and its generic real
plane/ring/substituent data. -/
@[simp] theorem physicalClosedRingObservationToFrame_ringAtoms_recovery
    {molecule : SemanticMolecule} (e : V ≃ Fin molecule.atomCount)
    (observation : PhysicalPlaneEvidence.PhysicalClosedRingObservation molecule) :
    (RealRingPlaneFrame.toPhysicalClosedRingObservation e observation.observation.conformation
      (physicalClosedRingObservationToRealRingPlaneFrame e observation)
      (physicalClosedRingObservationToFrameCertificate e observation)).observation.ringAtoms =
      observation.observation.ringAtoms := by
  rw [RealRingPlaneFrame.toPhysicalClosedRingObservation_ringAtoms]
  show List.map e (observation.observation.ringAtoms.map e.symm) =
    observation.observation.ringAtoms
  rw [List.map_map]
  simp [Function.comp_def]

/-- Fieldwise round-trip for the first substituent. -/
@[simp] theorem physicalClosedRingObservationToFrame_firstSubstituent_recovery
    {molecule : SemanticMolecule} (e : V ≃ Fin molecule.atomCount)
    (observation : PhysicalPlaneEvidence.PhysicalClosedRingObservation molecule) :
    (RealRingPlaneFrame.toPhysicalClosedRingObservation e observation.observation.conformation
      (physicalClosedRingObservationToRealRingPlaneFrame e observation)
      (physicalClosedRingObservationToFrameCertificate e observation)).observation.firstSubstituent =
      observation.observation.firstSubstituent := by
  rw [RealRingPlaneFrame.toPhysicalClosedRingObservation_firstSubstituent]
  show e (e.symm observation.observation.firstSubstituent) =
    observation.observation.firstSubstituent
  simp

/-- Fieldwise round-trip for the second substituent. -/
@[simp] theorem physicalClosedRingObservationToFrame_secondSubstituent_recovery
    {molecule : SemanticMolecule} (e : V ≃ Fin molecule.atomCount)
    (observation : PhysicalPlaneEvidence.PhysicalClosedRingObservation molecule) :
    (RealRingPlaneFrame.toPhysicalClosedRingObservation e observation.observation.conformation
      (physicalClosedRingObservationToRealRingPlaneFrame e observation)
      (physicalClosedRingObservationToFrameCertificate e observation)).observation.secondSubstituent =
      observation.observation.secondSubstituent := by
  rw [RealRingPlaneFrame.toPhysicalClosedRingObservation_secondSubstituent]
  show e (e.symm observation.observation.secondSubstituent) =
    observation.observation.secondSubstituent
  simp

/-- Fieldwise round-trip for the first selected ring position. -/
@[simp] theorem physicalClosedRingObservationToFrame_firstAttachment_recovery
    {molecule : SemanticMolecule} (e : V ≃ Fin molecule.atomCount)
    (observation : PhysicalPlaneEvidence.PhysicalClosedRingObservation molecule) :
    (RealRingPlaneFrame.toPhysicalClosedRingObservation e observation.observation.conformation
      (physicalClosedRingObservationToRealRingPlaneFrame e observation)
      (physicalClosedRingObservationToFrameCertificate e observation)).firstAttachment.ringPosition =
      observation.firstAttachment.ringPosition := by
  rw [RealRingPlaneFrame.toPhysicalClosedRingObservation_firstAttachment_ringPosition]
  show e (e.symm observation.firstAttachment.ringPosition) =
    observation.firstAttachment.ringPosition
  simp

/-- Fieldwise round-trip for the first actual attachment interaction: the decoded lookup at the
chosen occurrence index is the original interaction. -/
@[simp] theorem physicalClosedRingObservationToFrame_firstInteraction_recovery
    {molecule : SemanticMolecule} (e : V ≃ Fin molecule.atomCount)
    (observation : PhysicalPlaneEvidence.PhysicalClosedRingObservation molecule) :
    (RealRingPlaneFrame.toPhysicalClosedRingObservation e observation.observation.conformation
      (physicalClosedRingObservationToRealRingPlaneFrame e observation)
      (physicalClosedRingObservationToFrameCertificate e observation)).firstAttachment.interaction =
      observation.firstAttachment.interaction := by
  rw [RealRingPlaneFrame.toPhysicalClosedRingObservation_firstAttachment_interaction]
  simp only [physicalClosedRingObservationToFrameCertificate]
  exact sourceInteractionIndex_get observation.firstAttachment.interaction
    observation.firstAttachment.interaction_mem

/-- Fieldwise round-trip for the second selected ring position. -/
@[simp] theorem physicalClosedRingObservationToFrame_secondAttachment_recovery
    {molecule : SemanticMolecule} (e : V ≃ Fin molecule.atomCount)
    (observation : PhysicalPlaneEvidence.PhysicalClosedRingObservation molecule) :
    (RealRingPlaneFrame.toPhysicalClosedRingObservation e observation.observation.conformation
      (physicalClosedRingObservationToRealRingPlaneFrame e observation)
      (physicalClosedRingObservationToFrameCertificate e observation)).secondAttachment.ringPosition =
      observation.secondAttachment.ringPosition := by
  rw [RealRingPlaneFrame.toPhysicalClosedRingObservation_secondAttachment_ringPosition]
  show e (e.symm observation.secondAttachment.ringPosition) =
    observation.secondAttachment.ringPosition
  simp

/-- Fieldwise round-trip for the second actual attachment interaction: the decoded lookup at the
chosen occurrence index is the original interaction. -/
@[simp] theorem physicalClosedRingObservationToFrame_secondInteraction_recovery
    {molecule : SemanticMolecule} (e : V ≃ Fin molecule.atomCount)
    (observation : PhysicalPlaneEvidence.PhysicalClosedRingObservation molecule) :
    (RealRingPlaneFrame.toPhysicalClosedRingObservation e observation.observation.conformation
      (physicalClosedRingObservationToRealRingPlaneFrame e observation)
      (physicalClosedRingObservationToFrameCertificate e observation)).secondAttachment.interaction =
      observation.secondAttachment.interaction := by
  rw [RealRingPlaneFrame.toPhysicalClosedRingObservation_secondAttachment_interaction]
  simp only [physicalClosedRingObservationToFrameCertificate]
  exact sourceInteractionIndex_get observation.secondAttachment.interaction
    observation.secondAttachment.interaction_mem

/-- Adapt the existing source-indexed axial frame.  The six source positions are converted with
the frame's own `Bounded` evidence, and the caller's incidence order is retained.  No high/low
ranking is claimed, because this source record supplies none. -/
def sourceIndexedAxialToFrame (frame : SourceIndexedAxialFrame)
    (e : V ≃ Fin frame.source.molecule.atomCount)
    (bounded : frame.Bounded) : FrameAnnotation V :=
  .axial
    { axisStart := sourceAtomOfIndex e frame.axisStart bounded.1
      axisEnd := sourceAtomOfIndex e frame.axisEnd bounded.2.1
      startFirst := sourceAtomOfIndex e frame.startFirst.referenceAtom bounded.2.2.1
      startSecond := sourceAtomOfIndex e frame.startSecond.referenceAtom bounded.2.2.2.1
      endFirst := sourceAtomOfIndex e frame.endFirst.referenceAtom bounded.2.2.2.2.1
      endSecond := sourceAtomOfIndex e frame.endSecond.referenceAtom bounded.2.2.2.2.2
      roles := .orderedIncidencePair
      sense? := none }

/-- The actual-incidence layer projects to the bounded source frame, hence to an annotation. -/
def actualSourceIndexedAxialToFrame (frame : SourceIndexedAxialFrame)
    (e : V ≃ Fin frame.source.molecule.atomCount)
    (actual : ActualAxialIncidence frame) : FrameAnnotation V :=
  sourceIndexedAxialToFrame frame e actual.1

/-! ## Adapter recovery facts -/

@[simp] theorem indexedAxialToFrame_atomRefs (e : V ≃ Fin n)
    (record : IndexedAxialGeometryObservation)
    (bounded : IndexedAxialSourceBounded n record) :
    (indexedAxialToFrame (V := V) e record bounded).atomRefs =
      [sourceAtomOfIndex e record.axisStart bounded.1,
        sourceAtomOfIndex e record.axisEnd bounded.2.1,
        sourceAtomOfIndex e record.startFirst bounded.2.2.1,
        sourceAtomOfIndex e record.startSecond bounded.2.2.2.1,
        sourceAtomOfIndex e record.endFirst bounded.2.2.2.2.1,
        sourceAtomOfIndex e record.endSecond bounded.2.2.2.2.2] := rfl

@[simp] theorem indexedHelicalToFrame_atomRefs (e : V ≃ Fin n)
    (record : IndexedHelicalGeometryObservation)
    (bounded : IndexedHelicalSourceBounded n record) :
    (indexedHelicalToFrame (V := V) e record bounded).atomRefs =
      sourceAtomListOfIndices e record.helixPath bounded.1 ++
        [sourceAtomOfIndex e record.frontReference bounded.2.1,
          sourceAtomOfIndex e record.backReference bounded.2.2] := rfl

@[simp] theorem indexedPolyhedralToFrame_positionRoles (e : V ≃ Fin n)
    (record : IndexedPolyhedralGeometryObservation)
    (bounded : IndexedPolyhedralSourceBounded n record) :
    (indexedPolyhedralToFrame (V := V) e record bounded).positionRoleObservation? =
      some record.configurationPositions := rfl

/-- The P-94 adapter retains the supplied torsion angle literally. -/
@[simp] theorem p94TorsionEvidenceToFrame_angle (e : V ≃ Fin n)
    (record : P94TorsionEvidence)
    (pathBounded : TorsionAxisPathSourceBounded n record.unit.atoms)
    (frontBounded : TorsionParticipantSourceBounded n record.frame.front)
    (rearBounded : TorsionParticipantSourceBounded n record.frame.rear) :
    (p94TorsionEvidenceToFrame (V := V) e record pathBounded frontBounded
      rearBounded).torsionAngle? = some record.frame.angle := rfl

/-- Unit adapters followed by the source traversal projection recover the source traversal. -/
@[simp] theorem planarUnitToFrame_planeAtoms? (unit : PlanarUnit V) :
    (planarUnitToFrame unit).planeAtoms? = some unit.planeAtoms := rfl

/-- Unit adapters followed by the source path projection recover the source path. -/
@[simp] theorem helicalUnitToFrame_helixPath? (unit : HelicalUnit V) :
    (helicalUnitToFrame unit).helixPath? = some unit.helixPath := rfl

end Adapters

/-! ## Concrete non-vacuity example -/

namespace FrameAnnotationExample

/-- A three-atom ordered helix observation. -/
def indexedHelix : IndexedHelicalGeometryObservation where
  helixPath := [0, 1, 2]
  frontReference := 0
  backReference := 2
  sense := .positive

/-- Its bounds against a three-atom source. -/
theorem indexedHelix_bounded : IndexedHelicalSourceBounded 3 indexedHelix := by
  refine ⟨?_, by decide, by decide⟩
  intro atom member
  simp [indexedHelix] at member
  rcases member with rfl | rfl | rfl <;> decide

/-- The corresponding annotation on `Fin 3`. -/
def frame : FrameAnnotation (Fin 3) :=
  indexedHelicalToFrame (Equiv.refl (Fin 3)) indexedHelix indexedHelix_bounded

/-- The ordered atom references are exactly the supplied path followed by the two references. -/
theorem frame_atomRefs : frame.atomRefs = [0, 1, 2, 0, 2] := by
  decide

/-- Relabelling by the identity returns the same annotation. -/
theorem frame_relabel_refl :
    relabelFrameAnnotation (Equiv.refl (Fin 3)) frame = frame := by
  simpa using relabelFrameAnnotation_symm (Equiv.refl (Fin 3)) frame

end FrameAnnotationExample

end TetraStereo.OneCenter
