import TetraStereo.UniversalProof.SemanticCoordinationPerceptionProofs.SemanticBinaryCoordinationPerception
import TetraStereo.OneCenter.IR9OctahedronSpatialPerception

set_option autoImplicit false

namespace TetraStereo.UniversalProof
namespace SemanticCoordinationPerceptionProofs

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RedBookIR9



























/-! ## Structural admission -/

/-- Spatially indexed source position lookup.  The point frame is built from the source, so there is
no caller-supplied frame. -/
def spatialPosition? (source : AuthoritativeChemicalInput) (index : ℕ) : Option CartesianPoint3 :=
  source.spatial?.bind fun spatial => listGet? spatial.positions index

theorem spatialPosition?_eq_some_iff (source : AuthoritativeChemicalInput) (index : ℕ)
    (point : CartesianPoint3) :
    spatialPosition? source index = some point ↔
      ∃ spatial : SpatialConfiguration,
        source.spatial? = some spatial ∧ listGet? spatial.positions index = some point := by
  simp only [spatialPosition?, Option.bind_eq_some_iff]

/-- Focused structural admission of a semantic coordination source: the finite molecule graph is
well formed (every interaction has at least two distinct in-range participants) and the spatial
index list matches the atom count. -/
def SemanticSourceWellFormed (source : AuthoritativeChemicalInput) : Prop :=
  source.molecule.StructurallyWellFormed ∧ source.SpatialIndicesWellFormed

def semanticSourceWellFormed? (source : AuthoritativeChemicalInput) : Bool :=
  source.molecule.structurallyWellFormed? && source.spatialIndicesWellFormed?

@[simp] theorem semanticSourceWellFormed?_eq_true_iff (source : AuthoritativeChemicalInput) :
    semanticSourceWellFormed? source = true ↔ SemanticSourceWellFormed source := by
  simp only [semanticSourceWellFormed?, SemanticSourceWellFormed, Bool.and_eq_true,
    SemanticMolecule.structurallyWellFormed?_eq_true_iff,
    AuthoritativeChemicalInput.spatialIndicesWellFormed?_eq_true_iff]

/-- Every interaction of a well-formed semantic source is a `WellFormed` interaction for the same
atom count. -/
theorem SemanticSourceWellFormed.interaction_wellFormed {source : AuthoritativeChemicalInput}
    (wellformed : SemanticSourceWellFormed source) {interaction : SemanticInteraction}
    (member : interaction ∈ source.molecule.interactions) :
    interaction.WellFormed source.molecule.atomCount := by
  have all := wellformed.1
  unfold SemanticMolecule.StructurallyWellFormed at all
  rw [List.all_eq_true] at all
  exact (SemanticInteraction.wellFormed?_eq_true_iff interaction source.molecule.atomCount).mp
    (all interaction member)

/-- A well-formed interaction has every participant inside the atom range. -/
theorem wellFormed_participant_bounded {interaction : SemanticInteraction}
    {atomCount : ℕ} (wellformed : interaction.WellFormed atomCount) {participant : ℕ}
    (member : participant ∈ interaction.participants) :
    participant < atomCount := by
  have all := wellformed.2.2
  rw [List.all_eq_true] at all
  exact of_decide_eq_true (all participant member)

/-- No out-of-range coordinate participant can hide behind the range filter: such a source is not
well formed, so it is refused instead of silently truncated. -/
theorem coordinateParticipant_outOfRange_not_wellFormed {source : AuthoritativeChemicalInput}
    {interaction : SemanticInteraction}
    (member : interaction ∈ source.molecule.interactions)
    (_kind : interaction.kind = SemanticInteractionKind.coordinate)
    {participant : ℕ} (inParticipants : participant ∈ interaction.participants)
    (outOfRange : source.molecule.atomCount ≤ participant) :
    ¬ SemanticSourceWellFormed source := by
  intro wellformed
  have bounded := wellFormed_participant_bounded
    (wellformed.interaction_wellFormed member) inParticipants
  exact absurd bounded (not_lt.mpr outOfRange)

/-- A discovered binary neighbour of a well-formed source is always inside the atom range. -/
theorem BinaryCoordinateDonor.bounded {source : AuthoritativeChemicalInput}
    (wellformed : SemanticSourceWellFormed source) {center donor : ℕ}
    (relation : BinaryCoordinateDonor source center donor) :
    donor < source.molecule.atomCount := by
  rcases relation with ⟨_, interaction, member, _, order⟩
  rcases order with forward | reverse
  · have inParticipants : donor ∈ interaction.participants := by
      rw [forward]; simp
    exact wellFormed_participant_bounded (wellformed.interaction_wellFormed member) inParticipants
  · have inParticipants : donor ∈ interaction.participants := by
      rw [reverse]; simp
    exact wellFormed_participant_bounded (wellformed.interaction_wellFormed member) inParticipants

/-- Under structural admission, a present spatial configuration has exactly the atom count of
positions. -/
theorem SemanticSourceWellFormed.spatial_positions_length {source : AuthoritativeChemicalInput}
    (wellformed : SemanticSourceWellFormed source) {spatial : SpatialConfiguration}
    (lookup : source.spatial? = some spatial) :
    spatial.positions.length = source.molecule.atomCount := by
  have h := wellformed.2
  unfold AuthoritativeChemicalInput.SpatialIndicesWellFormed at h
  rw [lookup] at h
  simpa using h

/-- Every source position lookup is inside the atom range under structural admission. -/
theorem spatialPosition?_bounded {source : AuthoritativeChemicalInput}
    (wellformed : SemanticSourceWellFormed source) {index : ℕ} {point : CartesianPoint3}
    (lookup : spatialPosition? source index = some point) :
    index < source.molecule.atomCount := by
  rcases (spatialPosition?_eq_some_iff source index point).mp lookup with
    ⟨spatial, spatialLookup, positionLookup⟩
  have lengthEq := wellformed.spatial_positions_length spatialLookup
  have bounded := listGet?_eq_some_implies_lt spatial.positions index point positionLookup
  rw [lengthEq] at bounded
  exact bounded

/-! ## Simple binary incidents and unsupported coordination -/

/-- A single interaction is a *simple binary coordination incident* for `center` when it has exactly
two distinct participants, one of which is `center`.  Three-or-more-participant records, self pairs,
and any other arity fall outside this predicate. -/
def IsSimpleBinaryCoordinateIncident (interaction : SemanticInteraction) (center : ℕ) : Prop :=
  match interaction.participants with
  | [first, second] =>
      interaction.kind = SemanticInteractionKind.coordinate ∧
        ((first = center ∧ second ≠ center) ∨ (second = center ∧ first ≠ center))
  | _ => False

def isSimpleBinaryCoordinateIncident? (interaction : SemanticInteraction) (center : ℕ) : Bool :=
  match interaction.participants with
  | [first, second] =>
      decide (interaction.kind = SemanticInteractionKind.coordinate ∧
        ((first = center ∧ second ≠ center) ∨ (second = center ∧ first ≠ center)))
  | _ => false

@[simp] theorem isSimpleBinaryCoordinateIncident?_eq_true_iff
    (interaction : SemanticInteraction) (center : ℕ) :
    isSimpleBinaryCoordinateIncident? interaction center = true ↔
      IsSimpleBinaryCoordinateIncident interaction center := by
  unfold isSimpleBinaryCoordinateIncident? IsSimpleBinaryCoordinateIncident
  generalize hparts : interaction.participants = parts
  cases parts with
  | nil => simp
  | cons first rest =>
      cases rest with
      | nil => simp
      | cons second rest' =>
          cases rest' with
          | nil => simp [decide_eq_true_eq]
          | cons third rest'' => simp

/-- The `coordinate` interactions incident on a centre (whether or not the centre is a participant is
checked at the use site). -/
def incidentCoordinateIncidents (source : AuthoritativeChemicalInput) (center : ℕ) :
    List SemanticInteraction :=
  source.molecule.interactions.filter fun interaction =>
    decide (interaction.kind = SemanticInteractionKind.coordinate ∧
      center ∈ interaction.participants)

@[simp] theorem mem_incidentCoordinateIncidents_iff (source : AuthoritativeChemicalInput)
    (center : ℕ) (interaction : SemanticInteraction) :
    interaction ∈ incidentCoordinateIncidents source center ↔
      interaction ∈ source.molecule.interactions ∧
        interaction.kind = SemanticInteractionKind.coordinate ∧
          center ∈ interaction.participants := by
  simp only [incidentCoordinateIncidents, List.mem_filter, decide_eq_true_eq]

/-- An incident coordinate interaction that is not a simple binary record. Retained explicitly. -/
def UnsupportedCoordinateIncident (source : AuthoritativeChemicalInput) (center : ℕ) : Prop :=
  ∃ interaction ∈ source.molecule.interactions,
    interaction.kind = SemanticInteractionKind.coordinate ∧
      center ∈ interaction.participants ∧
      ¬ IsSimpleBinaryCoordinateIncident interaction center

/-- Positive Boolean check: every incident coordinate record is a simple binary record. -/
def allSimpleBinaryIncidents? (source : AuthoritativeChemicalInput) (center : ℕ) : Bool :=
  (incidentCoordinateIncidents source center).all fun interaction =>
    isSimpleBinaryCoordinateIncident? interaction center

/-- The positive check is exactly the negation of the unsupported-incident condition. -/
@[simp] theorem allSimpleBinaryIncidents?_eq_true_iff (source : AuthoritativeChemicalInput)
    (center : ℕ) :
    allSimpleBinaryIncidents? source center = true ↔
      ¬ UnsupportedCoordinateIncident source center := by
  unfold allSimpleBinaryIncidents? UnsupportedCoordinateIncident
  rw [List.all_eq_true]
  constructor
  · rintro all ⟨interaction, member, kind, participant, notSimple⟩
    have incidentMember : interaction ∈ incidentCoordinateIncidents source center :=
      (mem_incidentCoordinateIncidents_iff source center interaction).mpr
        ⟨member, kind, participant⟩
    exact notSimple ((isSimpleBinaryCoordinateIncident?_eq_true_iff interaction center).mp
      (all interaction incidentMember))
  · intro notUnsupported interaction incidentMember
    have facts := (mem_incidentCoordinateIncidents_iff source center interaction).mp incidentMember
    by_contra notTrue
    exact notUnsupported ⟨interaction, facts.1, facts.2.1, facts.2.2,
      fun simple => notTrue
        ((isSimpleBinaryCoordinateIncident?_eq_true_iff interaction center).mpr simple)⟩

/-! ## Source-derived octahedral frame -/

/-- Build the exact octahedral perception frame from the source: the centre and its six canonical
donors are looked up in the source's own indexed positions.  A caller never supplies coordinates. -/
def octahedronFrameAt? (source : AuthoritativeChemicalInput) (center : ℕ) :
    Option OctahedronSpatialPerception.Frame :=
  match canonicalDonors source center with
  | [donor0, donor1, donor2, donor3, donor4, donor5] =>
      match spatialPosition? source center,
            spatialPosition? source donor0, spatialPosition? source donor1,
            spatialPosition? source donor2, spatialPosition? source donor3,
            spatialPosition? source donor4, spatialPosition? source donor5 with
      | some centerPosition, some position0, some position1, some position2,
        some position3, some position4, some position5 =>
          some
            { center := centerPosition
              donor0 := position0, donor1 := position1, donor2 := position2
              donor3 := position3, donor4 := position4, donor5 := position5 }
      | _, _, _, _, _, _, _ => none
  | _ => none

/-- Independent donor-to-coordinate binding: the six indices are exactly the canonical
source neighbours and every frame field is the corresponding actual source position. -/
def SourceOctahedronFrame (source : AuthoritativeChemicalInput) (center : ℕ)
    (frame : OctahedronSpatialPerception.Frame) : Prop :=
  ∃ donor0 donor1 donor2 donor3 donor4 donor5 : ℕ,
    canonicalDonors source center = [donor0, donor1, donor2, donor3, donor4, donor5] ∧
    spatialPosition? source center = some frame.center ∧
    spatialPosition? source donor0 = some frame.donor0 ∧
    spatialPosition? source donor1 = some frame.donor1 ∧
    spatialPosition? source donor2 = some frame.donor2 ∧
    spatialPosition? source donor3 = some frame.donor3 ∧
    spatialPosition? source donor4 = some frame.donor4 ∧
    spatialPosition? source donor5 = some frame.donor5

/-- The executable extractor realizes the independently specified seven source lookups. -/
theorem octahedronFrameAt?_eq_some_iff (source : AuthoritativeChemicalInput) (center : ℕ)
    (frame : OctahedronSpatialPerception.Frame) :
    octahedronFrameAt? source center = some frame ↔ SourceOctahedronFrame source center frame := by
  constructor
  · intro lookup
    unfold octahedronFrameAt? at lookup
    split at lookup
    · rename_i donor0 donor1 donor2 donor3 donor4 donor5 donorsEq
      split at lookup
      · rename_i centerPosition position0 position1 position2 position3 position4 position5
          centerEq positionEq0 positionEq1 positionEq2 positionEq3 positionEq4 positionEq5
        cases lookup
        exact ⟨donor0, donor1, donor2, donor3, donor4, donor5, donorsEq,
          centerEq, positionEq0, positionEq1, positionEq2, positionEq3, positionEq4, positionEq5⟩
      · contradiction
    · contradiction
  · rintro ⟨donor0, donor1, donor2, donor3, donor4, donor5, donorsEq,
      centerEq, positionEq0, positionEq1, positionEq2, positionEq3, positionEq4, positionEq5⟩
    unfold octahedronFrameAt?
    simp only [donorsEq, centerEq, positionEq0, positionEq1, positionEq2, positionEq3,
      positionEq4, positionEq5]

/-- Exact octahedral recognition of the source-derived frame. -/
def frameRecognition? (source : AuthoritativeChemicalInput) (center : ℕ) : Bool :=
  match octahedronFrameAt? source center with
  | some frame => OctahedronSpatialPerception.recognize? frame
  | none => false

/-- Literal extractor recognizer.  It never returns a certificate; it returns a Boolean that is
proved equivalent below to the independent relation `RecognizedExactOctahedron`. -/
def recognizesExactOctahedron? (source : AuthoritativeChemicalInput) (center : ℕ) : Bool :=
  semanticSourceWellFormed? source && allSimpleBinaryIncidents? source center &&
    ((canonicalDonors source center).length == 6) && frameRecognition? source center

/-- Independent specification of a recognized exact octahedral centre: structural admission, binary
incident-only coordination, exactly six canonical donors, a source-derived frame, and the existing
exact-octahedron shape predicate. -/
def RecognizedExactOctahedron (source : AuthoritativeChemicalInput) (center : ℕ) : Prop :=
  SemanticSourceWellFormed source ∧
    ¬ UnsupportedCoordinateIncident source center ∧
    (canonicalDonors source center).length = 6 ∧
    ∃ frame : OctahedronSpatialPerception.Frame,
      SourceOctahedronFrame source center frame ∧
        OctahedronSpatialPerception.IsExactOctahedron frame

/-- The frame recognition Bool realizes the existential source-derived exact-shape specification. -/
theorem frameRecognition?_eq_true_iff (source : AuthoritativeChemicalInput) (center : ℕ) :
    frameRecognition? source center = true ↔
      ∃ frame : OctahedronSpatialPerception.Frame,
        SourceOctahedronFrame source center frame ∧
          OctahedronSpatialPerception.IsExactOctahedron frame := by
  simp only [← octahedronFrameAt?_eq_some_iff]
  unfold frameRecognition?
  cases hframe : octahedronFrameAt? source center with
  | none => simp
  | some frame => simp [OctahedronSpatialPerception.recognize?_eq_true_iff]

/-- The literal extractor recognizer is equivalent to the independent relation. -/
theorem recognizesExactOctahedron?_eq_true_iff (source : AuthoritativeChemicalInput)
    (center : ℕ) :
    recognizesExactOctahedron? source center = true ↔
      RecognizedExactOctahedron source center := by
  simp only [recognizesExactOctahedron?, RecognizedExactOctahedron, Bool.and_eq_true,
    semanticSourceWellFormed?_eq_true_iff, allSimpleBinaryIncidents?_eq_true_iff,
    beq_iff_eq, frameRecognition?_eq_true_iff]
  tauto

/-! ## Derived facts about a recognized centre -/

theorem recognized_length_six (source : AuthoritativeChemicalInput) (center : ℕ)
    (recognized : RecognizedExactOctahedron source center) :
    (canonicalDonors source center).length = 6 :=
  recognized.2.2.1

/-- Every canonical donor of a recognized centre is an in-range atom. -/
theorem RecognizedExactOctahedron.donor_bounded {source : AuthoritativeChemicalInput}
    {center donor : ℕ} (recognized : RecognizedExactOctahedron source center)
    (member : donor ∈ canonicalDonors source center) :
    donor < source.molecule.atomCount :=
  BinaryCoordinateDonor.bounded recognized.1
    ((mem_canonicalDonors_iff source center donor).mp member).2

/-- Recognition itself proves the centre index is in range through its actual coordinate lookup. -/
theorem RecognizedExactOctahedron.center_bounded {source : AuthoritativeChemicalInput}
    {center : ℕ} (recognized : RecognizedExactOctahedron source center) :
    center < source.molecule.atomCount := by
  rcases recognized.2.2.2 with ⟨frame, binding, _⟩
  rcases binding with ⟨_, _, _, _, _, _, _, centerEq, _⟩
  exact spatialPosition?_bounded recognized.1 centerEq

/-! ## Bounded centre enumeration -/

/-- The bounded atom universe filtered by the extractor recognizer. -/
def exactOctahedronCenters (source : AuthoritativeChemicalInput) : List ℕ :=
  (List.range source.molecule.atomCount).filter fun center =>
    recognizesExactOctahedron? source center

theorem mem_exactOctahedronCenters_iff (source : AuthoritativeChemicalInput) (center : ℕ) :
    center ∈ exactOctahedronCenters source ↔
      center < source.molecule.atomCount ∧ RecognizedExactOctahedron source center := by
  simp only [exactOctahedronCenters, List.mem_filter, List.mem_range,
    recognizesExactOctahedron?_eq_true_iff]

/-- The bounded scan includes every recognized source centre; its bound is derived, not assumed. -/
theorem mem_exactOctahedronCenters_iff_recognized
    (source : AuthoritativeChemicalInput) (center : ℕ) :
    center ∈ exactOctahedronCenters source ↔ RecognizedExactOctahedron source center := by
  rw [mem_exactOctahedronCenters_iff]
  exact ⟨fun pair => pair.2, fun recognized => ⟨recognized.center_bounded, recognized⟩⟩

theorem exactOctahedronCenters_nodup (source : AuthoritativeChemicalInput) :
    (exactOctahedronCenters source).Nodup :=
  List.nodup_range.filter _

theorem exactOctahedronCenters_count_one (source : AuthoritativeChemicalInput) (center : ℕ)
    (member : center ∈ exactOctahedronCenters source) :
    (exactOctahedronCenters source).count center = 1 :=
  List.count_eq_one_of_mem (exactOctahedronCenters_nodup source) member

/-! ## Explicit refusal characterisations ("the checker emits none") -/

theorem not_recognizedExactOctahedron_of_false (source : AuthoritativeChemicalInput) (center : ℕ)
    (checked : recognizesExactOctahedron? source center = false) :
    ¬ RecognizedExactOctahedron source center :=
  fun recognized => by
    have htrue := (recognizesExactOctahedron?_eq_true_iff source center).mpr recognized
    rw [htrue] at checked
    cases checked

theorem recognizesExactOctahedron?_eq_false_of_not_wellFormed
    (source : AuthoritativeChemicalInput) (center : ℕ)
    (notWellFormed : ¬ SemanticSourceWellFormed source) :
    recognizesExactOctahedron? source center = false := by
  apply Bool.eq_false_of_not_eq_true
  intro recognized
  exact notWellFormed ((recognizesExactOctahedron?_eq_true_iff source center).mp recognized).1

theorem recognizesExactOctahedron?_eq_false_of_unsupported_incident
    (source : AuthoritativeChemicalInput) (center : ℕ)
    (unsupported : UnsupportedCoordinateIncident source center) :
    recognizesExactOctahedron? source center = false := by
  apply Bool.eq_false_of_not_eq_true
  intro recognized
  exact ((recognizesExactOctahedron?_eq_true_iff source center).mp recognized).2.1 unsupported

theorem recognizesExactOctahedron?_eq_false_of_length_ne_six
    (source : AuthoritativeChemicalInput) (center : ℕ)
    (notSix : (canonicalDonors source center).length ≠ 6) :
    recognizesExactOctahedron? source center = false := by
  apply Bool.eq_false_of_not_eq_true
  intro recognized
  exact notSix ((recognizesExactOctahedron?_eq_true_iff source center).mp recognized).2.2.1

theorem recognizesExactOctahedron?_eq_false_of_frame_none
    (source : AuthoritativeChemicalInput) (center : ℕ)
    (noFrame : octahedronFrameAt? source center = none) :
    recognizesExactOctahedron? source center = false := by
  apply Bool.eq_false_of_not_eq_true
  intro recognized
  rcases ((recognizesExactOctahedron?_eq_true_iff source center).mp recognized).2.2.2 with
    ⟨frame, lookup, _⟩
  have extracted := (octahedronFrameAt?_eq_some_iff source center frame).mpr lookup
  rw [noFrame] at extracted
  cases extracted

theorem frameRecognition?_eq_false_of_recognize_false (source : AuthoritativeChemicalInput)
    (center : ℕ) (frame : OctahedronSpatialPerception.Frame)
    (lookup : octahedronFrameAt? source center = some frame)
    (notExact : OctahedronSpatialPerception.recognize? frame = false) :
    frameRecognition? source center = false := by
  unfold frameRecognition?
  rw [lookup]
  exact notExact

theorem recognizesExactOctahedron?_eq_false_of_frameRecognition_false
    (source : AuthoritativeChemicalInput) (center : ℕ)
    (frameFalse : frameRecognition? source center = false) :
    recognizesExactOctahedron? source center = false := by
  apply Bool.eq_false_of_not_eq_true
  intro recognized
  have notFrame :
      ¬ ∃ frame : OctahedronSpatialPerception.Frame,
          SourceOctahedronFrame source center frame ∧
            OctahedronSpatialPerception.IsExactOctahedron frame := by
    intro existsFrame
    have computed : frameRecognition? source center = true :=
      (frameRecognition?_eq_true_iff source center).mpr existsFrame
    rw [computed] at frameFalse
    cases frameFalse
  exact notFrame ((recognizesExactOctahedron?_eq_true_iff source center).mp recognized).2.2.2

/-! ## Closed semantic example: idealized hexafluorocobaltate(III) -/

namespace HexafluorocobaltateIII

open TetraStereo.OneCenter

/-- Cobalt periodic identity (atomic number 27), independent of the organic parser's
element table. -/
def cobalt : PeriodicElement := (PeriodicElement.ofAtomicNumber? 27).get (by decide +kernel)

/-- Fluorine periodic identity (atomic number 9). -/
def fluorine : PeriodicElement := (PeriodicElement.ofAtomicNumber? 9).get (by decide +kernel)

def cobaltAtom : SemanticAtom := { element := cobalt, formalCharge := 3 }

def fluorineAtom : SemanticAtom := { element := fluorine, formalCharge := -1 }

/-- One cobalt centre (atom 0, formal charge +3) and six fluoride donors (atoms 1--6, formal charge
-1), joined by six actual binary `coordinate` records. -/
def molecule : SemanticMolecule :=
  { atoms := cobaltAtom :: List.replicate 6 fluorineAtom
    interactions := (List.range 6).map fun index =>
      { participants := [0, index + 1], kind := SemanticInteractionKind.coordinate } }

/-- Exact rational coordinates: the centre at the origin and the six donors along ±unit Cartesian
axes. -/
def positions : List CartesianPoint3 :=
  [ { x := 0, y := 0, z := 0 }
  , { x := 1, y := 0, z := 0 }, { x := -1, y := 0, z := 0 }
  , { x := 0, y := 1, z := 0 }, { x := 0, y := -1, z := 0 }
  , { x := 0, y := 0, z := 1 }, { x := 0, y := 0, z := -1 } ]

/-- The actual format-neutral source. -/
def source : AuthoritativeChemicalInput :=
  { molecule := molecule, spatial? := some { positions := positions } }

/-- The expected source-derived octahedral frame. -/
def frame : OctahedronSpatialPerception.Frame :=
  { center := { x := 0, y := 0, z := 0 }
    donor0 := { x := 1, y := 0, z := 0 }
    donor1 := { x := -1, y := 0, z := 0 }
    donor2 := { x := 0, y := 1, z := 0 }
    donor3 := { x := 0, y := -1, z := 0 }
    donor4 := { x := 0, y := 0, z := 1 }
    donor5 := { x := 0, y := 0, z := -1 } }

theorem canonicalDonors_center : canonicalDonors source 0 = [1, 2, 3, 4, 5, 6] := by decide +kernel

theorem frame_lookup : octahedronFrameAt? source 0 = some frame := by decide +kernel

theorem frame_exact : OctahedronSpatialPerception.IsExactOctahedron frame :=
  (OctahedronSpatialPerception.recognize?_eq_true_iff frame).mp (by decide +kernel)

theorem source_wellFormed : SemanticSourceWellFormed source :=
  (semanticSourceWellFormed?_eq_true_iff source).mp (by decide +kernel)

theorem source_noUnsupported : ¬ UnsupportedCoordinateIncident source 0 := by
  rw [← allSimpleBinaryIncidents?_eq_true_iff]
  decide +kernel

theorem source_recognized : RecognizedExactOctahedron source 0 :=
  ⟨source_wellFormed, source_noUnsupported, by rw [canonicalDonors_center]; rfl,
    ⟨frame, (octahedronFrameAt?_eq_some_iff source 0 frame).mp frame_lookup, frame_exact⟩⟩

theorem source_recognizer_true : recognizesExactOctahedron? source 0 = true :=
  (recognizesExactOctahedron?_eq_true_iff source 0).mpr source_recognized

/-- Exactly one centre of the whole bounded source universe is an exact octahedral centre. -/
theorem exactOctahedronCenters_exactly : exactOctahedronCenters source = [0] := by decide +kernel

theorem exactOctahedronCenters_count_one_at_zero :
    (exactOctahedronCenters source).count 0 = 1 :=
  exactOctahedronCenters_count_one source 0 (by rw [exactOctahedronCenters_exactly]; simp)

/-! ### Closed invariance regressions -/

/-- The same molecule with every participant list recorded in the opposite order. -/
def moleculeReversed : SemanticMolecule :=
  { molecule with interactions := (List.range 6).map fun index =>
      { participants := [index + 1, 0], kind := SemanticInteractionKind.coordinate } }

def sourceReversed : AuthoritativeChemicalInput :=
  { source with molecule := moleculeReversed }

theorem reversed_canonicalDonors : canonicalDonors sourceReversed 0 = [1, 2, 3, 4, 5, 6] := by
  decide +kernel

theorem reversed_recognized : recognizesExactOctahedron? sourceReversed 0 = true := by decide +kernel

/-- The same molecule with the coordinate record list duplicated. -/
def moleculeDuplicated : SemanticMolecule :=
  { molecule with interactions := molecule.interactions ++ molecule.interactions }

def sourceDuplicated : AuthoritativeChemicalInput :=
  { source with molecule := moleculeDuplicated }

theorem duplicated_canonicalDonors : canonicalDonors sourceDuplicated 0 = [1, 2, 3, 4, 5, 6] := by
  decide +kernel

theorem duplicated_recognized : recognizesExactOctahedron? sourceDuplicated 0 = true := by
  decide +kernel

/-! ### Closed refusal regressions -/

/-- Only five coordinate records: one donor missing. -/
def moleculeMissingDonor : SemanticMolecule :=
  { molecule with interactions := (List.range 5).map fun index =>
      { participants := [0, index + 1], kind := SemanticInteractionKind.coordinate } }

def sourceMissingDonor : AuthoritativeChemicalInput :=
  { source with molecule := moleculeMissingDonor }

theorem missingDonor_refused : recognizesExactOctahedron? sourceMissingDonor 0 = false := by
  decide +kernel

theorem missingDonor_notRecognized : ¬ RecognizedExactOctahedron sourceMissingDonor 0 :=
  not_recognizedExactOctahedron_of_false sourceMissingDonor 0 missingDonor_refused

/-- No spatial configuration at all: coordinates are absent. -/
def sourceNoCoordinates : AuthoritativeChemicalInput := { source with spatial? := none }

theorem noCoordinates_frame_none : octahedronFrameAt? sourceNoCoordinates 0 = none := by decide +kernel

theorem noCoordinates_refused : recognizesExactOctahedron? sourceNoCoordinates 0 = false :=
  recognizesExactOctahedron?_eq_false_of_frame_none sourceNoCoordinates 0 noCoordinates_frame_none

/-- A three-participant `coordinate` record incident on the centre (a haptic/multicenter record
that must never be flattened into a pair). -/
def hapticInteraction : SemanticInteraction :=
  { participants := [0, 1, 2], kind := SemanticInteractionKind.coordinate }

def sourceHaptic : AuthoritativeChemicalInput :=
  withInteractions source (hapticInteraction :: molecule.interactions)

theorem haptic_unsupported : UnsupportedCoordinateIncident sourceHaptic 0 := by
  refine ⟨hapticInteraction, ?_, rfl, ?_, ?_⟩
  · simp [sourceHaptic]
  · simp [hapticInteraction]
  · intro simple
    exact simple

theorem haptic_refused : recognizesExactOctahedron? sourceHaptic 0 = false :=
  recognizesExactOctahedron?_eq_false_of_unsupported_incident sourceHaptic 0 haptic_unsupported

/-- A self pair `[0, 0]`: not a well-formed interaction, hence refused. -/
def selfInteraction : SemanticInteraction :=
  { participants := [0, 0], kind := SemanticInteractionKind.coordinate }

def moleculeSelf : SemanticMolecule :=
  { molecule with interactions := selfInteraction :: molecule.interactions }

def sourceSelf : AuthoritativeChemicalInput := { source with molecule := moleculeSelf }

theorem self_refused : recognizesExactOctahedron? sourceSelf 0 = false := by decide +kernel

/-- An out-of-range coordinate participant (`7`, one past the atom range). -/
def outOfRangeInteraction : SemanticInteraction :=
  { participants := [0, 7], kind := SemanticInteractionKind.coordinate }

def sourceOutOfRange : AuthoritativeChemicalInput :=
  withInteractions source (outOfRangeInteraction :: molecule.interactions)

theorem outOfRange_notWellFormed : ¬ SemanticSourceWellFormed sourceOutOfRange :=
  coordinateParticipant_outOfRange_not_wellFormed
    (interaction := outOfRangeInteraction) (participant := 7)
    (by simp [sourceOutOfRange])
    rfl
    (by simp [outOfRangeInteraction])
    (by decide +kernel)

theorem outOfRange_refused : recognizesExactOctahedron? sourceOutOfRange 0 = false :=
  recognizesExactOctahedron?_eq_false_of_not_wellFormed sourceOutOfRange 0 outOfRange_notWellFormed

/-- All six donors collapse onto the centre: the frame is degenerate and not an exact octahedron. -/
def collapsedPositions : List CartesianPoint3 :=
  List.replicate 7 { x := 0, y := 0, z := 0 }

def sourceCollapsed : AuthoritativeChemicalInput :=
  { source with spatial? := some { positions := collapsedPositions } }

theorem collapsed_refused : recognizesExactOctahedron? sourceCollapsed 0 = false := by
  decide +kernel

end HexafluorocobaltateIII

end SemanticCoordinationPerceptionProofs
end TetraStereo.UniversalProof
