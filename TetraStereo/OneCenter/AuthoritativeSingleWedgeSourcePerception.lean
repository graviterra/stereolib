import TetraStereo.UniversalProof.DiagramSingleWedgeGeometryProofs.DiagramSingleWedgeTetrahedralParity
import TetraStereo.OneCenter.AuthoritativeTetrahedralPointParityReindex

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput
namespace SingleWedgeSource

/-!
# Extraction of one absolute wedge from the actual source diagram

The public extractor takes only a source and its centre atom. Its four records, endpoint IDs,
coordinates and wedge slot come from that source; it takes no caller depiction or permutation.
The incident filter retains written order and multiplicity. The independent admission predicate
requires exactly four records with distinct endpoints, exactly three plain records and one
absolute solid/hashed wedge narrow at the centre, and three surrounding plain rays.

Every semantic interaction is structurally checked. Every interaction incident at the centre
must be binary covalent order one and must name one of the drawn endpoints; every drawn
endpoint must have such an interaction. This intentionally restricted domain excludes higher
orders, aromatic, coordinate and multicentre centre incidences, including incompatible extra
interactions hidden behind an otherwise valid single bond. Semantic interactions elsewhere may
have any structurally valid represented kind.

The signed depth is the drawing convention representatives `+1` (solid, toward the viewer) and
`-1` (hashed, away from the viewer), not a physical reconstruction.  The downstream point-parity
producer uses the calibrated standard right-handed Cartesian frame, so a written-order solid
wedge on a positively surrounding plain triple is the `.clockwise` carrier and a hashed wedge is
the `.anticlockwise` carrier.  Neither spatial data nor atom `@`/`@@` annotations are read. The
endpoint frame is source-written order, not an assumed CIP occurrence frame. Occurrence alignment
and scientific approval of the wedge convention remain separate obligations.
-/

open TetraStereo.UniversalProof.DiagramSingleWedgeGeometryProofs

def incidentRecords (diagram : DiagramConfiguration) (center : Nat) : List DiagramBond :=
  diagram.bonds.filter fun bond => decide (bond.source = center ∨ bond.target = center)

def endpoint (center : Nat) (bond : DiagramBond) : Nat :=
  if bond.source = center then bond.target else bond.source

def isWedge (bond : DiagramBond) : Bool :=
  decide (bond.style = .solidWedge ∨ bond.style = .hashedWedge)

def plainRecords (records : List DiagramBond) : List DiagramBond :=
  records.filter fun bond => decide (bond.style = .plain)

def wedgeRecords (records : List DiagramBond) : List DiagramBond :=
  records.filter isWedge

def position (positions : List CartesianPoint2) (atom : Nat) : CartesianPoint2 :=
  positions.getD atom ⟨0, 0⟩

def defaultRecord : DiagramBond := ⟨0, 0, .plain, .absolute⟩

/-- Lift a drawn endpoint to its drawing-depth representative.  A solid wedge is `+1` (toward the
viewer) and a hashed wedge is `-1` (away from the viewer); every other style lies in the drawing
plane.  Only the sign is consumed by the parity producer. -/
def liftedPoint (point : CartesianPoint2) (style : DiagramBondStyle) : CartesianPoint3 :=
  match style with
  | .solidWedge => liftedTip point 1
  | .hashedWedge => liftedTip point (-1)
  | _ => planePoint point

def liftedRecord (positions : List CartesianPoint2) (center : Nat)
    (bond : DiagramBond) : CartesianPoint3 :=
  liftedPoint (position positions (endpoint center bond)) bond.style

/-- Literal finite test of the complete allowed kind and both participant orders. -/
def binarySingleIncident? (center : Nat) (endpoints : List Nat)
    (interaction : SemanticInteraction) : Bool :=
  match interaction.participants with
  | [first, second] =>
      decide (interaction.kind = .covalent 1) &&
        decide ((first = center ∧ second ∈ endpoints) ∨
          (second = center ∧ first ∈ endpoints))
  | _ => false

/-- Independent declarative counterpart of the participant/kind test. -/
def BinarySingleIncident (center : Nat) (endpoints : List Nat)
    (interaction : SemanticInteraction) : Prop :=
  ∃ first second,
    interaction.participants = [first, second] ∧ interaction.kind = .covalent 1 ∧
      ((first = center ∧ second ∈ endpoints) ∨ (second = center ∧ first ∈ endpoints))

theorem binarySingleIncident?_eq_true_iff (center : Nat) (endpoints : List Nat)
    (interaction : SemanticInteraction) :
    binarySingleIncident? center endpoints interaction = true ↔
      BinarySingleIncident center endpoints interaction := by
  rcases interaction with ⟨participants, kind⟩
  rcases participants with _ | ⟨first, participants⟩
  · simp [binarySingleIncident?, BinarySingleIncident]
  rcases participants with _ | ⟨second, participants⟩
  · simp [binarySingleIncident?, BinarySingleIncident]
  rcases participants with _ | ⟨third, rest⟩
  · simp [binarySingleIncident?, BinarySingleIncident]
  · simp [binarySingleIncident?, BinarySingleIncident]

/-- Every actual centre incidence must lie in the admitted single-bond subdomain. -/
def semanticIncidentsAllowed? (source : AuthoritativeChemicalInput) (center : Nat)
    (endpoints : List Nat) : Bool :=
  source.molecule.interactions.all fun interaction =>
    !decide (center ∈ interaction.participants) ||
      binarySingleIncident? center endpoints interaction

theorem semanticIncidentsAllowed?_eq_true_iff
    (source : AuthoritativeChemicalInput) (center : Nat) (endpoints : List Nat) :
    semanticIncidentsAllowed? source center endpoints = true ↔
      ∀ interaction ∈ source.molecule.interactions,
        center ∈ interaction.participants → BinarySingleIncident center endpoints interaction := by
  unfold semanticIncidentsAllowed?
  rw [List.all_eq_true]
  constructor
  · intro allowed interaction present incident
    apply (binarySingleIncident?_eq_true_iff center endpoints interaction).mp
    simpa [incident] using allowed interaction present
  · intro allowed interaction present
    by_cases incident : center ∈ interaction.participants
    · simpa [incident] using
        (binarySingleIncident?_eq_true_iff center endpoints interaction).mpr
          (allowed interaction present incident)
    · simp [incident]

/-- Existence is checked against both participant orders of an exact covalent-1 interaction. -/
def singleNeighbor? (source : AuthoritativeChemicalInput) (center neighbor : Nat) : Bool :=
  source.molecule.interactions.any fun interaction =>
    decide (interaction.kind = .covalent 1 ∧
      (interaction.participants = [center, neighbor] ∨
        interaction.participants = [neighbor, center]))

instance plainRaysSurroundDecidable (center first second third : CartesianPoint2) :
    Decidable (PlainRaysSurround center first second third) := by
  unfold PlainRaysSurround CyclicSurround
  infer_instance

/-- The finite source conditions, independently of extraction and descriptor success.
The coordinate fallback used in total helper functions is guarded by exact table length and
the bounds of every diagram record; it cannot supply missing admitted coordinates. -/
def AdmittedDiagram (source : AuthoritativeChemicalInput) (center : Nat)
    (diagram : DiagramConfiguration) (positions : List CartesianPoint2) : Prop :=
  source.molecule.StructurallyWellFormed ∧
  positions.length = source.molecule.atomCount ∧
  center < source.molecule.atomCount ∧
  diagram.bonds.all (fun bond => decide
    (bond.source < source.molecule.atomCount ∧ bond.target < source.molecule.atomCount ∧
      bond.source ≠ bond.target)) = true ∧
  (incidentRecords diagram center).length = 4 ∧
  (incidentRecords diagram center).Nodup ∧
  ((incidentRecords diagram center).map (endpoint center)).Nodup ∧
  (incidentRecords diagram center).all (fun bond => decide
    (endpoint center bond ≠ center ∧ bond.scope = .absolute)) = true ∧
  (plainRecords (incidentRecords diagram center)).length = 3 ∧
  (wedgeRecords (incidentRecords diagram center)).length = 1 ∧
  (wedgeRecords (incidentRecords diagram center)).all
    (fun bond => decide (bond.source = center)) = true ∧
  semanticIncidentsAllowed? source center
    ((incidentRecords diagram center).map (endpoint center)) = true ∧
  (incidentRecords diagram center).all
    (fun bond => singleNeighbor? source center (endpoint center bond)) = true ∧
  PlainRaysSurround (position positions center)
    (position positions (endpoint center
      ((plainRecords (incidentRecords diagram center)).getD 0 defaultRecord)))
    (position positions (endpoint center
      ((plainRecords (incidentRecords diagram center)).getD 1 defaultRecord)))
    (position positions (endpoint center
      ((plainRecords (incidentRecords diagram center)).getD 2 defaultRecord)))

instance admittedDiagramDecidable (source : AuthoritativeChemicalInput) (center : Nat)
    (diagram : DiagramConfiguration) (positions : List CartesianPoint2) :
    Decidable (AdmittedDiagram source center diagram positions) := by
  unfold AdmittedDiagram SemanticMolecule.StructurallyWellFormed
  infer_instance

theorem admitted_center_and_endpoint_positions_exact
    (source : AuthoritativeChemicalInput) (center : Nat)
    (diagram : DiagramConfiguration) (positions : List CartesianPoint2)
    (admitted : AdmittedDiagram source center diagram positions) :
    positions[center]? = some (position positions center) ∧
      ∀ bond ∈ incidentRecords diagram center,
        positions[endpoint center bond]? = some (position positions (endpoint center bond)) := by
  have centerBound : center < positions.length := by
    rw [admitted.2.1]
    exact admitted.2.2.1
  refine ⟨?_, ?_⟩
  · simp [position, List.getD, centerBound]
  · intro bond incident
    have retained : bond ∈ diagram.bonds := (List.mem_filter.mp incident).1
    have bounds : bond.source < source.molecule.atomCount ∧
        bond.target < source.molecule.atomCount ∧ bond.source ≠ bond.target :=
      of_decide_eq_true (List.all_eq_true.mp admitted.2.2.2.1 bond retained)
    have endpointBound : endpoint center bond < positions.length := by
      rw [admitted.2.1]
      unfold endpoint
      split
      · exact bounds.2.1
      · exact bounds.1
    simp [position, List.getD, endpointBound]

/-- Ordinary output data, with no proof fields or caller-chosen frame. -/
structure Frame where
  records : List DiagramBond
  endpoints : List Nat
  first : CartesianPoint3
  second : CartesianPoint3
  third : CartesianPoint3
  fourth : CartesianPoint3
  wedgeSlot : Nat
  deriving DecidableEq, Repr

def Frame.points (frame : Frame) : List CartesianPoint3 :=
  [frame.first, frame.second, frame.third, frame.fourth]

def frameOfDiagram (center : Nat) (diagram : DiagramConfiguration)
    (positions : List CartesianPoint2) : Frame :=
  let records := incidentRecords diagram center
  { records := records
    endpoints := records.map (endpoint center)
    first := liftedRecord positions center (records.getD 0 defaultRecord)
    second := liftedRecord positions center (records.getD 1 defaultRecord)
    third := liftedRecord positions center (records.getD 2 defaultRecord)
    fourth := liftedRecord positions center (records.getD 3 defaultRecord)
    wedgeSlot := records.findIdx isWedge }

/-- An independent source-level recognition predicate, expressed by the actual channel bindings
and the explicit finite drawing/semantic conditions. It does not mention the extractor. -/
def Recognized (source : AuthoritativeChemicalInput) (center : Nat) : Prop :=
  ∃ diagram positions,
    source.diagram? = some diagram ∧ diagram.atomPositions? = some positions ∧
      AdmittedDiagram source center diagram positions

/-- Meaning of an exact extracted frame, retaining its binding to the actual source order. -/
def SourceFrame (source : AuthoritativeChemicalInput) (center : Nat) (frame : Frame) : Prop :=
  ∃ diagram positions,
    source.diagram? = some diagram ∧ diagram.atomPositions? = some positions ∧
      AdmittedDiagram source center diagram positions ∧
        frame = frameOfDiagram center diagram positions

/-- Actual source-to-frame extraction. No depiction witness, parity, or permutation is an input. -/
def extract? (source : AuthoritativeChemicalInput) (center : Fin source.molecule.atomCount) :
    Option Frame :=
  match source.diagram? with
  | none => none
  | some diagram =>
      match diagram.atomPositions? with
      | none => none
      | some positions =>
          if AdmittedDiagram source center.val diagram positions then
            some (frameOfDiagram center.val diagram positions)
          else none

theorem extract?_eq_some_iff
    (source : AuthoritativeChemicalInput) (center : Fin source.molecule.atomCount) (frame : Frame) :
    extract? source center = some frame ↔ SourceFrame source center.val frame := by
  cases diagramObserved : source.diagram? with
  | none => simp [extract?, SourceFrame, diagramObserved]
  | some diagram =>
      cases positionsObserved : diagram.atomPositions? with
      | none => simp [extract?, SourceFrame, diagramObserved, positionsObserved]
      | some positions =>
          by_cases admitted : AdmittedDiagram source center.val diagram positions
          · simp [extract?, SourceFrame, diagramObserved, positionsObserved, admitted, eq_comm]
          · simp [extract?, SourceFrame, diagramObserved, positionsObserved, admitted]

theorem recognized_iff_exists_extracted_frame
    (source : AuthoritativeChemicalInput) (center : Fin source.molecule.atomCount) :
    Recognized source center.val ↔ ∃ frame, extract? source center = some frame := by
  constructor
  · rintro ⟨diagram, positions, diagramEq, positionsEq, admitted⟩
    refine ⟨frameOfDiagram center.val diagram positions,
      (extract?_eq_some_iff source center _).mpr ?_⟩
    exact ⟨diagram, positions, diagramEq, positionsEq, admitted, rfl⟩
  · rintro ⟨frame, extracted⟩
    rcases (extract?_eq_some_iff source center frame).mp extracted with
      ⟨diagram, positions, diagramEq, positionsEq, admitted, _⟩
    exact ⟨diagram, positions, diagramEq, positionsEq, admitted⟩

theorem extract?_eq_none_iff_not_recognized
    (source : AuthoritativeChemicalInput) (center : Fin source.molecule.atomCount) :
    extract? source center = none ↔ ¬Recognized source center.val := by
  rw [recognized_iff_exists_extracted_frame]
  cases extract? source center <;> simp

/-- All four lifted points are the actual incident-list map; default records do not survive
the exact four-record admission guard. -/
theorem extracted_points_are_source_written_map
    (source : AuthoritativeChemicalInput) (center : Fin source.molecule.atomCount) (frame : Frame)
    (extracted : extract? source center = some frame) :
    ∃ diagram positions,
      source.diagram? = some diagram ∧ diagram.atomPositions? = some positions ∧
        frame.records = incidentRecords diagram center.val ∧
        frame.endpoints = (incidentRecords diagram center.val).map (endpoint center.val) ∧
        frame.points = (incidentRecords diagram center.val).map
          (liftedRecord positions center.val) := by
  rcases (extract?_eq_some_iff source center frame).mp extracted with
    ⟨diagram, positions, diagramEq, positionsEq, admitted, frameEq⟩
  have lengthFour : (incidentRecords diagram center.val).length = 4 :=
    admitted.2.2.2.2.1
  rcases List.length_eq_four.mp lengthFour with ⟨first, second, third, fourth, recordsEq⟩
  subst frame
  refine ⟨diagram, positions, diagramEq, positionsEq, rfl, rfl, ?_⟩
  simp [Frame.points, frameOfDiagram, recordsEq]

/-- Completeness is conditional on the explicitly listed finite source domain, not descriptor
success. Incompatible semantic centre incidences are ruled out by actual source data. -/
theorem extracted_semantic_incidents_are_binary_single
    (source : AuthoritativeChemicalInput) (center : Fin source.molecule.atomCount) (frame : Frame)
    (extracted : extract? source center = some frame) :
    source.molecule.StructurallyWellFormed ∧
      ∀ interaction ∈ source.molecule.interactions,
        center.val ∈ interaction.participants →
          BinarySingleIncident center.val frame.endpoints interaction := by
  rcases (extract?_eq_some_iff source center frame).mp extracted with
    ⟨diagram, positions, _, _, admitted, frameEq⟩
  subst frame
  refine ⟨admitted.1, ?_⟩
  exact (semanticIncidentsAllowed?_eq_true_iff source center.val _).mp
    admitted.2.2.2.2.2.2.2.2.2.2.2.1

/-- Compute parity solely from the extracted drawing-depth representatives in source order. -/
def parity? (source : AuthoritativeChemicalInput) (center : Fin source.molecule.atomCount) :
    Option TetrahedralInputParity :=
  (extract? source center).bind fun frame => tetrahedralInputParityOfPoints? frame.points

theorem parity?_of_extracted_frame
    (source : AuthoritativeChemicalInput) (center : Fin source.molecule.atomCount) (frame : Frame)
    (extracted : extract? source center = some frame) :
    parity? source center = tetrahedralInputParityOfPoints? frame.points := by
  simp [parity?, extracted]

/-- Exact parity transport of an extracted frame, using the separately validated all-S4 Option
bridge. This theorem is a downstream algebraic view, not a permutation argument to extraction. -/
theorem extracted_point_parity_reindex (frame : Frame) (newToOld : Equiv.Perm (Fin 4)) :
    tetrahedralInputParityOfPoints?
        (RationalTetrahedralPermutation.permutedPoints
          frame.first frame.second frame.third frame.fourth newToOld) =
      (tetrahedralInputParityOfPoints? frame.points).map
        (fun parity => reindexTetrahedralInputParity parity newToOld) :=
  tetrahedralInputParityOfPoints?_permutedPoints
    frame.first frame.second frame.third frame.fourth newToOld

private theorem plain_triple_of_filter_length (first second third : DiagramBond)
    (lengthThree : (plainRecords [first, second, third]).length = 3) :
    first.style = .plain ∧ second.style = .plain ∧ third.style = .plain := by
  have allPlain : ∀ bond ∈ [first, second, third], decide (bond.style = .plain) = true :=
    List.length_filter_eq_length_iff.mp (by simpa [plainRecords] using lengthThree)
  exact ⟨of_decide_eq_true (allPlain first (by simp)),
    of_decide_eq_true (allPlain second (by simp)),
    of_decide_eq_true (allPlain third (by simp))⟩

private theorem wedgeStyle_of_isWedge (bond : DiagramBond) (wedge : isWedge bond = true) :
    bond.style = .solidWedge ∨ bond.style = .hashedWedge := by
  exact of_decide_eq_true (by simpa only [isWedge] using wedge)

private theorem wedge_style_not_plain (bond : DiagramBond)
    (wedge : bond.style = .solidWedge ∨ bond.style = .hashedWedge) :
    bond.style ≠ .plain := by
  rcases wedge with solid | hashed
  · simp [solid]
  · simp [hashed]

/-- Complete finite glyph classification from the actual four-record counts. -/
private theorem four_record_shape_of_counts (first second third fourth : DiagramBond)
    (plainCount : (plainRecords [first, second, third, fourth]).length = 3)
    (wedgeCount : (wedgeRecords [first, second, third, fourth]).length = 1) :
    (first.style = .plain ∧ second.style = .plain ∧ third.style = .plain ∧
      (fourth.style = .solidWedge ∨ fourth.style = .hashedWedge)) ∨
    (first.style = .plain ∧ second.style = .plain ∧ fourth.style = .plain ∧
      (third.style = .solidWedge ∨ third.style = .hashedWedge)) ∨
    (first.style = .plain ∧ third.style = .plain ∧ fourth.style = .plain ∧
      (second.style = .solidWedge ∨ second.style = .hashedWedge)) ∨
    (second.style = .plain ∧ third.style = .plain ∧ fourth.style = .plain ∧
      (first.style = .solidWedge ∨ first.style = .hashedWedge)) := by
  cases firstWedge : isWedge first <;> cases secondWedge : isWedge second <;>
    cases thirdWedge : isWedge third <;> cases fourthWedge : isWedge fourth <;>
      simp [wedgeRecords, firstWedge, secondWedge, thirdWedge, fourthWedge] at wedgeCount
  · have style := wedgeStyle_of_isWedge fourth fourthWedge
    have three := plain_triple_of_filter_length first second third
      (by simpa [plainRecords, List.filter_cons, wedge_style_not_plain fourth style] using plainCount)
    exact Or.inl ⟨three.1, three.2.1, three.2.2, style⟩
  · have style := wedgeStyle_of_isWedge third thirdWedge
    have three := plain_triple_of_filter_length first second fourth
      (by simpa [plainRecords, List.filter_cons, wedge_style_not_plain third style] using plainCount)
    exact Or.inr (Or.inl ⟨three.1, three.2.1, three.2.2, style⟩)
  · have style := wedgeStyle_of_isWedge second secondWedge
    have three := plain_triple_of_filter_length first third fourth
      (by simpa [plainRecords, List.filter_cons, wedge_style_not_plain second style] using plainCount)
    exact Or.inr (Or.inr (Or.inl ⟨three.1, three.2.1, three.2.2, style⟩))
  · have style := wedgeStyle_of_isWedge first firstWedge
    have three := plain_triple_of_filter_length second third fourth
      (by simpa [plainRecords, List.filter_cons, wedge_style_not_plain first style] using plainCount)
    exact Or.inr (Or.inr (Or.inr ⟨three.1, three.2.1, three.2.2, style⟩))

private theorem normalized_plain_wedge_parity_not_none
    (center first second third wedge : CartesianPoint2) (style : DiagramBondStyle)
    (wedgeStyle : style = .solidWedge ∨ style = .hashedWedge)
    (surround : PlainRaysSurround center first second third) :
    tetrahedralInputParityOfPoints?
      [planePoint first, planePoint second, planePoint third, liftedPoint wedge style] ≠ none := by
  intro refused
  have zero := (tetrahedralInputParityOfFourPoints?_eq_none_iff_zero
    (planePoint first) (planePoint second) (planePoint third) (liftedPoint wedge style)).mp refused
  rw [orientedVolume_plain_wedge_factor _ _ _ _ rfl rfl rfl] at zero
  have areaNonzero := plainRaysSurround_area_ne_zero center first second third surround
  rcases wedgeStyle with solid | hashed
  · exact areaNonzero (by simpa [liftedPoint, solid] using zero)
  · exact areaNonzero (by simpa [liftedPoint, hashed] using zero)

/-- A recognized actual source always gives a nondegenerate parity. The finite slot analysis
derives its reordering from the unique wedge position; no caller permutation is assumed. -/
theorem extracted_frame_parity_not_none
    (source : AuthoritativeChemicalInput) (center : Fin source.molecule.atomCount) (frame : Frame)
    (extracted : extract? source center = some frame) :
    tetrahedralInputParityOfPoints? frame.points ≠ none := by
  rcases (extract?_eq_some_iff source center frame).mp extracted with
    ⟨drawing, positions, _, _, admitted, frameEq⟩
  rcases admitted with ⟨_, _, _, _, lengthFour, _, _, _, plainCount,
    wedgeCount, _, _, _, surrounding⟩
  rcases List.length_eq_four.mp lengthFour with ⟨first, second, third, fourth, recordsEq⟩
  rw [recordsEq] at plainCount wedgeCount surrounding
  rcases four_record_shape_of_counts first second third fourth plainCount wedgeCount with
    ⟨firstPlain, secondPlain, thirdPlain, wedgeStyle⟩ |
    ⟨firstPlain, secondPlain, fourthPlain, wedgeStyle⟩ |
    ⟨firstPlain, thirdPlain, fourthPlain, wedgeStyle⟩ |
    ⟨secondPlain, thirdPlain, fourthPlain, wedgeStyle⟩
  · have surround : PlainRaysSurround (position positions center.val)
        (position positions (endpoint center.val first))
        (position positions (endpoint center.val second))
        (position positions (endpoint center.val third)) := by
      simpa [plainRecords, firstPlain, secondPlain, thirdPlain,
        wedge_style_not_plain fourth wedgeStyle] using surrounding
    simpa [frameEq, Frame.points, frameOfDiagram, recordsEq, liftedRecord,
      liftedPoint, firstPlain, secondPlain, thirdPlain] using
      normalized_plain_wedge_parity_not_none
        (position positions center.val)
        (position positions (endpoint center.val first))
        (position positions (endpoint center.val second))
        (position positions (endpoint center.val third))
        (position positions (endpoint center.val fourth)) fourth.style wedgeStyle surround
  · have surround : PlainRaysSurround (position positions center.val)
        (position positions (endpoint center.val first))
        (position positions (endpoint center.val second))
        (position positions (endpoint center.val fourth)) := by
      simpa [plainRecords, firstPlain, secondPlain, fourthPlain,
        wedge_style_not_plain third wedgeStyle] using surrounding
    have normalized := normalized_plain_wedge_parity_not_none
      (position positions center.val)
      (position positions (endpoint center.val first))
      (position positions (endpoint center.val second))
      (position positions (endpoint center.val fourth))
      (position positions (endpoint center.val third)) third.style wedgeStyle surround
    have transport := tetrahedralInputParityOfPoints?_permutedPoints_eq_none_iff
      (planePoint (position positions (endpoint center.val first)))
      (planePoint (position positions (endpoint center.val second)))
      (planePoint (position positions (endpoint center.val fourth)))
      (liftedPoint (position positions (endpoint center.val third)) third.style)
      (Equiv.swap (2 : Fin 4) 3)
    intro refused
    apply normalized
    apply transport.mp
    simpa [frameEq, Frame.points, frameOfDiagram, recordsEq, liftedRecord,
      liftedPoint, firstPlain, secondPlain, fourthPlain,
      RationalTetrahedralPermutation.permutedPoints,
      RationalTetrahedralPermutation.pointVector,
      Equiv.trans_apply, Equiv.swap_apply_def] using refused
  · have surround : PlainRaysSurround (position positions center.val)
        (position positions (endpoint center.val first))
        (position positions (endpoint center.val third))
        (position positions (endpoint center.val fourth)) := by
      simpa [plainRecords, firstPlain, thirdPlain, fourthPlain,
        wedge_style_not_plain second wedgeStyle] using surrounding
    have normalized := normalized_plain_wedge_parity_not_none
      (position positions center.val)
      (position positions (endpoint center.val first))
      (position positions (endpoint center.val third))
      (position positions (endpoint center.val fourth))
      (position positions (endpoint center.val second)) second.style wedgeStyle surround
    have transport := tetrahedralInputParityOfPoints?_permutedPoints_eq_none_iff
      (planePoint (position positions (endpoint center.val first)))
      (planePoint (position positions (endpoint center.val third)))
      (planePoint (position positions (endpoint center.val fourth)))
      (liftedPoint (position positions (endpoint center.val second)) second.style)
      ((Equiv.swap (1 : Fin 4) 2).trans (Equiv.swap (2 : Fin 4) 3))
    intro refused
    apply normalized
    apply transport.mp
    simpa [frameEq, Frame.points, frameOfDiagram, recordsEq, liftedRecord,
      liftedPoint, firstPlain, thirdPlain, fourthPlain,
      RationalTetrahedralPermutation.permutedPoints,
      RationalTetrahedralPermutation.pointVector,
      Equiv.trans_apply, Equiv.swap_apply_def] using refused
  · have surround : PlainRaysSurround (position positions center.val)
        (position positions (endpoint center.val second))
        (position positions (endpoint center.val third))
        (position positions (endpoint center.val fourth)) := by
      simpa [plainRecords, secondPlain, thirdPlain, fourthPlain,
        wedge_style_not_plain first wedgeStyle] using surrounding
    have normalized := normalized_plain_wedge_parity_not_none
      (position positions center.val)
      (position positions (endpoint center.val second))
      (position positions (endpoint center.val third))
      (position positions (endpoint center.val fourth))
      (position positions (endpoint center.val first)) first.style wedgeStyle surround
    have transport := tetrahedralInputParityOfPoints?_permutedPoints_eq_none_iff
      (planePoint (position positions (endpoint center.val second)))
      (planePoint (position positions (endpoint center.val third)))
      (planePoint (position positions (endpoint center.val fourth)))
      (liftedPoint (position positions (endpoint center.val first)) first.style)
      ((Equiv.swap (0 : Fin 4) 1).trans
        ((Equiv.swap (1 : Fin 4) 2).trans (Equiv.swap (2 : Fin 4) 3)))
    intro refused
    apply normalized
    apply transport.mp
    simpa [frameEq, Frame.points, frameOfDiagram, recordsEq, liftedRecord,
      liftedPoint, secondPlain, thirdPlain, fourthPlain,
      RationalTetrahedralPermutation.permutedPoints,
      RationalTetrahedralPermutation.pointVector,
      Equiv.trans_apply, Equiv.swap_apply_def] using refused

/-- Source recognition is exactly successful parity availability in the stated finite domain. -/
theorem recognized_iff_exists_parity
    (source : AuthoritativeChemicalInput) (center : Fin source.molecule.atomCount) :
    Recognized source center.val ↔ ∃ parity, parity? source center = some parity := by
  constructor
  · intro recognized
    rcases (recognized_iff_exists_extracted_frame source center).mp recognized with
      ⟨frame, extracted⟩
    have nonempty := extracted_frame_parity_not_none source center frame extracted
    rw [parity?_of_extracted_frame source center frame extracted]
    cases observed : tetrahedralInputParityOfPoints? frame.points with
    | none => exact False.elim (nonempty observed)
    | some parity => exact ⟨parity, rfl⟩
  · rintro ⟨parity, succeeded⟩
    cases observed : extract? source center with
    | none => simp [parity?, observed] at succeeded
    | some frame =>
        exact (recognized_iff_exists_extracted_frame source center).mpr ⟨frame, observed⟩

theorem parity?_eq_none_iff_not_recognized
    (source : AuthoritativeChemicalInput) (center : Fin source.molecule.atomCount) :
    parity? source center = none ↔ ¬Recognized source center.val := by
  rw [recognized_iff_exists_parity]
  cases parity? source center <;> simp

end SingleWedgeSource
end AuthoritativeChemicalInput

namespace SingleWedgeSourceRegression

open AuthoritativeChemicalInput.SingleWedgeSource

def carbon : SemanticAtom := { element := ⟨6, by decide, by decide⟩ }
def fluorine : SemanticAtom := { element := ⟨9, by decide, by decide⟩ }
def chlorine : SemanticAtom := { element := ⟨17, by decide, by decide⟩ }
def bromine : SemanticAtom := { element := ⟨35, by decide, by decide⟩ }
def iodine : SemanticAtom := { element := ⟨53, by decide, by decide⟩ }

def molecule : SemanticMolecule :=
  { atoms := [carbon, fluorine, chlorine, bromine, iodine]
    interactions := [
      ⟨[0, 1], .covalent 1⟩, ⟨[0, 2], .covalent 1⟩,
      ⟨[0, 3], .covalent 1⟩, ⟨[0, 4], .covalent 1⟩] }

def positions : List CartesianPoint2 :=
  [⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨1, 1⟩]

def diagramWithStyle (style : DiagramBondStyle) : DiagramConfiguration :=
  { atomPositions? := some positions
    bonds := [⟨0, 1, .plain, .absolute⟩, ⟨0, 2, .plain, .absolute⟩,
      ⟨0, 3, .plain, .absolute⟩, ⟨0, 4, style, .absolute⟩] }

def diagram : DiagramConfiguration := diagramWithStyle .solidWedge

def sourceWithStyle (style : DiagramBondStyle) : AuthoritativeChemicalInput :=
  { molecule := molecule, diagram? := some (diagramWithStyle style) }

def source : AuthoritativeChemicalInput := sourceWithStyle .solidWedge

def center (input : AuthoritativeChemicalInput) (bounded : 0 < input.molecule.atomCount) :
    Fin input.molecule.atomCount := ⟨0, bounded⟩

def withDiagram (drawing : DiagramConfiguration) : AuthoritativeChemicalInput :=
  { molecule := molecule, diagram? := some drawing }

def withInteractions (interactions : List SemanticInteraction) : AuthoritativeChemicalInput :=
  { molecule := { molecule with interactions := interactions }, diagram? := some (diagram) }

theorem solid_source_recognized :
    (extract? (source) (center (source) (by decide))).isSome = true := by decide +kernel

theorem hashed_source_recognized :
    (extract? (sourceWithStyle .hashedWedge)
      (center (sourceWithStyle .hashedWedge) (by decide))).isSome = true := by
  decide +kernel

/-! ### Exact parity fixtures

The plain endpoints at `(1, 0)`, `(0, 1)`, `(-1, -1)` surround the centre `(0, 0)` in the
positive cyclic sense, so their doubled plain area is `3`.  The written-order affine determinant
anchored at the wedge endpoint is `-3` for the solid wedge (`z = +1`, toward the viewer) and `+3`
for the hashed wedge (`z = -1`, away from the viewer).  Under the calibrated right-handed carrier
assignment a negative determinant is `.clockwise` and a positive determinant is `.anticlockwise`.

Five of the declaration names below are historical API keys pinned by the kernel certificate and
predate the handedness calibration; their suffixes name the old carrier assignment.  Each retains
its old identifier with the corrected statement, and an accurately named sibling states the same
result for new code. -/

/-- **Solid wedge fixture, historical API key.**  The old suffix says `anticlockwise`; the
corrected carrier for a positive solid-wedge depth is `.clockwise`.  Use
`solid_source_has_clockwise_parity` for new code. -/
theorem solid_source_has_anticlockwise_parity :
    parity? (source) (center (source) (by decide)) = some .clockwise := by decide +kernel

/-- **Solid wedge fixture, accurate name.** -/
theorem solid_source_has_clockwise_parity :
    parity? (source) (center (source) (by decide)) = some .clockwise :=
  solid_source_has_anticlockwise_parity

/-- **Hashed wedge fixture, historical API key.**  The old suffix says `clockwise`; the corrected
carrier for a negative hashed-wedge depth is `.anticlockwise`.  Use
`hashed_source_has_anticlockwise_parity` for new code. -/
theorem hashed_source_has_clockwise_parity :
    parity? (sourceWithStyle .hashedWedge)
      (center (sourceWithStyle .hashedWedge) (by decide)) =
      some .anticlockwise := by decide +kernel

/-- **Hashed wedge fixture, accurate name.** -/
theorem hashed_source_has_anticlockwise_parity :
    parity? (sourceWithStyle .hashedWedge)
      (center (sourceWithStyle .hashedWedge) (by decide)) =
      some .anticlockwise :=
  hashed_source_has_clockwise_parity

def wedgeFirstSource : AuthoritativeChemicalInput :=
  withDiagram { (diagram) with bonds :=
    [⟨0, 4, .solidWedge, .absolute⟩, ⟨0, 1, .plain, .absolute⟩,
      ⟨0, 2, .plain, .absolute⟩, ⟨0, 3, .plain, .absolute⟩] }

def wedgeSecondSource : AuthoritativeChemicalInput :=
  withDiagram { (diagram) with bonds :=
    [⟨0, 1, .plain, .absolute⟩, ⟨0, 4, .solidWedge, .absolute⟩,
      ⟨0, 2, .plain, .absolute⟩, ⟨0, 3, .plain, .absolute⟩] }

def wedgeThirdSource : AuthoritativeChemicalInput :=
  withDiagram { (diagram) with bonds :=
    [⟨0, 1, .plain, .absolute⟩, ⟨0, 2, .plain, .absolute⟩,
      ⟨0, 4, .solidWedge, .absolute⟩, ⟨0, 3, .plain, .absolute⟩] }

/-- **Wedge-first frame, historical API key.**  The written order starts with the solid-wedge
endpoint, so the written-order determinant is the opposite of the plain-first base frame:
`+3`, hence `.anticlockwise`.  The old suffix says `clockwise`; use
`wedge_first_source_has_anticlockwise_parity` for new code. -/
theorem wedge_first_source_has_clockwise_parity :
    parity? wedgeFirstSource (center wedgeFirstSource (by decide)) = some .anticlockwise := by
  decide +kernel

/-- **Wedge-first frame, accurate name.** -/
theorem wedge_first_source_has_anticlockwise_parity :
    parity? wedgeFirstSource (center wedgeFirstSource (by decide)) = some .anticlockwise :=
  wedge_first_source_has_clockwise_parity

/-- **Wedge-second frame, historical API key.**  Moving the solid wedge from the fourth to the
second written slot is an even permutation of the base frame, so the determinant stays `-3` and
the carrier is `.clockwise`.  The old suffix says `anticlockwise`; use
`wedge_second_source_has_clockwise_parity` for new code. -/
theorem wedge_second_source_has_anticlockwise_parity :
    parity? wedgeSecondSource (center wedgeSecondSource (by decide)) =
      some .clockwise := by decide +kernel

/-- **Wedge-second frame, accurate name.** -/
theorem wedge_second_source_has_clockwise_parity :
    parity? wedgeSecondSource (center wedgeSecondSource (by decide)) = some .clockwise :=
  wedge_second_source_has_anticlockwise_parity

/-- **Wedge-third frame, historical API key.**  Moving the solid wedge from the fourth to the
third written slot is an odd permutation of the base frame, so the determinant is `+3` and the
carrier is `.anticlockwise`.  The old suffix says `clockwise`; use
`wedge_third_source_has_anticlockwise_parity` for new code. -/
theorem wedge_third_source_has_clockwise_parity :
    parity? wedgeThirdSource (center wedgeThirdSource (by decide)) = some .anticlockwise := by
  decide +kernel

/-- **Wedge-third frame, accurate name.** -/
theorem wedge_third_source_has_anticlockwise_parity :
    parity? wedgeThirdSource (center wedgeThirdSource (by decide)) = some .anticlockwise :=
  wedge_third_source_has_clockwise_parity

theorem wedge_first_endpoint_order_is_source_order :
    (extract? wedgeFirstSource (center wedgeFirstSource (by decide))).map
        (fun frame => (frame.endpoints, frame.wedgeSlot)) = some ([4, 1, 2, 3], 0) := by
  decide +kernel

theorem wedge_last_endpoint_order_is_source_order :
    (extract? source (center source (by decide))).map
        (fun frame => (frame.endpoints, frame.wedgeSlot)) = some ([1, 2, 3, 4], 3) := by
  decide +kernel

def nonAbsoluteSource (scope : DiagramConfigurationScope) : AuthoritativeChemicalInput :=
  withDiagram { (diagram) with bonds :=
    [⟨0, 1, .plain, .absolute⟩, ⟨0, 2, .plain, .absolute⟩,
      ⟨0, 3, .plain, .absolute⟩, ⟨0, 4, .solidWedge, scope⟩] }

theorem relative_source_refused :
    extract? (nonAbsoluteSource (.relative 1))
      (center (nonAbsoluteSource (.relative 1)) (by decide)) = none := by decide +kernel

theorem racemic_source_refused :
    extract? (nonAbsoluteSource (.racemic 1))
      (center (nonAbsoluteSource (.racemic 1)) (by decide)) = none := by decide +kernel

theorem unknown_source_refused :
    extract? (nonAbsoluteSource .unknown)
      (center (nonAbsoluteSource .unknown) (by decide)) = none := by decide +kernel

def reversedSource : AuthoritativeChemicalInput :=
  withDiagram { (diagram) with bonds :=
    [⟨0, 1, .plain, .absolute⟩, ⟨0, 2, .plain, .absolute⟩,
      ⟨0, 3, .plain, .absolute⟩, ⟨4, 0, .solidWedge, .absolute⟩] }

theorem reversed_source_refused :
    extract? reversedSource (center reversedSource (by decide)) = none := by decide +kernel

def secondWedgeSource : AuthoritativeChemicalInput :=
  withDiagram { (diagram) with bonds :=
    [⟨0, 1, .plain, .absolute⟩, ⟨0, 2, .plain, .absolute⟩,
      ⟨0, 3, .hashedWedge, .absolute⟩, ⟨0, 4, .solidWedge, .absolute⟩] }

theorem second_wedge_source_refused :
    extract? secondWedgeSource (center secondWedgeSource (by decide)) = none := by decide +kernel

def duplicateSource : AuthoritativeChemicalInput :=
  withDiagram { (diagram) with bonds := (diagram).bonds ++ [⟨0, 4, .solidWedge, .absolute⟩] }

theorem duplicate_source_refused :
    extract? duplicateSource (center duplicateSource (by decide)) = none := by decide +kernel

def slashSource : AuthoritativeChemicalInput :=
  withDiagram { (diagram) with bonds :=
    [⟨0, 1, .directionalUp, .absolute⟩, ⟨0, 2, .plain, .absolute⟩,
      ⟨0, 3, .plain, .absolute⟩, ⟨0, 4, .solidWedge, .absolute⟩] }

theorem slash_source_refused :
    extract? slashSource (center slashSource (by decide)) = none := by decide +kernel

def higherBondSource : AuthoritativeChemicalInput :=
  withInteractions (molecule.interactions ++ [⟨[0, 1], .covalent 2⟩])

theorem hidden_higher_bond_source_refused :
    extract? higherBondSource (center higherBondSource (by decide)) = none := by decide +kernel

def coordinateSource : AuthoritativeChemicalInput :=
  withInteractions (molecule.interactions ++ [⟨[0, 1], .coordinate⟩])

theorem hidden_coordinate_source_refused :
    extract? coordinateSource (center coordinateSource (by decide)) = none := by decide +kernel

def multicenterSource : AuthoritativeChemicalInput :=
  withInteractions (molecule.interactions ++ [⟨[0, 1, 2], .multicenter 2⟩])

theorem hidden_multicenter_source_refused :
    extract? multicenterSource (center multicenterSource (by decide)) = none := by decide +kernel

def outOfRangeSource : AuthoritativeChemicalInput :=
  withInteractions (molecule.interactions ++ [⟨[0, 5], .covalent 1⟩])

theorem hidden_out_of_range_source_refused :
    extract? outOfRangeSource (center outOfRangeSource (by decide)) = none := by decide +kernel

def missingPositionsSource : AuthoritativeChemicalInput :=
  withDiagram { (diagram) with atomPositions? := none }

theorem missing_positions_source_refused :
    extract? missingPositionsSource (center missingPositionsSource (by decide)) = none := by decide +kernel

def shortPositionsSource : AuthoritativeChemicalInput :=
  withDiagram { (diagram) with atomPositions? := some [⟨0, 0⟩] }

theorem short_positions_source_refused :
    extract? shortPositionsSource (center shortPositionsSource (by decide)) = none := by decide +kernel

def nonSurroundingSource : AuthoritativeChemicalInput :=
  withDiagram { (diagram) with
    atomPositions? := some [⟨0, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨3, 0⟩, ⟨1, 1⟩] }

theorem non_surrounding_source_refused :
    extract? nonSurroundingSource (center nonSurroundingSource (by decide)) = none := by decide +kernel

end SingleWedgeSourceRegression
end TetraStereo.OneCenter
