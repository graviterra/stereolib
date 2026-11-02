import TetraStereo.OneCenter.P94CoordinateTorsion

set_option autoImplicit false

namespace TetraStereo.OneCenter

open BlueBookP94

/-!
# Molecule- and participant-backed P-94 coordinate torsions

This module joins the exact point-frame construction to the molecule-bound P-94 report.  The
physical carrier now names a finite bonded `A-...-B` axis and its typed terminal participants.
Ordinary participants must be bonded to the corresponding axis endpoint, lone-pair phantoms must
belong to that endpoint, and duplicate participants must name an atom joined by bond order greater
than one.  Exact virtual points remain explicit geometry evidence because nuclear coordinates do
not by themselves determine an electron-pair direction.
-/

namespace BlueBookP94.CoordinateTorsion

inductive VirtualTorsionParticipant where
  | lonePair (center : ℕ)
  | duplicateAtom (original : ℕ)
  deriving DecidableEq, Repr

namespace VirtualTorsionParticipant

def toParticipant : VirtualTorsionParticipant → TorsionParticipant ℕ
  | .lonePair center => .lonePair center
  | .duplicateAtom original => .duplicateAtom original

end VirtualTorsionParticipant

structure VirtualTorsionPoint where
  participant : VirtualTorsionParticipant
  point : CartesianPoint3
  deriving DecidableEq, Repr

abbrev VirtualTorsionPointLedger := List VirtualTorsionPoint

namespace VirtualTorsionPointLedger

def keys (ledger : VirtualTorsionPointLedger) : List VirtualTorsionParticipant :=
  ledger.map VirtualTorsionPoint.participant

def Valid (ledger : VirtualTorsionPointLedger) : Prop :=
  (keys ledger).Nodup

def PointAt (ledger : VirtualTorsionPointLedger)
    (participant : VirtualTorsionParticipant) (point : CartesianPoint3) : Prop :=
  ∃ entry ∈ ledger, entry.participant = participant ∧ entry.point = point

def lookup : VirtualTorsionPointLedger →
    VirtualTorsionParticipant → Option CartesianPoint3
  | [], _ => none
  | entry :: rest, participant =>
      if entry.participant = participant then some entry.point
      else lookup rest participant

theorem lookup_eq_some_iff (ledger : VirtualTorsionPointLedger)
    (valid : Valid ledger) (participant : VirtualTorsionParticipant)
    (point : CartesianPoint3) :
    lookup ledger participant = some point ↔ PointAt ledger participant point := by
  induction ledger with
  | nil => simp [lookup, PointAt]
  | cons entry rest ih =>
      have nodup : (entry.participant :: keys rest).Nodup := by
        simpa [Valid, keys] using valid
      have entryNotIn : entry.participant ∉ keys rest := (List.nodup_cons.mp nodup).1
      have restValid : Valid rest := by
        simpa [Valid, keys] using (List.nodup_cons.mp nodup).2
      by_cases same : entry.participant = participant
      · subst participant
        constructor
        · intro computed
          have pointEq : entry.point = point := by
            simpa [lookup] using computed
          exact ⟨entry, by simp, rfl, pointEq⟩
        · rintro ⟨selected, selectedPresent, participantEq, pointEq⟩
          rcases List.mem_cons.mp selectedPresent with selectedEq | selectedInRest
          · subst selected
            simpa [lookup] using congrArg some pointEq
          · exfalso
            apply entryNotIn
            apply List.mem_map.mpr
            exact ⟨selected, selectedInRest, participantEq⟩
      · constructor
        · intro computed
          have tailComputed : lookup rest participant = some point := by
            simpa [lookup, same] using computed
          rcases (ih restValid).mp tailComputed with
            ⟨selected, selectedPresent, participantEq, pointEq⟩
          exact ⟨selected, by simp [selectedPresent], participantEq, pointEq⟩
        · rintro ⟨selected, selectedPresent, participantEq, pointEq⟩
          rcases List.mem_cons.mp selectedPresent with selectedEq | selectedInRest
          · subst selected
            exact False.elim (same participantEq)
          · have tailComputed : lookup rest participant = some point :=
              (ih restValid).mpr
                ⟨selected, selectedInRest, participantEq, pointEq⟩
            simpa [lookup, same] using tailComputed

end VirtualTorsionPointLedger

/-- Independent point meaning for every P-94 participant kind.  Physical atoms come from the
spatial configuration; only the two source-defined phantom kinds consult the virtual ledger. -/
def ParticipantPointAt (spatial : SpatialConfiguration)
    (ledger : VirtualTorsionPointLedger) (participant : TorsionParticipant ℕ)
    (point : CartesianPoint3) : Prop :=
  match participant with
  | .atom atom => spatial.positions[atom]? = some point
  | .lonePair center => VirtualTorsionPointLedger.PointAt ledger (.lonePair center) point
  | .duplicateAtom original =>
      VirtualTorsionPointLedger.PointAt ledger (.duplicateAtom original) point

def participantPoint? (spatial : SpatialConfiguration)
    (ledger : VirtualTorsionPointLedger) :
    TorsionParticipant ℕ → Option CartesianPoint3
  | .atom atom => spatial.positions[atom]?
  | .lonePair center => VirtualTorsionPointLedger.lookup ledger (.lonePair center)
  | .duplicateAtom original =>
      VirtualTorsionPointLedger.lookup ledger (.duplicateAtom original)

theorem participantPoint?_eq_some_iff (spatial : SpatialConfiguration)
    (ledger : VirtualTorsionPointLedger) (valid : VirtualTorsionPointLedger.Valid ledger)
    (participant : TorsionParticipant ℕ) (point : CartesianPoint3) :
    participantPoint? spatial ledger participant = some point ↔
      ParticipantPointAt spatial ledger participant point := by
  cases participant with
  | atom atom => rfl
  | lonePair center =>
      exact VirtualTorsionPointLedger.lookup_eq_some_iff
        ledger valid (.lonePair center) point
  | duplicateAtom original =>
      exact VirtualTorsionPointLedger.lookup_eq_some_iff
        ledger valid (.duplicateAtom original) point

/-- Replace only the angle of a molecule-backed torsion record. -/
def withAngle (record : P94TorsionEvidence)
    (angle : TorsionAngle) : P94TorsionEvidence :=
  { record with frame := { record.frame with angle := angle } }

@[simp] theorem withAngle_unit
    (record : P94TorsionEvidence) (angle : TorsionAngle) :
    (withAngle record angle).unit = record.unit :=
  rfl

@[simp] theorem withAngle_frame_front
    (record : P94TorsionEvidence) (angle : TorsionAngle) :
    (withAngle record angle).frame.front = record.frame.front :=
  rfl

@[simp] theorem withAngle_frame_rear
    (record : P94TorsionEvidence) (angle : TorsionAngle) :
    (withAngle record angle).frame.rear = record.frame.rear :=
  rfl

@[simp] theorem withAngle_frame_angle
    (record : P94TorsionEvidence) (angle : TorsionAngle) :
    (withAngle record angle).frame.angle = angle :=
  rfl

theorem withAngle_selectedBySourceCriteria_iff
    (record : P94TorsionEvidence) (angle : TorsionAngle) :
    (withAngle record angle).SelectedBySourceCriteria ↔ record.SelectedBySourceCriteria :=
  Iff.rfl

theorem withAngle_candidateParticipantsBounded_iff
    (record : P94TorsionEvidence) (angle : TorsionAngle) (atomCount : ℕ) :
    (withAngle record angle).CandidateParticipantsBounded atomCount ↔
      record.CandidateParticipantsBounded atomCount :=
  Iff.rfl

theorem withAngle_axisParticipantsValid_iff
    (record : P94TorsionEvidence) (angle : TorsionAngle) (molecule : RawMolecule) :
    (withAngle record angle).AxisParticipantsValid molecule ↔
      record.AxisParticipantsValid molecule :=
  Iff.rfl

/-- Every point on a multi-atom rotation axis lies on the exact line through its named endpoints. -/
def AxisPathCollinear (spatial : SpatialConfiguration) (unit : P94ConformationUnit)
    (axisFrontPoint axisRearPoint : CartesianPoint3) : Prop :=
  ∀ atom ∈ unit.atoms,
    ∃ point,
      spatial.positions[atom]? = some point ∧
      RationalVector3.cross
        (CartesianPoint3.displacement axisFrontPoint axisRearPoint)
        (CartesianPoint3.displacement axisFrontPoint point) =
          { x := 0, y := 0, z := 0 }

/-- Non-geometric gates needed before a coordinate-derived record may enter the public report. -/
def CoordinateTorsionMolecularGate (molecule : RawMolecule)
    (ledger : VirtualTorsionPointLedger) (record : P94TorsionEvidence) : Prop :=
  record.unit.kind = .torsionAxis ∧
    record.unit.ValidFor molecule ∧
    (record.CandidateParticipantsBounded molecule.atomCount ∧
      record.AxisParticipantsValid molecule) ∧
    record.SelectedBySourceCriteria ∧ VirtualTorsionPointLedger.Valid ledger

/-- Independent full judgment for deriving one P-94 torsion record from a molecule, its exact
spatial configuration, and any explicitly supplied phantom points. -/
def CoordinateTorsionEvidenceJudgment (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (ledger : VirtualTorsionPointLedger)
    (input output : P94TorsionEvidence) : Prop :=
  CoordinateTorsionMolecularGate molecule ledger input ∧
  ∃ axisFront axisRear frontPoint axisFrontPoint axisRearPoint rearPoint angle,
    input.unit.AxisEndpoints axisFront axisRear ∧
    ParticipantPointAt spatial ledger input.frame.front frontPoint ∧
    spatial.positions[axisFront]? = some axisFrontPoint ∧
    spatial.positions[axisRear]? = some axisRearPoint ∧
    ParticipantPointAt spatial ledger input.frame.rear rearPoint ∧
    AxisPathCollinear spatial input.unit axisFrontPoint axisRearPoint ∧
    ExactTorsionAngle
      { front := frontPoint
        axisFront := axisFrontPoint
        axisRear := axisRearPoint
        rear := rearPoint }
      angle ∧
    output = withAngle input angle

/-- Specification-level coordinate constructor.  All real and proposition decisions remain exact;
there is no floating-point or compiler-native evaluation. -/
noncomputable def coordinateTorsionEvidence? (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (ledger : VirtualTorsionPointLedger)
    (input : P94TorsionEvidence) : Option P94TorsionEvidence := by
  classical
  exact do
    let axisFront ← input.unit.atoms.head?
    let axisRear ← input.unit.atoms.getLast?
    let frontPoint ← participantPoint? spatial ledger input.frame.front
    let axisFrontPoint ← spatial.positions[axisFront]?
    let axisRearPoint ← spatial.positions[axisRear]?
    let rearPoint ← participantPoint? spatial ledger input.frame.rear
    let angle ← torsionAngleOfPoints?
      { front := frontPoint
        axisFront := axisFrontPoint
        axisRear := axisRearPoint
        rear := rearPoint }
    if accepted : CoordinateTorsionMolecularGate molecule ledger input ∧
        AxisPathCollinear spatial input.unit axisFrontPoint axisRearPoint then
      some (withAngle input angle)
    else none

theorem coordinateTorsionEvidence?_eq_some_iff (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (ledger : VirtualTorsionPointLedger)
    (input output : P94TorsionEvidence) :
    coordinateTorsionEvidence? molecule spatial ledger input = some output ↔
      CoordinateTorsionEvidenceJudgment molecule spatial ledger input output := by
  classical
  constructor
  · intro computed
    cases axisFrontEq : input.unit.atoms.head? with
    | none => simp [coordinateTorsionEvidence?, axisFrontEq] at computed
    | some axisFront =>
        cases axisRearEq : input.unit.atoms.getLast? with
        | none => simp [coordinateTorsionEvidence?, axisFrontEq, axisRearEq] at computed
        | some axisRear =>
            cases frontPointEq : participantPoint? spatial ledger input.frame.front with
            | none =>
                simp [coordinateTorsionEvidence?, axisFrontEq, axisRearEq,
                  frontPointEq] at computed
            | some frontPoint =>
                cases axisFrontPointEq : spatial.positions[axisFront]? with
                | none =>
                    simp [coordinateTorsionEvidence?, axisFrontEq, axisRearEq,
                      frontPointEq, axisFrontPointEq] at computed
                | some axisFrontPoint =>
                    cases axisRearPointEq : spatial.positions[axisRear]? with
                    | none =>
                        simp [coordinateTorsionEvidence?, axisFrontEq, axisRearEq,
                          frontPointEq, axisRearPointEq] at computed
                    | some axisRearPoint =>
                        cases rearPointEq : participantPoint? spatial ledger input.frame.rear with
                        | none =>
                            simp [coordinateTorsionEvidence?, axisFrontEq, axisRearEq,
                              frontPointEq, rearPointEq] at computed
                        | some rearPoint =>
                            let frame : PointFrame :=
                              { front := frontPoint
                                axisFront := axisFrontPoint
                                axisRear := axisRearPoint
                                rear := rearPoint }
                            cases angleEq : torsionAngleOfPoints? frame with
                            | none =>
                                simp [coordinateTorsionEvidence?, axisFrontEq, axisRearEq,
                                  frontPointEq, axisFrontPointEq, axisRearPointEq,
                                  rearPointEq, frame, angleEq] at computed
                            | some angle =>
                                by_cases accepted :
                                    CoordinateTorsionMolecularGate molecule ledger input ∧
                                      AxisPathCollinear spatial input.unit
                                        axisFrontPoint axisRearPoint
                                · have outputEq : output = withAngle input angle := by
                                    simpa [coordinateTorsionEvidence?, axisFrontEq, axisRearEq,
                                      frontPointEq, axisFrontPointEq, axisRearPointEq,
                                      rearPointEq, frame, angleEq, accepted] using computed.symm
                                  refine ⟨accepted.1, axisFront, axisRear, frontPoint,
                                    axisFrontPoint, axisRearPoint, rearPoint, angle, ?_, ?_,
                                    axisFrontPointEq, axisRearPointEq, ?_, accepted.2, ?_, outputEq⟩
                                  · exact ⟨axisFrontEq, axisRearEq⟩
                                  · exact (participantPoint?_eq_some_iff
                                      spatial ledger accepted.1.2.2.2.2 input.frame.front
                                        frontPoint).mp frontPointEq
                                  · exact (participantPoint?_eq_some_iff
                                      spatial ledger accepted.1.2.2.2.2 input.frame.rear
                                        rearPoint).mp rearPointEq
                                  · exact (torsionAngleOfPoints?_eq_some_iff frame angle).mp angleEq
                                · simp [coordinateTorsionEvidence?, axisFrontEq, axisRearEq,
                                    frontPointEq, axisFrontPointEq, axisRearPointEq,
                                    rearPointEq, frame, angleEq, accepted] at computed
  · rintro ⟨gate, axisFront, axisRear, frontPoint, axisFrontPoint,
      axisRearPoint, rearPoint, angle, endpoints, frontJudgment,
      axisFrontPointEq, axisRearPointEq, rearJudgment, collinear,
      angleJudgment, outputEq⟩
    have frontPointEq := (participantPoint?_eq_some_iff
      spatial ledger gate.2.2.2.2 input.frame.front frontPoint).mpr frontJudgment
    have rearPointEq := (participantPoint?_eq_some_iff
      spatial ledger gate.2.2.2.2 input.frame.rear rearPoint).mpr rearJudgment
    have angleEq := (torsionAngleOfPoints?_eq_some_iff _ angle).mpr angleJudgment
    subst output
    simp [coordinateTorsionEvidence?, endpoints.1, endpoints.2, frontPointEq,
      axisFrontPointEq, axisRearPointEq, rearPointEq, angleEq, gate, collinear]

theorem coordinateTorsionEvidence?_eq_none_iff (molecule : RawMolecule)
    (spatial : SpatialConfiguration) (ledger : VirtualTorsionPointLedger)
    (input : P94TorsionEvidence) :
    coordinateTorsionEvidence? molecule spatial ledger input = none ↔
      ¬∃ output, CoordinateTorsionEvidenceJudgment molecule spatial ledger input output := by
  constructor
  · intro computed ⟨output, judgment⟩
    have some := (coordinateTorsionEvidence?_eq_some_iff
      molecule spatial ledger input output).mpr judgment
    rw [computed] at some
    simp at some
  · intro absent
    cases computed : coordinateTorsionEvidence? molecule spatial ledger input with
    | none => rfl
    | some output =>
        exfalso
        exact absent ⟨output,
          (coordinateTorsionEvidence?_eq_some_iff
            molecule spatial ledger input output).mp computed⟩

/-- Every successful molecule/coordinate record supports at least one exact P-94 angular class. -/
theorem coordinateTorsionEvidence_success_supports_classification
    (molecule : RawMolecule) (spatial : SpatialConfiguration)
    (ledger : VirtualTorsionPointLedger) (input output : P94TorsionEvidence)
    (computed : coordinateTorsionEvidence? molecule spatial ledger input = some output) :
    ∃ classification,
      (P94ConformationEvidence.torsion output :
        P94ConformationEvidence PUnit PUnit).Supports (.torsionClass classification) := by
  rcases (coordinateTorsionEvidence?_eq_some_iff
    molecule spatial ledger input output).mp computed with
    ⟨gate, axisFront, axisRear, frontPoint, axisFrontPoint,
      axisRearPoint, rearPoint, angle, endpoints, frontJudgment,
      axisFrontPointEq, axisRearPointEq, rearJudgment, collinear,
      angleJudgment, outputEq⟩
  subst output
  rcases every_torsionAngle_classified angle with ⟨classification, classified⟩
  refine ⟨classification, ?_⟩
  exact ⟨gate.1, (withAngle_selectedBySourceCriteria_iff
    input angle).2 gate.2.2.2.1, by simpa using classified⟩

/-- A successfully derived coordinate record reaches the public report exactly once for at least
one P-94 angular class. -/
theorem coordinateTorsionAssignment_count_eq_one
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (ledger : VirtualTorsionPointLedger) (input output : P94TorsionEvidence)
    (computed : coordinateTorsionEvidence? certified.result.parsed spatial ledger input =
      some output) :
    ∃ classification,
      List.count
        ({ unit := output.unit, descriptor := .torsionClass classification } :
          P94ConformationAssignment)
        (certified.analyzeP94Conformation
          [(P94ConformationEvidence.torsion output :
            P94ConformationEvidence PUnit PUnit)]) = 1 := by
  have judgment := (coordinateTorsionEvidence?_eq_some_iff
    certified.result.parsed spatial ledger input output).mp computed
  rcases coordinateTorsionEvidence_success_supports_classification
    certified.result.parsed spatial ledger input output computed with
    ⟨classification, support⟩
  refine ⟨classification,
    (analyzeP94Conformation_count_eq_one_iff certified
      [(P94ConformationEvidence.torsion output :
        P94ConformationEvidence PUnit PUnit)] _).mpr ?_⟩
  rcases judgment with
    ⟨gate, axisFront, axisRear, frontPoint, axisFrontPoint,
      axisRearPoint, rearPoint, angle, endpoints, frontJudgment,
      axisFrontPointEq, axisRearPointEq, rearJudgment, collinear,
      angleJudgment, outputEq⟩
  subst output
  refine ⟨(P94ConformationEvidence.torsion (withAngle input angle) :
      P94ConformationEvidence PUnit PUnit), by simp,
    rfl, ?_, ?_, support⟩
  · simpa using gate.2.1
  · exact (P94TorsionEvidence.molecularRolesValid_iff_axisParticipants
      (State := PUnit) (Framework := PUnit) (withAngle input angle)
      certified.result.parsed).mpr
        ⟨(withAngle_candidateParticipantsBounded_iff
            input angle _).2
            gate.2.2.1.1,
          (withAngle_axisParticipantsValid_iff
            input angle _).2
            gate.2.2.1.2⟩

end BlueBookP94.CoordinateTorsion

end TetraStereo.OneCenter
