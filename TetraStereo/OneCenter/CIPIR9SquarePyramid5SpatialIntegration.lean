import TetraStereo.OneCenter.IR9SquarePyramid5SpatialPerception
import TetraStereo.OneCenter.CIPIR9SquarePyramidOctahedronIntegration

set_option autoImplicit false

namespace TetraStereo.OneCenter

open RedBookIR9
open RedBookIR9.FourCoordinateSpatialRoles
open RedBookIR9.SeeSawSpatialOrientation
open RedBookIR9.SquarePyramid5SpatialOrientation
open RedBookIR9.SquarePyramid5SpatialPerception

/-! # Public molecule/coordinate integration for exact SPY-5 -/

/-- Position-indexed form of exactly five molecule-derived priorities. -/
def fivePriorityPlacement
    (priority0 priority1 priority2 priority3 priority4 : PolyhedralPriorityNumber) :
    Fin 5 → PolyhedralPriorityNumber
  | 0 => priority0
  | 1 => priority1
  | 2 => priority2
  | 3 => priority3
  | 4 => priority4

def fivePriorityPlacement? (priorities : List PolyhedralPriorityNumber) :
    Option (Fin 5 → PolyhedralPriorityNumber) :=
  match priorities with
  | [priority0, priority1, priority2, priority3, priority4] =>
      some (fivePriorityPlacement priority0 priority1 priority2 priority3 priority4)
  | _ => none

@[simp] theorem fivePriorityPlacement?_explicit
    (priority0 priority1 priority2 priority3 priority4 : PolyhedralPriorityNumber) :
    fivePriorityPlacement? [priority0, priority1, priority2, priority3, priority4] =
      some (fivePriorityPlacement priority0 priority1 priority2 priority3 priority4) := rfl

@[simp] theorem fivePriorityPlacement_lookup
    (priority0 priority1 priority2 priority3 priority4 : PolyhedralPriorityNumber)
    (position : Fin 5) :
    [priority0, priority1, priority2, priority3, priority4][position.val]? =
      some (fivePriorityPlacement priority0 priority1 priority2 priority3 priority4 position) := by
  fin_cases position <;> rfl

/-- Restrict a five-position priority placement to the four normalized basal positions. -/
def squarePyramid5BasePlacement
    (placement : Fin 5 → PolyhedralPriorityNumber) (apex : Fin 5) :
    Fin 4 → PolyhedralPriorityNumber :=
  fun position => placement
    (SquarePyramid5SpatialPerception.Frame.baseOriginalPosition apex position)

theorem squarePyramid5_apex_basePosition_distinct
    (apex : Fin 5) (basePosition : Fin 4) :
    [apex.val,
      (SquarePyramid5SpatialPerception.Frame.baseOriginalPosition
        apex basePosition).val].eraseDups.length = 2 := by
  fin_cases apex <;> fin_cases basePosition <;> decide

/-- SPY-5 public input with no geometry label, apex, trans site, rotation sense, or descriptor. -/
structure IndexedSquarePyramid5SpatialObservation where
  center : ℕ
  ligands : List ℕ
  deriving DecidableEq, Repr

/-- Collect one center and exactly five donor coordinates. -/
def SpatialConfiguration.squarePyramid5Frame?
    (spatial : SpatialConfiguration) (center : ℕ) (ligands : List ℕ) :
    Option SquarePyramid5SpatialPerception.Frame :=
  match ligands with
  | [donor0, donor1, donor2, donor3, donor4] => do
      let centerPoint ← spatial.positions[center]?
      let donorPoint0 ← spatial.positions[donor0]?
      let donorPoint1 ← spatial.positions[donor1]?
      let donorPoint2 ← spatial.positions[donor2]?
      let donorPoint3 ← spatial.positions[donor3]?
      let donorPoint4 ← spatial.positions[donor4]?
      some
        { center := centerPoint
          donor0 := donorPoint0
          donor1 := donorPoint1
          donor2 := donorPoint2
          donor3 := donorPoint3
          donor4 := donorPoint4 }
  | _ => none

theorem SpatialConfiguration.squarePyramid5Frame?_explicit
    (spatial : SpatialConfiguration) (center donor0 donor1 donor2 donor3 donor4 : ℕ)
    (centerPoint donorPoint0 donorPoint1 donorPoint2 donorPoint3 donorPoint4 : CartesianPoint3)
    (centerEq : spatial.positions[center]? = some centerPoint)
    (donorEq0 : spatial.positions[donor0]? = some donorPoint0)
    (donorEq1 : spatial.positions[donor1]? = some donorPoint1)
    (donorEq2 : spatial.positions[donor2]? = some donorPoint2)
    (donorEq3 : spatial.positions[donor3]? = some donorPoint3)
    (donorEq4 : spatial.positions[donor4]? = some donorPoint4) :
    spatial.squarePyramid5Frame? center [donor0, donor1, donor2, donor3, donor4] =
      some
        { center := centerPoint
          donor0 := donorPoint0
          donor1 := donorPoint1
          donor2 := donorPoint2
          donor3 := donorPoint3
          donor4 := donorPoint4 } := by
  simp [SpatialConfiguration.squarePyramid5Frame?, centerEq, donorEq0, donorEq1,
    donorEq2, donorEq3, donorEq4]

namespace IndexedSquarePyramid5SpatialObservation

def withDerivedData
    (record : IndexedSquarePyramid5SpatialObservation)
    (apex : Fin 5) (trans : Fin 4) (sense : PolyhedralRotationSense) :
    IndexedPolyhedralGeometryObservation :=
  { center := record.center
    geometry := .squarePyramid
    recognition := .higherCoordinationNearestIdealized .squarePyramid
    ligands := record.ligands
    configurationPositions := .squarePyramid apex.val
      (SquarePyramid5SpatialPerception.Frame.baseOriginalPosition apex trans).val
    absoluteOrientation := .squarePyramidAC (BlueBookP93.rotationOfProduction sense) }

/-- Derive the unique apex, normalized base, molecular priorities, trans site, and physical A/C. -/
def derivedRecord?
    (record : IndexedSquarePyramid5SpatialObservation)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration) :
    Option IndexedPolyhedralGeometryObservation := do
  let frame ← spatial.squarePyramid5Frame? record.center record.ligands
  let perceived ← SquarePyramid5SpatialPerception.perceive? frame
  let apex := perceived.1
  let normalized := perceived.2
  let priorities ← result.molecularPolyhedralPriorityNumbers?
    record.center .squarePyramid record.ligands
  let placement ← fivePriorityPlacement? priorities
  let basePlacement := squarePyramid5BasePlacement placement apex
  let senior ← strictSeniorPosition? basePlacement
  let trans ← oppositePosition? normalized.baseFrame senior
  let sense ← SquarePyramid5SpatialOrientation.rotationSense? normalized basePlacement
  some (record.withDerivedData apex trans sense)

end IndexedSquarePyramid5SpatialObservation

/-- Complete declarative meaning of a successfully derived SPY-5 observation. -/
def SquarePyramid5DerivedRecordJudgment
    (record : IndexedSquarePyramid5SpatialObservation)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (derived : IndexedPolyhedralGeometryObservation) : Prop :=
  ∃ frame apex normalized priorities placement senior trans sense,
    spatial.squarePyramid5Frame? record.center record.ligands = some frame ∧
    SquarePyramid5SpatialPerception.perceive? frame = some (apex, normalized) ∧
    result.molecularPolyhedralPriorityNumbers?
      record.center .squarePyramid record.ligands = some priorities ∧
    fivePriorityPlacement? priorities = some placement ∧
    IsStrictSenior (squarePyramid5BasePlacement placement apex) senior ∧
    IsOppositePair normalized.baseFrame senior trans ∧
    (∀ other, IsOppositePair normalized.baseFrame senior other → other = trans) ∧
    SquarePyramid5SpatialOrientation.Judgment
      normalized (squarePyramid5BasePlacement placement apex) sense ∧
    derived = record.withDerivedData apex trans sense

theorem IndexedSquarePyramid5SpatialObservation.derivedRecord?_eq_some_iff
    (record : IndexedSquarePyramid5SpatialObservation)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (derived : IndexedPolyhedralGeometryObservation) :
    record.derivedRecord? result spatial = some derived ↔
      SquarePyramid5DerivedRecordJudgment record result spatial derived := by
  constructor
  · intro computed
    unfold IndexedSquarePyramid5SpatialObservation.derivedRecord? at computed
    cases frameEq : spatial.squarePyramid5Frame? record.center record.ligands with
    | none => simp [frameEq] at computed
    | some frame =>
        cases perceivedEq : SquarePyramid5SpatialPerception.perceive? frame with
        | none => simp [frameEq, perceivedEq] at computed
        | some perceived =>
            rcases perceived with ⟨apex, normalized⟩
            cases priorityEq : result.molecularPolyhedralPriorityNumbers?
                record.center .squarePyramid record.ligands with
            | none => simp [frameEq, priorityEq] at computed
            | some priorities =>
                cases placementEq : fivePriorityPlacement? priorities with
                | none => simp [frameEq, priorityEq, placementEq] at computed
                | some placement =>
                    let basePlacement := squarePyramid5BasePlacement placement apex
                    cases seniorEq : strictSeniorPosition? basePlacement with
                    | none =>
                        simp [frameEq, perceivedEq, priorityEq, placementEq,
                          basePlacement, seniorEq] at computed
                    | some senior =>
                        cases transEq : oppositePosition? normalized.baseFrame senior with
                        | none =>
                            simp [frameEq, perceivedEq, priorityEq, placementEq,
                              basePlacement, seniorEq, transEq] at computed
                        | some trans =>
                            cases senseEq : SquarePyramid5SpatialOrientation.rotationSense?
                                normalized basePlacement with
                            | none =>
                                simp [frameEq, perceivedEq, priorityEq, placementEq,
                                  basePlacement, seniorEq, senseEq] at computed
                            | some sense =>
                                have derivedEq :
                                    derived = record.withDerivedData apex trans sense := by
                                  simpa [frameEq, perceivedEq, priorityEq, placementEq,
                                    basePlacement, seniorEq, transEq, senseEq] using computed.symm
                                have seniority :=
                                  (strictSeniorPosition?_eq_some_iff basePlacement senior).mp seniorEq
                                have transFacts :=
                                  (oppositePosition?_eq_some_iff
                                    normalized.baseFrame senior trans).mp transEq
                                have orientation :=
                                  (SquarePyramid5SpatialOrientation.rotationSense?_eq_some_iff
                                    normalized basePlacement sense).mp senseEq
                                exact ⟨frame, apex, normalized, priorities, placement, senior,
                                  trans, sense, frameEq, perceivedEq, priorityEq, placementEq,
                                  seniority, transFacts.1, transFacts.2, orientation, derivedEq⟩
  · rintro ⟨frame, apex, normalized, priorities, placement, senior, trans, sense,
      frameEq, perceivedEq, priorityEq, placementEq, seniority, opposite, unique,
      orientation, rfl⟩
    let basePlacement := squarePyramid5BasePlacement placement apex
    have seniorEq : strictSeniorPosition? basePlacement = some senior :=
      (strictSeniorPosition?_eq_some_iff basePlacement senior).mpr seniority
    have transEq : oppositePosition? normalized.baseFrame senior = some trans :=
      (oppositePosition?_eq_some_iff normalized.baseFrame senior trans).mpr
        ⟨opposite, unique⟩
    have senseEq : SquarePyramid5SpatialOrientation.rotationSense?
        normalized basePlacement = some sense :=
      (SquarePyramid5SpatialOrientation.rotationSense?_eq_some_iff
        normalized basePlacement sense).mpr orientation
    simp [IndexedSquarePyramid5SpatialObservation.derivedRecord?, frameEq, perceivedEq,
      priorityEq, placementEq, basePlacement, seniorEq, transEq, senseEq]

/-- Public exact SPY-5 molecule/coordinate analyzer. -/
def ChemistryNormalizationResult.squarePyramid5SpatialAssignment?
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedSquarePyramid5SpatialObservation) : Option StereoAssignment := do
  let derived ← record.derivedRecord? result spatial
  result.polyhedralGeometryObservationAssignment? derived

theorem ChemistryNormalizationResult.squarePyramid5SpatialAssignment?_eq_none_iff
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedSquarePyramid5SpatialObservation) :
    result.squarePyramid5SpatialAssignment? spatial record = none ↔
      record.derivedRecord? result spatial = none ∨
        ∃ derived, record.derivedRecord? result spatial = some derived ∧
          result.polyhedralGeometryObservationAssignment? derived = none := by
  unfold ChemistryNormalizationResult.squarePyramid5SpatialAssignment?
  cases derivedEq : record.derivedRecord? result spatial with
  | none => simp
  | some derived =>
      cases producedEq : result.polyhedralGeometryObservationAssignment? derived <;>
        simp [producedEq]

/-- Exact final descriptor once every independently stated exact SPY-5 premise is available. -/
theorem ChemistryNormalizationResult.squarePyramid5Spatial_exact
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (center : ℕ) (ligands : List ℕ)
    (frame : SquarePyramid5SpatialPerception.Frame) (apex : Fin 5)
    (priority0 priority1 priority2 priority3 priority4 : PolyhedralPriorityNumber)
    (senior trans : Fin 4) (remaining adjacentOrder : Fin 4 × Fin 4)
    (sense : PolyhedralRotationSense)
    (frameEq : spatial.squarePyramid5Frame? center ligands = some frame)
    (apexCandidate : SquarePyramid5SpatialPerception.IsApexCandidate frame apex)
    (apexUnique : ∀ other,
      SquarePyramid5SpatialPerception.IsApexCandidate frame other → other = apex)
    (priorityEq : result.molecularPolyhedralPriorityNumbers? center .squarePyramid ligands =
      some [priority0, priority1, priority2, priority3, priority4])
    (prioritiesDistinct :
      [priority0, priority1, priority2, priority3, priority4].eraseDups.length = 5)
    (seniority : IsStrictSenior
      (squarePyramid5BasePlacement
        (fivePriorityPlacement priority0 priority1 priority2 priority3 priority4) apex) senior)
    (opposite : IsOppositePair (frame.normalize apex).baseFrame senior trans)
    (unique : ∀ other,
      IsOppositePair (frame.normalize apex).baseFrame senior other → other = trans)
    (remainingEq : SquarePyramid4SpatialOrientation.remainingPair? senior trans = some remaining)
    (adjacentOrdered : IsStrictOrder
      (squarePyramid5BasePlacement
        (fivePriorityPlacement priority0 priority1 priority2 priority3 priority4) apex)
      remaining adjacentOrder)
    (progression :
      (sense = .counterclockwise ∧
        0 < SquarePyramid5SpatialOrientation.progressionDeterminant
          (frame.normalize apex) senior adjacentOrder.1) ∨
      (sense = .clockwise ∧
        SquarePyramid5SpatialOrientation.progressionDeterminant
          (frame.normalize apex) senior adjacentOrder.1 < 0)) :
    result.squarePyramid5SpatialAssignment? spatial { center := center, ligands := ligands } =
      some
        { unit := StereoUnit.polyhedron center
          outcome := StereoOutcome.polyhedral
            { geometry := .squarePyramid
              configurationIndex :=
                [[fivePriorityPlacement priority0 priority1 priority2 priority3 priority4 apex,
                  fivePriorityPlacement priority0 priority1 priority2 priority3 priority4
                    (SquarePyramid5SpatialPerception.Frame.baseOriginalPosition apex trans)]]
              absolute? := some (.ac (PolyhedralChiralitySymbol.ofRotation sense)) } } := by
  let placement := fivePriorityPlacement priority0 priority1 priority2 priority3 priority4
  let basePlacement := squarePyramid5BasePlacement placement apex
  have perceivedEq : SquarePyramid5SpatialPerception.perceive? frame =
      some (apex, frame.normalize apex) :=
    (SquarePyramid5SpatialPerception.perceive?_eq_some_iff
      frame apex (frame.normalize apex)).mpr ⟨rfl, apexCandidate, apexUnique⟩
  have seniorEq : strictSeniorPosition? basePlacement = some senior :=
    (strictSeniorPosition?_eq_some_iff basePlacement senior).mpr seniority
  have transEq : oppositePosition? (frame.normalize apex).baseFrame senior = some trans :=
    (oppositePosition?_eq_some_iff (frame.normalize apex).baseFrame senior trans).mpr
      ⟨opposite, unique⟩
  have orientation : SquarePyramid5SpatialOrientation.Judgment
      (frame.normalize apex) basePlacement sense :=
    ⟨senior, trans, remaining, adjacentOrder, seniority, opposite, unique,
      remainingEq, adjacentOrdered, progression⟩
  have senseEq : SquarePyramid5SpatialOrientation.rotationSense?
      (frame.normalize apex) basePlacement = some sense :=
    (SquarePyramid5SpatialOrientation.rotationSense?_eq_some_iff
      (frame.normalize apex) basePlacement sense).mpr orientation
  have derivedEq :
      IndexedSquarePyramid5SpatialObservation.derivedRecord?
          ({ center := center, ligands := ligands }) result spatial =
        some (IndexedSquarePyramid5SpatialObservation.withDerivedData
          ({ center := center, ligands := ligands }) apex trans sense) := by
    simp [IndexedSquarePyramid5SpatialObservation.derivedRecord?, frameEq, perceivedEq,
      priorityEq, fivePriorityPlacement?_explicit, placement, basePlacement,
      seniorEq, transEq, senseEq]
  have positionsDistinct := squarePyramid5_apex_basePosition_distinct apex trans
  have lookups :
      [apex.val,
        (SquarePyramid5SpatialPerception.Frame.baseOriginalPosition apex trans).val].mapM
          (fun position =>
            [priority0, priority1, priority2, priority3, priority4][position]?) =
        some
          [placement apex,
            placement (SquarePyramid5SpatialPerception.Frame.baseOriginalPosition apex trans)] := by
    fin_cases apex <;> fin_cases trans <;> rfl
  have downstream := squarePyramidGeometryObservationAssignment_exact result center ligands sense
    [priority0, priority1, priority2, priority3, priority4]
    apex.val (SquarePyramid5SpatialPerception.Frame.baseOriginalPosition apex trans).val
    (placement apex)
    (placement (SquarePyramid5SpatialPerception.Frame.baseOriginalPosition apex trans))
    priorityEq prioritiesDistinct positionsDistinct lookups
  simpa [ChemistryNormalizationResult.squarePyramid5SpatialAssignment?, derivedEq,
    IndexedSquarePyramid5SpatialObservation.withDerivedData, placement] using downstream

/-- Completeness: exact uniquely perceived SPY-5 geometry necessarily emits one exact A/C result. -/
theorem ChemistryNormalizationResult.squarePyramid5Spatial_exists_exact
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (center : ℕ) (ligands : List ℕ)
    (frame : SquarePyramid5SpatialPerception.Frame) (apex : Fin 5)
    (priority0 priority1 priority2 priority3 priority4 : PolyhedralPriorityNumber)
    (senior trans : Fin 4) (remaining adjacentOrder : Fin 4 × Fin 4)
    (frameEq : spatial.squarePyramid5Frame? center ligands = some frame)
    (apexCandidate : SquarePyramid5SpatialPerception.IsApexCandidate frame apex)
    (apexUnique : ∀ other,
      SquarePyramid5SpatialPerception.IsApexCandidate frame other → other = apex)
    (priorityEq : result.molecularPolyhedralPriorityNumbers? center .squarePyramid ligands =
      some [priority0, priority1, priority2, priority3, priority4])
    (prioritiesDistinct :
      [priority0, priority1, priority2, priority3, priority4].eraseDups.length = 5)
    (seniority : IsStrictSenior
      (squarePyramid5BasePlacement
        (fivePriorityPlacement priority0 priority1 priority2 priority3 priority4) apex) senior)
    (opposite : IsOppositePair (frame.normalize apex).baseFrame senior trans)
    (unique : ∀ other,
      IsOppositePair (frame.normalize apex).baseFrame senior other → other = trans)
    (remainingEq : SquarePyramid4SpatialOrientation.remainingPair? senior trans = some remaining)
    (adjacentOrdered : IsStrictOrder
      (squarePyramid5BasePlacement
        (fivePriorityPlacement priority0 priority1 priority2 priority3 priority4) apex)
      remaining adjacentOrder) :
    ∃ sense,
      result.squarePyramid5SpatialAssignment? spatial { center := center, ligands := ligands } =
        some
          { unit := StereoUnit.polyhedron center
            outcome := StereoOutcome.polyhedral
              { geometry := .squarePyramid
                configurationIndex :=
                  [[fivePriorityPlacement priority0 priority1 priority2 priority3 priority4 apex,
                    fivePriorityPlacement priority0 priority1 priority2 priority3 priority4
                      (SquarePyramid5SpatialPerception.Frame.baseOriginalPosition apex trans)]]
                absolute? := some (.ac (PolyhedralChiralitySymbol.ofRotation sense)) } } := by
  let placement := fivePriorityPlacement priority0 priority1 priority2 priority3 priority4
  let basePlacement := squarePyramid5BasePlacement placement apex
  have determinantNonzero :
      SquarePyramid5SpatialOrientation.progressionDeterminant
          (frame.normalize apex) senior adjacentOrder.1 ≠ 0 :=
    SquarePyramid5SpatialOrientation.progressionDeterminant_ne_zero
      (frame.normalize apex) basePlacement senior trans remaining adjacentOrder
      apexCandidate.1 apexCandidate.2.1 opposite remainingEq adjacentOrdered
  rcases lt_trichotomy
      (SquarePyramid5SpatialOrientation.progressionDeterminant
        (frame.normalize apex) senior adjacentOrder.1) 0 with
    clockwise | zero | counterclockwise
  · refine ⟨.clockwise, ?_⟩
    exact result.squarePyramid5Spatial_exact spatial center ligands frame apex
      priority0 priority1 priority2 priority3 priority4 senior trans remaining adjacentOrder
      .clockwise frameEq apexCandidate apexUnique priorityEq prioritiesDistinct seniority opposite
      unique remainingEq adjacentOrdered (Or.inr ⟨rfl, clockwise⟩)
  · exact (determinantNonzero zero).elim
  · refine ⟨.counterclockwise, ?_⟩
    exact result.squarePyramid5Spatial_exact spatial center ligands frame apex
      priority0 priority1 priority2 priority3 priority4 senior trans remaining adjacentOrder
      .counterclockwise frameEq apexCandidate apexUnique priorityEq prioritiesDistinct seniority
      opposite unique remainingEq adjacentOrdered (Or.inl ⟨rfl, counterclockwise⟩)

end TetraStereo.OneCenter
