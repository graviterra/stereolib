import TetraStereo.OneCenter.IR9TrigonalBipyramid5SpatialOrientation
import TetraStereo.OneCenter.CIPIR9BipyramidalIntegration

set_option autoImplicit false

namespace TetraStereo.OneCenter

open RedBookIR9
open RedBookIR9.BipyramidalSourceIndexCompleteness
open RedBookIR9.TrigonalBipyramid5SpatialPerception
open RedBookIR9.TrigonalBipyramid5SpatialOrientation

/-! # Public molecule/coordinate integration for exact TBPY-5 -/

def trigonalBipyramidFivePriorityPlacement
    (priority0 priority1 priority2 priority3 priority4 : PolyhedralPriorityNumber) :
    Fin 5 → PolyhedralPriorityNumber
  | 0 => priority0
  | 1 => priority1
  | 2 => priority2
  | 3 => priority3
  | 4 => priority4

def trigonalBipyramidFivePriorityPlacement?
    (priorities : List PolyhedralPriorityNumber) :
    Option (Fin 5 → PolyhedralPriorityNumber) :=
  match priorities with
  | [priority0, priority1, priority2, priority3, priority4] =>
      some (trigonalBipyramidFivePriorityPlacement
        priority0 priority1 priority2 priority3 priority4)
  | _ => none

@[simp] theorem trigonalBipyramidFivePriorityPlacement?_explicit
    (priority0 priority1 priority2 priority3 priority4 : PolyhedralPriorityNumber) :
    trigonalBipyramidFivePriorityPlacement?
        [priority0, priority1, priority2, priority3, priority4] =
      some (trigonalBipyramidFivePriorityPlacement
        priority0 priority1 priority2 priority3 priority4) := rfl

@[simp] theorem trigonalBipyramidFivePriorityPlacement_lookup
    (priority0 priority1 priority2 priority3 priority4 : PolyhedralPriorityNumber)
    (position : Fin 5) :
    [priority0, priority1, priority2, priority3, priority4][position.val]? =
      some (trigonalBipyramidFivePriorityPlacement
        priority0 priority1 priority2 priority3 priority4 position) := by
  fin_cases position <;> rfl

theorem trigonalBipyramidFinPairPositionValues_eraseDups_length
    (first second : Fin 5) (distinct : first ≠ second) :
    [first.val, second.val].eraseDups.length = 2 := by
  fin_cases first <;> fin_cases second <;>
    simp [List.eraseDups, List.eraseDupsBy, List.eraseDupsBy.loop] at distinct ⊢

theorem trigonalBipyramidFivePriorityPlacement_pair_lookups
    (priority0 priority1 priority2 priority3 priority4 : PolyhedralPriorityNumber)
    (first second : Fin 5) :
    [first.val, second.val].mapM
        (fun position =>
          [priority0, priority1, priority2, priority3, priority4][position]?) =
      some
        [trigonalBipyramidFivePriorityPlacement
          priority0 priority1 priority2 priority3 priority4 first,
         trigonalBipyramidFivePriorityPlacement
          priority0 priority1 priority2 priority3 priority4 second] := by
  fin_cases first <;> fin_cases second <;> rfl

/-- TBPY-5 input with no geometry label, axial pair, rotation sense, or descriptor. -/
structure IndexedTrigonalBipyramid5SpatialObservation where
  center : ℕ
  ligands : List ℕ
  deriving DecidableEq, Repr

/-- Collect one center and exactly five donor coordinates. -/
def SpatialConfiguration.trigonalBipyramid5Frame?
    (spatial : SpatialConfiguration) (center : ℕ) (ligands : List ℕ) :
    Option TrigonalBipyramid5SpatialPerception.Frame :=
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

theorem SpatialConfiguration.trigonalBipyramid5Frame?_explicit
    (spatial : SpatialConfiguration) (center donor0 donor1 donor2 donor3 donor4 : ℕ)
    (centerPoint donorPoint0 donorPoint1 donorPoint2 donorPoint3 donorPoint4 :
      CartesianPoint3)
    (centerEq : spatial.positions[center]? = some centerPoint)
    (donorEq0 : spatial.positions[donor0]? = some donorPoint0)
    (donorEq1 : spatial.positions[donor1]? = some donorPoint1)
    (donorEq2 : spatial.positions[donor2]? = some donorPoint2)
    (donorEq3 : spatial.positions[donor3]? = some donorPoint3)
    (donorEq4 : spatial.positions[donor4]? = some donorPoint4) :
    spatial.trigonalBipyramid5Frame? center [donor0, donor1, donor2, donor3, donor4] =
      some
        { center := centerPoint
          donor0 := donorPoint0
          donor1 := donorPoint1
          donor2 := donorPoint2
          donor3 := donorPoint3
          donor4 := donorPoint4 } := by
  simp [SpatialConfiguration.trigonalBipyramid5Frame?, centerEq, donorEq0, donorEq1,
    donorEq2, donorEq3, donorEq4]

namespace IndexedTrigonalBipyramid5SpatialObservation

def withDerivedData
    (record : IndexedTrigonalBipyramid5SpatialObservation)
    (axialOrder : Fin 5 × Fin 5) (sense : PolyhedralRotationSense) :
    IndexedPolyhedralGeometryObservation :=
  { center := record.center
    geometry := .trigonalBipyramid
    recognition := .higherCoordinationNearestIdealized .trigonalBipyramid
    ligands := record.ligands
    configurationPositions := .trigonalBipyramid axialOrder.1.val axialOrder.2.val
    absoluteOrientation := .trigonalBipyramidAC (BlueBookP93.rotationOfProduction sense) }

/-- Derive the axial pair, all five molecular priorities, their strict axial order, and physical
A/C sense from exact coordinates. -/
def derivedRecord?
    (record : IndexedTrigonalBipyramid5SpatialObservation)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration) :
    Option IndexedPolyhedralGeometryObservation := do
  let frame ← spatial.trigonalBipyramid5Frame? record.center record.ligands
  let axialPair ← TrigonalBipyramid5SpatialPerception.perceive? frame
  let priorities ← result.molecularPolyhedralPriorityNumbers?
    record.center .trigonalBipyramid record.ligands
  let placement ← trigonalBipyramidFivePriorityPlacement? priorities
  let axialOrder ← strictOrderAxialPair? placement axialPair
  let sense ← TrigonalBipyramid5SpatialOrientation.rotationSense?
    frame axialPair placement
  some (record.withDerivedData axialOrder sense)

end IndexedTrigonalBipyramid5SpatialObservation

/-- Complete independent meaning of the coordinate-derived internal TBPY-5 record. -/
def TrigonalBipyramid5DerivedRecordJudgment
    (record : IndexedTrigonalBipyramid5SpatialObservation)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (derived : IndexedPolyhedralGeometryObservation) : Prop :=
  ∃ frame axialPair priorities placement axialOrder sense,
    spatial.trigonalBipyramid5Frame? record.center record.ligands = some frame ∧
    TrigonalBipyramid5SpatialPerception.Judgment frame axialPair ∧
    result.molecularPolyhedralPriorityNumbers?
      record.center .trigonalBipyramid record.ligands = some priorities ∧
    trigonalBipyramidFivePriorityPlacement? priorities = some placement ∧
    IsStrictAxialOrder placement axialPair axialOrder ∧
    TrigonalBipyramid5SpatialOrientation.Judgment frame axialPair placement sense ∧
    derived = record.withDerivedData axialOrder sense

theorem IndexedTrigonalBipyramid5SpatialObservation.derivedRecord?_eq_some_iff
    (record : IndexedTrigonalBipyramid5SpatialObservation)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (derived : IndexedPolyhedralGeometryObservation) :
    record.derivedRecord? result spatial = some derived ↔
      TrigonalBipyramid5DerivedRecordJudgment record result spatial derived := by
  constructor
  · intro computed
    unfold IndexedTrigonalBipyramid5SpatialObservation.derivedRecord? at computed
    cases frameEq : spatial.trigonalBipyramid5Frame? record.center record.ligands with
    | none => simp [frameEq] at computed
    | some frame =>
        cases pairEq : TrigonalBipyramid5SpatialPerception.perceive? frame with
        | none => simp [frameEq, pairEq] at computed
        | some axialPair =>
            cases priorityEq : result.molecularPolyhedralPriorityNumbers?
                record.center .trigonalBipyramid record.ligands with
            | none => simp [frameEq, priorityEq] at computed
            | some priorities =>
                cases placementEq : trigonalBipyramidFivePriorityPlacement? priorities with
                | none => simp [frameEq, priorityEq, placementEq] at computed
                | some placement =>
                    cases axialEq : strictOrderAxialPair? placement axialPair with
                    | none =>
                        simp [frameEq, pairEq, priorityEq, placementEq, axialEq] at computed
                    | some axialOrder =>
                        cases senseEq : TrigonalBipyramid5SpatialOrientation.rotationSense?
                            frame axialPair placement with
                        | none =>
                            simp [frameEq, pairEq, priorityEq, placementEq, axialEq, senseEq]
                              at computed
                        | some sense =>
                            have derivedEq : derived = record.withDerivedData axialOrder sense := by
                              simpa [frameEq, pairEq, priorityEq, placementEq, axialEq, senseEq]
                                using computed.symm
                            exact ⟨frame, axialPair, priorities, placement, axialOrder, sense,
                              frameEq,
                              (TrigonalBipyramid5SpatialPerception.perceive?_eq_some_iff
                                frame axialPair).mp pairEq,
                              priorityEq, placementEq,
                              (strictOrderAxialPair?_eq_some_iff
                                placement axialPair axialOrder).mp axialEq,
                              (TrigonalBipyramid5SpatialOrientation.rotationSense?_eq_some_iff
                                frame axialPair placement sense).mp senseEq,
                              derivedEq⟩
  · rintro ⟨frame, axialPair, priorities, placement, axialOrder, sense,
      frameEq, perceived, priorityEq, placementEq, axialOrdered, orientation, rfl⟩
    have pairEq : TrigonalBipyramid5SpatialPerception.perceive? frame = some axialPair :=
      (TrigonalBipyramid5SpatialPerception.perceive?_eq_some_iff frame axialPair).mpr perceived
    have axialEq : strictOrderAxialPair? placement axialPair = some axialOrder :=
      (strictOrderAxialPair?_eq_some_iff placement axialPair axialOrder).mpr axialOrdered
    have senseEq : TrigonalBipyramid5SpatialOrientation.rotationSense?
        frame axialPair placement = some sense :=
      (TrigonalBipyramid5SpatialOrientation.rotationSense?_eq_some_iff
        frame axialPair placement sense).mpr orientation
    simp [IndexedTrigonalBipyramid5SpatialObservation.derivedRecord?, frameEq, pairEq,
      priorityEq, placementEq, axialEq, senseEq]

/-- Public molecule/coordinate-to-TBPY-5 assignment with no caller-supplied geometry, roles,
rotation sense, or descriptor. -/
def ChemistryNormalizationResult.trigonalBipyramid5SpatialAssignment?
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedTrigonalBipyramid5SpatialObservation) : Option StereoAssignment := do
  let derived ← record.derivedRecord? result spatial
  result.polyhedralGeometryObservationAssignment? derived

/-- Independent success judgment for the composed coordinate and public IR-9 stages. -/
def TrigonalBipyramid5SpatialAssignmentJudgment
    (record : IndexedTrigonalBipyramid5SpatialObservation)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (assignment : StereoAssignment) : Prop :=
  ∃ derived,
    TrigonalBipyramid5DerivedRecordJudgment record result spatial derived ∧
      result.polyhedralGeometryObservationAssignment? derived = some assignment

theorem ChemistryNormalizationResult.trigonalBipyramid5SpatialAssignment?_eq_some_iff
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedTrigonalBipyramid5SpatialObservation)
    (assignment : StereoAssignment) :
    result.trigonalBipyramid5SpatialAssignment? spatial record = some assignment ↔
      TrigonalBipyramid5SpatialAssignmentJudgment record result spatial assignment := by
  unfold ChemistryNormalizationResult.trigonalBipyramid5SpatialAssignment?
  constructor
  · intro computed
    cases derivedEq : record.derivedRecord? result spatial with
    | none => simp [derivedEq] at computed
    | some derived =>
        exact ⟨derived,
          (record.derivedRecord?_eq_some_iff result spatial derived).mp derivedEq,
          by simpa [derivedEq] using computed⟩
  · rintro ⟨derived, derivedJudged, produced⟩
    have derivedEq :=
      (record.derivedRecord?_eq_some_iff result spatial derived).mpr derivedJudged
    simp [derivedEq, produced]

theorem ChemistryNormalizationResult.trigonalBipyramid5SpatialAssignment?_eq_none_iff
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedTrigonalBipyramid5SpatialObservation) :
    result.trigonalBipyramid5SpatialAssignment? spatial record = none ↔
      ¬ ∃ assignment,
        TrigonalBipyramid5SpatialAssignmentJudgment record result spatial assignment := by
  constructor
  · intro absent ⟨assignment, judged⟩
    have present :=
      (result.trigonalBipyramid5SpatialAssignment?_eq_some_iff
        spatial record assignment).mpr judged
    rw [absent] at present
    contradiction
  · intro noJudgment
    cases computed : result.trigonalBipyramid5SpatialAssignment? spatial record with
    | none => rfl
    | some assignment =>
        exact False.elim (noJudgment ⟨assignment,
          (result.trigonalBipyramid5SpatialAssignment?_eq_some_iff
            spatial record assignment).mp computed⟩)

/-- Exact final descriptor on a fully stated exact TBPY-5 geometry and strict-priority frame. -/
theorem ChemistryNormalizationResult.trigonalBipyramid5Spatial_exact
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (center : ℕ) (ligands : List ℕ)
    (frame : TrigonalBipyramid5SpatialPerception.Frame)
    (axialPair axialOrder : Fin 5 × Fin 5)
    (priority0 priority1 priority2 priority3 priority4 : PolyhedralPriorityNumber)
    (sense : PolyhedralRotationSense)
    (frameEq : spatial.trigonalBipyramid5Frame? center ligands = some frame)
    (perceived : TrigonalBipyramid5SpatialPerception.Judgment frame axialPair)
    (priorityEq : result.molecularPolyhedralPriorityNumbers?
      center .trigonalBipyramid ligands =
        some [priority0, priority1, priority2, priority3, priority4])
    (prioritiesDistinct :
      [priority0, priority1, priority2, priority3, priority4].eraseDups.length = 5)
    (axialOrdered : IsStrictAxialOrder
      (trigonalBipyramidFivePriorityPlacement
        priority0 priority1 priority2 priority3 priority4) axialPair axialOrder)
    (orientation : TrigonalBipyramid5SpatialOrientation.Judgment frame axialPair
      (trigonalBipyramidFivePriorityPlacement
        priority0 priority1 priority2 priority3 priority4) sense) :
    result.trigonalBipyramid5SpatialAssignment? spatial
        { center := center, ligands := ligands } =
      some
        { unit := StereoUnit.polyhedron center
          outcome := StereoOutcome.polyhedral
            { geometry := .trigonalBipyramid
              configurationIndex :=
                [trigonalBipyramidConfigurationIndex
                  (trigonalBipyramidFivePriorityPlacement
                    priority0 priority1 priority2 priority3 priority4 axialOrder.1)
                  (trigonalBipyramidFivePriorityPlacement
                    priority0 priority1 priority2 priority3 priority4 axialOrder.2)]
              absolute? := some (.ac (PolyhedralChiralitySymbol.ofRotation sense)) } } := by
  let placement := trigonalBipyramidFivePriorityPlacement
    priority0 priority1 priority2 priority3 priority4
  have pairEq : TrigonalBipyramid5SpatialPerception.perceive? frame = some axialPair :=
    (TrigonalBipyramid5SpatialPerception.perceive?_eq_some_iff frame axialPair).mpr perceived
  have axialEq : strictOrderAxialPair? placement axialPair = some axialOrder :=
    (strictOrderAxialPair?_eq_some_iff placement axialPair axialOrder).mpr axialOrdered
  have senseEq : TrigonalBipyramid5SpatialOrientation.rotationSense?
      frame axialPair placement = some sense :=
    (TrigonalBipyramid5SpatialOrientation.rotationSense?_eq_some_iff
      frame axialPair placement sense).mpr orientation
  have derivedEq :
      ({ center := center, ligands := ligands } :
        IndexedTrigonalBipyramid5SpatialObservation).derivedRecord? result spatial =
        some (({ center := center, ligands := ligands } :
          IndexedTrigonalBipyramid5SpatialObservation).withDerivedData axialOrder sense) := by
    simp [IndexedTrigonalBipyramid5SpatialObservation.derivedRecord?, frameEq, pairEq,
      priorityEq, trigonalBipyramidFivePriorityPlacement?_explicit, placement, axialEq, senseEq]
  have positionsDistinct :
      ([axialOrder.1.val, axialOrder.2.val] : List ℕ).eraseDups.length = 2 := by
    have pairDistinct := axialPair_distinct perceived.1
    rcases axialOrdered with ⟨same, _⟩ | ⟨reversed, _⟩
    · rw [same]
      exact trigonalBipyramidFinPairPositionValues_eraseDups_length
        axialPair.1 axialPair.2 pairDistinct
    · rw [reversed]
      exact trigonalBipyramidFinPairPositionValues_eraseDups_length
        axialPair.2 axialPair.1 (Ne.symm pairDistinct)
  have lookups :
      [axialOrder.1.val, axialOrder.2.val].mapM
          (fun position =>
            [priority0, priority1, priority2, priority3, priority4][position]?) =
        some [placement axialOrder.1, placement axialOrder.2] := by
    exact trigonalBipyramidFivePriorityPlacement_pair_lookups
      priority0 priority1 priority2 priority3 priority4 axialOrder.1 axialOrder.2
  have downstream := bipyramidalGeometryObservationAssignment_exact result
    .trigonal5 center ligands sense
    [priority0, priority1, priority2, priority3, priority4]
    axialOrder.1.val axialOrder.2.val []
    (placement axialOrder.1) (placement axialOrder.2) []
    priorityEq prioritiesDistinct rfl positionsDistinct lookups
  simpa [ChemistryNormalizationResult.trigonalBipyramid5SpatialAssignment?, derivedEq,
    IndexedTrigonalBipyramid5SpatialObservation.withDerivedData,
    RedBookIR9.BipyramidKind.expectedIndex, placement] using downstream

/-- Exact-domain completeness: strict axial/equatorial priorities and exact TBPY-5 geometry
necessarily determine and emit one A/C result. -/
theorem ChemistryNormalizationResult.trigonalBipyramid5Spatial_exists_exact
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (center : ℕ) (ligands : List ℕ)
    (frame : TrigonalBipyramid5SpatialPerception.Frame)
    (axialPair axialOrder : Fin 5 × Fin 5)
    (priority0 priority1 priority2 priority3 priority4 : PolyhedralPriorityNumber)
    (senior : Fin 3) (remaining remainingOrder : Fin 3 × Fin 3)
    (frameEq : spatial.trigonalBipyramid5Frame? center ligands = some frame)
    (perceived : TrigonalBipyramid5SpatialPerception.Judgment frame axialPair)
    (priorityEq : result.molecularPolyhedralPriorityNumbers?
      center .trigonalBipyramid ligands =
        some [priority0, priority1, priority2, priority3, priority4])
    (prioritiesDistinct :
      [priority0, priority1, priority2, priority3, priority4].eraseDups.length = 5)
    (axialOrdered : IsStrictAxialOrder
      (trigonalBipyramidFivePriorityPlacement
        priority0 priority1 priority2 priority3 priority4) axialPair axialOrder)
    (seniority : IsStrictSenior3
      (equatorialPlacement
        (trigonalBipyramidFivePriorityPlacement
          priority0 priority1 priority2 priority3 priority4) axialPair) senior)
    (remainingEq : remainingPair3? senior = some remaining)
    (equatorialOrdered : IsStrictEquatorialOrder
      (equatorialPlacement
        (trigonalBipyramidFivePriorityPlacement
          priority0 priority1 priority2 priority3 priority4) axialPair)
      remaining remainingOrder) :
    ∃ sense,
      result.trigonalBipyramid5SpatialAssignment? spatial
          { center := center, ligands := ligands } =
        some
          { unit := StereoUnit.polyhedron center
            outcome := StereoOutcome.polyhedral
              { geometry := .trigonalBipyramid
                configurationIndex :=
                  [trigonalBipyramidConfigurationIndex
                    (trigonalBipyramidFivePriorityPlacement
                      priority0 priority1 priority2 priority3 priority4 axialOrder.1)
                    (trigonalBipyramidFivePriorityPlacement
                      priority0 priority1 priority2 priority3 priority4 axialOrder.2)]
                absolute? := some (.ac (PolyhedralChiralitySymbol.ofRotation sense)) } } := by
  let placement := trigonalBipyramidFivePriorityPlacement
    priority0 priority1 priority2 priority3 priority4
  obtain ⟨sense, _senseEq, orientation⟩ :=
    TrigonalBipyramid5SpatialOrientation.rotationSense?_exists_of_exactGeometry
      frame axialPair placement perceived axialOrder senior remaining remainingOrder
      axialOrdered seniority remainingEq equatorialOrdered
  exact ⟨sense, result.trigonalBipyramid5Spatial_exact spatial center ligands frame
    axialPair axialOrder priority0 priority1 priority2 priority3 priority4 sense frameEq perceived
    priorityEq prioritiesDistinct axialOrdered orientation⟩

end TetraStereo.OneCenter
