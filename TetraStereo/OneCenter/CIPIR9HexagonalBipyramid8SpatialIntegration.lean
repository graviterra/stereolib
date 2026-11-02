import TetraStereo.OneCenter.IR9HexagonalBipyramid8SpatialOrientation
import TetraStereo.OneCenter.CIPIR9BipyramidalIntegration

set_option autoImplicit false

namespace TetraStereo.OneCenter

open RedBookIR9
open RedBookIR9.HexagonalBipyramid8SpatialPerception
open RedBookIR9.HexagonalBipyramid8SpatialOrientation

/-! # Public molecule/coordinate integration for exact HBPY-8 -/

def hexagonalBipyramidEightPriorityPlacement
    (priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7 :
      PolyhedralPriorityNumber) : Fin 8 → PolyhedralPriorityNumber
  | 0 => priority0
  | 1 => priority1
  | 2 => priority2
  | 3 => priority3
  | 4 => priority4
  | 5 => priority5
  | 6 => priority6
  | 7 => priority7

def hexagonalBipyramidEightPriorityPlacement?
    (priorities : List PolyhedralPriorityNumber) :
    Option (Fin 8 → PolyhedralPriorityNumber) :=
  match priorities with
  | [priority0, priority1, priority2, priority3, priority4, priority5, priority6, priority7] =>
      some (hexagonalBipyramidEightPriorityPlacement
        priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7)
  | _ => none

@[simp] theorem hexagonalBipyramidEightPriorityPlacement?_explicit
    (priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7 :
      PolyhedralPriorityNumber) :
    hexagonalBipyramidEightPriorityPlacement?
        [priority0, priority1, priority2, priority3, priority4, priority5, priority6, priority7] =
      some (hexagonalBipyramidEightPriorityPlacement
        priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7) := rfl

@[simp] theorem hexagonalBipyramidEightPriorityPlacement_lookup
    (priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7 :
      PolyhedralPriorityNumber) (position : Fin 8) :
    [priority0, priority1, priority2, priority3, priority4, priority5, priority6, priority7][position.val]? =
      some (hexagonalBipyramidEightPriorityPlacement
        priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7 position) := by
  fin_cases position <;> rfl

theorem hexagonalBipyramidPositionValues_lookups
    (priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7 :
      PolyhedralPriorityNumber) (positions : List (Fin 8)) :
    (positions.map Fin.val).mapM
        (fun position =>
          [priority0, priority1, priority2, priority3, priority4, priority5,
            priority6, priority7][position]?) =
      some (positions.map (hexagonalBipyramidEightPriorityPlacement
        priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7)) := by
  induction positions with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      fin_cases head <;>
        simp [hexagonalBipyramidEightPriorityPlacement, inductionHypothesis]

private theorem eraseDups_eq_self_of_nodup
    {alpha : Type*} [BEq alpha] [LawfulBEq alpha]
    (values : List alpha) (nodup : values.Nodup) : values.eraseDups = values := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      have parts := List.nodup_cons.mp nodup
      have filtered : tail.filter (fun value => !value == head) = tail := by
        apply List.filter_eq_self.mpr
        intro value member
        have different : value ≠ head := by
          intro same
          exact parts.1 (same ▸ member)
        simp [different]
      rw [List.eraseDups_cons, filtered, inductionHypothesis parts.2]

theorem hexagonalBipyramidFlattenedPositionValues_eraseDups_length
    (partition : HexagonalBipyramid8SpatialPerception.Partition)
    (member : partition ∈ HexagonalBipyramid8SpatialPerception.partitions) :
    (((partition.axial.1 :: partition.axial.2 :: partition.equatorialCycle).map
        Fin.val).eraseDups.length) = 8 := by
  have positionNodup :=
    HexagonalBipyramid8SpatialPerception.flattenedPositions_nodup_of_mem member
  have valuesNodup :
      ((partition.axial.1 :: partition.axial.2 :: partition.equatorialCycle).map
        Fin.val).Nodup :=
    positionNodup.map (by
      intro first second same
      exact Fin.ext same)
  rw [eraseDups_eq_self_of_nodup _ valuesNodup]
  simpa using
    HexagonalBipyramid8SpatialPerception.flattenedPositions_length_of_mem member

structure IndexedHexagonalBipyramid8SpatialObservation where
  center : ℕ
  ligands : List ℕ
  deriving DecidableEq, Repr

def SpatialConfiguration.hexagonalBipyramid8Frame?
    (spatial : SpatialConfiguration) (center : ℕ) (ligands : List ℕ) :
    Option HexagonalBipyramid8SpatialPerception.Frame :=
  match ligands with
  | [donor0, donor1, donor2, donor3, donor4, donor5, donor6, donor7] => do
      let centerPoint ← spatial.positions[center]?
      let donorPoint0 ← spatial.positions[donor0]?
      let donorPoint1 ← spatial.positions[donor1]?
      let donorPoint2 ← spatial.positions[donor2]?
      let donorPoint3 ← spatial.positions[donor3]?
      let donorPoint4 ← spatial.positions[donor4]?
      let donorPoint5 ← spatial.positions[donor5]?
      let donorPoint6 ← spatial.positions[donor6]?
      let donorPoint7 ← spatial.positions[donor7]?
      some
        { center := centerPoint
          donor0 := donorPoint0
          donor1 := donorPoint1
          donor2 := donorPoint2
          donor3 := donorPoint3
          donor4 := donorPoint4
          donor5 := donorPoint5
          donor6 := donorPoint6
          donor7 := donorPoint7 }
  | _ => none

namespace IndexedHexagonalBipyramid8SpatialObservation

def withDerivedData (record : IndexedHexagonalBipyramid8SpatialObservation)
    (partition : HexagonalBipyramid8SpatialPerception.Partition)
    (sense : PolyhedralRotationSense) : IndexedPolyhedralGeometryObservation :=
  { center := record.center
    geometry := .hexagonalBipyramid
    recognition := .higherCoordinationNearestIdealized .hexagonalBipyramid
    ligands := record.ligands
    configurationPositions := .hexagonalBipyramid
      partition.axial.1.val partition.axial.2.val
      (partition.equatorialCycle.map Fin.val)
    absoluteOrientation := .hexagonalBipyramidAC
      (BlueBookP93.rotationOfProduction sense) }

def derivedRecord? (record : IndexedHexagonalBipyramid8SpatialObservation)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration) :
    Option IndexedPolyhedralGeometryObservation := do
  let frame ← spatial.hexagonalBipyramid8Frame? record.center record.ligands
  let partition ← HexagonalBipyramid8SpatialPerception.perceive? frame
  let priorities ← result.molecularPolyhedralPriorityNumbers?
    record.center .hexagonalBipyramid record.ligands
  let placement ← hexagonalBipyramidEightPriorityPlacement? priorities
  let sense ← HexagonalBipyramid8SpatialOrientation.rotationSense?
    frame partition placement
  some (record.withDerivedData partition sense)

end IndexedHexagonalBipyramid8SpatialObservation

def HexagonalBipyramid8DerivedRecordJudgment
    (record : IndexedHexagonalBipyramid8SpatialObservation)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (derived : IndexedPolyhedralGeometryObservation) : Prop :=
  ∃ frame partition priorities placement sense,
    spatial.hexagonalBipyramid8Frame? record.center record.ligands = some frame ∧
    HexagonalBipyramid8SpatialPerception.Judgment frame partition ∧
    result.molecularPolyhedralPriorityNumbers?
      record.center .hexagonalBipyramid record.ligands = some priorities ∧
    hexagonalBipyramidEightPriorityPlacement? priorities = some placement ∧
    HexagonalBipyramid8SpatialOrientation.Judgment frame partition placement sense ∧
    derived = record.withDerivedData partition sense

theorem IndexedHexagonalBipyramid8SpatialObservation.derivedRecord?_eq_some_iff
    (record : IndexedHexagonalBipyramid8SpatialObservation)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (derived : IndexedPolyhedralGeometryObservation) :
    record.derivedRecord? result spatial = some derived ↔
      HexagonalBipyramid8DerivedRecordJudgment record result spatial derived := by
  constructor
  · intro computed
    unfold IndexedHexagonalBipyramid8SpatialObservation.derivedRecord? at computed
    cases frameEq : spatial.hexagonalBipyramid8Frame? record.center record.ligands with
    | none => simp [frameEq] at computed
    | some frame =>
        cases partitionEq : HexagonalBipyramid8SpatialPerception.perceive? frame with
        | none => simp [frameEq, partitionEq] at computed
        | some partition =>
            cases priorityEq : result.molecularPolyhedralPriorityNumbers?
                record.center .hexagonalBipyramid record.ligands with
            | none => simp [frameEq, priorityEq] at computed
            | some priorities =>
                cases placementEq : hexagonalBipyramidEightPriorityPlacement? priorities with
                | none => simp [frameEq, priorityEq, placementEq] at computed
                | some placement =>
                    cases senseEq : HexagonalBipyramid8SpatialOrientation.rotationSense?
                        frame partition placement with
                    | none =>
                        simp [frameEq, partitionEq, priorityEq, placementEq, senseEq] at computed
                    | some sense =>
                        have derivedEq : derived = record.withDerivedData partition sense := by
                          simpa [frameEq, partitionEq, priorityEq, placementEq, senseEq]
                            using computed.symm
                        exact ⟨frame, partition, priorities, placement, sense, frameEq,
                          (HexagonalBipyramid8SpatialPerception.perceive?_eq_some_iff
                            frame partition).mp partitionEq,
                          priorityEq, placementEq,
                          (HexagonalBipyramid8SpatialOrientation.rotationSense?_eq_some_iff
                            frame partition placement sense).mp senseEq,
                          derivedEq⟩
  · rintro ⟨frame, partition, priorities, placement, sense, frameEq, perceived,
      priorityEq, placementEq, orientation, rfl⟩
    have partitionEq : HexagonalBipyramid8SpatialPerception.perceive? frame = some partition :=
      (HexagonalBipyramid8SpatialPerception.perceive?_eq_some_iff
        frame partition).mpr perceived
    have senseEq : HexagonalBipyramid8SpatialOrientation.rotationSense?
        frame partition placement = some sense :=
      (HexagonalBipyramid8SpatialOrientation.rotationSense?_eq_some_iff
        frame partition placement sense).mpr orientation
    simp [IndexedHexagonalBipyramid8SpatialObservation.derivedRecord?, frameEq, partitionEq,
      priorityEq, placementEq, senseEq]

def ChemistryNormalizationResult.hexagonalBipyramid8SpatialAssignment?
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedHexagonalBipyramid8SpatialObservation) : Option StereoAssignment := do
  let derived ← record.derivedRecord? result spatial
  result.polyhedralGeometryObservationAssignment? derived

def HexagonalBipyramid8SpatialAssignmentJudgment
    (record : IndexedHexagonalBipyramid8SpatialObservation)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (assignment : StereoAssignment) : Prop :=
  ∃ derived,
    HexagonalBipyramid8DerivedRecordJudgment record result spatial derived ∧
      result.polyhedralGeometryObservationAssignment? derived = some assignment

theorem ChemistryNormalizationResult.hexagonalBipyramid8SpatialAssignment?_eq_some_iff
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedHexagonalBipyramid8SpatialObservation) (assignment : StereoAssignment) :
    result.hexagonalBipyramid8SpatialAssignment? spatial record = some assignment ↔
      HexagonalBipyramid8SpatialAssignmentJudgment record result spatial assignment := by
  unfold ChemistryNormalizationResult.hexagonalBipyramid8SpatialAssignment?
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

theorem ChemistryNormalizationResult.hexagonalBipyramid8SpatialAssignment?_eq_none_iff
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedHexagonalBipyramid8SpatialObservation) :
    result.hexagonalBipyramid8SpatialAssignment? spatial record = none ↔
      ¬ ∃ assignment,
        HexagonalBipyramid8SpatialAssignmentJudgment record result spatial assignment := by
  constructor
  · intro absent ⟨assignment, judged⟩
    have present :=
      (result.hexagonalBipyramid8SpatialAssignment?_eq_some_iff
        spatial record assignment).mpr judged
    rw [absent] at present
    contradiction
  · intro noJudgment
    cases computed : result.hexagonalBipyramid8SpatialAssignment? spatial record with
    | none => rfl
    | some assignment =>
        exact False.elim (noJudgment ⟨assignment,
          (result.hexagonalBipyramid8SpatialAssignment?_eq_some_iff
            spatial record assignment).mp computed⟩)

/-- Exact final molecule/coordinate HBPY-8 descriptor. -/
theorem ChemistryNormalizationResult.hexagonalBipyramid8Spatial_exact
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (center : ℕ) (ligands : List ℕ)
    (frame : HexagonalBipyramid8SpatialPerception.Frame)
    (partition : HexagonalBipyramid8SpatialPerception.Partition)
    (priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7 :
      PolyhedralPriorityNumber) (sense : PolyhedralRotationSense)
    (frameEq : spatial.hexagonalBipyramid8Frame? center ligands = some frame)
    (perceived : HexagonalBipyramid8SpatialPerception.Judgment frame partition)
    (priorityEq : result.molecularPolyhedralPriorityNumbers?
      center .hexagonalBipyramid ligands =
        some [priority0, priority1, priority2, priority3, priority4, priority5, priority6, priority7])
    (prioritiesDistinct :
      [priority0, priority1, priority2, priority3, priority4, priority5,
        priority6, priority7].eraseDups.length = 8)
    (orientation : HexagonalBipyramid8SpatialOrientation.Judgment frame partition
      (hexagonalBipyramidEightPriorityPlacement
        priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7) sense) :
    result.hexagonalBipyramid8SpatialAssignment? spatial
        { center := center, ligands := ligands } =
      some
        { unit := StereoUnit.polyhedron center
          outcome := StereoOutcome.polyhedral
            { geometry := .hexagonalBipyramid
              configurationIndex := bipyramidalConfigurationIndex
                (hexagonalBipyramidEightPriorityPlacement
                  priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7
                  partition.axial.1)
                (hexagonalBipyramidEightPriorityPlacement
                  priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7
                  partition.axial.2)
                (partition.equatorialCycle.map
                  (hexagonalBipyramidEightPriorityPlacement
                    priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7))
              absolute? := some (.ac (PolyhedralChiralitySymbol.ofRotation sense)) } } := by
  let placement := hexagonalBipyramidEightPriorityPlacement
    priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7
  have partitionEq : HexagonalBipyramid8SpatialPerception.perceive? frame = some partition :=
    (HexagonalBipyramid8SpatialPerception.perceive?_eq_some_iff
      frame partition).mpr perceived
  have senseEq : HexagonalBipyramid8SpatialOrientation.rotationSense?
      frame partition placement = some sense :=
    (HexagonalBipyramid8SpatialOrientation.rotationSense?_eq_some_iff
      frame partition placement sense).mpr orientation
  have derivedEq :
      ({ center := center, ligands := ligands } :
        IndexedHexagonalBipyramid8SpatialObservation).derivedRecord? result spatial =
        some (({ center := center, ligands := ligands } :
          IndexedHexagonalBipyramid8SpatialObservation).withDerivedData partition sense) := by
    simp [IndexedHexagonalBipyramid8SpatialObservation.derivedRecord?, frameEq, partitionEq,
      priorityEq, hexagonalBipyramidEightPriorityPlacement?_explicit, placement, senseEq]
  have positionsDistinct :=
    hexagonalBipyramidFlattenedPositionValues_eraseDups_length partition perceived.1
  have cycleLength :=
    HexagonalBipyramid8SpatialPerception.equatorialCycle_length_of_mem perceived.1
  have lookups := hexagonalBipyramidPositionValues_lookups
    priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7
    (partition.axial.1 :: partition.axial.2 :: partition.equatorialCycle)
  have downstream := bipyramidalGeometryObservationAssignment_exact result .hexagonal8
    center ligands sense
    [priority0, priority1, priority2, priority3, priority4, priority5, priority6, priority7]
    partition.axial.1.val partition.axial.2.val
    (partition.equatorialCycle.map Fin.val)
    (placement partition.axial.1) (placement partition.axial.2)
    (partition.equatorialCycle.map placement)
    priorityEq prioritiesDistinct
    (by simpa [RedBookIR9.BipyramidKind.positions,
      RedBookIR9.BipyramidKind.configurationArity] using
        HexagonalBipyramid8SpatialPerception.flattenedPositions_length_of_mem perceived.1)
    (by simpa [RedBookIR9.BipyramidKind.positions, cycleLength] using positionsDistinct)
    (by simpa [RedBookIR9.BipyramidKind.positions,
      RedBookIR9.BipyramidKind.entries] using lookups)
  simpa [ChemistryNormalizationResult.hexagonalBipyramid8SpatialAssignment?, derivedEq,
    IndexedHexagonalBipyramid8SpatialObservation.withDerivedData, placement] using downstream

/-- Constructive exact-domain completeness for strict idealized HBPY-8. -/
theorem ChemistryNormalizationResult.hexagonalBipyramid8Spatial_exists_exact
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (center : ℕ) (ligands : List ℕ)
    (frame : HexagonalBipyramid8SpatialPerception.Frame)
    (partition : HexagonalBipyramid8SpatialPerception.Partition)
    (priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7 :
      PolyhedralPriorityNumber)
    (axialOrder : Fin 8 × Fin 8) (senior : Fin 6)
    (direction : HexagonalBipyramid8SpatialOrientation.CycleDirection)
    (frameEq : spatial.hexagonalBipyramid8Frame? center ligands = some frame)
    (perceived : HexagonalBipyramid8SpatialPerception.Judgment frame partition)
    (priorityEq : result.molecularPolyhedralPriorityNumbers?
      center .hexagonalBipyramid ligands =
        some [priority0, priority1, priority2, priority3, priority4, priority5, priority6, priority7])
    (prioritiesDistinct :
      [priority0, priority1, priority2, priority3, priority4, priority5,
        priority6, priority7].eraseDups.length = 8)
    (axialOrdered : HexagonalBipyramid8SpatialOrientation.IsStrictAxialOrder
      (hexagonalBipyramidEightPriorityPlacement
        priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7)
      partition.axial axialOrder)
    (seniority : HexagonalBipyramid8SpatialOrientation.IsStrictSenior6
      (HexagonalBipyramid8SpatialOrientation.cyclePlacement
        (hexagonalBipyramidEightPriorityPlacement
          priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7) partition)
      senior)
    (directionPreferred : HexagonalBipyramid8SpatialOrientation.IsPreferredCycleDirection
      (HexagonalBipyramid8SpatialOrientation.cyclePlacement
        (hexagonalBipyramidEightPriorityPlacement
          priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7) partition)
      senior direction) :
    ∃ sense,
      result.hexagonalBipyramid8SpatialAssignment? spatial
          { center := center, ligands := ligands } =
        some
          { unit := StereoUnit.polyhedron center
            outcome := StereoOutcome.polyhedral
              { geometry := .hexagonalBipyramid
                configurationIndex := bipyramidalConfigurationIndex
                  (hexagonalBipyramidEightPriorityPlacement
                    priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7
                    partition.axial.1)
                  (hexagonalBipyramidEightPriorityPlacement
                    priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7
                    partition.axial.2)
                  (partition.equatorialCycle.map
                    (hexagonalBipyramidEightPriorityPlacement
                      priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7))
                absolute? := some (.ac (PolyhedralChiralitySymbol.ofRotation sense)) } } := by
  let placement := hexagonalBipyramidEightPriorityPlacement
    priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7
  obtain ⟨sense, _senseEq, orientation⟩ :=
    HexagonalBipyramid8SpatialOrientation.rotationSense?_exists_of_exactGeometry
      frame partition placement perceived axialOrder senior direction
      axialOrdered seniority directionPreferred
  exact ⟨sense, result.hexagonalBipyramid8Spatial_exact spatial center ligands frame partition
    priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7 sense frameEq perceived
    priorityEq prioritiesDistinct orientation⟩

end TetraStereo.OneCenter
