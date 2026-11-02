import TetraStereo.OneCenter.IR9PentagonalBipyramid7SpatialOrientation
import TetraStereo.OneCenter.CIPIR9BipyramidalIntegration

set_option autoImplicit false

namespace TetraStereo.OneCenter

open RedBookIR9
open RedBookIR9.PentagonalBipyramid7SpatialPerception
open RedBookIR9.PentagonalBipyramid7SpatialOrientation

/-! # Public molecule/coordinate integration for exact PBPY-7 -/

def pentagonalBipyramidSevenPriorityPlacement
    (priority0 priority1 priority2 priority3 priority4 priority5 priority6 :
      PolyhedralPriorityNumber) : Fin 7 → PolyhedralPriorityNumber
  | 0 => priority0
  | 1 => priority1
  | 2 => priority2
  | 3 => priority3
  | 4 => priority4
  | 5 => priority5
  | 6 => priority6

def pentagonalBipyramidSevenPriorityPlacement?
    (priorities : List PolyhedralPriorityNumber) :
    Option (Fin 7 → PolyhedralPriorityNumber) :=
  match priorities with
  | [priority0, priority1, priority2, priority3, priority4, priority5, priority6] =>
      some (pentagonalBipyramidSevenPriorityPlacement
        priority0 priority1 priority2 priority3 priority4 priority5 priority6)
  | _ => none

@[simp] theorem pentagonalBipyramidSevenPriorityPlacement?_explicit
    (priority0 priority1 priority2 priority3 priority4 priority5 priority6 :
      PolyhedralPriorityNumber) :
    pentagonalBipyramidSevenPriorityPlacement?
        [priority0, priority1, priority2, priority3, priority4, priority5, priority6] =
      some (pentagonalBipyramidSevenPriorityPlacement
        priority0 priority1 priority2 priority3 priority4 priority5 priority6) := rfl

@[simp] theorem pentagonalBipyramidSevenPriorityPlacement_lookup
    (priority0 priority1 priority2 priority3 priority4 priority5 priority6 :
      PolyhedralPriorityNumber) (position : Fin 7) :
    [priority0, priority1, priority2, priority3, priority4, priority5, priority6][position.val]? =
      some (pentagonalBipyramidSevenPriorityPlacement
        priority0 priority1 priority2 priority3 priority4 priority5 priority6 position) := by
  fin_cases position <;> rfl

theorem pentagonalBipyramidPositionValues_lookups
    (priority0 priority1 priority2 priority3 priority4 priority5 priority6 :
      PolyhedralPriorityNumber) (positions : List (Fin 7)) :
    (positions.map Fin.val).mapM
        (fun position =>
          [priority0, priority1, priority2, priority3, priority4, priority5,
            priority6][position]?) =
      some (positions.map (pentagonalBipyramidSevenPriorityPlacement
        priority0 priority1 priority2 priority3 priority4 priority5 priority6)) := by
  induction positions with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      fin_cases head <;>
        simp [pentagonalBipyramidSevenPriorityPlacement, inductionHypothesis]

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

theorem pentagonalBipyramidFlattenedPositionValues_eraseDups_length
    (partition : PentagonalBipyramid7SpatialPerception.Partition)
    (member : partition ∈ PentagonalBipyramid7SpatialPerception.partitions) :
    (((partition.axial.1 :: partition.axial.2 :: partition.equatorialCycle).map
        Fin.val).eraseDups.length) = 7 := by
  have positionNodup :=
    PentagonalBipyramid7SpatialPerception.flattenedPositions_nodup_of_mem member
  have valuesNodup :
      ((partition.axial.1 :: partition.axial.2 :: partition.equatorialCycle).map
        Fin.val).Nodup :=
    positionNodup.map (by
      intro first second same
      exact Fin.ext same)
  rw [eraseDups_eq_self_of_nodup _ valuesNodup]
  simpa using
    PentagonalBipyramid7SpatialPerception.flattenedPositions_length_of_mem member

structure IndexedPentagonalBipyramid7SpatialObservation where
  center : ℕ
  ligands : List ℕ
  deriving DecidableEq, Repr

def SpatialConfiguration.pentagonalBipyramid7Frame?
    (spatial : SpatialConfiguration) (center : ℕ) (ligands : List ℕ) :
    Option PentagonalBipyramid7SpatialPerception.Frame :=
  match ligands with
  | [donor0, donor1, donor2, donor3, donor4, donor5, donor6] => do
      let centerPoint ← spatial.positions[center]?
      let donorPoint0 ← spatial.positions[donor0]?
      let donorPoint1 ← spatial.positions[donor1]?
      let donorPoint2 ← spatial.positions[donor2]?
      let donorPoint3 ← spatial.positions[donor3]?
      let donorPoint4 ← spatial.positions[donor4]?
      let donorPoint5 ← spatial.positions[donor5]?
      let donorPoint6 ← spatial.positions[donor6]?
      some
        { center := centerPoint
          donor0 := donorPoint0
          donor1 := donorPoint1
          donor2 := donorPoint2
          donor3 := donorPoint3
          donor4 := donorPoint4
          donor5 := donorPoint5
          donor6 := donorPoint6 }
  | _ => none

namespace IndexedPentagonalBipyramid7SpatialObservation

def withDerivedData (record : IndexedPentagonalBipyramid7SpatialObservation)
    (partition : PentagonalBipyramid7SpatialPerception.Partition)
    (sense : PolyhedralRotationSense) : IndexedPolyhedralGeometryObservation :=
  { center := record.center
    geometry := .pentagonalBipyramid
    recognition := .higherCoordinationNearestIdealized .pentagonalBipyramid
    ligands := record.ligands
    configurationPositions := .pentagonalBipyramid
      partition.axial.1.val partition.axial.2.val
      (partition.equatorialCycle.map Fin.val)
    absoluteOrientation := .pentagonalBipyramidAC
      (BlueBookP93.rotationOfProduction sense) }

def derivedRecord? (record : IndexedPentagonalBipyramid7SpatialObservation)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration) :
    Option IndexedPolyhedralGeometryObservation := do
  let frame ← spatial.pentagonalBipyramid7Frame? record.center record.ligands
  let partition ← PentagonalBipyramid7SpatialPerception.perceive? frame
  let priorities ← result.molecularPolyhedralPriorityNumbers?
    record.center .pentagonalBipyramid record.ligands
  let placement ← pentagonalBipyramidSevenPriorityPlacement? priorities
  let sense ← PentagonalBipyramid7SpatialOrientation.rotationSense?
    frame partition placement
  some (record.withDerivedData partition sense)

end IndexedPentagonalBipyramid7SpatialObservation

def PentagonalBipyramid7DerivedRecordJudgment
    (record : IndexedPentagonalBipyramid7SpatialObservation)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (derived : IndexedPolyhedralGeometryObservation) : Prop :=
  ∃ frame partition priorities placement sense,
    spatial.pentagonalBipyramid7Frame? record.center record.ligands = some frame ∧
    PentagonalBipyramid7SpatialPerception.Judgment frame partition ∧
    result.molecularPolyhedralPriorityNumbers?
      record.center .pentagonalBipyramid record.ligands = some priorities ∧
    pentagonalBipyramidSevenPriorityPlacement? priorities = some placement ∧
    PentagonalBipyramid7SpatialOrientation.Judgment frame partition placement sense ∧
    derived = record.withDerivedData partition sense

theorem IndexedPentagonalBipyramid7SpatialObservation.derivedRecord?_eq_some_iff
    (record : IndexedPentagonalBipyramid7SpatialObservation)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (derived : IndexedPolyhedralGeometryObservation) :
    record.derivedRecord? result spatial = some derived ↔
      PentagonalBipyramid7DerivedRecordJudgment record result spatial derived := by
  constructor
  · intro computed
    unfold IndexedPentagonalBipyramid7SpatialObservation.derivedRecord? at computed
    cases frameEq : spatial.pentagonalBipyramid7Frame? record.center record.ligands with
    | none => simp [frameEq] at computed
    | some frame =>
        cases partitionEq : PentagonalBipyramid7SpatialPerception.perceive? frame with
        | none => simp [frameEq, partitionEq] at computed
        | some partition =>
            cases priorityEq : result.molecularPolyhedralPriorityNumbers?
                record.center .pentagonalBipyramid record.ligands with
            | none => simp [frameEq, priorityEq] at computed
            | some priorities =>
                cases placementEq : pentagonalBipyramidSevenPriorityPlacement? priorities with
                | none => simp [frameEq, priorityEq, placementEq] at computed
                | some placement =>
                    cases senseEq : PentagonalBipyramid7SpatialOrientation.rotationSense?
                        frame partition placement with
                    | none =>
                        simp [frameEq, partitionEq, priorityEq, placementEq, senseEq] at computed
                    | some sense =>
                        have derivedEq : derived = record.withDerivedData partition sense := by
                          simpa [frameEq, partitionEq, priorityEq, placementEq, senseEq]
                            using computed.symm
                        exact ⟨frame, partition, priorities, placement, sense, frameEq,
                          (PentagonalBipyramid7SpatialPerception.perceive?_eq_some_iff
                            frame partition).mp partitionEq,
                          priorityEq, placementEq,
                          (PentagonalBipyramid7SpatialOrientation.rotationSense?_eq_some_iff
                            frame partition placement sense).mp senseEq,
                          derivedEq⟩
  · rintro ⟨frame, partition, priorities, placement, sense, frameEq, perceived,
      priorityEq, placementEq, orientation, rfl⟩
    have partitionEq : PentagonalBipyramid7SpatialPerception.perceive? frame = some partition :=
      (PentagonalBipyramid7SpatialPerception.perceive?_eq_some_iff
        frame partition).mpr perceived
    have senseEq : PentagonalBipyramid7SpatialOrientation.rotationSense?
        frame partition placement = some sense :=
      (PentagonalBipyramid7SpatialOrientation.rotationSense?_eq_some_iff
        frame partition placement sense).mpr orientation
    simp [IndexedPentagonalBipyramid7SpatialObservation.derivedRecord?, frameEq, partitionEq,
      priorityEq, placementEq, senseEq]

def ChemistryNormalizationResult.pentagonalBipyramid7SpatialAssignment?
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedPentagonalBipyramid7SpatialObservation) : Option StereoAssignment := do
  let derived ← record.derivedRecord? result spatial
  result.polyhedralGeometryObservationAssignment? derived

def PentagonalBipyramid7SpatialAssignmentJudgment
    (record : IndexedPentagonalBipyramid7SpatialObservation)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (assignment : StereoAssignment) : Prop :=
  ∃ derived,
    PentagonalBipyramid7DerivedRecordJudgment record result spatial derived ∧
      result.polyhedralGeometryObservationAssignment? derived = some assignment

theorem ChemistryNormalizationResult.pentagonalBipyramid7SpatialAssignment?_eq_some_iff
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedPentagonalBipyramid7SpatialObservation) (assignment : StereoAssignment) :
    result.pentagonalBipyramid7SpatialAssignment? spatial record = some assignment ↔
      PentagonalBipyramid7SpatialAssignmentJudgment record result spatial assignment := by
  unfold ChemistryNormalizationResult.pentagonalBipyramid7SpatialAssignment?
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

theorem ChemistryNormalizationResult.pentagonalBipyramid7SpatialAssignment?_eq_none_iff
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedPentagonalBipyramid7SpatialObservation) :
    result.pentagonalBipyramid7SpatialAssignment? spatial record = none ↔
      ¬ ∃ assignment,
        PentagonalBipyramid7SpatialAssignmentJudgment record result spatial assignment := by
  constructor
  · intro absent ⟨assignment, judged⟩
    have present :=
      (result.pentagonalBipyramid7SpatialAssignment?_eq_some_iff
        spatial record assignment).mpr judged
    rw [absent] at present
    contradiction
  · intro noJudgment
    cases computed : result.pentagonalBipyramid7SpatialAssignment? spatial record with
    | none => rfl
    | some assignment =>
        exact False.elim (noJudgment ⟨assignment,
          (result.pentagonalBipyramid7SpatialAssignment?_eq_some_iff
            spatial record assignment).mp computed⟩)

/-- Exact final molecule/coordinate PBPY-7 descriptor. -/
theorem ChemistryNormalizationResult.pentagonalBipyramid7Spatial_exact
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (center : ℕ) (ligands : List ℕ)
    (frame : PentagonalBipyramid7SpatialPerception.Frame)
    (partition : PentagonalBipyramid7SpatialPerception.Partition)
    (priority0 priority1 priority2 priority3 priority4 priority5 priority6 :
      PolyhedralPriorityNumber) (sense : PolyhedralRotationSense)
    (frameEq : spatial.pentagonalBipyramid7Frame? center ligands = some frame)
    (perceived : PentagonalBipyramid7SpatialPerception.Judgment frame partition)
    (priorityEq : result.molecularPolyhedralPriorityNumbers?
      center .pentagonalBipyramid ligands =
        some [priority0, priority1, priority2, priority3, priority4, priority5, priority6])
    (prioritiesDistinct :
      [priority0, priority1, priority2, priority3, priority4, priority5,
        priority6].eraseDups.length = 7)
    (orientation : PentagonalBipyramid7SpatialOrientation.Judgment frame partition
      (pentagonalBipyramidSevenPriorityPlacement
        priority0 priority1 priority2 priority3 priority4 priority5 priority6) sense) :
    result.pentagonalBipyramid7SpatialAssignment? spatial
        { center := center, ligands := ligands } =
      some
        { unit := StereoUnit.polyhedron center
          outcome := StereoOutcome.polyhedral
            { geometry := .pentagonalBipyramid
              configurationIndex := bipyramidalConfigurationIndex
                (pentagonalBipyramidSevenPriorityPlacement
                  priority0 priority1 priority2 priority3 priority4 priority5 priority6
                  partition.axial.1)
                (pentagonalBipyramidSevenPriorityPlacement
                  priority0 priority1 priority2 priority3 priority4 priority5 priority6
                  partition.axial.2)
                (partition.equatorialCycle.map
                  (pentagonalBipyramidSevenPriorityPlacement
                    priority0 priority1 priority2 priority3 priority4 priority5 priority6))
              absolute? := some (.ac (PolyhedralChiralitySymbol.ofRotation sense)) } } := by
  let placement := pentagonalBipyramidSevenPriorityPlacement
    priority0 priority1 priority2 priority3 priority4 priority5 priority6
  have partitionEq : PentagonalBipyramid7SpatialPerception.perceive? frame = some partition :=
    (PentagonalBipyramid7SpatialPerception.perceive?_eq_some_iff
      frame partition).mpr perceived
  have senseEq : PentagonalBipyramid7SpatialOrientation.rotationSense?
      frame partition placement = some sense :=
    (PentagonalBipyramid7SpatialOrientation.rotationSense?_eq_some_iff
      frame partition placement sense).mpr orientation
  have derivedEq :
      ({ center := center, ligands := ligands } :
        IndexedPentagonalBipyramid7SpatialObservation).derivedRecord? result spatial =
        some (({ center := center, ligands := ligands } :
          IndexedPentagonalBipyramid7SpatialObservation).withDerivedData partition sense) := by
    simp [IndexedPentagonalBipyramid7SpatialObservation.derivedRecord?, frameEq, partitionEq,
      priorityEq, pentagonalBipyramidSevenPriorityPlacement?_explicit, placement, senseEq]
  have positionsDistinct :=
    pentagonalBipyramidFlattenedPositionValues_eraseDups_length partition perceived.1
  have cycleLength :=
    PentagonalBipyramid7SpatialPerception.equatorialCycle_length_of_mem perceived.1
  have lookups := pentagonalBipyramidPositionValues_lookups
    priority0 priority1 priority2 priority3 priority4 priority5 priority6
    (partition.axial.1 :: partition.axial.2 :: partition.equatorialCycle)
  have downstream := bipyramidalGeometryObservationAssignment_exact result .pentagonal7
    center ligands sense
    [priority0, priority1, priority2, priority3, priority4, priority5, priority6]
    partition.axial.1.val partition.axial.2.val
    (partition.equatorialCycle.map Fin.val)
    (placement partition.axial.1) (placement partition.axial.2)
    (partition.equatorialCycle.map placement)
    priorityEq prioritiesDistinct
    (by simpa [RedBookIR9.BipyramidKind.positions,
      RedBookIR9.BipyramidKind.configurationArity] using
        PentagonalBipyramid7SpatialPerception.flattenedPositions_length_of_mem perceived.1)
    (by simpa [RedBookIR9.BipyramidKind.positions, cycleLength] using positionsDistinct)
    (by simpa [RedBookIR9.BipyramidKind.positions,
      RedBookIR9.BipyramidKind.entries] using lookups)
  simpa [ChemistryNormalizationResult.pentagonalBipyramid7SpatialAssignment?, derivedEq,
    IndexedPentagonalBipyramid7SpatialObservation.withDerivedData, placement] using downstream

/-- Constructive exact-domain completeness for strict idealized PBPY-7. -/
theorem ChemistryNormalizationResult.pentagonalBipyramid7Spatial_exists_exact
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (center : ℕ) (ligands : List ℕ)
    (frame : PentagonalBipyramid7SpatialPerception.Frame)
    (partition : PentagonalBipyramid7SpatialPerception.Partition)
    (priority0 priority1 priority2 priority3 priority4 priority5 priority6 :
      PolyhedralPriorityNumber)
    (axialOrder : Fin 7 × Fin 7) (senior : Fin 5)
    (direction : PentagonalBipyramid7SpatialOrientation.CycleDirection)
    (frameEq : spatial.pentagonalBipyramid7Frame? center ligands = some frame)
    (perceived : PentagonalBipyramid7SpatialPerception.Judgment frame partition)
    (priorityEq : result.molecularPolyhedralPriorityNumbers?
      center .pentagonalBipyramid ligands =
        some [priority0, priority1, priority2, priority3, priority4, priority5, priority6])
    (prioritiesDistinct :
      [priority0, priority1, priority2, priority3, priority4, priority5,
        priority6].eraseDups.length = 7)
    (axialOrdered : PentagonalBipyramid7SpatialOrientation.IsStrictAxialOrder
      (pentagonalBipyramidSevenPriorityPlacement
        priority0 priority1 priority2 priority3 priority4 priority5 priority6)
      partition.axial axialOrder)
    (seniority : PentagonalBipyramid7SpatialOrientation.IsStrictSenior5
      (PentagonalBipyramid7SpatialOrientation.cyclePlacement
        (pentagonalBipyramidSevenPriorityPlacement
          priority0 priority1 priority2 priority3 priority4 priority5 priority6) partition)
      senior)
    (directionPreferred : PentagonalBipyramid7SpatialOrientation.IsPreferredCycleDirection
      (PentagonalBipyramid7SpatialOrientation.cyclePlacement
        (pentagonalBipyramidSevenPriorityPlacement
          priority0 priority1 priority2 priority3 priority4 priority5 priority6) partition)
      senior direction) :
    ∃ sense,
      result.pentagonalBipyramid7SpatialAssignment? spatial
          { center := center, ligands := ligands } =
        some
          { unit := StereoUnit.polyhedron center
            outcome := StereoOutcome.polyhedral
              { geometry := .pentagonalBipyramid
                configurationIndex := bipyramidalConfigurationIndex
                  (pentagonalBipyramidSevenPriorityPlacement
                    priority0 priority1 priority2 priority3 priority4 priority5 priority6
                    partition.axial.1)
                  (pentagonalBipyramidSevenPriorityPlacement
                    priority0 priority1 priority2 priority3 priority4 priority5 priority6
                    partition.axial.2)
                  (partition.equatorialCycle.map
                    (pentagonalBipyramidSevenPriorityPlacement
                      priority0 priority1 priority2 priority3 priority4 priority5 priority6))
                absolute? := some (.ac (PolyhedralChiralitySymbol.ofRotation sense)) } } := by
  let placement := pentagonalBipyramidSevenPriorityPlacement
    priority0 priority1 priority2 priority3 priority4 priority5 priority6
  obtain ⟨sense, _senseEq, orientation⟩ :=
    PentagonalBipyramid7SpatialOrientation.rotationSense?_exists_of_exactGeometry
      frame partition placement perceived axialOrder senior direction
      axialOrdered seniority directionPreferred
  exact ⟨sense, result.pentagonalBipyramid7Spatial_exact spatial center ligands frame partition
    priority0 priority1 priority2 priority3 priority4 priority5 priority6 sense frameEq perceived
    priorityEq prioritiesDistinct orientation⟩

end TetraStereo.OneCenter
