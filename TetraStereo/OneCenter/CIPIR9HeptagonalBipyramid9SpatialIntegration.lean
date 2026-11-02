import TetraStereo.OneCenter.IR9HeptagonalBipyramid9SpatialOrientation
import TetraStereo.OneCenter.CIPIR9BipyramidalIntegration

set_option autoImplicit false

namespace TetraStereo.OneCenter

open RedBookIR9
open RedBookIR9.HeptagonalBipyramid9SpatialPerception
open RedBookIR9.HeptagonalBipyramid9SpatialOrientation

/-! # Public molecule/coordinate integration for exact HBPY-9 -/

def heptagonalBipyramidNinePriorityPlacement
    (priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7 priority8 :
      PolyhedralPriorityNumber) : Fin 9 → PolyhedralPriorityNumber
  | 0 => priority0
  | 1 => priority1
  | 2 => priority2
  | 3 => priority3
  | 4 => priority4
  | 5 => priority5
  | 6 => priority6
  | 7 => priority7
  | 8 => priority8

def heptagonalBipyramidNinePriorityPlacement?
    (priorities : List PolyhedralPriorityNumber) :
    Option (Fin 9 → PolyhedralPriorityNumber) :=
  match priorities with
  | [priority0, priority1, priority2, priority3, priority4, priority5, priority6, priority7, priority8] =>
      some (heptagonalBipyramidNinePriorityPlacement
        priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7 priority8)
  | _ => none

@[simp] theorem heptagonalBipyramidNinePriorityPlacement?_explicit
    (priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7 priority8 :
      PolyhedralPriorityNumber) :
    heptagonalBipyramidNinePriorityPlacement?
        [priority0, priority1, priority2, priority3, priority4, priority5, priority6, priority7, priority8] =
      some (heptagonalBipyramidNinePriorityPlacement
        priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7 priority8) := rfl

@[simp] theorem heptagonalBipyramidNinePriorityPlacement_lookup
    (priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7 priority8 :
      PolyhedralPriorityNumber) (position : Fin 9) :
    [priority0, priority1, priority2, priority3, priority4, priority5, priority6, priority7, priority8][position.val]? =
      some (heptagonalBipyramidNinePriorityPlacement
        priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7 priority8 position) := by
  fin_cases position <;> rfl

theorem heptagonalBipyramidPositionValues_lookups
    (priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7 priority8 :
      PolyhedralPriorityNumber) (positions : List (Fin 9)) :
    (positions.map Fin.val).mapM
        (fun position =>
          [priority0, priority1, priority2, priority3, priority4, priority5,
            priority6, priority7, priority8][position]?) =
      some (positions.map (heptagonalBipyramidNinePriorityPlacement
        priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7 priority8)) := by
  induction positions with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      fin_cases head <;>
        simp [heptagonalBipyramidNinePriorityPlacement, inductionHypothesis]

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

theorem heptagonalBipyramidFlattenedPositionValues_eraseDups_length
    (partition : HeptagonalBipyramid9SpatialPerception.Partition)
    (member : partition ∈ HeptagonalBipyramid9SpatialPerception.partitions) :
    (((partition.axial.1 :: partition.axial.2 :: partition.equatorialCycle).map
        Fin.val).eraseDups.length) = 9 := by
  have positionNodup :=
    HeptagonalBipyramid9SpatialPerception.flattenedPositions_nodup_of_mem member
  have valuesNodup :
      ((partition.axial.1 :: partition.axial.2 :: partition.equatorialCycle).map
        Fin.val).Nodup :=
    positionNodup.map (by
      intro first second same
      exact Fin.ext same)
  rw [eraseDups_eq_self_of_nodup _ valuesNodup]
  simpa using
    HeptagonalBipyramid9SpatialPerception.flattenedPositions_length_of_mem member

structure IndexedHeptagonalBipyramid9SpatialObservation where
  center : ℕ
  ligands : List ℕ
  deriving DecidableEq, Repr

def SpatialConfiguration.heptagonalBipyramid9Frame?
    (spatial : SpatialConfiguration) (center : ℕ) (ligands : List ℕ) :
    Option HeptagonalBipyramid9SpatialPerception.Frame :=
  match ligands with
  | [donor0, donor1, donor2, donor3, donor4, donor5, donor6, donor7, donor8] => do
      let centerPoint ← spatial.positions[center]?
      let donorPoint0 ← spatial.positions[donor0]?
      let donorPoint1 ← spatial.positions[donor1]?
      let donorPoint2 ← spatial.positions[donor2]?
      let donorPoint3 ← spatial.positions[donor3]?
      let donorPoint4 ← spatial.positions[donor4]?
      let donorPoint5 ← spatial.positions[donor5]?
      let donorPoint6 ← spatial.positions[donor6]?
      let donorPoint7 ← spatial.positions[donor7]?
      let donorPoint8 ← spatial.positions[donor8]?
      some
        { center := centerPoint
          donor0 := donorPoint0
          donor1 := donorPoint1
          donor2 := donorPoint2
          donor3 := donorPoint3
          donor4 := donorPoint4
          donor5 := donorPoint5
          donor6 := donorPoint6
          donor7 := donorPoint7
          donor8 := donorPoint8 }
  | _ => none

namespace IndexedHeptagonalBipyramid9SpatialObservation

def withDerivedData (record : IndexedHeptagonalBipyramid9SpatialObservation)
    (partition : HeptagonalBipyramid9SpatialPerception.Partition)
    (sense : PolyhedralRotationSense) : IndexedPolyhedralGeometryObservation :=
  { center := record.center
    geometry := .heptagonalBipyramid
    recognition := .higherCoordinationNearestIdealized .heptagonalBipyramid
    ligands := record.ligands
    configurationPositions := .heptagonalBipyramid
      partition.axial.1.val partition.axial.2.val
      (partition.equatorialCycle.map Fin.val)
    absoluteOrientation := .heptagonalBipyramidAC
      (BlueBookP93.rotationOfProduction sense) }

def derivedRecord? (record : IndexedHeptagonalBipyramid9SpatialObservation)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration) :
    Option IndexedPolyhedralGeometryObservation := do
  let frame ← spatial.heptagonalBipyramid9Frame? record.center record.ligands
  let partition ← HeptagonalBipyramid9SpatialPerception.perceive? frame
  let priorities ← result.molecularPolyhedralPriorityNumbers?
    record.center .heptagonalBipyramid record.ligands
  let placement ← heptagonalBipyramidNinePriorityPlacement? priorities
  let sense ← HeptagonalBipyramid9SpatialOrientation.rotationSense?
    frame partition placement
  some (record.withDerivedData partition sense)

end IndexedHeptagonalBipyramid9SpatialObservation

def HeptagonalBipyramid9DerivedRecordJudgment
    (record : IndexedHeptagonalBipyramid9SpatialObservation)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (derived : IndexedPolyhedralGeometryObservation) : Prop :=
  ∃ frame partition priorities placement sense,
    spatial.heptagonalBipyramid9Frame? record.center record.ligands = some frame ∧
    HeptagonalBipyramid9SpatialPerception.Judgment frame partition ∧
    result.molecularPolyhedralPriorityNumbers?
      record.center .heptagonalBipyramid record.ligands = some priorities ∧
    heptagonalBipyramidNinePriorityPlacement? priorities = some placement ∧
    HeptagonalBipyramid9SpatialOrientation.Judgment frame partition placement sense ∧
    derived = record.withDerivedData partition sense

theorem IndexedHeptagonalBipyramid9SpatialObservation.derivedRecord?_eq_some_iff
    (record : IndexedHeptagonalBipyramid9SpatialObservation)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (derived : IndexedPolyhedralGeometryObservation) :
    record.derivedRecord? result spatial = some derived ↔
      HeptagonalBipyramid9DerivedRecordJudgment record result spatial derived := by
  constructor
  · intro computed
    unfold IndexedHeptagonalBipyramid9SpatialObservation.derivedRecord? at computed
    cases frameEq : spatial.heptagonalBipyramid9Frame? record.center record.ligands with
    | none => simp [frameEq] at computed
    | some frame =>
        cases partitionEq : HeptagonalBipyramid9SpatialPerception.perceive? frame with
        | none => simp [frameEq, partitionEq] at computed
        | some partition =>
            cases priorityEq : result.molecularPolyhedralPriorityNumbers?
                record.center .heptagonalBipyramid record.ligands with
            | none => simp [frameEq, priorityEq] at computed
            | some priorities =>
                cases placementEq : heptagonalBipyramidNinePriorityPlacement? priorities with
                | none => simp [frameEq, priorityEq, placementEq] at computed
                | some placement =>
                    cases senseEq : HeptagonalBipyramid9SpatialOrientation.rotationSense?
                        frame partition placement with
                    | none =>
                        simp [frameEq, partitionEq, priorityEq, placementEq, senseEq] at computed
                    | some sense =>
                        have derivedEq : derived = record.withDerivedData partition sense := by
                          simpa [frameEq, partitionEq, priorityEq, placementEq, senseEq]
                            using computed.symm
                        exact ⟨frame, partition, priorities, placement, sense, frameEq,
                          (HeptagonalBipyramid9SpatialPerception.perceive?_eq_some_iff
                            frame partition).mp partitionEq,
                          priorityEq, placementEq,
                          (HeptagonalBipyramid9SpatialOrientation.rotationSense?_eq_some_iff
                            frame partition placement sense).mp senseEq,
                          derivedEq⟩
  · rintro ⟨frame, partition, priorities, placement, sense, frameEq, perceived,
      priorityEq, placementEq, orientation, rfl⟩
    have partitionEq : HeptagonalBipyramid9SpatialPerception.perceive? frame = some partition :=
      (HeptagonalBipyramid9SpatialPerception.perceive?_eq_some_iff
        frame partition).mpr perceived
    have senseEq : HeptagonalBipyramid9SpatialOrientation.rotationSense?
        frame partition placement = some sense :=
      (HeptagonalBipyramid9SpatialOrientation.rotationSense?_eq_some_iff
        frame partition placement sense).mpr orientation
    simp [IndexedHeptagonalBipyramid9SpatialObservation.derivedRecord?, frameEq, partitionEq,
      priorityEq, placementEq, senseEq]

def ChemistryNormalizationResult.heptagonalBipyramid9SpatialAssignment?
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedHeptagonalBipyramid9SpatialObservation) : Option StereoAssignment := do
  let derived ← record.derivedRecord? result spatial
  result.polyhedralGeometryObservationAssignment? derived

def HeptagonalBipyramid9SpatialAssignmentJudgment
    (record : IndexedHeptagonalBipyramid9SpatialObservation)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (assignment : StereoAssignment) : Prop :=
  ∃ derived,
    HeptagonalBipyramid9DerivedRecordJudgment record result spatial derived ∧
      result.polyhedralGeometryObservationAssignment? derived = some assignment

theorem ChemistryNormalizationResult.heptagonalBipyramid9SpatialAssignment?_eq_some_iff
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedHeptagonalBipyramid9SpatialObservation) (assignment : StereoAssignment) :
    result.heptagonalBipyramid9SpatialAssignment? spatial record = some assignment ↔
      HeptagonalBipyramid9SpatialAssignmentJudgment record result spatial assignment := by
  unfold ChemistryNormalizationResult.heptagonalBipyramid9SpatialAssignment?
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

theorem ChemistryNormalizationResult.heptagonalBipyramid9SpatialAssignment?_eq_none_iff
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedHeptagonalBipyramid9SpatialObservation) :
    result.heptagonalBipyramid9SpatialAssignment? spatial record = none ↔
      ¬ ∃ assignment,
        HeptagonalBipyramid9SpatialAssignmentJudgment record result spatial assignment := by
  constructor
  · intro absent ⟨assignment, judged⟩
    have present :=
      (result.heptagonalBipyramid9SpatialAssignment?_eq_some_iff
        spatial record assignment).mpr judged
    rw [absent] at present
    contradiction
  · intro noJudgment
    cases computed : result.heptagonalBipyramid9SpatialAssignment? spatial record with
    | none => rfl
    | some assignment =>
        exact False.elim (noJudgment ⟨assignment,
          (result.heptagonalBipyramid9SpatialAssignment?_eq_some_iff
            spatial record assignment).mp computed⟩)

/-- Exact final molecule/coordinate HBPY-9 descriptor. -/
theorem ChemistryNormalizationResult.heptagonalBipyramid9Spatial_exact
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (center : ℕ) (ligands : List ℕ)
    (frame : HeptagonalBipyramid9SpatialPerception.Frame)
    (partition : HeptagonalBipyramid9SpatialPerception.Partition)
    (priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7 priority8 :
      PolyhedralPriorityNumber) (sense : PolyhedralRotationSense)
    (frameEq : spatial.heptagonalBipyramid9Frame? center ligands = some frame)
    (perceived : HeptagonalBipyramid9SpatialPerception.Judgment frame partition)
    (priorityEq : result.molecularPolyhedralPriorityNumbers?
      center .heptagonalBipyramid ligands =
        some [priority0, priority1, priority2, priority3, priority4, priority5, priority6, priority7, priority8])
    (prioritiesDistinct :
      [priority0, priority1, priority2, priority3, priority4, priority5,
        priority6, priority7, priority8].eraseDups.length = 9)
    (orientation : HeptagonalBipyramid9SpatialOrientation.Judgment frame partition
      (heptagonalBipyramidNinePriorityPlacement
        priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7 priority8) sense) :
    result.heptagonalBipyramid9SpatialAssignment? spatial
        { center := center, ligands := ligands } =
      some
        { unit := StereoUnit.polyhedron center
          outcome := StereoOutcome.polyhedral
            { geometry := .heptagonalBipyramid
              configurationIndex := bipyramidalConfigurationIndex
                (heptagonalBipyramidNinePriorityPlacement
                  priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7 priority8
                  partition.axial.1)
                (heptagonalBipyramidNinePriorityPlacement
                  priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7 priority8
                  partition.axial.2)
                (partition.equatorialCycle.map
                  (heptagonalBipyramidNinePriorityPlacement
                    priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7 priority8))
              absolute? := some (.ac (PolyhedralChiralitySymbol.ofRotation sense)) } } := by
  let placement := heptagonalBipyramidNinePriorityPlacement
    priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7 priority8
  have partitionEq : HeptagonalBipyramid9SpatialPerception.perceive? frame = some partition :=
    (HeptagonalBipyramid9SpatialPerception.perceive?_eq_some_iff
      frame partition).mpr perceived
  have senseEq : HeptagonalBipyramid9SpatialOrientation.rotationSense?
      frame partition placement = some sense :=
    (HeptagonalBipyramid9SpatialOrientation.rotationSense?_eq_some_iff
      frame partition placement sense).mpr orientation
  have derivedEq :
      ({ center := center, ligands := ligands } :
        IndexedHeptagonalBipyramid9SpatialObservation).derivedRecord? result spatial =
        some (({ center := center, ligands := ligands } :
          IndexedHeptagonalBipyramid9SpatialObservation).withDerivedData partition sense) := by
    simp [IndexedHeptagonalBipyramid9SpatialObservation.derivedRecord?, frameEq, partitionEq,
      priorityEq, heptagonalBipyramidNinePriorityPlacement?_explicit, placement, senseEq]
  have positionsDistinct :=
    heptagonalBipyramidFlattenedPositionValues_eraseDups_length partition perceived.1
  have cycleLength :=
    HeptagonalBipyramid9SpatialPerception.equatorialCycle_length_of_mem perceived.1
  have lookups := heptagonalBipyramidPositionValues_lookups
    priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7 priority8
    (partition.axial.1 :: partition.axial.2 :: partition.equatorialCycle)
  have downstream := bipyramidalGeometryObservationAssignment_exact result .heptagonal9
    center ligands sense
    [priority0, priority1, priority2, priority3, priority4, priority5, priority6, priority7, priority8]
    partition.axial.1.val partition.axial.2.val
    (partition.equatorialCycle.map Fin.val)
    (placement partition.axial.1) (placement partition.axial.2)
    (partition.equatorialCycle.map placement)
    priorityEq prioritiesDistinct
    (by simpa [RedBookIR9.BipyramidKind.positions,
      RedBookIR9.BipyramidKind.configurationArity] using
        HeptagonalBipyramid9SpatialPerception.flattenedPositions_length_of_mem perceived.1)
    (by simpa [RedBookIR9.BipyramidKind.positions, cycleLength] using positionsDistinct)
    (by simpa [RedBookIR9.BipyramidKind.positions,
      RedBookIR9.BipyramidKind.entries] using lookups)
  simpa [ChemistryNormalizationResult.heptagonalBipyramid9SpatialAssignment?, derivedEq,
    IndexedHeptagonalBipyramid9SpatialObservation.withDerivedData, placement] using downstream

/-- Constructive exact-domain completeness for strict idealized HBPY-9. -/
theorem ChemistryNormalizationResult.heptagonalBipyramid9Spatial_exists_exact
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (center : ℕ) (ligands : List ℕ)
    (frame : HeptagonalBipyramid9SpatialPerception.Frame)
    (partition : HeptagonalBipyramid9SpatialPerception.Partition)
    (priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7 priority8 :
      PolyhedralPriorityNumber)
    (axialOrder : Fin 9 × Fin 9) (senior : Fin 7)
    (direction : HeptagonalBipyramid9SpatialOrientation.CycleDirection)
    (frameEq : spatial.heptagonalBipyramid9Frame? center ligands = some frame)
    (perceived : HeptagonalBipyramid9SpatialPerception.Judgment frame partition)
    (priorityEq : result.molecularPolyhedralPriorityNumbers?
      center .heptagonalBipyramid ligands =
        some [priority0, priority1, priority2, priority3, priority4, priority5, priority6, priority7, priority8])
    (prioritiesDistinct :
      [priority0, priority1, priority2, priority3, priority4, priority5,
        priority6, priority7, priority8].eraseDups.length = 9)
    (axialOrdered : HeptagonalBipyramid9SpatialOrientation.IsStrictAxialOrder
      (heptagonalBipyramidNinePriorityPlacement
        priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7 priority8)
      partition.axial axialOrder)
    (seniority : HeptagonalBipyramid9SpatialOrientation.IsStrictSenior7
      (HeptagonalBipyramid9SpatialOrientation.cyclePlacement
        (heptagonalBipyramidNinePriorityPlacement
          priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7 priority8) partition)
      senior)
    (directionPreferred : HeptagonalBipyramid9SpatialOrientation.IsPreferredCycleDirection
      (HeptagonalBipyramid9SpatialOrientation.cyclePlacement
        (heptagonalBipyramidNinePriorityPlacement
          priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7 priority8) partition)
      senior direction) :
    ∃ sense,
      result.heptagonalBipyramid9SpatialAssignment? spatial
          { center := center, ligands := ligands } =
        some
          { unit := StereoUnit.polyhedron center
            outcome := StereoOutcome.polyhedral
              { geometry := .heptagonalBipyramid
                configurationIndex := bipyramidalConfigurationIndex
                  (heptagonalBipyramidNinePriorityPlacement
                    priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7 priority8
                    partition.axial.1)
                  (heptagonalBipyramidNinePriorityPlacement
                    priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7 priority8
                    partition.axial.2)
                  (partition.equatorialCycle.map
                    (heptagonalBipyramidNinePriorityPlacement
                      priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7 priority8))
                absolute? := some (.ac (PolyhedralChiralitySymbol.ofRotation sense)) } } := by
  let placement := heptagonalBipyramidNinePriorityPlacement
    priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7 priority8
  obtain ⟨sense, _senseEq, orientation⟩ :=
    HeptagonalBipyramid9SpatialOrientation.rotationSense?_exists_of_exactGeometry
      frame partition placement perceived axialOrder senior direction
      axialOrdered seniority directionPreferred
  exact ⟨sense, result.heptagonalBipyramid9Spatial_exact spatial center ligands frame partition
    priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7 priority8 sense frameEq perceived
    priorityEq prioritiesDistinct orientation⟩

end TetraStereo.OneCenter
