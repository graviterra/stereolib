import TetraStereo.OneCenter.IR9TrigonalPrism6SpatialOrientation
import TetraStereo.OneCenter.GeometryAnnotatedCIPConformance

set_option autoImplicit false

namespace TetraStereo.OneCenter

open RedBookIR9
open RedBookIR9.TrigonalPrism6SpatialPerception
open RedBookIR9.TrigonalPrism6SpatialOrientation

/-! # Public molecule/coordinate integration for exact TPR-6 -/

def trigonalPrismSixPriorityPlacement
    (priority0 priority1 priority2 priority3 priority4 priority5 :
      PolyhedralPriorityNumber) : Fin 6 → PolyhedralPriorityNumber
  | 0 => priority0
  | 1 => priority1
  | 2 => priority2
  | 3 => priority3
  | 4 => priority4
  | 5 => priority5

def trigonalPrismSixPriorityPlacement? (priorities : List PolyhedralPriorityNumber) :
    Option (Fin 6 → PolyhedralPriorityNumber) :=
  match priorities with
  | [priority0, priority1, priority2, priority3, priority4, priority5] =>
      some (trigonalPrismSixPriorityPlacement
        priority0 priority1 priority2 priority3 priority4 priority5)
  | _ => none

@[simp] theorem trigonalPrismSixPriorityPlacement?_explicit
    (priority0 priority1 priority2 priority3 priority4 priority5 :
      PolyhedralPriorityNumber) :
    trigonalPrismSixPriorityPlacement?
        [priority0, priority1, priority2, priority3, priority4, priority5] =
      some (trigonalPrismSixPriorityPlacement
        priority0 priority1 priority2 priority3 priority4 priority5) := rfl

@[simp] theorem trigonalPrismSixPriorityPlacement_lookup
    (priority0 priority1 priority2 priority3 priority4 priority5 :
      PolyhedralPriorityNumber) (position : Fin 6) :
    [priority0, priority1, priority2, priority3, priority4, priority5][position.val]? =
      some (trigonalPrismSixPriorityPlacement
        priority0 priority1 priority2 priority3 priority4 priority5 position) := by
  fin_cases position <;> rfl

def trigonalPrismFacePlacement
    (placement : Fin 6 → PolyhedralPriorityNumber)
    (face : TrigonalPrism6SpatialPerception.Face) : List PolyhedralPriorityNumber :=
  [placement face.position0, placement face.position1, placement face.position2]

theorem trigonalPrismFacePositionValues_lookups
    (priority0 priority1 priority2 priority3 priority4 priority5 :
      PolyhedralPriorityNumber)
    (face : TrigonalPrism6SpatialPerception.Face) :
    (face.positions.map Fin.val).mapM
        (fun position =>
          [priority0, priority1, priority2, priority3, priority4, priority5][position]?) =
      some (trigonalPrismFacePlacement
        (trigonalPrismSixPriorityPlacement
          priority0 priority1 priority2 priority3 priority4 priority5) face) := by
  simp [TrigonalPrism6SpatialPerception.Face.positions, trigonalPrismFacePlacement]
  constructor
  · generalize face.position0 = position
    fin_cases position <;> rfl
  constructor
  · generalize face.position1 = position
    fin_cases position <;> rfl
  · generalize face.position2 = position
    fin_cases position <;> rfl

theorem trigonalPrismCorrespondingFacePositionValues_lookups
    (priority0 priority1 priority2 priority3 priority4 priority5 :
      PolyhedralPriorityNumber)
    (faces : TrigonalPrism6SpatialPerception.CorrespondingFaces) :
    ((faces.first.positions ++ faces.second.positions).map Fin.val).mapM
        (fun position =>
          [priority0, priority1, priority2, priority3, priority4, priority5][position]?) =
      some
        (trigonalPrismFacePlacement
            (trigonalPrismSixPriorityPlacement
              priority0 priority1 priority2 priority3 priority4 priority5) faces.first ++
          trigonalPrismFacePlacement
            (trigonalPrismSixPriorityPlacement
              priority0 priority1 priority2 priority3 priority4 priority5) faces.second) := by
  rw [List.map_append, List.mapM_append,
    trigonalPrismFacePositionValues_lookups
      priority0 priority1 priority2 priority3 priority4 priority5 faces.first,
    trigonalPrismFacePositionValues_lookups
      priority0 priority1 priority2 priority3 priority4 priority5 faces.second]
  rfl

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

theorem trigonalPrismCorrespondingFacePositionValues_eraseDups_length
    (faces : TrigonalPrism6SpatialPerception.CorrespondingFaces)
    (nodup : (faces.first.positions ++ faces.second.positions).Nodup) :
    (((faces.first.positions ++ faces.second.positions).map Fin.val).eraseDups.length) = 6 := by
  have valuesNodup :
      ((faces.first.positions ++ faces.second.positions).map Fin.val).Nodup :=
    nodup.map (by
      intro first second same
      exact Fin.ext same)
  have originalLength :
      ((faces.first.positions ++ faces.second.positions).map Fin.val).length = 6 := by
    simp [TrigonalPrism6SpatialPerception.Face.positions]
  rw [eraseDups_eq_self_of_nodup _ valuesNodup]
  exact originalLength

structure IndexedTrigonalPrism6SpatialObservation where
  center : ℕ
  ligands : List ℕ
  deriving DecidableEq, Repr

def SpatialConfiguration.trigonalPrism6Frame?
    (spatial : SpatialConfiguration) (center : ℕ) (ligands : List ℕ) :
    Option TrigonalPrism6SpatialPerception.Frame :=
  match ligands with
  | [donor0, donor1, donor2, donor3, donor4, donor5] => do
      let centerPoint ← spatial.positions[center]?
      let donorPoint0 ← spatial.positions[donor0]?
      let donorPoint1 ← spatial.positions[donor1]?
      let donorPoint2 ← spatial.positions[donor2]?
      let donorPoint3 ← spatial.positions[donor3]?
      let donorPoint4 ← spatial.positions[donor4]?
      let donorPoint5 ← spatial.positions[donor5]?
      some
        { center := centerPoint
          donor0 := donorPoint0
          donor1 := donorPoint1
          donor2 := donorPoint2
          donor3 := donorPoint3
          donor4 := donorPoint4
          donor5 := donorPoint5 }
  | _ => none

namespace IndexedTrigonalPrism6SpatialObservation

def withDerivedData
    (record : IndexedTrigonalPrism6SpatialObservation)
    (faces : TrigonalPrism6SpatialPerception.CorrespondingFaces)
    (sense : PolyhedralRotationSense) : IndexedPolyhedralGeometryObservation :=
  { center := record.center
    geometry := .trigonalPrism
    recognition := .higherCoordinationNearestIdealized .trigonalPrism
    ligands := record.ligands
    configurationPositions := .trigonalPrism
      (faces.first.positions.map Fin.val) (faces.second.positions.map Fin.val)
    absoluteOrientation := .trigonalPrismAC (BlueBookP93.rotationOfProduction sense) }

def derivedRecord?
    (record : IndexedTrigonalPrism6SpatialObservation)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration) :
    Option IndexedPolyhedralGeometryObservation := do
  let frame ← spatial.trigonalPrism6Frame? record.center record.ligands
  let faces ← TrigonalPrism6SpatialPerception.perceive? frame
  let priorities ← result.molecularPolyhedralPriorityNumbers?
    record.center .trigonalPrism record.ligands
  let placement ← trigonalPrismSixPriorityPlacement? priorities
  let sense ← TrigonalPrism6SpatialOrientation.rotationSense? frame faces placement
  some (record.withDerivedData faces sense)

end IndexedTrigonalPrism6SpatialObservation

def TrigonalPrism6DerivedRecordJudgment
    (record : IndexedTrigonalPrism6SpatialObservation)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (derived : IndexedPolyhedralGeometryObservation) : Prop :=
  ∃ frame faces priorities placement sense,
    spatial.trigonalPrism6Frame? record.center record.ligands = some frame ∧
    TrigonalPrism6SpatialPerception.Judgment frame faces ∧
    result.molecularPolyhedralPriorityNumbers?
      record.center .trigonalPrism record.ligands = some priorities ∧
    trigonalPrismSixPriorityPlacement? priorities = some placement ∧
    TrigonalPrism6SpatialOrientation.Judgment frame faces placement sense ∧
    derived = record.withDerivedData faces sense

theorem IndexedTrigonalPrism6SpatialObservation.derivedRecord?_eq_some_iff
    (record : IndexedTrigonalPrism6SpatialObservation)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (derived : IndexedPolyhedralGeometryObservation) :
    record.derivedRecord? result spatial = some derived ↔
      TrigonalPrism6DerivedRecordJudgment record result spatial derived := by
  constructor
  · intro computed
    unfold IndexedTrigonalPrism6SpatialObservation.derivedRecord? at computed
    cases frameEq : spatial.trigonalPrism6Frame? record.center record.ligands with
    | none => simp [frameEq] at computed
    | some frame =>
        cases facesEq : TrigonalPrism6SpatialPerception.perceive? frame with
        | none => simp [frameEq, facesEq] at computed
        | some faces =>
            cases priorityEq : result.molecularPolyhedralPriorityNumbers?
                record.center .trigonalPrism record.ligands with
            | none => simp [frameEq, priorityEq] at computed
            | some priorities =>
                cases placementEq : trigonalPrismSixPriorityPlacement? priorities with
                | none => simp [frameEq, priorityEq, placementEq] at computed
                | some placement =>
                    cases senseEq : TrigonalPrism6SpatialOrientation.rotationSense?
                        frame faces placement with
                    | none =>
                        simp [frameEq, facesEq, priorityEq, placementEq, senseEq] at computed
                    | some sense =>
                        have derivedEq : derived = record.withDerivedData faces sense := by
                          simpa [frameEq, facesEq, priorityEq, placementEq, senseEq]
                            using computed.symm
                        exact ⟨frame, faces, priorities, placement, sense, frameEq,
                          (TrigonalPrism6SpatialPerception.perceive?_eq_some_iff
                            frame faces).mp facesEq,
                          priorityEq, placementEq,
                          (TrigonalPrism6SpatialOrientation.rotationSense?_eq_some_iff
                            frame faces placement sense).mp senseEq,
                          derivedEq⟩
  · rintro ⟨frame, faces, priorities, placement, sense, frameEq, perceived,
      priorityEq, placementEq, orientation, rfl⟩
    have facesEq : TrigonalPrism6SpatialPerception.perceive? frame = some faces :=
      (TrigonalPrism6SpatialPerception.perceive?_eq_some_iff frame faces).mpr perceived
    have senseEq : TrigonalPrism6SpatialOrientation.rotationSense?
        frame faces placement = some sense :=
      (TrigonalPrism6SpatialOrientation.rotationSense?_eq_some_iff
        frame faces placement sense).mpr orientation
    simp [IndexedTrigonalPrism6SpatialObservation.derivedRecord?, frameEq, facesEq,
      priorityEq, placementEq, senseEq]

def ChemistryNormalizationResult.trigonalPrism6SpatialAssignment?
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedTrigonalPrism6SpatialObservation) : Option StereoAssignment := do
  let derived ← record.derivedRecord? result spatial
  result.polyhedralGeometryObservationAssignment? derived

def TrigonalPrism6SpatialAssignmentJudgment
    (record : IndexedTrigonalPrism6SpatialObservation)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (assignment : StereoAssignment) : Prop :=
  ∃ derived,
    TrigonalPrism6DerivedRecordJudgment record result spatial derived ∧
      result.polyhedralGeometryObservationAssignment? derived = some assignment

theorem ChemistryNormalizationResult.trigonalPrism6SpatialAssignment?_eq_some_iff
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedTrigonalPrism6SpatialObservation) (assignment : StereoAssignment) :
    result.trigonalPrism6SpatialAssignment? spatial record = some assignment ↔
      TrigonalPrism6SpatialAssignmentJudgment record result spatial assignment := by
  unfold ChemistryNormalizationResult.trigonalPrism6SpatialAssignment?
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

theorem ChemistryNormalizationResult.trigonalPrism6SpatialAssignment?_eq_none_iff
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedTrigonalPrism6SpatialObservation) :
    result.trigonalPrism6SpatialAssignment? spatial record = none ↔
      ¬ ∃ assignment, TrigonalPrism6SpatialAssignmentJudgment
        record result spatial assignment := by
  constructor
  · intro absent ⟨assignment, judged⟩
    have present :=
      (result.trigonalPrism6SpatialAssignment?_eq_some_iff
        spatial record assignment).mpr judged
    rw [absent] at present
    contradiction
  · intro noJudgment
    cases computed : result.trigonalPrism6SpatialAssignment? spatial record with
    | none => rfl
    | some assignment =>
        exact False.elim (noJudgment ⟨assignment,
          (result.trigonalPrism6SpatialAssignment?_eq_some_iff
            spatial record assignment).mp computed⟩)

/-- Exact final molecule/coordinate TPR-6 descriptor. -/
theorem ChemistryNormalizationResult.trigonalPrism6Spatial_exact
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (center : ℕ) (ligands : List ℕ)
    (frame : TrigonalPrism6SpatialPerception.Frame)
    (faces : TrigonalPrism6SpatialPerception.CorrespondingFaces)
    (priority0 priority1 priority2 priority3 priority4 priority5 :
      PolyhedralPriorityNumber) (sense : PolyhedralRotationSense)
    (frameEq : spatial.trigonalPrism6Frame? center ligands = some frame)
    (perceived : TrigonalPrism6SpatialPerception.Judgment frame faces)
    (priorityEq : result.molecularPolyhedralPriorityNumbers?
      center .trigonalPrism ligands =
        some [priority0, priority1, priority2, priority3, priority4, priority5])
    (prioritiesDistinct :
      [priority0, priority1, priority2, priority3, priority4, priority5].eraseDups.length = 6)
    (orientation : TrigonalPrism6SpatialOrientation.Judgment frame faces
      (trigonalPrismSixPriorityPlacement
        priority0 priority1 priority2 priority3 priority4 priority5) sense) :
    result.trigonalPrism6SpatialAssignment? spatial { center := center, ligands := ligands } =
      some
        { unit := StereoUnit.polyhedron center
          outcome := StereoOutcome.polyhedral
            { geometry := .trigonalPrism
              configurationIndex :=
                [trigonalPrismConfigurationIndex
                  (trigonalPrismFacePlacement
                    (trigonalPrismSixPriorityPlacement
                      priority0 priority1 priority2 priority3 priority4 priority5) faces.first)
                  (trigonalPrismFacePlacement
                    (trigonalPrismSixPriorityPlacement
                      priority0 priority1 priority2 priority3 priority4 priority5) faces.second)]
              absolute? := some (.ac (PolyhedralChiralitySymbol.ofRotation sense)) } } := by
  let placement := trigonalPrismSixPriorityPlacement
    priority0 priority1 priority2 priority3 priority4 priority5
  have facesEq : TrigonalPrism6SpatialPerception.perceive? frame = some faces :=
    (TrigonalPrism6SpatialPerception.perceive?_eq_some_iff frame faces).mpr perceived
  have senseEq : TrigonalPrism6SpatialOrientation.rotationSense?
      frame faces placement = some sense :=
    (TrigonalPrism6SpatialOrientation.rotationSense?_eq_some_iff
      frame faces placement sense).mpr orientation
  have derivedEq :
      ({ center := center, ligands := ligands } :
        IndexedTrigonalPrism6SpatialObservation).derivedRecord? result spatial =
        some (({ center := center, ligands := ligands } :
          IndexedTrigonalPrism6SpatialObservation).withDerivedData faces sense) := by
    simp [IndexedTrigonalPrism6SpatialObservation.derivedRecord?, frameEq, facesEq,
      priorityEq, trigonalPrismSixPriorityPlacement?_explicit, placement, senseEq]
  have positionsDistinct :=
    trigonalPrismCorrespondingFacePositionValues_eraseDups_length faces
      (TrigonalPrism6SpatialPerception.flattenedPositions_nodup_of_judgment perceived)
  have lookups := trigonalPrismCorrespondingFacePositionValues_lookups
    priority0 priority1 priority2 priority3 priority4 priority5 faces
  have downstream := trigonalPrismGeometryObservationAssignment_exact result center ligands sense
    [priority0, priority1, priority2, priority3, priority4, priority5]
    faces.first.position0.val faces.first.position1.val faces.first.position2.val
    faces.second.position0.val faces.second.position1.val faces.second.position2.val
    (placement faces.first.position0) (placement faces.first.position1)
    (placement faces.first.position2) (placement faces.second.position0)
    (placement faces.second.position1) (placement faces.second.position2)
    priorityEq prioritiesDistinct positionsDistinct (by
      simpa [TrigonalPrism6SpatialPerception.Face.positions,
        trigonalPrismFacePlacement] using lookups)
  simpa [ChemistryNormalizationResult.trigonalPrism6SpatialAssignment?, derivedEq,
    IndexedTrigonalPrism6SpatialObservation.withDerivedData, placement,
    trigonalPrismFacePlacement] using downstream

/-- Exact-domain completeness: a perceived TPR-6 frame, a strict preferred-face/read-face
priority presentation, and nondegenerate exact prism geometry necessarily determine and emit one
P-93 A/C assignment.  The preferred face is the face containing the unique global senior ligand;
this is the distinct-priority specialization of the Red Book preferred-face convention used by
the public polyhedral analyzer. -/
theorem ChemistryNormalizationResult.trigonalPrism6Spatial_exists_exact
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (center : ℕ) (ligands : List ℕ)
    (frame : TrigonalPrism6SpatialPerception.Frame)
    (faces : TrigonalPrism6SpatialPerception.CorrespondingFaces)
    (priority0 priority1 priority2 priority3 priority4 priority5 :
      PolyhedralPriorityNumber)
    (choice : TrigonalPrism6SpatialOrientation.PreferredFaces)
    (senior : Fin 3) (remaining remainingOrder : Fin 3 × Fin 3)
    (frameEq : spatial.trigonalPrism6Frame? center ligands = some frame)
    (perceived : TrigonalPrism6SpatialPerception.Judgment frame faces)
    (priorityEq : result.molecularPolyhedralPriorityNumbers?
      center .trigonalPrism ligands =
        some [priority0, priority1, priority2, priority3, priority4, priority5])
    (prioritiesDistinct :
      [priority0, priority1, priority2, priority3, priority4, priority5].eraseDups.length = 6)
    (preferred : TrigonalPrism6SpatialOrientation.PreferredFacesJudgment faces
      (trigonalPrismSixPriorityPlacement
        priority0 priority1 priority2 priority3 priority4 priority5) choice)
    (seniority : TrigonalBipyramid5SpatialOrientation.IsStrictSenior3
      (TrigonalPrism6SpatialOrientation.facePlacement
        (trigonalPrismSixPriorityPlacement
          priority0 priority1 priority2 priority3 priority4 priority5) choice.read) senior)
    (remainingEq :
      TrigonalBipyramid5SpatialOrientation.remainingPair3? senior = some remaining)
    (ordered : TrigonalBipyramid5SpatialOrientation.IsStrictEquatorialOrder
      (TrigonalPrism6SpatialOrientation.facePlacement
        (trigonalPrismSixPriorityPlacement
          priority0 priority1 priority2 priority3 priority4 priority5) choice.read)
      remaining remainingOrder) :
    ∃ sense,
      result.trigonalPrism6SpatialAssignment? spatial
          { center := center, ligands := ligands } =
        some
          { unit := StereoUnit.polyhedron center
            outcome := StereoOutcome.polyhedral
              { geometry := .trigonalPrism
                configurationIndex :=
                  [trigonalPrismConfigurationIndex
                    (trigonalPrismFacePlacement
                      (trigonalPrismSixPriorityPlacement
                        priority0 priority1 priority2 priority3 priority4 priority5) faces.first)
                    (trigonalPrismFacePlacement
                      (trigonalPrismSixPriorityPlacement
                        priority0 priority1 priority2 priority3 priority4 priority5) faces.second)]
                absolute? := some (.ac (PolyhedralChiralitySymbol.ofRotation sense)) } } := by
  let placement := trigonalPrismSixPriorityPlacement
    priority0 priority1 priority2 priority3 priority4 priority5
  obtain ⟨sense, _senseEq, orientation⟩ :=
    TrigonalPrism6SpatialOrientation.rotationSense?_exists_of_exactGeometry
      frame faces placement perceived choice senior remaining remainingOrder
      preferred seniority remainingEq ordered
  exact ⟨sense, result.trigonalPrism6Spatial_exact spatial center ligands frame faces
    priority0 priority1 priority2 priority3 priority4 priority5 sense frameEq perceived
    priorityEq prioritiesDistinct orientation⟩

end TetraStereo.OneCenter
