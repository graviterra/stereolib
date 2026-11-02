import TetraStereo.OneCenter.CIPIR9GenericCoordinationSourceSchedule
import TetraStereo.OneCenter.IR9CubeSpatialOrbitCompleteness
import TetraStereo.OneCenter.GeometryAnnotatedCIPConformance

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace CubeExecutable

abbrev Frame := RedBookIR9.CubeSpatialPerception.Frame
abbrev Placement := RedBookIR9.CubeSpatialPerception.Placement
abbrev IsExactPlacement := RedBookIR9.CubeSpatialPerception.IsExactPlacement
noncomputable abbrev recognizedPlacements :=
  RedBookIR9.CubeSpatialPerception.recognizedPlacements

end CubeExecutable

namespace CubeSourceIndex

abbrev Position := RedBookIR9.CubeSourceIndexCompleteness.Position
abbrev PriorityDigit := RedBookIR9.CubeSourceIndexCompleteness.PriorityDigit
noncomputable abbrev completeIndex :=
  RedBookIR9.CubeSourceIndexCompleteness.cubeCompleteConfigurationIndex

end CubeSourceIndex

/-!
# Molecular CU-8 mathematical-index integration

This module composes the canonical coordination-eight molecular schedule, exact coordinate lookup,
strict ideal-cube perception, molecularly derived IR-9.3.5 priority numbers, and the complete
48-frame CU-8 mathematical symmetry index.  The spatial-orbit theorem proves that every admitted
role placement has the same index, so the result is single-valued without choosing an arbitrary
coordinate ordering.

The emitted word remains explicitly a complete mathematical symmetry index.  The transcribed
source contains neither a CU-8 short-index recipe nor a cube-specific `A`/`C` convention, and this
module does not attribute either to IUPAC.
-/

/-! ## Exact coordinate ingress -/

/-- Look up one canonical coordination-eight source record as an unordered exact cube frame. -/
def SpatialConfiguration.cubeFrame?
    (spatial : SpatialConfiguration) (record : IndexedIR9CoordinationSourceRecord) :
    Option CubeExecutable.Frame :=
  if record.coordinationNumber = 8 then
    match record.ligands with
    | [donor0, donor1, donor2, donor3, donor4, donor5, donor6, donor7] => do
        let centerPoint ← spatial.positions[record.center]?
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
  else none

/-- Declarative meaning of successful CU-8 coordinate ingress. -/
def CubeFrameJudgment
    (spatial : SpatialConfiguration) (record : IndexedIR9CoordinationSourceRecord)
    (frame : CubeExecutable.Frame) : Prop :=
  ∃ donor0 donor1 donor2 donor3 donor4 donor5 donor6 donor7,
    record.coordinationNumber = 8 ∧
    record.ligands = [donor0, donor1, donor2, donor3, donor4, donor5, donor6, donor7] ∧
    spatial.positions[record.center]? = some frame.center ∧
    spatial.positions[donor0]? = some frame.donor0 ∧
    spatial.positions[donor1]? = some frame.donor1 ∧
    spatial.positions[donor2]? = some frame.donor2 ∧
    spatial.positions[donor3]? = some frame.donor3 ∧
    spatial.positions[donor4]? = some frame.donor4 ∧
    spatial.positions[donor5]? = some frame.donor5 ∧
    spatial.positions[donor6]? = some frame.donor6 ∧
    spatial.positions[donor7]? = some frame.donor7

theorem cubeFrame?_eq_some_iff
    (spatial : SpatialConfiguration) (record : IndexedIR9CoordinationSourceRecord)
    (frame : CubeExecutable.Frame) :
    spatial.cubeFrame? record = some frame ↔ CubeFrameJudgment spatial record frame := by
  rcases record with ⟨coordinationNumber, center, ligands⟩
  simp only [SpatialConfiguration.cubeFrame?, CubeFrameJudgment]
  by_cases coordination : coordinationNumber = 8
  · simp only [coordination, if_pos, true_and]
    rcases ligands with _ | ⟨donor0, ligands⟩
    · simp
    rcases ligands with _ | ⟨donor1, ligands⟩
    · simp
    rcases ligands with _ | ⟨donor2, ligands⟩
    · simp
    rcases ligands with _ | ⟨donor3, ligands⟩
    · simp
    rcases ligands with _ | ⟨donor4, ligands⟩
    · simp
    rcases ligands with _ | ⟨donor5, ligands⟩
    · simp
    rcases ligands with _ | ⟨donor6, ligands⟩
    · simp
    rcases ligands with _ | ⟨donor7, ligands⟩
    · simp
    rcases ligands with _ | ⟨extra, tail⟩
    · cases centerEq : spatial.positions[center]? with
      | none => simp
      | some centerPoint =>
          cases donorEq0 : spatial.positions[donor0]? with
          | none => simp [donorEq0]
          | some donorPoint0 =>
              cases donorEq1 : spatial.positions[donor1]? with
              | none => simp [donorEq0, donorEq1]
              | some donorPoint1 =>
                  cases donorEq2 : spatial.positions[donor2]? with
                  | none => simp [donorEq0, donorEq1, donorEq2]
                  | some donorPoint2 =>
                      cases donorEq3 : spatial.positions[donor3]? with
                      | none => simp [donorEq0, donorEq1, donorEq2, donorEq3]
                      | some donorPoint3 =>
                          cases donorEq4 : spatial.positions[donor4]? with
                          | none =>
                              simp [donorEq0, donorEq1, donorEq2, donorEq3,
                                donorEq4]
                          | some donorPoint4 =>
                              cases donorEq5 : spatial.positions[donor5]? with
                              | none =>
                                  simp [donorEq0, donorEq1, donorEq2, donorEq3,
                                    donorEq4, donorEq5]
                              | some donorPoint5 =>
                                  cases donorEq6 : spatial.positions[donor6]? with
                                  | none =>
                                      simp [donorEq0, donorEq1, donorEq2, donorEq3,
                                        donorEq4, donorEq5, donorEq6]
                                  | some donorPoint6 =>
                                      cases donorEq7 : spatial.positions[donor7]? with
                                      | none =>
                                          simp [donorEq0, donorEq1, donorEq2,
                                            donorEq3, donorEq4, donorEq5, donorEq6, donorEq7]
                                      | some donorPoint7 =>
                                          rcases frame with
                                            ⟨frameCenter, frameDonor0, frameDonor1,
                                              frameDonor2, frameDonor3, frameDonor4,
                                              frameDonor5, frameDonor6, frameDonor7⟩
                                          simp [donorEq0, donorEq1, donorEq2,
                                            donorEq3, donorEq4, donorEq5, donorEq6, donorEq7]
    · simp
  · simp [coordination]

/-! ## Exact eight-priority ingress -/

def cubeEightPriorityPlacement
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

def cubeEightPriorityPlacement?
    (priorities : List PolyhedralPriorityNumber) :
    Option (Fin 8 → PolyhedralPriorityNumber) :=
  match priorities with
  | [priority0, priority1, priority2, priority3, priority4, priority5, priority6, priority7] =>
      some (cubeEightPriorityPlacement
        priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7)
  | _ => none

def CubeEightPriorityPlacementJudgment
    (priorities : List PolyhedralPriorityNumber)
    (placement : Fin 8 → PolyhedralPriorityNumber) : Prop :=
  ∃ priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7,
    priorities =
      [priority0, priority1, priority2, priority3, priority4, priority5, priority6, priority7] ∧
    placement = cubeEightPriorityPlacement
      priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7

theorem cubeEightPriorityPlacement?_eq_some_iff
    (priorities : List PolyhedralPriorityNumber)
    (placement : Fin 8 → PolyhedralPriorityNumber) :
    cubeEightPriorityPlacement? priorities = some placement ↔
      CubeEightPriorityPlacementJudgment priorities placement := by
  simp only [CubeEightPriorityPlacementJudgment]
  rcases priorities with _ | ⟨priority0, priorities⟩
  · simp [cubeEightPriorityPlacement?]
  rcases priorities with _ | ⟨priority1, priorities⟩
  · simp [cubeEightPriorityPlacement?]
  rcases priorities with _ | ⟨priority2, priorities⟩
  · simp [cubeEightPriorityPlacement?]
  rcases priorities with _ | ⟨priority3, priorities⟩
  · simp [cubeEightPriorityPlacement?]
  rcases priorities with _ | ⟨priority4, priorities⟩
  · simp [cubeEightPriorityPlacement?]
  rcases priorities with _ | ⟨priority5, priorities⟩
  · simp [cubeEightPriorityPlacement?]
  rcases priorities with _ | ⟨priority6, priorities⟩
  · simp [cubeEightPriorityPlacement?]
  rcases priorities with _ | ⟨priority7, priorities⟩
  · simp [cubeEightPriorityPlacement?]
  rcases priorities with _ | ⟨extra, tail⟩
  · simp [cubeEightPriorityPlacement?, eq_comm]
  · simp [cubeEightPriorityPlacement?]

/-! ## Exact candidates and automatic orbit coherence -/

structure CubeMathematicalIndexCandidate where
  placement : CubeExecutable.Placement
  index : List CubeSourceIndex.PriorityDigit
  deriving DecidableEq

/-- Complete CU-8 mathematical index for one admitted role placement. -/
noncomputable def cubeMathematicalIndexCandidateOf
    (priorityPlacement : Fin 8 → PolyhedralPriorityNumber)
    (placement : CubeExecutable.Placement) : CubeMathematicalIndexCandidate :=
  { placement := placement
    index := CubeSourceIndex.completeIndex fun position =>
      priorityPlacement (placement position) }

/-- Every exact role placement retained with its complete mathematical index. -/
noncomputable def IndexedIR9CoordinationSourceRecord.cubeMathematicalIndexCandidates
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration) :
    List CubeMathematicalIndexCandidate :=
  match spatial.cubeFrame? record with
  | none => []
  | some frame =>
      match result.molecularPolyhedralPriorityNumbers? record.center .cube record.ligands with
      | none => []
      | some priorities =>
          match cubeEightPriorityPlacement? priorities with
          | none => []
          | some priorityPlacement =>
              (CubeExecutable.recognizedPlacements frame).map
                (cubeMathematicalIndexCandidateOf priorityPlacement)

/-- Independent conjunction defining exactly one admitted molecular CU-8 candidate. -/
def CubeMathematicalIndexCandidateJudgment
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (candidate : CubeMathematicalIndexCandidate) : Prop :=
  ∃ frame priorities priorityPlacement placement,
    CubeFrameJudgment spatial record frame ∧
    result.molecularPolyhedralPriorityNumbers? record.center .cube record.ligands =
      some priorities ∧
    CubeEightPriorityPlacementJudgment priorities priorityPlacement ∧
    CubeExecutable.IsExactPlacement frame placement ∧
    candidate = cubeMathematicalIndexCandidateOf priorityPlacement placement

theorem mem_cubeMathematicalIndexCandidates_iff
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (candidate : CubeMathematicalIndexCandidate) :
    candidate ∈ record.cubeMathematicalIndexCandidates result spatial ↔
      CubeMathematicalIndexCandidateJudgment record result spatial candidate := by
  constructor
  · intro present
    unfold IndexedIR9CoordinationSourceRecord.cubeMathematicalIndexCandidates at present
    cases frameEq : spatial.cubeFrame? record with
    | none => simp [frameEq] at present
    | some frame =>
        cases priorityEq : result.molecularPolyhedralPriorityNumbers?
            record.center .cube record.ligands with
        | none => simp [frameEq, priorityEq] at present
        | some priorities =>
            cases placementEq : cubeEightPriorityPlacement? priorities with
            | none => simp [frameEq, priorityEq, placementEq] at present
            | some priorityPlacement =>
                simp only [frameEq, priorityEq, placementEq] at present
                rcases List.mem_map.mp present with ⟨placement, placementPresent, rfl⟩
                exact ⟨frame, priorities, priorityPlacement, placement,
                  (cubeFrame?_eq_some_iff spatial record frame).mp frameEq,
                  priorityEq,
                  (cubeEightPriorityPlacement?_eq_some_iff priorities priorityPlacement).mp
                    placementEq,
                  (RedBookIR9.CubeSpatialPerception.mem_recognizedPlacements_iff
                    frame placement).mp placementPresent,
                  rfl⟩
  · rintro ⟨frame, priorities, priorityPlacement, placement, frameJudged,
      priorityEq, placementJudged, geometryJudged, rfl⟩
    have frameEq := (cubeFrame?_eq_some_iff spatial record frame).mpr frameJudged
    have placementEq :=
      (cubeEightPriorityPlacement?_eq_some_iff priorities priorityPlacement).mpr
        placementJudged
    unfold IndexedIR9CoordinationSourceRecord.cubeMathematicalIndexCandidates
    simp only [frameEq, priorityEq, placementEq]
    exact List.mem_map.mpr ⟨placement,
      (RedBookIR9.CubeSpatialPerception.mem_recognizedPlacements_iff
        frame placement).mpr geometryJudged, rfl⟩

theorem cubeMathematicalIndexCandidates_nodup
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration) :
    (record.cubeMathematicalIndexCandidates result spatial).Nodup := by
  unfold IndexedIR9CoordinationSourceRecord.cubeMathematicalIndexCandidates
  cases frameEq : spatial.cubeFrame? record with
  | none => simp
  | some frame =>
      cases priorityEq : result.molecularPolyhedralPriorityNumbers?
          record.center .cube record.ligands with
      | none => simp
      | some priorities =>
          cases placementEq : cubeEightPriorityPlacement? priorities with
          | none => simp [placementEq]
          | some priorityPlacement =>
              simp only [placementEq]
              apply List.Nodup.map
              · intro left right same
                exact congrArg CubeMathematicalIndexCandidate.placement same
              · exact RedBookIR9.CubeSpatialPerception.recognizedPlacements_nodup frame

theorem cubeMathematicalIndexCandidates_nonempty_iff
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration) :
    record.cubeMathematicalIndexCandidates result spatial ≠ [] ↔
      ∃ candidate, CubeMathematicalIndexCandidateJudgment
        record result spatial candidate := by
  constructor
  · intro nonempty
    obtain ⟨candidate, present⟩ := List.exists_mem_of_ne_nil _ nonempty
    exact ⟨candidate,
      (mem_cubeMathematicalIndexCandidates_iff record result spatial candidate).mp present⟩
  · rintro ⟨candidate, judged⟩ equal
    have present :=
      (mem_cubeMathematicalIndexCandidates_iff record result spatial candidate).mpr judged
    simp [equal] at present

/-- Exhaustive semantic refusal: no complete coordinate/priority/placement candidate exists. -/
def CubeMathematicalIndexRefused
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration) : Prop :=
  ∀ candidate, ¬ CubeMathematicalIndexCandidateJudgment record result spatial candidate

theorem cubeMathematicalIndexCandidates_eq_nil_iff_refused
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration) :
    record.cubeMathematicalIndexCandidates result spatial = [] ↔
      CubeMathematicalIndexRefused record result spatial := by
  constructor
  · intro equal candidate judged
    have present :=
      (mem_cubeMathematicalIndexCandidates_iff record result spatial candidate).mpr judged
    simp [equal] at present
  · intro refused
    by_contra nonempty
    rcases (cubeMathematicalIndexCandidates_nonempty_iff record result spatial).mp nonempty with
      ⟨candidate, judged⟩
    exact refused candidate judged

/-- Evaluation-order-independent names for the four exhaustive operational failure stages. -/
def CubeMathematicalIndexOperationalRefusal
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration) : Prop :=
  spatial.cubeFrame? record = none ∨
    ∃ frame, spatial.cubeFrame? record = some frame ∧
      (result.molecularPolyhedralPriorityNumbers? record.center .cube record.ligands = none ∨
        ∃ priorities,
          result.molecularPolyhedralPriorityNumbers? record.center .cube record.ligands =
              some priorities ∧
          (cubeEightPriorityPlacement? priorities = none ∨
            ∃ priorityPlacement,
              cubeEightPriorityPlacement? priorities = some priorityPlacement ∧
              CubeExecutable.recognizedPlacements frame = []))

/-- Semantic refusal is exactly one of coordinate ingress failure, molecular priority failure,
eight-entry priority-placement failure, or absence of every exact cube role placement. -/
theorem cubeMathematicalIndexRefused_iff_operationalRefusal
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration) :
    CubeMathematicalIndexRefused record result spatial ↔
      CubeMathematicalIndexOperationalRefusal record result spatial := by
  rw [← cubeMathematicalIndexCandidates_eq_nil_iff_refused]
  unfold IndexedIR9CoordinationSourceRecord.cubeMathematicalIndexCandidates
  cases frameEq : spatial.cubeFrame? record with
  | none => simp [CubeMathematicalIndexOperationalRefusal, frameEq]
  | some frame =>
      cases priorityEq : result.molecularPolyhedralPriorityNumbers?
          record.center .cube record.ligands with
      | none =>
          simp [CubeMathematicalIndexOperationalRefusal, frameEq, priorityEq]
      | some priorities =>
          cases placementEq : cubeEightPriorityPlacement? priorities with
          | none =>
              simp [CubeMathematicalIndexOperationalRefusal, frameEq, priorityEq, placementEq]
          | some priorityPlacement =>
              simp [CubeMathematicalIndexOperationalRefusal, frameEq, priorityEq, placementEq]

/-- The CU-8 rigidity theorem makes every admitted candidate index identical. -/
theorem cubeMathematicalIndexCandidates_indices_eq
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (left right : CubeMathematicalIndexCandidate)
    (leftPresent : left ∈ record.cubeMathematicalIndexCandidates result spatial)
    (rightPresent : right ∈ record.cubeMathematicalIndexCandidates result spatial) :
    left.index = right.index := by
  rcases (mem_cubeMathematicalIndexCandidates_iff record result spatial left).mp leftPresent with
    ⟨leftFrame, leftPriorities, leftPriorityPlacement, leftPlacement,
      leftFrameJudged, leftPrioritiesEq, leftPriorityPlacementJudged,
      leftExact, leftEq⟩
  rcases (mem_cubeMathematicalIndexCandidates_iff record result spatial right).mp rightPresent with
    ⟨rightFrame, rightPriorities, rightPriorityPlacement, rightPlacement,
      rightFrameJudged, rightPrioritiesEq, rightPriorityPlacementJudged,
      rightExact, rightEq⟩
  have leftFrameEq : spatial.cubeFrame? record = some leftFrame :=
    (cubeFrame?_eq_some_iff spatial record leftFrame).mpr leftFrameJudged
  have rightFrameEq : spatial.cubeFrame? record = some rightFrame :=
    (cubeFrame?_eq_some_iff spatial record rightFrame).mpr rightFrameJudged
  have frameEq : leftFrame = rightFrame :=
    Option.some.inj (leftFrameEq.symm.trans rightFrameEq)
  have prioritiesEq : leftPriorities = rightPriorities :=
    Option.some.inj (leftPrioritiesEq.symm.trans rightPrioritiesEq)
  subst rightFrame
  subst rightPriorities
  have leftPriorityPlacementEq :
      cubeEightPriorityPlacement? leftPriorities = some leftPriorityPlacement :=
    (cubeEightPriorityPlacement?_eq_some_iff
      leftPriorities leftPriorityPlacement).mpr leftPriorityPlacementJudged
  have rightPriorityPlacementEq :
      cubeEightPriorityPlacement? leftPriorities = some rightPriorityPlacement :=
    (cubeEightPriorityPlacement?_eq_some_iff
      leftPriorities rightPriorityPlacement).mpr rightPriorityPlacementJudged
  have priorityPlacementEq : leftPriorityPlacement = rightPriorityPlacement :=
    Option.some.inj (leftPriorityPlacementEq.symm.trans rightPriorityPlacementEq)
  subst rightPriorityPlacement
  rw [leftEq, rightEq]
  exact RedBookIR9.CubeSpatialOrbitCompleteness.recognizedPlacements_priorityIndex_eq
    leftFrame leftPriorityPlacement leftPlacement rightPlacement
    ((RedBookIR9.CubeSpatialPerception.mem_recognizedPlacements_iff
      leftFrame leftPlacement).mpr leftExact)
    ((RedBookIR9.CubeSpatialPerception.mem_recognizedPlacements_iff
      leftFrame rightPlacement).mpr rightExact)

/-! ## Exact single-valued resolution -/

/-- Take the first complete word only after the orbit theorem has proved that every candidate word
is equal to it. -/
noncomputable def IndexedIR9CoordinationSourceRecord.cubeResolvedMathematicalIndex?
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration) :
    Option (List CubeSourceIndex.PriorityDigit) :=
  match record.cubeMathematicalIndexCandidates result spatial with
  | [] => none
  | first :: _ => some first.index

theorem cubeResolvedMathematicalIndex?_eq_some_iff
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (index : List CubeSourceIndex.PriorityDigit) :
    record.cubeResolvedMathematicalIndex? result spatial = some index ↔
      ∃ candidate,
        CubeMathematicalIndexCandidateJudgment record result spatial candidate ∧
        candidate.index = index := by
  cases candidatesEq : record.cubeMathematicalIndexCandidates result spatial with
  | nil =>
      constructor
      · intro impossible
        simp [IndexedIR9CoordinationSourceRecord.cubeResolvedMathematicalIndex?,
          candidatesEq] at impossible
      · rintro ⟨candidate, judged, _same⟩
        have present :=
          (mem_cubeMathematicalIndexCandidates_iff record result spatial candidate).mpr judged
        simp [candidatesEq] at present
  | cons first rest =>
      have firstPresent : first ∈ record.cubeMathematicalIndexCandidates result spatial := by
        simp [candidatesEq]
      constructor
      · intro computed
        refine ⟨first,
          (mem_cubeMathematicalIndexCandidates_iff record result spatial first).mp firstPresent,
          ?_⟩
        have reduced : some first.index = some index := by
          simpa [IndexedIR9CoordinationSourceRecord.cubeResolvedMathematicalIndex?,
            candidatesEq] using computed
        exact Option.some.inj reduced
      · rintro ⟨candidate, judged, candidateIndex⟩
        have candidatePresent :=
          (mem_cubeMathematicalIndexCandidates_iff record result spatial candidate).mpr judged
        have same := cubeMathematicalIndexCandidates_indices_eq
          record result spatial first candidate firstPresent candidatePresent
        simpa [IndexedIR9CoordinationSourceRecord.cubeResolvedMathematicalIndex?,
          candidatesEq] using congrArg some (same.trans candidateIndex)

theorem cubeResolvedMathematicalIndex?_eq_none_iff_refused
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration) :
    record.cubeResolvedMathematicalIndex? result spatial = none ↔
      CubeMathematicalIndexRefused record result spatial := by
  rw [← cubeMathematicalIndexCandidates_eq_nil_iff_refused]
  cases candidatesEq : record.cubeMathematicalIndexCandidates result spatial with
  | nil => simp [IndexedIR9CoordinationSourceRecord.cubeResolvedMathematicalIndex?, candidatesEq]
  | cons first rest =>
      simp [IndexedIR9CoordinationSourceRecord.cubeResolvedMathematicalIndex?, candidatesEq]

theorem cubeResolvedMathematicalIndex?_eq_none_iff_operationalRefusal
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration) :
    record.cubeResolvedMathematicalIndex? result spatial = none ↔
      CubeMathematicalIndexOperationalRefusal record result spatial := by
  rw [cubeResolvedMathematicalIndex?_eq_none_iff_refused,
    cubeMathematicalIndexRefused_iff_operationalRefusal]

/-- Every record has a unique resolved index or the explicit exhaustive refusal predicate. -/
theorem cubeMathematicalIndexResolution_exhaustive
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration) :
    (∃! index, record.cubeResolvedMathematicalIndex? result spatial = some index) ∨
      CubeMathematicalIndexRefused record result spatial := by
  by_cases refused : CubeMathematicalIndexRefused record result spatial
  · exact .inr refused
  · left
    have nonempty : record.cubeMathematicalIndexCandidates result spatial ≠ [] := by
      intro empty
      exact refused
        ((cubeMathematicalIndexCandidates_eq_nil_iff_refused
          record result spatial).mp empty)
    obtain ⟨candidate, present⟩ := List.exists_mem_of_ne_nil _ nonempty
    have judged :=
      (mem_cubeMathematicalIndexCandidates_iff record result spatial candidate).mp present
    have computed := (cubeResolvedMathematicalIndex?_eq_some_iff
      record result spatial candidate.index).mpr ⟨candidate, judged, rfl⟩
    refine ⟨candidate.index, computed, ?_⟩
    intro other otherComputed
    exact Option.some.inj (otherComputed.symm.trans computed)

/-! ## Molecular IR-9.3.5 priority provenance -/

def CubeMolecularIR9PriorityCertificate
    (result : ChemistryNormalizationResult) (record : IndexedIR9CoordinationSourceRecord)
    (priorities : List PolyhedralPriorityNumber) : Prop :=
  ∃ memberships,
    result.deriveRepeatedLigandPrimingMemberships?
        result.geometryPriorityState.1 result.geometryPriorityState.2.2
        record.center record.ligands = some memberships ∧
    result.repeatedLigandPrimingMembershipsOK?
        result.geometryPriorityState.1 result.geometryPriorityState.2.2
        record.center record.ligands memberships = true ∧
    ∃ compareAt baseNumbers primeCounts,
      result.polyhedralPriorityComparisonFrame? record.center .cube record.ligands =
        some compareAt ∧
      deriveDensePolyhedralBasePriorityNumbers? record.ligands.length compareAt =
        some baseNumbers ∧
      RedBookIR9.FinitePriorityNumbering record.ligands.length compareAt baseNumbers ∧
      canonicalPolyhedralPrimeCounts? record.ligands.length memberships = some primeCounts ∧
      RedBookIR9.FinitePrimingAssignment record.ligands.length
        (effectivePolyhedralPrimingMemberships record.ligands.length memberships) primeCounts ∧
      baseNumbers.zipWithM (fun number primes =>
        some { number := number, primes := primes }) primeCounts = some priorities

theorem cubeMathematicalIndexCandidate_has_IR9_priority_certificate
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (candidate : CubeMathematicalIndexCandidate)
    (present : candidate ∈ record.cubeMathematicalIndexCandidates result spatial) :
    ∃ frame priorities priorityPlacement placement,
      CubeFrameJudgment spatial record frame ∧
      CubeMolecularIR9PriorityCertificate result record priorities ∧
      CubeEightPriorityPlacementJudgment priorities priorityPlacement ∧
      CubeExecutable.IsExactPlacement frame placement ∧
      candidate = cubeMathematicalIndexCandidateOf priorityPlacement placement := by
  rcases (mem_cubeMathematicalIndexCandidates_iff
      record result spatial candidate).mp present with
    ⟨frame, priorities, priorityPlacement, placement, frameJudged, priorityEq,
      placementJudged, geometryJudged, candidateEq⟩
  refine ⟨frame, priorities, priorityPlacement, placement, frameJudged, ?_,
    placementJudged, geometryJudged, candidateEq⟩
  exact result.molecularPolyhedralPriorityNumbers?_sound_IR9
    record.center .cube record.ligands priorities priorityEq

end TetraStereo.OneCenter
