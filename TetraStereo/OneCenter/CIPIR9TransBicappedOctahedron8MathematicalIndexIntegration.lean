import TetraStereo.OneCenter.CIPIR9GenericCoordinationSourceSchedule
import TetraStereo.OneCenter.IR9TransBicappedOctahedron8ExecutableSpatialPerception
import TetraStereo.OneCenter.GeometryAnnotatedCIPConformance

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace OCT8Executable

abbrev Frame :=
  RedBookIR9.TransBicappedOctahedron8ExecutableSpatialPerception.Frame
abbrev Placement :=
  RedBookIR9.TransBicappedOctahedron8ExecutableSpatialPerception.ExecutablePlacement
abbrev IsExactPlacement :=
  RedBookIR9.TransBicappedOctahedron8ExecutableSpatialPerception.IsExactExecutablePlacement
abbrev recognizedPlacements :=
  RedBookIR9.TransBicappedOctahedron8ExecutableSpatialPerception.recognizedExecutablePlacements
abbrev donorIndexAt :=
  RedBookIR9.TransBicappedOctahedron8ExecutableSpatialPerception.ExecutablePlacement.donorIndexAt

end OCT8Executable

namespace OCT8SourceIndex

abbrev Position :=
  RedBookIR9.TransBicappedOctahedron8SourceIndexCompleteness.Position
abbrev PriorityDigit :=
  RedBookIR9.TransBicappedOctahedron8SourceIndexCompleteness.PriorityDigit
noncomputable abbrev completeIndex :=
  RedBookIR9.TransBicappedOctahedron8SourceIndexCompleteness.transBicappedOctahedronCompleteConfigurationIndex

end OCT8SourceIndex



















/-! ## Exact coordinate ingress -/

/-- Look up an eight-coordinate source record as one unordered exact OCT-8 frame. -/
def SpatialConfiguration.transBicappedOctahedron8Frame?
    (spatial : SpatialConfiguration) (record : IndexedIR9CoordinationSourceRecord) :
    Option OCT8Executable.Frame :=
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

/-- Declarative meaning of successful coordinate ingress. -/
def TransBicappedOctahedron8FrameJudgment
    (spatial : SpatialConfiguration) (record : IndexedIR9CoordinationSourceRecord)
    (frame : OCT8Executable.Frame) : Prop :=
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

theorem transBicappedOctahedron8Frame?_eq_some_iff
    (spatial : SpatialConfiguration) (record : IndexedIR9CoordinationSourceRecord)
    (frame : OCT8Executable.Frame) :
    spatial.transBicappedOctahedron8Frame? record = some frame ↔
      TransBicappedOctahedron8FrameJudgment spatial record frame := by
  rcases record with ⟨coordinationNumber, center, ligands⟩
  simp only [SpatialConfiguration.transBicappedOctahedron8Frame?,
    TransBicappedOctahedron8FrameJudgment]
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

def eightPriorityPlacement
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

def eightPriorityPlacement?
    (priorities : List PolyhedralPriorityNumber) :
    Option (Fin 8 → PolyhedralPriorityNumber) :=
  match priorities with
  | [priority0, priority1, priority2, priority3, priority4, priority5, priority6, priority7] =>
      some (eightPriorityPlacement
        priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7)
  | _ => none

def EightPriorityPlacementJudgment
    (priorities : List PolyhedralPriorityNumber)
    (placement : Fin 8 → PolyhedralPriorityNumber) : Prop :=
  ∃ priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7,
    priorities =
      [priority0, priority1, priority2, priority3, priority4, priority5, priority6, priority7] ∧
    placement = eightPriorityPlacement
      priority0 priority1 priority2 priority3 priority4 priority5 priority6 priority7

theorem eightPriorityPlacement?_eq_some_iff
    (priorities : List PolyhedralPriorityNumber)
    (placement : Fin 8 → PolyhedralPriorityNumber) :
    eightPriorityPlacement? priorities = some placement ↔
      EightPriorityPlacementJudgment priorities placement := by
  simp only [EightPriorityPlacementJudgment]
  rcases priorities with _ | ⟨priority0, priorities⟩
  · simp [eightPriorityPlacement?]
  rcases priorities with _ | ⟨priority1, priorities⟩
  · simp [eightPriorityPlacement?]
  rcases priorities with _ | ⟨priority2, priorities⟩
  · simp [eightPriorityPlacement?]
  rcases priorities with _ | ⟨priority3, priorities⟩
  · simp [eightPriorityPlacement?]
  rcases priorities with _ | ⟨priority4, priorities⟩
  · simp [eightPriorityPlacement?]
  rcases priorities with _ | ⟨priority5, priorities⟩
  · simp [eightPriorityPlacement?]
  rcases priorities with _ | ⟨priority6, priorities⟩
  · simp [eightPriorityPlacement?]
  rcases priorities with _ | ⟨priority7, priorities⟩
  · simp [eightPriorityPlacement?]
  rcases priorities with _ | ⟨extra, tail⟩
  · simp [eightPriorityPlacement?, eq_comm]
  · simp [eightPriorityPlacement?]

/-! ## Ambiguity-preserving per-record mathematical indices -/

structure TransBicappedOctahedron8MathematicalIndexCandidate where
  placement : OCT8Executable.Placement
  index : List OCT8SourceIndex.PriorityDigit
  deriving DecidableEq

/-- The complete mathematical symmetry index for one admitted executable role placement. -/
noncomputable def transBicappedOctahedron8MathematicalIndexCandidateOf
    (priorityPlacement : Fin 8 → PolyhedralPriorityNumber)
    (placement : OCT8Executable.Placement) :
    TransBicappedOctahedron8MathematicalIndexCandidate :=
  { placement := placement
    index := OCT8SourceIndex.completeIndex fun position =>
      priorityPlacement (OCT8Executable.donorIndexAt placement position) }

/-- All admitted role placements and their complete mathematical indices for one source record. -/
noncomputable def IndexedIR9CoordinationSourceRecord.transBicappedOctahedron8MathematicalIndexCandidates
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration) :
    List TransBicappedOctahedron8MathematicalIndexCandidate :=
  match spatial.transBicappedOctahedron8Frame? record with
  | none => []
  | some frame =>
      match result.molecularPolyhedralPriorityNumbers?
          record.center .transBicappedOctahedron record.ligands with
      | none => []
      | some priorities =>
          match eightPriorityPlacement? priorities with
          | none => []
          | some priorityPlacement =>
              (OCT8Executable.recognizedPlacements frame).map
                (transBicappedOctahedron8MathematicalIndexCandidateOf priorityPlacement)

/-- Independent conjunction defining exactly one admitted mathematical-index candidate. -/
def TransBicappedOctahedron8MathematicalIndexCandidateJudgment
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (candidate : TransBicappedOctahedron8MathematicalIndexCandidate) : Prop :=
  ∃ frame priorities priorityPlacement placement,
    TransBicappedOctahedron8FrameJudgment spatial record frame ∧
    result.molecularPolyhedralPriorityNumbers?
      record.center .transBicappedOctahedron record.ligands = some priorities ∧
    EightPriorityPlacementJudgment priorities priorityPlacement ∧
    OCT8Executable.IsExactPlacement frame placement ∧
    candidate = transBicappedOctahedron8MathematicalIndexCandidateOf
      priorityPlacement placement

theorem mem_transBicappedOctahedron8MathematicalIndexCandidates_iff
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (candidate : TransBicappedOctahedron8MathematicalIndexCandidate) :
    candidate ∈ record.transBicappedOctahedron8MathematicalIndexCandidates result spatial ↔
      TransBicappedOctahedron8MathematicalIndexCandidateJudgment
        record result spatial candidate := by
  constructor
  · intro present
    unfold IndexedIR9CoordinationSourceRecord.transBicappedOctahedron8MathematicalIndexCandidates at present
    cases frameEq : spatial.transBicappedOctahedron8Frame? record with
    | none => simp [frameEq] at present
    | some frame =>
        cases priorityEq : result.molecularPolyhedralPriorityNumbers?
            record.center .transBicappedOctahedron record.ligands with
        | none => simp [frameEq, priorityEq] at present
        | some priorities =>
            cases placementEq : eightPriorityPlacement? priorities with
            | none => simp [frameEq, priorityEq, placementEq] at present
            | some priorityPlacement =>
                simp only [frameEq, priorityEq, placementEq] at present
                change candidate ∈
                  (OCT8Executable.recognizedPlacements frame).map
                    (transBicappedOctahedron8MathematicalIndexCandidateOf
                      priorityPlacement) at present
                rcases List.mem_map.mp present with
                  ⟨placement, placementPresent, rfl⟩
                exact ⟨frame, priorities, priorityPlacement, placement,
                  (transBicappedOctahedron8Frame?_eq_some_iff
                    spatial record frame).mp frameEq,
                  priorityEq,
                  (eightPriorityPlacement?_eq_some_iff
                    priorities priorityPlacement).mp placementEq,
                  (RedBookIR9.TransBicappedOctahedron8ExecutableSpatialPerception.mem_recognizedExecutablePlacements_iff
                    frame placement).mp placementPresent,
                  rfl⟩
  · rintro ⟨frame, priorities, priorityPlacement, placement, frameJudged,
      priorityEq, placementJudged, geometryJudged, rfl⟩
    have frameEq :=
      (transBicappedOctahedron8Frame?_eq_some_iff spatial record frame).mpr frameJudged
    have placementEq :=
      (eightPriorityPlacement?_eq_some_iff priorities priorityPlacement).mpr placementJudged
    unfold IndexedIR9CoordinationSourceRecord.transBicappedOctahedron8MathematicalIndexCandidates
    simp only [frameEq, priorityEq, placementEq]
    exact List.mem_map.mpr ⟨placement,
      (RedBookIR9.TransBicappedOctahedron8ExecutableSpatialPerception.mem_recognizedExecutablePlacements_iff
        frame placement).mpr geometryJudged, rfl⟩

theorem transBicappedOctahedron8MathematicalIndexCandidates_nodup
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration) :
    (record.transBicappedOctahedron8MathematicalIndexCandidates result spatial).Nodup := by
  unfold IndexedIR9CoordinationSourceRecord.transBicappedOctahedron8MathematicalIndexCandidates
  cases frameEq : spatial.transBicappedOctahedron8Frame? record with
  | none => simp
  | some frame =>
      cases priorityEq : result.molecularPolyhedralPriorityNumbers?
          record.center .transBicappedOctahedron record.ligands with
      | none => simp
      | some priorities =>
          cases placementEq : eightPriorityPlacement? priorities with
          | none => simp [placementEq]
          | some priorityPlacement =>
              simp only [placementEq]
              apply List.Nodup.map
              · intro left right same
                exact congrArg TransBicappedOctahedron8MathematicalIndexCandidate.placement same
              · exact RedBookIR9.TransBicappedOctahedron8ExecutableSpatialPerception.recognizedExecutablePlacements_nodup
                  frame

theorem transBicappedOctahedron8MathematicalIndexCandidates_nonempty_iff
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration) :
    record.transBicappedOctahedron8MathematicalIndexCandidates result spatial ≠ [] ↔
      ∃ candidate,
        TransBicappedOctahedron8MathematicalIndexCandidateJudgment
          record result spatial candidate := by
  constructor
  · intro nonempty
    obtain ⟨candidate, present⟩ := List.exists_mem_of_ne_nil _ nonempty
    exact ⟨candidate,
      (mem_transBicappedOctahedron8MathematicalIndexCandidates_iff
        record result spatial candidate).mp present⟩
  · rintro ⟨candidate, judged⟩ equal
    have present :=
      (mem_transBicappedOctahedron8MathematicalIndexCandidates_iff
        record result spatial candidate).mpr judged
    simp [equal] at present

/-- Exhaustive semantic refusal of the complete per-record integration. -/
def TransBicappedOctahedron8MathematicalIndexRefused
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration) : Prop :=
  ∀ candidate,
    ¬ TransBicappedOctahedron8MathematicalIndexCandidateJudgment
      record result spatial candidate

theorem transBicappedOctahedron8MathematicalIndexCandidates_eq_nil_iff_refused
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration) :
    record.transBicappedOctahedron8MathematicalIndexCandidates result spatial = [] ↔
      TransBicappedOctahedron8MathematicalIndexRefused record result spatial := by
  constructor
  · intro equal candidate judged
    have present :=
      (mem_transBicappedOctahedron8MathematicalIndexCandidates_iff
        record result spatial candidate).mpr judged
    simp [equal] at present
  · intro refused
    by_contra nonempty
    rcases (transBicappedOctahedron8MathematicalIndexCandidates_nonempty_iff
      record result spatial).mp nonempty with ⟨candidate, judged⟩
    exact refused candidate judged

/-! ## Molecular IR-9.3.5 priority provenance -/

/-- The proof-relevant IR-9.3.5 certificate exposed by safe molecular priority ingress. -/
def TransBicappedOctahedron8MolecularIR9PriorityCertificate
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
      result.polyhedralPriorityComparisonFrame?
          record.center .transBicappedOctahedron record.ligands = some compareAt ∧
      deriveDensePolyhedralBasePriorityNumbers? record.ligands.length compareAt =
        some baseNumbers ∧
      RedBookIR9.FinitePriorityNumbering record.ligands.length compareAt baseNumbers ∧
      canonicalPolyhedralPrimeCounts? record.ligands.length memberships = some primeCounts ∧
      RedBookIR9.FinitePrimingAssignment record.ligands.length
        (effectivePolyhedralPrimingMemberships record.ligands.length memberships) primeCounts ∧
      baseNumbers.zipWithM (fun number primes =>
        some { number := number, primes := primes }) primeCounts = some priorities

theorem transBicappedOctahedron8MathematicalIndexCandidate_has_IR9_priority_certificate
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (candidate : TransBicappedOctahedron8MathematicalIndexCandidate)
    (present :
      candidate ∈ record.transBicappedOctahedron8MathematicalIndexCandidates result spatial) :
    ∃ frame priorities priorityPlacement placement,
      TransBicappedOctahedron8FrameJudgment spatial record frame ∧
      TransBicappedOctahedron8MolecularIR9PriorityCertificate result record priorities ∧
      EightPriorityPlacementJudgment priorities priorityPlacement ∧
      OCT8Executable.IsExactPlacement frame placement ∧
      candidate = transBicappedOctahedron8MathematicalIndexCandidateOf
        priorityPlacement placement := by
  rcases (mem_transBicappedOctahedron8MathematicalIndexCandidates_iff
      record result spatial candidate).mp present with
    ⟨frame, priorities, priorityPlacement, placement, frameJudged, priorityEq,
      placementJudged, geometryJudged, candidateEq⟩
  refine ⟨frame, priorities, priorityPlacement, placement, frameJudged, ?_,
    placementJudged, geometryJudged, candidateEq⟩
  exact result.molecularPolyhedralPriorityNumbers?_sound_IR9
    record.center .transBicappedOctahedron record.ligands priorities priorityEq

/-! ## Exhaustive whole-molecule schedule -/

structure TransBicappedOctahedron8MathematicalIndexAssignment where
  record : IndexedIR9CoordinationSourceRecord
  candidate : TransBicappedOctahedron8MathematicalIndexCandidate
  deriving DecidableEq

/-- Analyze every canonical coordination-eight source record, retaining all admitted placements. -/
noncomputable def CertifiedChemistryNormalizationResult.analyzeTransBicappedOctahedron8MathematicalIndices
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration) :
    List TransBicappedOctahedron8MathematicalIndexAssignment :=
  (certified.ir9CoordinationSourceRecords 8).flatMap fun record =>
    (record.transBicappedOctahedron8MathematicalIndexCandidates certified.result spatial).map
      fun candidate => { record := record, candidate := candidate }

theorem mem_analyzeTransBicappedOctahedron8MathematicalIndices_iff
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedIR9CoordinationSourceRecord)
    (candidate : TransBicappedOctahedron8MathematicalIndexCandidate) :
    ({ record := record, candidate := candidate } :
        TransBicappedOctahedron8MathematicalIndexAssignment) ∈
        certified.analyzeTransBicappedOctahedron8MathematicalIndices spatial ↔
      record ∈ certified.ir9CoordinationSourceRecords 8 ∧
      TransBicappedOctahedron8MathematicalIndexCandidateJudgment
        record certified.result spatial candidate := by
  unfold CertifiedChemistryNormalizationResult.analyzeTransBicappedOctahedron8MathematicalIndices
  constructor
  · rw [List.mem_flatMap]
    rintro ⟨otherRecord, otherPresent, assignmentPresent⟩
    rcases List.mem_map.mp assignmentPresent with
      ⟨otherCandidate, candidatePresent, equal⟩
    have recordEqual : otherRecord = record :=
      congrArg TransBicappedOctahedron8MathematicalIndexAssignment.record equal
    have candidateEqual : otherCandidate = candidate :=
      congrArg TransBicappedOctahedron8MathematicalIndexAssignment.candidate equal
    subst otherRecord
    subst otherCandidate
    exact ⟨otherPresent,
      (mem_transBicappedOctahedron8MathematicalIndexCandidates_iff
        record certified.result spatial candidate).mp candidatePresent⟩
  · rintro ⟨recordPresent, candidateJudged⟩
    rw [List.mem_flatMap]
    refine ⟨record, recordPresent, List.mem_map.mpr ⟨candidate, ?_, rfl⟩⟩
    exact (mem_transBicappedOctahedron8MathematicalIndexCandidates_iff
      record certified.result spatial candidate).mpr candidateJudged

theorem analyzeTransBicappedOctahedron8MathematicalIndices_nodup
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration) :
    (certified.analyzeTransBicappedOctahedron8MathematicalIndices spatial).Nodup := by
  unfold CertifiedChemistryNormalizationResult.analyzeTransBicappedOctahedron8MathematicalIndices
  rw [List.nodup_flatMap]
  constructor
  · intro record recordPresent
    exact (transBicappedOctahedron8MathematicalIndexCandidates_nodup
      record certified.result spatial).map (by
        intro left right equal
        exact congrArg TransBicappedOctahedron8MathematicalIndexAssignment.candidate equal)
  · have recordsNodup := certified.ir9CoordinationSourceRecords_nodup 8
    rw [List.nodup_iff_pairwise_ne] at recordsNodup
    apply recordsNodup.imp
    intro left right different
    rw [Function.onFun, List.disjoint_left]
    intro assignment leftPresent rightPresent
    rcases List.mem_map.mp leftPresent with ⟨leftCandidate, _leftCandidatePresent, rfl⟩
    rcases List.mem_map.mp rightPresent with
      ⟨rightCandidate, _rightCandidatePresent, equal⟩
    exact different
      (congrArg TransBicappedOctahedron8MathematicalIndexAssignment.record equal).symm

/-- Every admitted molecular record/placement pair occurs literally once in the whole analyzer. -/
theorem analyzeTransBicappedOctahedron8MathematicalIndices_count_eq_one
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (assignment : TransBicappedOctahedron8MathematicalIndexAssignment)
    (present : assignment ∈
      certified.analyzeTransBicappedOctahedron8MathematicalIndices spatial) :
    List.count assignment
      (certified.analyzeTransBicappedOctahedron8MathematicalIndices spatial) = 1 := by
  exact List.count_eq_one_of_mem
    (analyzeTransBicappedOctahedron8MathematicalIndices_nodup certified spatial) present

end TetraStereo.OneCenter
