import TetraStereo.OneCenter.CIPIR9CubeMathematicalIndexIntegration

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Whole-molecule analysis of resolved CU-8 mathematical indices

Every canonical coordination-eight molecular source record is attempted.  A record emits exactly
one complete mathematical CU-8 word when coordinate ingress, molecular priority construction, and
strict ideal-cube recognition all succeed.  The spatial-orbit theorem makes the word independent
of the admitted role placement.  Refusal is exactly the absence of a complete candidate.

This is still a mathematical symmetry index, not a source-unpublished CU-8 short index or `A/C`
descriptor.
-/

structure CubeResolvedMathematicalIndexAssignment where
  record : IndexedIR9CoordinationSourceRecord
  index : List CubeSourceIndex.PriorityDigit
  deriving DecidableEq

/-- Package one source record exactly when its CU-8 mathematical word resolves. -/
noncomputable def IndexedIR9CoordinationSourceRecord.cubeResolvedMathematicalIndexAssignment?
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration) :
    Option CubeResolvedMathematicalIndexAssignment :=
  (record.cubeResolvedMathematicalIndex? result spatial).map fun index =>
    { record := record, index := index }

theorem cubeResolvedMathematicalIndexAssignment?_eq_some_iff
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (assignment : CubeResolvedMathematicalIndexAssignment) :
    record.cubeResolvedMathematicalIndexAssignment? result spatial = some assignment ↔
      assignment.record = record ∧
      record.cubeResolvedMathematicalIndex? result spatial = some assignment.index := by
  rcases assignment with ⟨assignmentRecord, assignmentIndex⟩
  unfold IndexedIR9CoordinationSourceRecord.cubeResolvedMathematicalIndexAssignment?
  cases computed : record.cubeResolvedMathematicalIndex? result spatial with
  | none => simp
  | some index => simp [eq_comm]

/-- Whole-molecule CU-8 analysis over the exact duplicate-free coordination-eight schedule. -/
noncomputable def CertifiedChemistryNormalizationResult.analyzeResolvedCubeMathematicalIndices
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration) :
    List CubeResolvedMathematicalIndexAssignment :=
  (certified.ir9CoordinationSourceRecords 8).filterMap fun record =>
    record.cubeResolvedMathematicalIndexAssignment? certified.result spatial

/-- Exact executable membership in the whole-molecule CU-8 analyzer. -/
theorem mem_analyzeResolvedCubeMathematicalIndices_iff
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedIR9CoordinationSourceRecord)
    (index : List CubeSourceIndex.PriorityDigit) :
    ({ record := record, index := index } : CubeResolvedMathematicalIndexAssignment) ∈
        certified.analyzeResolvedCubeMathematicalIndices spatial ↔
      record ∈ certified.ir9CoordinationSourceRecords 8 ∧
      record.cubeResolvedMathematicalIndex? certified.result spatial = some index := by
  unfold CertifiedChemistryNormalizationResult.analyzeResolvedCubeMathematicalIndices
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨otherRecord, otherPresent, computed⟩
    have packaged :=
      (cubeResolvedMathematicalIndexAssignment?_eq_some_iff
        otherRecord certified.result spatial { record := record, index := index }).mp computed
    have recordEq : record = otherRecord := packaged.1
    subst otherRecord
    exact ⟨otherPresent, packaged.2⟩
  · rintro ⟨recordPresent, computed⟩
    exact ⟨record, recordPresent,
      (cubeResolvedMathematicalIndexAssignment?_eq_some_iff
        record certified.result spatial { record := record, index := index }).mpr
          ⟨rfl, computed⟩⟩

/-- Membership expanded to independent frame, priority, and exact-placement semantics. -/
theorem mem_analyzeResolvedCubeMathematicalIndices_iff_semantic
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedIR9CoordinationSourceRecord)
    (index : List CubeSourceIndex.PriorityDigit) :
    ({ record := record, index := index } : CubeResolvedMathematicalIndexAssignment) ∈
        certified.analyzeResolvedCubeMathematicalIndices spatial ↔
      record ∈ certified.ir9CoordinationSourceRecords 8 ∧
      ∃ candidate,
        CubeMathematicalIndexCandidateJudgment
          record certified.result spatial candidate ∧
        candidate.index = index := by
  rw [mem_analyzeResolvedCubeMathematicalIndices_iff,
    cubeResolvedMathematicalIndex?_eq_some_iff]

/-- Whole-molecule resolved CU-8 assignments are duplicate-free. -/
theorem analyzeResolvedCubeMathematicalIndices_nodup
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration) :
    (certified.analyzeResolvedCubeMathematicalIndices spatial).Nodup := by
  unfold CertifiedChemistryNormalizationResult.analyzeResolvedCubeMathematicalIndices
  apply List.Nodup.filterMap
  · intro left right assignment leftComputed rightComputed
    have leftRecord :=
      (cubeResolvedMathematicalIndexAssignment?_eq_some_iff
        left certified.result spatial assignment).mp leftComputed |>.1
    have rightRecord :=
      (cubeResolvedMathematicalIndexAssignment?_eq_some_iff
        right certified.result spatial assignment).mp rightComputed |>.1
    exact leftRecord.symm.trans rightRecord
  · exact certified.ir9CoordinationSourceRecords_nodup 8

/-- Forgetting the resolved word still leaves a duplicate-free list of source records. -/
theorem analyzeResolvedCubeMathematicalIndices_records_nodup
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration) :
    ((certified.analyzeResolvedCubeMathematicalIndices spatial).map
      CubeResolvedMathematicalIndexAssignment.record).Nodup := by
  apply (analyzeResolvedCubeMathematicalIndices_nodup certified spatial).map_on
  intro left leftPresent right rightPresent recordEq
  rcases left with ⟨leftRecord, leftIndex⟩
  rcases right with ⟨rightRecord, rightIndex⟩
  simp only at recordEq ⊢
  have leftComputed :=
    (mem_analyzeResolvedCubeMathematicalIndices_iff
      certified spatial leftRecord leftIndex).mp leftPresent |>.2
  have rightComputed :=
    (mem_analyzeResolvedCubeMathematicalIndices_iff
      certified spatial rightRecord rightIndex).mp rightPresent |>.2
  subst rightRecord
  have indexEq : leftIndex = rightIndex :=
    Option.some.inj (leftComputed.symm.trans rightComputed)
  subst rightIndex
  rfl

/-- Every emitted record/index pair occurs literally once. -/
theorem analyzeResolvedCubeMathematicalIndices_count_eq_one
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (assignment : CubeResolvedMathematicalIndexAssignment)
    (present : assignment ∈ certified.analyzeResolvedCubeMathematicalIndices spatial) :
    List.count assignment (certified.analyzeResolvedCubeMathematicalIndices spatial) = 1 := by
  exact List.count_eq_one_of_mem
    (analyzeResolvedCubeMathematicalIndices_nodup certified spatial) present

/-- A scheduled coordination-eight record fails to emit exactly when no complete CU-8 candidate
exists. -/
theorem scheduledCubeResolvedMathematicalIndex_refused_iff
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedIR9CoordinationSourceRecord)
    (recordPresent : record ∈ certified.ir9CoordinationSourceRecords 8) :
    (¬ ∃ index,
      ({ record := record, index := index } : CubeResolvedMathematicalIndexAssignment) ∈
        certified.analyzeResolvedCubeMathematicalIndices spatial) ↔
      CubeMathematicalIndexRefused record certified.result spatial := by
  rw [← cubeResolvedMathematicalIndex?_eq_none_iff_refused]
  constructor
  · intro noEmission
    cases computed : record.cubeResolvedMathematicalIndex? certified.result spatial with
    | none => rfl
    | some index =>
        exfalso
        exact noEmission ⟨index,
          (mem_analyzeResolvedCubeMathematicalIndices_iff
            certified spatial record index).mpr ⟨recordPresent, computed⟩⟩
  · intro computed
    rintro ⟨index, emitted⟩
    have resolved :=
      (mem_analyzeResolvedCubeMathematicalIndices_iff
        certified spatial record index).mp emitted |>.2
    rw [computed] at resolved
    cases resolved

/-- Scheduled non-emission expanded to the four exhaustive operational failure stages. -/
theorem scheduledCubeResolvedMathematicalIndex_refused_iff_operationalRefusal
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedIR9CoordinationSourceRecord)
    (recordPresent : record ∈ certified.ir9CoordinationSourceRecords 8) :
    (¬ ∃ index,
      ({ record := record, index := index } : CubeResolvedMathematicalIndexAssignment) ∈
        certified.analyzeResolvedCubeMathematicalIndices spatial) ↔
      CubeMathematicalIndexOperationalRefusal record certified.result spatial := by
  rw [scheduledCubeResolvedMathematicalIndex_refused_iff
      certified spatial record recordPresent,
    cubeMathematicalIndexRefused_iff_operationalRefusal]

/-- Every scheduled coordination-eight record has exactly one CU-8 mathematical index or the
exhaustive semantic refusal. -/
theorem scheduledCubeResolvedMathematicalIndex_exhaustive
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedIR9CoordinationSourceRecord)
    (recordPresent : record ∈ certified.ir9CoordinationSourceRecords 8) :
    (∃! index,
      ({ record := record, index := index } : CubeResolvedMathematicalIndexAssignment) ∈
        certified.analyzeResolvedCubeMathematicalIndices spatial) ∨
      CubeMathematicalIndexRefused record certified.result spatial := by
  rcases cubeMathematicalIndexResolution_exhaustive
      record certified.result spatial with resolved | refused
  · left
    rcases resolved with ⟨index, computed, unique⟩
    refine ⟨index,
      (mem_analyzeResolvedCubeMathematicalIndices_iff
        certified spatial record index).mpr ⟨recordPresent, computed⟩, ?_⟩
    intro other otherPresent
    have otherComputed :=
      (mem_analyzeResolvedCubeMathematicalIndices_iff
        certified spatial record other).mp otherPresent |>.2
    exact unique other otherComputed
  · exact .inr refused

/-- Every scheduled record emits exactly one index or has one of the exhaustive operational
failure reasons. -/
theorem scheduledCubeResolvedMathematicalIndex_exhaustive_operational
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedIR9CoordinationSourceRecord)
    (recordPresent : record ∈ certified.ir9CoordinationSourceRecords 8) :
    (∃! index,
      ({ record := record, index := index } : CubeResolvedMathematicalIndexAssignment) ∈
        certified.analyzeResolvedCubeMathematicalIndices spatial) ∨
      CubeMathematicalIndexOperationalRefusal record certified.result spatial := by
  rcases scheduledCubeResolvedMathematicalIndex_exhaustive
      certified spatial record recordPresent with emitted | refused
  · exact .inl emitted
  · exact .inr ((cubeMathematicalIndexRefused_iff_operationalRefusal
      record certified.result spatial).mp refused)

end TetraStereo.OneCenter
