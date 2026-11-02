import TetraStereo.OneCenter.CIPIR9TransBicappedOctahedron8MathematicalIndexResolution

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Whole-molecule analysis of resolved OCT-8 mathematical indices

The preceding ambiguity-aware resolver is per source record.  This module lifts it over the exact,
duplicate-free coordination-eight molecular schedule.  At most one index is emitted for a source
record, and an index is emitted exactly when at least one complete placement candidate exists and
all admitted candidates agree.

This remains a mathematical symmetry index.  It is not an OCT-8 short index or `A`/`C` descriptor
that the transcribed source does not define.
-/

structure TransBicappedOctahedron8ResolvedMathematicalIndexAssignment where
  record : IndexedIR9CoordinationSourceRecord
  index : List OCT8SourceIndex.PriorityDigit
  deriving DecidableEq

/-- Package one record exactly when its ambiguity-aware mathematical index resolves. -/
noncomputable def IndexedIR9CoordinationSourceRecord.transBicappedOctahedron8ResolvedMathematicalIndexAssignment?
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration) :
    Option TransBicappedOctahedron8ResolvedMathematicalIndexAssignment :=
  (record.transBicappedOctahedron8ResolvedMathematicalIndex? result spatial).map fun index =>
    { record := record, index := index }

theorem transBicappedOctahedron8ResolvedMathematicalIndexAssignment?_eq_some_iff
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (assignment : TransBicappedOctahedron8ResolvedMathematicalIndexAssignment) :
    record.transBicappedOctahedron8ResolvedMathematicalIndexAssignment? result spatial =
        some assignment ↔
      assignment.record = record ∧
      record.transBicappedOctahedron8ResolvedMathematicalIndex? result spatial =
        some assignment.index := by
  rcases assignment with ⟨assignmentRecord, assignmentIndex⟩
  unfold IndexedIR9CoordinationSourceRecord.transBicappedOctahedron8ResolvedMathematicalIndexAssignment?
  cases computed :
      record.transBicappedOctahedron8ResolvedMathematicalIndex? result spatial with
  | none => simp
  | some index => simp [eq_comm]

/-- Analyze every canonical coordination-eight source record, emitting only resolved words. -/
noncomputable def CertifiedChemistryNormalizationResult.analyzeResolvedTransBicappedOctahedron8MathematicalIndices
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration) :
    List TransBicappedOctahedron8ResolvedMathematicalIndexAssignment :=
  (certified.ir9CoordinationSourceRecords 8).filterMap fun record =>
    record.transBicappedOctahedron8ResolvedMathematicalIndexAssignment?
      certified.result spatial

/-- Exact executable membership in the whole-molecule resolved analyzer. -/
theorem mem_analyzeResolvedTransBicappedOctahedron8MathematicalIndices_iff
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedIR9CoordinationSourceRecord)
    (index : List OCT8SourceIndex.PriorityDigit) :
    ({ record := record, index := index } :
        TransBicappedOctahedron8ResolvedMathematicalIndexAssignment) ∈
        certified.analyzeResolvedTransBicappedOctahedron8MathematicalIndices spatial ↔
      record ∈ certified.ir9CoordinationSourceRecords 8 ∧
      record.transBicappedOctahedron8ResolvedMathematicalIndex?
        certified.result spatial = some index := by
  unfold CertifiedChemistryNormalizationResult.analyzeResolvedTransBicappedOctahedron8MathematicalIndices
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨otherRecord, otherPresent, computed⟩
    have packaged :=
      (transBicappedOctahedron8ResolvedMathematicalIndexAssignment?_eq_some_iff
        otherRecord certified.result spatial
        { record := record, index := index }).mp computed
    have recordEq : record = otherRecord := packaged.1
    subst otherRecord
    exact ⟨otherPresent, packaged.2⟩
  · rintro ⟨recordPresent, computed⟩
    exact ⟨record, recordPresent,
      (transBicappedOctahedron8ResolvedMathematicalIndexAssignment?_eq_some_iff
        record certified.result spatial
        { record := record, index := index }).mpr ⟨rfl, computed⟩⟩

/-- Membership expanded to the independent nonempty/unanimous candidate semantics. -/
theorem mem_analyzeResolvedTransBicappedOctahedron8MathematicalIndices_iff_semantic
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedIR9CoordinationSourceRecord)
    (index : List OCT8SourceIndex.PriorityDigit) :
    ({ record := record, index := index } :
        TransBicappedOctahedron8ResolvedMathematicalIndexAssignment) ∈
        certified.analyzeResolvedTransBicappedOctahedron8MathematicalIndices spatial ↔
      record ∈ certified.ir9CoordinationSourceRecords 8 ∧
      record.transBicappedOctahedron8MathematicalIndexCandidates
          certified.result spatial ≠ [] ∧
      ∀ candidate,
        candidate ∈ record.transBicappedOctahedron8MathematicalIndexCandidates
          certified.result spatial →
        candidate.index = index := by
  rw [mem_analyzeResolvedTransBicappedOctahedron8MathematicalIndices_iff,
    transBicappedOctahedron8ResolvedMathematicalIndex?_eq_some_iff]

/-- Whole-molecule resolved assignments are duplicate-free. -/
theorem analyzeResolvedTransBicappedOctahedron8MathematicalIndices_nodup
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration) :
    (certified.analyzeResolvedTransBicappedOctahedron8MathematicalIndices spatial).Nodup := by
  unfold CertifiedChemistryNormalizationResult.analyzeResolvedTransBicappedOctahedron8MathematicalIndices
  apply List.Nodup.filterMap
  · intro left right assignment leftComputed rightComputed
    have leftRecord :=
      (transBicappedOctahedron8ResolvedMathematicalIndexAssignment?_eq_some_iff
        left certified.result spatial assignment).mp leftComputed |>.1
    have rightRecord :=
      (transBicappedOctahedron8ResolvedMathematicalIndexAssignment?_eq_some_iff
        right certified.result spatial assignment).mp rightComputed |>.1
    exact leftRecord.symm.trans rightRecord
  · exact certified.ir9CoordinationSourceRecords_nodup 8

/-- Even after forgetting the resolved word, emitted source records remain duplicate-free. -/
theorem analyzeResolvedTransBicappedOctahedron8MathematicalIndices_records_nodup
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration) :
    ((certified.analyzeResolvedTransBicappedOctahedron8MathematicalIndices spatial).map
      TransBicappedOctahedron8ResolvedMathematicalIndexAssignment.record).Nodup := by
  apply (analyzeResolvedTransBicappedOctahedron8MathematicalIndices_nodup
    certified spatial).map_on
  intro left leftPresent right rightPresent recordEq
  rcases left with ⟨leftRecord, leftIndex⟩
  rcases right with ⟨rightRecord, rightIndex⟩
  simp only at recordEq ⊢
  have leftComputed :=
    (mem_analyzeResolvedTransBicappedOctahedron8MathematicalIndices_iff
      certified spatial leftRecord leftIndex).mp leftPresent |>.2
  have rightComputed :=
    (mem_analyzeResolvedTransBicappedOctahedron8MathematicalIndices_iff
      certified spatial rightRecord rightIndex).mp rightPresent |>.2
  subst rightRecord
  have indexEq : leftIndex = rightIndex :=
    Option.some.inj (leftComputed.symm.trans rightComputed)
  subst rightIndex
  rfl

/-- Every emitted whole-molecule record/index pair occurs literally once. -/
theorem analyzeResolvedTransBicappedOctahedron8MathematicalIndices_count_eq_one
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (assignment : TransBicappedOctahedron8ResolvedMathematicalIndexAssignment)
    (present : assignment ∈
      certified.analyzeResolvedTransBicappedOctahedron8MathematicalIndices spatial) :
    List.count assignment
      (certified.analyzeResolvedTransBicappedOctahedron8MathematicalIndices spatial) = 1 := by
  exact List.count_eq_one_of_mem
    (analyzeResolvedTransBicappedOctahedron8MathematicalIndices_nodup
      certified spatial) present

/-- For a scheduled record, failure to emit is exactly absence or witnessed index conflict. -/
theorem scheduledTransBicappedOctahedron8ResolvedMathematicalIndex_refused_iff
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedIR9CoordinationSourceRecord)
    (recordPresent : record ∈ certified.ir9CoordinationSourceRecords 8) :
    (¬ ∃ index,
      ({ record := record, index := index } :
          TransBicappedOctahedron8ResolvedMathematicalIndexAssignment) ∈
        certified.analyzeResolvedTransBicappedOctahedron8MathematicalIndices spatial) ↔
      record.transBicappedOctahedron8MathematicalIndexCandidates
          certified.result spatial = [] ∨
      TransBicappedOctahedron8MathematicalIndexAmbiguous
        record certified.result spatial := by
  rw [← transBicappedOctahedron8ResolvedMathematicalIndex?_eq_none_iff]
  constructor
  · intro noEmission
    cases computed :
        record.transBicappedOctahedron8ResolvedMathematicalIndex?
          certified.result spatial with
    | none => rfl
    | some index =>
        exfalso
        exact noEmission ⟨index,
          (mem_analyzeResolvedTransBicappedOctahedron8MathematicalIndices_iff
            certified spatial record index).mpr ⟨recordPresent, computed⟩⟩
  · intro computed
    rintro ⟨index, emitted⟩
    have resolved :=
      (mem_analyzeResolvedTransBicappedOctahedron8MathematicalIndices_iff
        certified spatial record index).mp emitted |>.2
    rw [computed] at resolved
    cases resolved

/-- Every scheduled record has exactly one emitted index, no candidate, or a witnessed conflict. -/
theorem scheduledTransBicappedOctahedron8ResolvedMathematicalIndex_exhaustive
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (record : IndexedIR9CoordinationSourceRecord)
    (recordPresent : record ∈ certified.ir9CoordinationSourceRecords 8) :
    (∃! index,
      ({ record := record, index := index } :
          TransBicappedOctahedron8ResolvedMathematicalIndexAssignment) ∈
        certified.analyzeResolvedTransBicappedOctahedron8MathematicalIndices spatial) ∨
      record.transBicappedOctahedron8MathematicalIndexCandidates
          certified.result spatial = [] ∨
      TransBicappedOctahedron8MathematicalIndexAmbiguous
        record certified.result spatial := by
  rcases transBicappedOctahedron8MathematicalIndexResolution_exhaustive
      record certified.result spatial with
    resolved | refused
  · left
    rcases resolved with ⟨index, computed⟩
    refine ⟨index,
      (mem_analyzeResolvedTransBicappedOctahedron8MathematicalIndices_iff
        certified spatial record index).mpr ⟨recordPresent, computed⟩, ?_⟩
    intro other otherPresent
    have otherComputed :=
      (mem_analyzeResolvedTransBicappedOctahedron8MathematicalIndices_iff
        certified spatial record other).mp otherPresent |>.2
    exact Option.some.inj (otherComputed.symm.trans computed)
  · exact Or.inr refused

end TetraStereo.OneCenter
