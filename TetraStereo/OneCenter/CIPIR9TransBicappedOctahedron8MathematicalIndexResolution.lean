import TetraStereo.OneCenter.CIPIR9TransBicappedOctahedron8MathematicalIndexIntegration

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Exact ambiguity-aware resolution of molecular OCT-8 mathematical indices

The exact affine OCT-8 recognizer deliberately returns every admitted role placement.  Coordinate
evidence alone need not prove that all such placements belong to one structural frame orbit, so a
resolver must not silently choose the first candidate.  This module returns an index exactly when
the candidate list is nonempty and every candidate has that same index.  Failure is classified
exactly as either absence of every complete candidate or a witnessed pair of conflicting indices.

The final section isolates the stronger geometric premise that would make resolution automatic:
all exact role placements for one frame induce priority placements in the same twelve-element
OCT-8 structural orbit.  Under that premise, the already proved collision-free source index makes
all candidate indices equal and the resolver has exactly one result.
-/

/-! ## Generic exact resolver over admitted candidates -/

/-- Resolve only a nonempty list whose complete mathematical indices all agree. -/
def resolveTransBicappedOctahedron8CandidateIndices?
    (candidates : List TransBicappedOctahedron8MathematicalIndexCandidate) :
    Option (List OCT8SourceIndex.PriorityDigit) :=
  match candidates with
  | [] => none
  | first :: rest =>
      if rest.all fun candidate => candidate.index == first.index then
        some first.index
      else none

theorem resolveTransBicappedOctahedron8CandidateIndices?_eq_some_iff
    (candidates : List TransBicappedOctahedron8MathematicalIndexCandidate)
    (index : List OCT8SourceIndex.PriorityDigit) :
    resolveTransBicappedOctahedron8CandidateIndices? candidates = some index ↔
      candidates ≠ [] ∧
        ∀ candidate, candidate ∈ candidates → candidate.index = index := by
  cases candidates with
  | nil => simp [resolveTransBicappedOctahedron8CandidateIndices?]
  | cons first rest =>
      unfold resolveTransBicappedOctahedron8CandidateIndices?
      change (if (rest.all fun candidate => candidate.index == first.index) = true then
          some first.index else none) = some index ↔
        first :: rest ≠ [] ∧
          ∀ candidate, candidate ∈ first :: rest → candidate.index = index
      by_cases agreement :
          (rest.all fun candidate => candidate.index == first.index) = true
      · rw [if_pos agreement]
        have every : ∀ candidate ∈ rest, candidate.index = first.index := by
          simpa only [List.all_eq_true, beq_iff_eq] using agreement
        constructor
        · intro computed
          have firstIndex : first.index = index := Option.some.inj computed
          refine ⟨by simp, ?_⟩
          intro candidate present
          simp only [List.mem_cons] at present
          rcases present with rfl | present
          · exact firstIndex
          · exact (every candidate present).trans firstIndex
        · rintro ⟨_nonempty, everyCandidate⟩
          exact congrArg some (everyCandidate first (by simp))
      · rw [if_neg agreement]
        constructor
        · intro impossible
          contradiction
        · rintro ⟨_nonempty, everyCandidate⟩
          exfalso
          apply agreement
          apply List.all_eq_true.mpr
          intro candidate present
          simp only [beq_iff_eq]
          exact (everyCandidate candidate (by simp [present])).trans
            (everyCandidate first (by simp)).symm

theorem resolveTransBicappedOctahedron8CandidateIndices?_eq_none_iff
    (candidates : List TransBicappedOctahedron8MathematicalIndexCandidate) :
    resolveTransBicappedOctahedron8CandidateIndices? candidates = none ↔
      candidates = [] ∨
        ∃ left, left ∈ candidates ∧
          ∃ right, right ∈ candidates ∧ left.index ≠ right.index := by
  classical
  cases candidates with
  | nil => simp [resolveTransBicappedOctahedron8CandidateIndices?]
  | cons first rest =>
      unfold resolveTransBicappedOctahedron8CandidateIndices?
      change (if (rest.all fun candidate => candidate.index == first.index) = true then
          some first.index else none) = none ↔
        first :: rest = [] ∨
          ∃ left, left ∈ first :: rest ∧
            ∃ right, right ∈ first :: rest ∧ left.index ≠ right.index
      by_cases agreement :
          (rest.all fun candidate => candidate.index == first.index) = true
      · rw [if_pos agreement]
        have everyRest : ∀ candidate ∈ rest, candidate.index = first.index := by
          simpa only [List.all_eq_true, beq_iff_eq] using agreement
        have every : ∀ candidate ∈ first :: rest, candidate.index = first.index := by
          intro candidate present
          simp only [List.mem_cons] at present
          rcases present with rfl | present
          · rfl
          · exact everyRest candidate present
        constructor
        · intro impossible
          contradiction
        · rintro (impossible | ⟨left, leftPresent, right, rightPresent, different⟩)
          · contradiction
          · exact (different
              ((every left leftPresent).trans (every right rightPresent).symm)).elim
      · rw [if_neg agreement]
        constructor
        · intro _computed
          right
          have notEvery : ¬ ∀ candidate ∈ rest, candidate.index = first.index := by
            intro every
            apply agreement
            apply List.all_eq_true.mpr
            intro candidate present
            simpa only [beq_iff_eq] using every candidate present
          push_neg at notEvery
          rcases notEvery with ⟨right, rightPresent, different⟩
          exact ⟨first, by simp, right, by simp [rightPresent],
            fun same => different same.symm⟩
        · intro _witness
          rfl

/-! ## Per-record semantic classification -/

/-- The ambiguity-aware resolved mathematical index for one molecular source record. -/
noncomputable def IndexedIR9CoordinationSourceRecord.transBicappedOctahedron8ResolvedMathematicalIndex?
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration) :
    Option (List OCT8SourceIndex.PriorityDigit) :=
  resolveTransBicappedOctahedron8CandidateIndices?
    (record.transBicappedOctahedron8MathematicalIndexCandidates result spatial)

def TransBicappedOctahedron8MathematicalIndexCoherent
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration) : Prop :=
  ∀ left,
    left ∈ record.transBicappedOctahedron8MathematicalIndexCandidates result spatial →
    ∀ right,
      right ∈ record.transBicappedOctahedron8MathematicalIndexCandidates result spatial →
      left.index = right.index

def TransBicappedOctahedron8MathematicalIndexAmbiguous
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration) : Prop :=
  ∃ left,
    left ∈ record.transBicappedOctahedron8MathematicalIndexCandidates result spatial ∧
    ∃ right,
      right ∈ record.transBicappedOctahedron8MathematicalIndexCandidates result spatial ∧
      left.index ≠ right.index

theorem transBicappedOctahedron8ResolvedMathematicalIndex?_eq_some_iff
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (index : List OCT8SourceIndex.PriorityDigit) :
    record.transBicappedOctahedron8ResolvedMathematicalIndex? result spatial = some index ↔
      record.transBicappedOctahedron8MathematicalIndexCandidates result spatial ≠ [] ∧
      ∀ candidate,
        candidate ∈ record.transBicappedOctahedron8MathematicalIndexCandidates result spatial →
        candidate.index = index :=
  resolveTransBicappedOctahedron8CandidateIndices?_eq_some_iff
    (record.transBicappedOctahedron8MathematicalIndexCandidates result spatial) index

theorem transBicappedOctahedron8ResolvedMathematicalIndex?_eq_none_iff
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration) :
    record.transBicappedOctahedron8ResolvedMathematicalIndex? result spatial = none ↔
      record.transBicappedOctahedron8MathematicalIndexCandidates result spatial = [] ∨
      TransBicappedOctahedron8MathematicalIndexAmbiguous record result spatial :=
  resolveTransBicappedOctahedron8CandidateIndices?_eq_none_iff
    (record.transBicappedOctahedron8MathematicalIndexCandidates result spatial)

theorem transBicappedOctahedron8MathematicalIndexCoherent_iff_not_ambiguous
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration) :
    TransBicappedOctahedron8MathematicalIndexCoherent record result spatial ↔
      ¬ TransBicappedOctahedron8MathematicalIndexAmbiguous record result spatial := by
  constructor
  · intro coherent
    rintro ⟨left, leftPresent, right, rightPresent, different⟩
    exact different (coherent left leftPresent right rightPresent)
  · intro notAmbiguous left leftPresent right rightPresent
    by_contra different
    exact notAmbiguous ⟨left, leftPresent, right, rightPresent, different⟩

theorem transBicappedOctahedron8MathematicalIndexResolution_exhaustive
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration) :
    (∃ index,
      record.transBicappedOctahedron8ResolvedMathematicalIndex? result spatial = some index) ∨
      record.transBicappedOctahedron8MathematicalIndexCandidates result spatial = [] ∨
      TransBicappedOctahedron8MathematicalIndexAmbiguous record result spatial := by
  let candidates :=
    record.transBicappedOctahedron8MathematicalIndexCandidates result spatial
  by_cases empty : candidates = []
  · exact Or.inr (Or.inl empty)
  by_cases ambiguous :
      TransBicappedOctahedron8MathematicalIndexAmbiguous record result spatial
  · exact Or.inr (Or.inr ambiguous)
  have coherent :
      TransBicappedOctahedron8MathematicalIndexCoherent record result spatial :=
    (transBicappedOctahedron8MathematicalIndexCoherent_iff_not_ambiguous
      record result spatial).mpr ambiguous
  obtain ⟨candidate, candidatePresent⟩ := List.exists_mem_of_ne_nil candidates empty
  left
  refine ⟨candidate.index,
    (transBicappedOctahedron8ResolvedMathematicalIndex?_eq_some_iff
      record result spatial candidate.index).mpr ⟨empty, ?_⟩⟩
  intro other otherPresent
  exact coherent other otherPresent candidate candidatePresent

/-! ## Structural-orbit sufficiency -/

/-- The missing stronger shape fact, stated independently of the resolver: every two exact role
placements admitted after the same frame and molecular-priority construction lie in one
twelve-frame OCT-8 structural orbit. -/
def TransBicappedOctahedron8StructuralOrbitCoherent
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration) : Prop :=
  ∀ frame priorities priorityPlacement
      (left right : OCT8Executable.Placement),
    TransBicappedOctahedron8FrameJudgment spatial record frame →
    result.molecularPolyhedralPriorityNumbers?
      record.center .transBicappedOctahedron record.ligands = some priorities →
    EightPriorityPlacementJudgment priorities priorityPlacement →
    OCT8Executable.IsExactPlacement frame left →
    OCT8Executable.IsExactPlacement frame right →
    RedBookIR9.TransBicappedOctahedron8SourceIndexCompleteness.ProductionEquivalent
      (fun position => priorityPlacement (OCT8Executable.donorIndexAt left position))
      (fun position => priorityPlacement (OCT8Executable.donorIndexAt right position))

theorem transBicappedOctahedron8StructuralOrbitCoherent_implies_indexCoherent
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (orbitCoherent :
      TransBicappedOctahedron8StructuralOrbitCoherent record result spatial) :
    TransBicappedOctahedron8MathematicalIndexCoherent record result spatial := by
  intro left leftPresent right rightPresent
  rcases (mem_transBicappedOctahedron8MathematicalIndexCandidates_iff
      record result spatial left).mp leftPresent with
    ⟨leftFrame, leftPriorities, leftPriorityPlacement, leftPlacement,
      leftFrameJudged, leftPrioritiesEq, leftPriorityPlacementJudged,
      leftExact, leftEq⟩
  rcases (mem_transBicappedOctahedron8MathematicalIndexCandidates_iff
      record result spatial right).mp rightPresent with
    ⟨rightFrame, rightPriorities, rightPriorityPlacement, rightPlacement,
      rightFrameJudged, rightPrioritiesEq, rightPriorityPlacementJudged,
      rightExact, rightEq⟩
  have leftFrameEq :
      spatial.transBicappedOctahedron8Frame? record = some leftFrame :=
    (transBicappedOctahedron8Frame?_eq_some_iff
      spatial record leftFrame).mpr leftFrameJudged
  have rightFrameEq :
      spatial.transBicappedOctahedron8Frame? record = some rightFrame :=
    (transBicappedOctahedron8Frame?_eq_some_iff
      spatial record rightFrame).mpr rightFrameJudged
  have frameEq : leftFrame = rightFrame :=
    Option.some.inj (leftFrameEq.symm.trans rightFrameEq)
  have prioritiesEq : leftPriorities = rightPriorities :=
    Option.some.inj (leftPrioritiesEq.symm.trans rightPrioritiesEq)
  subst rightFrame
  subst rightPriorities
  have leftPriorityPlacementEq :
      eightPriorityPlacement? leftPriorities = some leftPriorityPlacement :=
    (eightPriorityPlacement?_eq_some_iff
      leftPriorities leftPriorityPlacement).mpr leftPriorityPlacementJudged
  have rightPriorityPlacementEq :
      eightPriorityPlacement? leftPriorities = some rightPriorityPlacement :=
    (eightPriorityPlacement?_eq_some_iff
      leftPriorities rightPriorityPlacement).mpr rightPriorityPlacementJudged
  have priorityPlacementEq : leftPriorityPlacement = rightPriorityPlacement :=
    Option.some.inj
      (leftPriorityPlacementEq.symm.trans rightPriorityPlacementEq)
  subst rightPriorityPlacement
  rw [leftEq, rightEq]
  change OCT8SourceIndex.completeIndex
      (fun position => leftPriorityPlacement
        (OCT8Executable.donorIndexAt leftPlacement position)) =
    OCT8SourceIndex.completeIndex
      (fun position => leftPriorityPlacement
        (OCT8Executable.donorIndexAt rightPlacement position))
  apply (RedBookIR9.TransBicappedOctahedron8SourceIndexCompleteness.productionCompleteIndex_eq_iff_symmetryEquivalent
    _ _).mpr
  exact orbitCoherent leftFrame leftPriorities leftPriorityPlacement
    leftPlacement rightPlacement leftFrameJudged leftPrioritiesEq
    leftPriorityPlacementJudged leftExact rightExact

theorem transBicappedOctahedron8StructuralOrbitCoherent_resolves_uniquely
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (orbitCoherent :
      TransBicappedOctahedron8StructuralOrbitCoherent record result spatial)
    (nonempty :
      record.transBicappedOctahedron8MathematicalIndexCandidates result spatial ≠ []) :
    ∃! index,
      record.transBicappedOctahedron8ResolvedMathematicalIndex? result spatial = some index := by
  obtain ⟨candidate, candidatePresent⟩ := List.exists_mem_of_ne_nil _ nonempty
  let coherent :=
    transBicappedOctahedron8StructuralOrbitCoherent_implies_indexCoherent
      record result spatial orbitCoherent
  refine ⟨candidate.index, ?_, ?_⟩
  · exact (transBicappedOctahedron8ResolvedMathematicalIndex?_eq_some_iff
      record result spatial candidate.index).mpr ⟨nonempty, by
        intro other otherPresent
        exact coherent other otherPresent candidate candidatePresent⟩
  · intro other otherComputed
    have candidateComputed :=
      (transBicappedOctahedron8ResolvedMathematicalIndex?_eq_some_iff
        record result spatial candidate.index).mpr ⟨nonempty, by
          intro current currentPresent
          exact coherent current currentPresent candidate candidatePresent⟩
    exact Option.some.inj (otherComputed.symm.trans candidateComputed)

end TetraStereo.OneCenter
