import TetraStereo.OneCenter.P93CyclicConfiguration

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP93.Cyclic

/-!
# Exact P-93.5.1.3.2 RCT reference selection

The independent cyclic module states the suffix-first/locant/sequence-priority reference relation.
This module proves that every nonempty finite candidate family has a reference, identifies the one
chemical well-formedness condition needed for uniqueness (one ligand per locant), and gives an
executable selector whose `some` and `none` results are exact.  It also proves the corrected
mean-plane boundary of the RCT cis/trans descriptor compiler.
-/

instance (candidates : List RCTReferenceCandidate) (selected : RCTReferenceCandidate) :
    Decidable (IsRCTReference candidates selected) := by
  unfold IsRCTReference
  infer_instance

/-- Physical ring locants identify at most one reference candidate. -/
def RCTCandidateLocantsUnique (candidates : List RCTReferenceCandidate) : Prop :=
  (candidates.map RCTReferenceCandidate.locant).Nodup

/-- A nonempty finite RCT candidate list always contains at least one independently valid
reference.  In the no-suffix branch, the construction first minimizes locant and then maximizes
sequence priority among candidates at that locant. -/
theorem exists_isRCTReference_of_ne_nil
    (candidates : List RCTReferenceCandidate)
    (nonempty : candidates ≠ []) :
    ∃ selected, IsRCTReference candidates selected := by
  classical
  let suffixes := candidates.toFinset.filter fun candidate =>
    candidate.namedAsSuffix = true
  by_cases suffixesNonempty : suffixes.Nonempty
  · obtain ⟨selected, selectedMinimal⟩ :=
      Finset.exists_minimalFor RCTReferenceCandidate.locant suffixes suffixesNonempty
    have selectedSuffix := Finset.mem_filter.mp selectedMinimal.prop
    have selectedPresent : selected ∈ candidates := by
      simpa [suffixes] using selectedSuffix.1
    refine ⟨selected, selectedPresent, .inl ⟨selectedSuffix.2, ?_⟩⟩
    intro other otherPresent otherSuffix
    have otherInSuffixes : other ∈ suffixes := by
      exact Finset.mem_filter.mpr ⟨by simpa [suffixes] using otherPresent, otherSuffix⟩
    exact selectedMinimal.le otherInSuffixes
  · let allCandidates := candidates.toFinset
    obtain ⟨first, firstPresent⟩ := List.exists_mem_of_ne_nil candidates nonempty
    have allCandidatesNonempty : allCandidates.Nonempty :=
      ⟨first, by simpa [allCandidates] using firstPresent⟩
    obtain ⟨minimumLocantCandidate, minimumLocant⟩ :=
      Finset.exists_minimalFor RCTReferenceCandidate.locant
        allCandidates allCandidatesNonempty
    let minimumLocantCandidates := allCandidates.filter fun candidate =>
      candidate.locant = minimumLocantCandidate.locant
    have minimumLocantCandidatesNonempty : minimumLocantCandidates.Nonempty := by
      exact ⟨minimumLocantCandidate, Finset.mem_filter.mpr
        ⟨minimumLocant.prop, rfl⟩⟩
    obtain ⟨selected, selectedMaximumPriority⟩ :=
      Finset.exists_maximalFor RCTReferenceCandidate.sequencePriority
        minimumLocantCandidates minimumLocantCandidatesNonempty
    have selectedAtMinimum := Finset.mem_filter.mp selectedMaximumPriority.prop
    have selectedPresent : selected ∈ candidates := by
      simpa [minimumLocantCandidates, allCandidates] using selectedAtMinimum.1
    have selectedLocant : selected.locant = minimumLocantCandidate.locant :=
      selectedAtMinimum.2
    have allNotSuffix :
        ∀ candidate ∈ candidates, candidate.namedAsSuffix = false := by
      intro candidate candidatePresent
      cases named : candidate.namedAsSuffix with
      | false => rfl
      | true =>
          exfalso
          apply suffixesNonempty
          exact ⟨candidate, Finset.mem_filter.mpr
            ⟨by simpa [suffixes] using candidatePresent, named⟩⟩
    refine ⟨selected, selectedPresent, .inr ⟨allNotSuffix, ?_⟩⟩
    intro other otherPresent
    have otherInAll : other ∈ allCandidates := by
      simpa [allCandidates] using otherPresent
    have minimumLeOther :
        minimumLocantCandidate.locant ≤ other.locant :=
      minimumLocant.le otherInAll
    by_cases sameLocant : selected.locant = other.locant
    · apply Or.inr
      refine ⟨sameLocant, ?_⟩
      have otherAtMinimum : other ∈ minimumLocantCandidates := by
        apply Finset.mem_filter.mpr
        refine ⟨otherInAll, ?_⟩
        omega
      exact selectedMaximumPriority.le otherAtMinimum
    · apply Or.inl
      omega

/-- With one candidate per physical locant, the independent RCT reference relation is
functional.  The hypothesis is essential for the suffix branch: two distinct suffix candidates
at the same locant would both satisfy the raw relation. -/
theorem isRCTReference_subsingleton_of_locantsUnique
    (candidates : List RCTReferenceCandidate)
    (locantsUnique : RCTCandidateLocantsUnique candidates)
    {left right : RCTReferenceCandidate}
    (leftReference : IsRCTReference candidates left)
    (rightReference : IsRCTReference candidates right) :
    left = right := by
  have candidatesNodup : candidates.Nodup :=
    List.Nodup.of_map RCTReferenceCandidate.locant locantsUnique
  have locantInjectiveOn :=
    (List.nodup_map_iff_inj_on candidatesNodup).mp locantsUnique
  rcases leftReference with ⟨leftPresent, leftSuffix | leftFallback⟩
  · rcases rightReference with ⟨rightPresent, rightSuffix | rightFallback⟩
    · apply locantInjectiveOn left leftPresent right rightPresent
      have leftLeRight := leftSuffix.2 right rightPresent rightSuffix.1
      have rightLeLeft := rightSuffix.2 left leftPresent leftSuffix.1
      omega
    · have leftNotSuffix := rightFallback.1 left leftPresent
      rw [leftSuffix.1] at leftNotSuffix
      contradiction
  · rcases rightReference with ⟨rightPresent, rightSuffix | rightFallback⟩
    · have rightNotSuffix := leftFallback.1 right rightPresent
      rw [rightSuffix.1] at rightNotSuffix
      contradiction
    · apply locantInjectiveOn left leftPresent right rightPresent
      have leftOrder := leftFallback.2 right rightPresent
      have rightOrder := rightFallback.2 left leftPresent
      rcases leftOrder with leftLess | ⟨leftLocantEq, _priority⟩
      · rcases rightOrder with rightLess | ⟨rightLocantEq, _priority⟩
        · omega
        · omega
      · exact leftLocantEq

/-- Executable finite selector for the independently stated RCT reference relation. -/
def rctReference? (candidates : List RCTReferenceCandidate) :
    Option RCTReferenceCandidate :=
  candidates.find? fun selected => decide (IsRCTReference candidates selected)

/-- On the chemically well-formed one-candidate-per-locant domain, executable selection is exact
for every proposed reference, not merely sound for the first match. -/
theorem rctReference?_eq_some_iff
    (candidates : List RCTReferenceCandidate)
    (locantsUnique : RCTCandidateLocantsUnique candidates)
    (selected : RCTReferenceCandidate) :
    rctReference? candidates = some selected ↔
      IsRCTReference candidates selected := by
  constructor
  · intro computed
    exact of_decide_eq_true
      (List.find?_some
        (p := fun candidate => decide (IsRCTReference candidates candidate)) computed)
  · intro selectedReference
    cases computed : rctReference? candidates with
    | none =>
        have rejected := List.find?_eq_none.mp computed selected selectedReference.1
        exact False.elim (rejected (decide_eq_true selectedReference))
    | some actual =>
        have actualReference : IsRCTReference candidates actual :=
          of_decide_eq_true
            (List.find?_some
              (p := fun candidate => decide (IsRCTReference candidates candidate)) computed)
        exact congrArg some
          (isRCTReference_subsingleton_of_locantsUnique candidates locantsUnique
            actualReference selectedReference)

/-- Under unique physical locants, the selector refuses exactly the empty candidate family. -/
theorem rctReference?_eq_none_iff_empty
    (candidates : List RCTReferenceCandidate)
    (locantsUnique : RCTCandidateLocantsUnique candidates) :
    rctReference? candidates = none ↔ candidates = [] := by
  constructor
  · intro refused
    by_contra nonempty
    obtain ⟨selected, selectedReference⟩ :=
      exists_isRCTReference_of_ne_nil candidates nonempty
    have selectedComputed :=
      (rctReference?_eq_some_iff candidates locantsUnique selected).mpr selectedReference
    rw [selectedComputed] at refused
    contradiction
  · rintro rfl
    rfl

/-- The corrected RCT ligand compiler emits `cis-to-reference` exactly for the independent
same-side relation. -/
theorem rctDescriptor_eq_cisToReference_iff
    (referenceSide ligandSide : RingSide) :
    rctDescriptor referenceSide ligandSide = some .cisToReference ↔
      RelativeRingSide referenceSide ligandSide .cis := by
  cases referenceSide <;> cases ligandSide <;>
    simp [rctDescriptor, RelativeRingSide]

/-- The corrected RCT ligand compiler emits `trans-to-reference` exactly for the independent
opposite-side relation. -/
theorem rctDescriptor_eq_transToReference_iff
    (referenceSide ligandSide : RingSide) :
    rctDescriptor referenceSide ligandSide = some .transToReference ↔
      RelativeRingSide referenceSide ligandSide .trans := by
  cases referenceSide <;> cases ligandSide <;>
    simp [rctDescriptor, RelativeRingSide]

/-- Missing RCT cis/trans output has one exhaustive spatial meaning: at least one of the two
positions lies on the ring mean plane. -/
theorem rctDescriptor_eq_none_iff_onMeanPlane
    (referenceSide ligandSide : RingSide) :
    rctDescriptor referenceSide ligandSide = none ↔
      referenceSide = .onMeanPlane ∨ ligandSide = .onMeanPlane := by
  cases referenceSide <;> cases ligandSide <;>
    simp [rctDescriptor]

end BlueBookP93.Cyclic
end TetraStereo.OneCenter
