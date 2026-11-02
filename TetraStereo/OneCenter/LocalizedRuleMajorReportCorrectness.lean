import TetraStereo.OneCenter.LocalizedRuleMajorFinalCenterOutcome
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The actual rule-major report enumerates every detected centre exactly once and returns
exactly its independent optional complete-root outcome, evaluated against the report's own
generated molecular evidence. Coordinate availability and nondegeneracy are explicit.
This is a final-centre report theorem, not an all-auxiliary-occurrence chemical fixed point. -/

namespace TetraStereo.OneCenter.LocalizedRuleMajorReference
open CertifiedLocalizedCIPInput DeclarativeCIP
noncomputable section
open scoped Classical

theorem analyze_center_indices (input : Input) :
    (analyze input).map Prod.fst =
      input.certified.canonicalTetrahedralCenters.map (fun center => center.1.1) :=
  report_centers input (referenceFacts input)

theorem analyze_indices_nodup (input : Input) :
    ((analyze input).map Prod.fst).Nodup := by
  rw [analyze_center_indices]
  unfold canonicalTetrahedralCenters
  simp only [List.map_map, Function.comp_def, List.attach_map_val]
  exact (Finset.sort_nodup input.certified.tetrahedralCenterSet (· ≤ ·)).map
    (fun _ _ h => Fin.ext h)

theorem analyze_length (input : Input) :
    (analyze input).length = input.certified.tetrahedralCenterSet.card := by
  rw [analyze_eq_referenceReport, List.length_map]
  unfold canonicalTetrahedralCenters
  rw [List.length_map, List.length_attach, Finset.length_sort]

theorem mem_analyze_iff (input : Input) (atom : Nat)
    (outcome : Option LocalizedAuxiliaryLabel) :
    (atom, outcome) ∈ analyze input ↔
      ∃ center : input.certified.TetrahedralCenter, center.1.1 = atom ∧
        referenceState input
          (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center) =
          outcome := by
  rw [analyze_eq_referenceReport]
  constructor
  · intro member
    obtain ⟨center, _, equation⟩ := List.mem_map.1 member
    exact ⟨center, congrArg Prod.fst equation, congrArg Prod.snd equation⟩
  · rintro ⟨center, atomEq, outcomeEq⟩
    apply List.mem_map.2
    exact ⟨center,
      (input.certified.mem_canonicalTetrahedralCenters_iff center).2 center.2,
      Prod.ext atomEq outcomeEq⟩

/-- Both returned labels and refusals agree with an independently defined optional judgment. -/
theorem generated_referenceState_eq_iff_root_outcome
    (input : Input) (center : input.certified.TetrahedralCenter)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (points : Fin 4 → CartesianPoint3)
    (pointsAvailable : ∀ index : Fin 4,
      input.certified.spatialPointAt?
        (input.certified.canonicalLigandAtom center index) = some (points index))
    (nonzero : CartesianPoint3.orientedVolume (points 0) (points 1)
      (points 2) (points 3) ≠ 0)
    (outcome : Option LocalizedAuxiliaryLabel) :
    referenceState input (generatedTarget input center) = outcome ↔
      CompleteRootOutcome
        (generatedFrameComparison input center singleBonded acyclic).data.fullKey
        points outcome := by
  cases outcome with
  | some descriptor =>
    exact generated_referenceState_some_iff_root_judgment input center singleBonded acyclic
      points pointsAvailable nonzero descriptor
  | none =>
    change _ = none ↔ ¬ ∃ descriptor, CompleteRootDescriptorJudgment _ points descriptor
    constructor
    · intro refused ⟨descriptor, judgment⟩
      have assigned := (generated_referenceState_some_iff_root_judgment input center
        singleBonded acyclic points pointsAvailable nonzero descriptor).2 judgment
      rw [refused] at assigned
      cases assigned
    · intro noJudgment
      cases actual : referenceState input (generatedTarget input center) with
      | none => rfl
      | some descriptor =>
        exact False.elim (noJudgment ⟨descriptor,
          (generated_referenceState_some_iff_root_judgment input center singleBonded acyclic
            points pointsAvailable nonzero descriptor).1 actual⟩)

/-- Every reported pair is precisely a detected centre and its independent optional outcome.
The molecular keys use the actual generated auxiliary map, not supplied auxiliary labels. -/
theorem mem_analyze_iff_independent_outcome
    (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (points : input.certified.TetrahedralCenter → Fin 4 → CartesianPoint3)
    (pointsAvailable : ∀ (center : input.certified.TetrahedralCenter) (index : Fin 4),
      input.certified.spatialPointAt?
        (input.certified.canonicalLigandAtom center index) = some (points center index))
    (nonzero : ∀ center : input.certified.TetrahedralCenter,
      CartesianPoint3.orientedVolume (points center 0) (points center 1)
        (points center 2) (points center 3) ≠ 0)
    (atom : Nat) (outcome : Option LocalizedAuxiliaryLabel) :
    (atom, outcome) ∈ analyze input ↔
      ∃ center : input.certified.TetrahedralCenter, center.1.1 = atom ∧
        CompleteRootOutcome
          (generatedFrameComparison input center singleBonded acyclic).data.fullKey
          (points center) outcome := by
  rw [mem_analyze_iff]
  apply exists_congr
  intro center
  apply and_congr_right
  intro _
  rw [input.certified.localizedFinalOccurrenceExecutable_eq_localizedFinalOccurrence]
  exact generated_referenceState_eq_iff_root_outcome input center singleBonded acyclic
    (points center) (pointsAvailable center) (nonzero center) outcome

/-- The full callable report has the actual detected inventory, no duplicate centres, and
exact agreement with independent final-centre judgments, including refusal. -/
theorem analyze_complete_root_outcomes
    (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (points : input.certified.TetrahedralCenter → Fin 4 → CartesianPoint3)
    (pointsAvailable : ∀ (center : input.certified.TetrahedralCenter) (index : Fin 4),
      input.certified.spatialPointAt?
        (input.certified.canonicalLigandAtom center index) = some (points center index))
    (nonzero : ∀ center : input.certified.TetrahedralCenter,
      CartesianPoint3.orientedVolume (points center 0) (points center 1)
        (points center 2) (points center 3) ≠ 0) :
    (analyze input).map Prod.fst =
        input.certified.canonicalTetrahedralCenters.map (fun center => center.1.1) ∧
      ((analyze input).map Prod.fst).Nodup ∧
      (analyze input).length = input.certified.tetrahedralCenterSet.card ∧
      ∀ atom outcome, (atom, outcome) ∈ analyze input ↔
        ∃ center : input.certified.TetrahedralCenter, center.1.1 = atom ∧
          CompleteRootOutcome
            (generatedFrameComparison input center singleBonded acyclic).data.fullKey
            (points center) outcome := by
  exact ⟨analyze_center_indices input, analyze_indices_nodup input, analyze_length input,
    mem_analyze_iff_independent_outcome input singleBonded acyclic points pointsAvailable nonzero⟩

end
end TetraStereo.OneCenter.LocalizedRuleMajorReference

assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.analyze_center_indices
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.analyze_indices_nodup
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.analyze_length
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.mem_analyze_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.generated_referenceState_eq_iff_root_outcome
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.mem_analyze_iff_independent_outcome
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.analyze_complete_root_outcomes
