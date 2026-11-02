import TetraStereo.OneCenter.LocalizedOrderedReferencePipeline
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter.LocalizedOrderedReference
open CertifiedLocalizedCIPInput

/-- The callable report enumerates precisely the actual detected centres, even if some are
physically unassignable and return `none`. -/
theorem analyze_center_indices (input : Input) :
    (analyze input).map Prod.fst =
      input.certified.canonicalTetrahedralCenters.map (fun center => center.1.1) :=
  report_centers input (referenceFacts input)

/-- Every detected centre contributes exactly one report position. -/
theorem analyze_indices_nodup (input : Input) :
    ((analyze input).map Prod.fst).Nodup := by
  rw [analyze_center_indices]
  unfold canonicalTetrahedralCenters
  simp only [List.map_map, Function.comp_def, List.attach_map_val]
  exact (Finset.sort_nodup input.certified.tetrahedralCenterSet (· ≤ ·)).map
    (fun _ _ h => Fin.ext h)

theorem analyze_length (input : Input) :
    (analyze input).length = input.certified.tetrahedralCenterSet.card := by
  rw [analyze_eq_orderedReferenceReport, List.length_map]
  unfold canonicalTetrahedralCenters
  rw [List.length_map, List.length_attach, Finset.length_sort]

/-- Membership of an actual result is equivalent to a detected centre and its own final
ordered-state value.  No independently supplied list of centres is accepted here. -/
theorem mem_analyze_iff (input : Input) (atom : Nat)
    (outcome : Option LocalizedAuxiliaryLabel) :
    (atom, outcome) ∈ analyze input ↔
      ∃ center : input.certified.TetrahedralCenter, center.1.1 = atom ∧
        input.certified.orderedReferenceState (carrierFuel input)
          (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center) =
          outcome := by
  rw [analyze_eq_orderedReferenceReport]
  constructor
  · intro member
    obtain ⟨center, _, equation⟩ := List.mem_map.1 member
    exact ⟨center, congrArg Prod.fst equation, congrArg Prod.snd equation⟩
  · rintro ⟨center, atomEq, outcomeEq⟩
    apply List.mem_map.2
    exact ⟨center,
      (input.certified.mem_canonicalTetrahedralCenters_iff center).2 center.2,
      Prod.ext atomEq outcomeEq⟩

theorem center_mem_analyze (input : Input) (center : input.certified.TetrahedralCenter) :
    (center.1.1, input.certified.orderedReferenceState (carrierFuel input)
      (input.certified.localizedFinalOccurrenceExecutable (carrierFuel input) center)) ∈
        analyze input :=
  (mem_analyze_iff input _ _).2 ⟨center, rfl, rfl⟩

end TetraStereo.OneCenter.LocalizedOrderedReference

assert_kernel_only TetraStereo.OneCenter.LocalizedOrderedReference.analyze_center_indices
assert_kernel_only TetraStereo.OneCenter.LocalizedOrderedReference.analyze_indices_nodup
assert_kernel_only TetraStereo.OneCenter.LocalizedOrderedReference.analyze_length
assert_kernel_only TetraStereo.OneCenter.LocalizedOrderedReference.mem_analyze_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedOrderedReference.center_mem_analyze
