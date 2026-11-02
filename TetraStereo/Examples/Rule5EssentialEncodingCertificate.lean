import TetraStereo.Examples.Rule5EssentialInputCertificate

set_option autoImplicit false

namespace TetraStereo.Examples.Rule5EssentialDependency

open OneCenter
open OneCenter.ProductionCIPOccurrenceDiscovery
open OneCenter.DeclarativeCIP
open OneCenter.DeclarativeCIP.OccurrenceSystem
open OneCenter.DeclarativeCIP.ProductionOccurrenceRules456

def slotZero : Fin 4 := ⟨0, by decide⟩
def slotOne : Fin 4 := ⟨1, by decide⟩

theorem occurrences_slots :
    occurrencesAtRoot discovery root =
      finalOccurrence discovery root ::
        (occurrencesAtSlot discovery root slotZero ++
          occurrencesAtSlot discovery root slotOne ++
          occurrencesAtSlot discovery root sourceSlot ++
          occurrencesAtSlot discovery root otherSlot) := by
  simpa [slotZero, slotOne, sourceSlot, otherSlot] using
    occurrencesAtRoot_four_slots discovery root

theorem source_mem_slot : source ∈ occurrencesAtSlot discovery root sourceSlot := by
  unfold occurrencesAtSlot
  apply List.mem_map.mpr
  exact ⟨sourceDedupNode, by simp, rfl⟩

theorem other_mem_slot : other ∈ occurrencesAtSlot discovery root otherSlot := by
  unfold occurrencesAtSlot
  apply List.mem_map.mpr
  exact ⟨otherDedupNode, by simp, rfl⟩

theorem occurrences_decompose_around_sources :
    ∃ before between after,
      occurrencesAtRoot discovery root =
        before ++ (source :: (between ++ (other :: after))) := by
  rcases (List.mem_iff_append.mp source_mem_slot) with ⟨sourceBefore, sourceAfter, sourceEq⟩
  rcases (List.mem_iff_append.mp other_mem_slot) with ⟨otherBefore, otherAfter, otherEq⟩
  refine ⟨finalOccurrence discovery root ::
      (occurrencesAtSlot discovery root slotZero ++
        occurrencesAtSlot discovery root slotOne ++ sourceBefore),
    sourceAfter ++ otherBefore, otherAfter, ?_⟩
  rw [occurrences_slots, sourceEq, otherEq]
  simp only [List.cons_append, List.append_assoc]

theorem executable_state :
    executableStateFor? discovery fullState target = some encodedState := by
  unfold executableStateFor? encodedState
  rcases occurrences_decompose_around_sources with ⟨before, between, after, decomposition⟩
  exact encodeOccurrenceFacts?_two_active_on_list discovery fullState target source other
    sourceFact otherFact (occurrencesAtRoot discovery target.root) before between after
    (by simpa [target] using decomposition)
    (occurrencesAtRoot_nodup discovery target.root)
    source_depth_dependency
    (by exact ⟨rfl, by decide⟩)
    source_label_capable other_label_capable source_input_accepted other_input_accepted
    facts_keys_distinct fullState_inactive

theorem withoutSource_other : withoutSource other = some otherLabel := by
  have notSource : sameOccurrence other source = false := by
    cases equal : sameOccurrence other source with
    | false => rfl
    | true =>
        exact (source_ne_other ((sameOccurrence_eq_true_iff other source).mp equal).symm).elim
  simp only [withoutSource, notSource, Bool.false_eq_true, ↓reduceIte]
  have self : sameOccurrence other other = true :=
    (sameOccurrence_eq_true_iff other other).2 rfl
  simp only [fullState, notSource, self, Bool.false_eq_true, ↓reduceIte]

theorem withoutSource_inactive (occurrence : ProductionOccurrence)
    (different : occurrence ≠ other) : withoutSource occurrence = none := by
  by_cases sourceEqual : occurrence = source
  · subst occurrence
    simp [withoutSource, sameOccurrence]
  · have fullNone := fullState_inactive occurrence sourceEqual different
    have sourceUnequal : sameOccurrence occurrence source = false := by
      cases equal : sameOccurrence occurrence source with
      | false => rfl
      | true =>
          exact (sourceEqual ((sameOccurrence_eq_true_iff occurrence source).mp equal)).elim
    simp only [withoutSource, sourceUnequal, Bool.false_eq_true, ↓reduceIte]
    exact fullNone

theorem other_input_accepted_removed :
    inputFact? withoutSource other = some otherFact := by
  simp [inputFact?, withoutSource_other, otherLabel, labelOfOrdinaryFact, otherFact,
    factKey, other_node, ligandRootNode, other_ligand_atom, descriptorOfFact,
    descriptorSense, canonicalOccurrenceKey, RawMolecule.canonicalRoot]

theorem executable_state_removed :
    executableStateFor? discovery withoutSource target = some encodedStateRemoved := by
  unfold executableStateFor? encodedStateRemoved
  exact encodeOccurrenceFacts?_singleton_active discovery withoutSource target other otherFact
    (occurrencesAtRoot_nodup discovery target.root)
    (by simpa [target] using other_mem_occurrences)
    (by exact ⟨rfl, by decide⟩)
    other_label_capable other_input_accepted_removed withoutSource_inactive

end TetraStereo.Examples.Rule5EssentialDependency
