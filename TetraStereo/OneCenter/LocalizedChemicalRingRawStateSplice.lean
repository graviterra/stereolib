import TetraStereo.OneCenter.LocalizedMarkedRetainedStateReader
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Two occurrence states can be combined by a predicate on full occurrence keys. Exact
first-match lookup is preserved on each side, including missing facts and duplicate keys.
Choosing the first root-branch path later permits two arm readers to share one state even
when their molecular atom sets overlap. Branch locality itself is not proved in this module. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingRawStateSplice

open CertifiedLocalizedCIPInput DeclarativeCIP LocalizedMarkedRetainedStateReader

def splice (chooseLeft : CanonicalOccurrenceKey → Bool)
    (left right : OccurrenceAuxState) : OccurrenceAuxState :=
  left.filter (fun fact => chooseLeft fact.key) ++
    right.filter (fun fact => !(chooseLeft fact.key))

theorem find_filtered_key (choose : CanonicalOccurrenceKey → Bool)
    (state : OccurrenceAuxState) (key : CanonicalOccurrenceKey) :
    (state.filter (fun fact => choose fact.key)).find? (fun fact => fact.key == key) =
      if choose key then state.find? (fun fact => fact.key == key) else none := by
  induction state with
  | nil => simp
  | cons fact rest ih =>
      by_cases same : fact.key = key
      · cases selected : choose key <;> simp [same, selected, ih]
      · cases selected : choose fact.key <;> simp [same, selected, ih]

/-- Splicing preserves the exact raw lookup; no state-uniqueness premise is required. -/
theorem find_splice (chooseLeft : CanonicalOccurrenceKey → Bool)
    (left right : OccurrenceAuxState) (key : CanonicalOccurrenceKey) :
    (splice chooseLeft left right).find? (fun fact => fact.key == key) =
      if chooseLeft key then left.find? (fun fact => fact.key == key)
      else right.find? (fun fact => fact.key == key) := by
  unfold splice
  rw [List.find?_append, find_filtered_key chooseLeft left key,
    find_filtered_key (fun k => !(chooseLeft k)) right key]
  cases chooseLeft key <;> simp

theorem rawStateFact_splice (chooseLeft : CanonicalOccurrenceKey → Bool)
    (left right : OccurrenceAuxState) {n : Nat} (unit : OccurrenceUnit (Fin n)) :
    rawStateFact? (splice chooseLeft left right) unit =
      if chooseLeft (rawOccurrenceKey unit) then rawStateFact? left unit
      else rawStateFact? right unit :=
  find_splice chooseLeft left right (rawOccurrenceKey unit)

theorem rawStateDescriptorMap_splice (input : CertifiedLocalizedCIPInput)
    (chooseLeft : CanonicalOccurrenceKey → Bool) (left right : OccurrenceAuxState)
    (unit : DetectedOccurrence input.moleculeGraph) :
    rawStateDescriptorMap input (splice chooseLeft left right) unit =
      if chooseLeft (rawOccurrenceKey unit.1) then rawStateDescriptorMap input left unit
      else rawStateDescriptorMap input right unit := by
  unfold rawStateDescriptorMap
  rw [rawStateFact_splice]
  cases selected : chooseLeft (rawOccurrenceKey unit.1) <;> rfl

end TetraStereo.OneCenter.LocalizedChemicalRingRawStateSplice

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRawStateSplice.find_filtered_key
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRawStateSplice.find_splice
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRawStateSplice.rawStateFact_splice
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRawStateSplice.rawStateDescriptorMap_splice
