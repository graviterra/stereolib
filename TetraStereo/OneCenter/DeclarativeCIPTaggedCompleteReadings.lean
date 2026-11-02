import TetraStereo.OneCenter.DeclarativeCIPCompleteReadingSignature
import TetraStereo.OneCenter.DeclarativeCIPCompleteReadingProjection
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Independent complete readings with reference identity retained.

The untagged complete list is the descending list of Rule-4b/4c values.  For a full tie, the
production rankReadings keeps its input order [R, S]; this file makes that stable convention
explicit as senior-sense first while retaining each alternative's tag. -/

namespace TetraStereo.OneCenter.DeclarativeCIP
noncomputable section
open scoped Classical
universe u

abbrev TaggedCompleteReading := Option DescriptorSense × CompleteReadingKey

section Reading
variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom)

/-- Reference identities in the independent complete-reading order.  Empty and singleton
populations keep their selected identity; two alternatives sort by complete Rule-4b/4c value,
with the senior sense first on equality. -/
def taggedAlternativeReferencesAt (W D : Nat) : List (Option DescriptorSense) :=
  match referenceSelection molecule descriptorMap unit graph with
  | .empty => [none]
  | .one sense => [some sense]
  | .both =>
      let senior := completeReadingAt molecule descriptorMap unit graph W D (some .senior)
      let junior := completeReadingAt molecule descriptorMap unit graph W D (some .junior)
      if compare senior junior = .lt then [some .junior, some .senior]
      else [some .senior, some .junior]

/-- The complete observable paired with its selected reference sense. -/
def taggedCompleteReadingsAt (W D : Nat) : List TaggedCompleteReading :=
  (taggedAlternativeReferencesAt molecule descriptorMap unit graph W D).map fun reference =>
    (reference, completeReadingAt molecule descriptorMap unit graph W D reference)

/-- Forgetting tags recovers the ordinary complete-reading value list. -/
theorem taggedAlternativeReferencesAt_projection (W D : Nat) :
    (taggedAlternativeReferencesAt molecule descriptorMap unit graph W D).map
        (fun reference => completeReadingAt molecule descriptorMap unit graph W D reference) =
      completeReadingsAt molecule descriptorMap unit graph W D := by
  unfold taggedAlternativeReferencesAt completeReadingsAt
  cases selection : referenceSelection molecule descriptorMap unit graph with
  | empty => simp [completeReadingAt]
  | one sense => simp
  | both =>
      let senior := completeReadingAt molecule descriptorMap unit graph W D (some .senior)
      let junior := completeReadingAt molecule descriptorMap unit graph W D (some .junior)
      have pair := completeReading_descendingPair senior junior
      have mapped :
          (if compare senior junior = .lt then [some .junior, some .senior]
            else [some .senior, some .junior]).map
              (fun reference => completeReadingAt molecule descriptorMap unit graph W D reference) =
            if compare senior junior = .lt then [junior, senior] else [senior, junior] := by
        by_cases h : compare senior junior = .lt
        · simp only [if_pos h, List.map_cons, List.map_nil, completeReadingAt]
          rfl
        · simp only [if_neg h, List.map_cons, List.map_nil, completeReadingAt]
          rfl
      rw [mapped]
      exact pair

/-- Projecting tagged complete readings to their values recovers the untagged list. -/
theorem taggedCompleteReadingsAt_projection (W D : Nat) :
    (taggedCompleteReadingsAt molecule descriptorMap unit graph W D).map Prod.snd =
      completeReadingsAt molecule descriptorMap unit graph W D := by
  simpa only [taggedCompleteReadingsAt, List.map_map, Function.comp_def] using
    taggedAlternativeReferencesAt_projection molecule descriptorMap unit graph W D

end Reading

section Iso
variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) {left right : RootedDigraph Atom}
  (iso : RootedDigraph.Iso left right)

include iso in
theorem taggedAlternativeReferencesAt_iso (W D : Nat) :
    taggedAlternativeReferencesAt molecule descriptorMap unit right W D =
      taggedAlternativeReferencesAt molecule descriptorMap unit left W D := by
  unfold taggedAlternativeReferencesAt
  rw [referenceSelection_iso molecule descriptorMap unit iso]
  cases selection : referenceSelection molecule descriptorMap unit left with
  | empty => rfl
  | one sense => rfl
  | both =>
      rw [completeReadingAt_iso molecule descriptorMap unit iso W D (some .senior),
        completeReadingAt_iso molecule descriptorMap unit iso W D (some .junior)]

include iso in
theorem taggedCompleteReadingsAt_iso (W D : Nat) :
    taggedCompleteReadingsAt molecule descriptorMap unit right W D =
      taggedCompleteReadingsAt molecule descriptorMap unit left W D := by
  unfold taggedCompleteReadingsAt
  rw [taggedAlternativeReferencesAt_iso molecule descriptorMap unit iso W D]
  apply List.map_congr_left
  intro reference _
  congr 1
  exact completeReadingAt_iso molecule descriptorMap unit iso W D reference

end Iso

section Faithful
variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) (externalParent ligand : Atom)
  {left right : RootedDigraph Atom}
  (faithfulL : RootedDigraph.FaithfulExactExpansion molecule externalParent ligand left)
  (faithfulR : RootedDigraph.FaithfulExactExpansion molecule externalParent ligand right)

include faithfulL faithfulR in
theorem taggedAlternativeReferencesAt_eq_of_faithful (W D : Nat) :
    taggedAlternativeReferencesAt molecule descriptorMap unit left W D =
      taggedAlternativeReferencesAt molecule descriptorMap unit right W D := by
  obtain ⟨iso⟩ := RootedDigraph.faithfulExactExpansion_unique_up_to_iso
    molecule externalParent ligand left right faithfulL faithfulR
  exact (taggedAlternativeReferencesAt_iso molecule descriptorMap unit iso W D).symm

include faithfulL faithfulR in
theorem taggedCompleteReadingsAt_eq_of_faithful (W D : Nat) :
    taggedCompleteReadingsAt molecule descriptorMap unit left W D =
      taggedCompleteReadingsAt molecule descriptorMap unit right W D := by
  obtain ⟨iso⟩ := RootedDigraph.faithfulExactExpansion_unique_up_to_iso
    molecule externalParent ligand left right faithfulL faithfulR
  exact (taggedCompleteReadingsAt_iso molecule descriptorMap unit iso W D).symm

end Faithful
end
end TetraStereo.OneCenter.DeclarativeCIP

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.taggedAlternativeReferencesAt_projection
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.taggedCompleteReadingsAt_projection
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.taggedAlternativeReferencesAt_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.taggedCompleteReadingsAt_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.taggedAlternativeReferencesAt_eq_of_faithful
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.taggedCompleteReadingsAt_eq_of_faithful
