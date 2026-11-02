import TetraStereo.OneCenter.DeclarativeCIPAbsoluteRule5Reading
import TetraStereo.OneCenter.DeclarativeCIPTaggedCompleteReadings
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Complete independent Rule-5 observations in the established alternative order. Each key
uses the alternative's own reference, while `common` selects the absolute R or S convention.
The absent-reference alternative is retained and carries the zero-bit Rule-4c observation. -/

namespace TetraStereo.OneCenter.DeclarativeCIP
open Certificate.CanonicalSphereKey (Key)
noncomputable section
universe u

section Reading
variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom)

/-- Every Rule-5 observation, in the independent complete Rule-4b/4c alternative order. -/
def completeRule5ReadingsAt (W D : Nat) (common : DescriptorSense) : List (Key StereoLabel) :=
  (taggedAlternativeReferencesAt molecule descriptorMap unit graph W D).map fun reference =>
    absoluteRule5ReadingAt molecule descriptorMap unit graph W D reference common

theorem completeRule5ReadingsAt_length (W D : Nat) (common : DescriptorSense) :
    (completeRule5ReadingsAt molecule descriptorMap unit graph W D common).length =
      (taggedAlternativeReferencesAt molecule descriptorMap unit graph W D).length := by
  simp [completeRule5ReadingsAt]

theorem completeRule5ReadingsAt_iso
    {left right : RootedDigraph Atom} (iso : RootedDigraph.Iso left right)
    (W D : Nat) (common : DescriptorSense) :
    completeRule5ReadingsAt molecule descriptorMap unit right W D common =
      completeRule5ReadingsAt molecule descriptorMap unit left W D common := by
  unfold completeRule5ReadingsAt
  rw [taggedAlternativeReferencesAt_iso molecule descriptorMap unit iso W D]
  apply List.map_congr_left
  intro reference _
  exact absoluteRule5ReadingAt_iso molecule descriptorMap unit iso W D reference common

end Reading

section Faithful
variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) (externalParent ligand : Atom)
  {left right : RootedDigraph Atom}
  (faithfulL : RootedDigraph.FaithfulExactExpansion molecule externalParent ligand left)
  (faithfulR : RootedDigraph.FaithfulExactExpansion molecule externalParent ligand right)

include faithfulL faithfulR in
theorem completeRule5ReadingsAt_eq_of_faithful (W D : Nat) (common : DescriptorSense) :
    completeRule5ReadingsAt molecule descriptorMap unit left W D common =
      completeRule5ReadingsAt molecule descriptorMap unit right W D common := by
  obtain ⟨iso⟩ := RootedDigraph.faithfulExactExpansion_unique_up_to_iso
    molecule externalParent ligand left right faithfulL faithfulR
  exact (completeRule5ReadingsAt_iso molecule descriptorMap unit iso W D common).symm

end Faithful
end
end TetraStereo.OneCenter.DeclarativeCIP

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.completeRule5ReadingsAt_length
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.completeRule5ReadingsAt_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.completeRule5ReadingsAt_eq_of_faithful
