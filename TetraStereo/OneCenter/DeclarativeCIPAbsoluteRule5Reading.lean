import TetraStereo.OneCenter.DeclarativeCIPCompleteReadingSignature
import TetraStereo.OneCenter.LocalizedActualRule4bTableBridge
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Absolute Rule-5 observations decoded independently from molecular like/unlike readings.
The selected sense identifies which absolute descriptor a pairing names. Neither a runtime
key nor a runtime comparison appears in the molecular reading defined here. Padding is preserved;
supported nonchiral nodes, including r/s nodes, carry the zero seniority bit. -/

namespace TetraStereo.OneCenter.DeclarativeCIP
open Certificate.CanonicalSphereKey
open Rule4aTableBridge (code)
noncomputable section
open scoped Classical
universe u v

def mapObservationKey {α : Type u} {β : Type v} (f : α → β) (key : Key α) : Key β :=
  key.map (List.map (WithBot.map f))

theorem mapObservationKey_wellShaped {α : Type u} {β : Type v}
    (f : α → β) {W D : Nat} {key : Key α} (shaped : WellShaped W D key) :
    WellShaped W D (mapObservationKey f key) := by
  constructor
  · simpa [mapObservationKey] using shaped.1
  · intro k hk
    simpa [mapObservationKey] using shaped.2 k (by simpa [mapObservationKey] using hk)

theorem keyObservation_mapObservationKey {α : Type u} {β : Type v}
    (f : α → β) (key : Key α) (k slot : Nat) :
    keyObservation (mapObservationKey f key) k slot = WithBot.map f (keyObservation key k slot) := by
  unfold keyObservation mapObservationKey
  rw [show ([] : List (WithBot β)) = List.map (WithBot.map f) [] from rfl, List.getD_map]
  rw [show (⊥ : WithBot β) = WithBot.map f (⊥ : WithBot α) from rfl, List.getD_map]

theorem pathObservationOf_mapObservationKey {α : Type u} {β : Type v}
    (f : α → β) (key : Key α) (W D : Nat) (path : List Nat) :
    pathObservationOf W D (mapObservationKey f key) path =
      WithBot.map f (pathObservationOf W D key path) := by
  unfold pathObservationOf
  split_ifs
  · exact keyObservation_mapObservationKey f key _ _
  · rfl

def absoluteRule5Bit (own common : DescriptorSense) (observation : WithBot StereoLabel) : Nat :=
  seniorityOf (if common = .senior then own else own.mirror) observation

def absoluteRule5Label (own common : DescriptorSense) (value : StereoLabel) : StereoLabel :=
  (code (absoluteRule5Bit own common (value : WithBot StereoLabel)) : StereoCode)

theorem absoluteRule5Bit_like (own common : DescriptorSense) :
    absoluteRule5Bit own common likeObservation = if own = common then 1 else 0 := by
  cases own <;> cases common <;> simp [absoluteRule5Bit, seniorityOf_like, DescriptorSense.mirror]

theorem absoluteRule5Bit_unlike (own common : DescriptorSense) :
    absoluteRule5Bit own common unlikeObservation = if own = common then 0 else 1 := by
  cases own <;> cases common <;> simp [absoluteRule5Bit, seniorityOf_unlike, DescriptorSense.mirror]

theorem absoluteRule5Bit_nonchiral (own common : DescriptorSense) :
    absoluteRule5Bit own common ((⊥ : StereoLabel) : WithBot StereoLabel) = 0 := by
  simp [absoluteRule5Bit, seniorityOf, likeObservation, unlikeObservation]

theorem absoluteRule5Bit_absent (own common : DescriptorSense) :
    absoluteRule5Bit own common ⊥ = 0 := by
  simp [absoluteRule5Bit, seniorityOf, likeObservation, unlikeObservation]

/-- The decoded bit names the molecular absolute descriptor, rather than the chosen reference.
Noneligible nodes have bit zero, independently of any pseudoasymmetric observation. -/
theorem absoluteRule5Bit_molecular
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom)
    (own common : DescriptorSense) (node : graph.Node) :
    absoluteRule5Bit own common
      ((stereoLabel graph (readingEvidence molecule descriptorMap unit graph own)
        .rule4bLikeUnlikeDescriptorPairs node : StereoLabel) : WithBot StereoLabel) =
      if eligibleSense molecule descriptorMap unit graph node = some common then 1 else 0 := by
  cases h : eligibleSense molecule descriptorMap unit graph node with
  | none =>
      simpa [stereoLabel, stereoValue, readingEvidence, h, liftObservation] using
        absoluteRule5Bit_nonchiral own common
  | some observed =>
      cases own <;> cases common <;> cases observed <;>
        simp [absoluteRule5Bit, seniorityOf, stereoLabel, stereoValue, readingEvidence, h,
          liftObservation, DescriptorPairKind.ofSenses, DescriptorPairKind.priority,
          DescriptorSense.mirror, likeObservation, unlikeObservation, encodeReadings]

/-- The complete absolute R/S stream for one alternative, on the independent molecular layout.
No-reference branches retain their support and carry zero Rule-5 bits. -/
def absoluteRule5ReadingAt {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom) (W D : Nat)
    (reference : Option DescriptorSense) (common : DescriptorSense) : Key StereoLabel :=
  match reference with
  | some own => mapObservationKey (absoluteRule5Label own common)
      (readingAt molecule descriptorMap unit graph W D own)
  | none => mapObservationKey (fun _ : StereoLabel => (code 0 : StereoCode))
      (ofLex (completeReadingAt molecule descriptorMap unit graph W D none)).2

theorem absoluteRule5ReadingAt_iso
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) {left right : RootedDigraph Atom}
    (iso : RootedDigraph.Iso left right) (W D : Nat)
    (reference : Option DescriptorSense) (common : DescriptorSense) :
    absoluteRule5ReadingAt molecule descriptorMap unit right W D reference common =
      absoluteRule5ReadingAt molecule descriptorMap unit left W D reference common := by
  cases reference with
  | none => simp only [absoluteRule5ReadingAt, completeReadingAt_iso molecule descriptorMap unit iso]
  | some own =>
      simp only [absoluteRule5ReadingAt, readingAt_iso molecule descriptorMap unit iso W D own]

theorem absoluteRule5ReadingAt_eq_of_faithful
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (parent ligand : Atom)
    {left right : RootedDigraph Atom}
    (faithfulL : left.FaithfulExactExpansion molecule parent ligand)
    (faithfulR : right.FaithfulExactExpansion molecule parent ligand)
    (W D : Nat) (reference : Option DescriptorSense) (common : DescriptorSense) :
    absoluteRule5ReadingAt molecule descriptorMap unit left W D reference common =
      absoluteRule5ReadingAt molecule descriptorMap unit right W D reference common := by
  obtain ⟨iso⟩ := RootedDigraph.faithfulExactExpansion_unique_up_to_iso
    molecule parent ligand left right faithfulL faithfulR
  exact (absoluteRule5ReadingAt_iso molecule descriptorMap unit iso W D reference common).symm

end
end TetraStereo.OneCenter.DeclarativeCIP

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.mapObservationKey_wellShaped
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.pathObservationOf_mapObservationKey
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.absoluteRule5Bit_molecular
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.absoluteRule5ReadingAt_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.absoluteRule5ReadingAt_eq_of_faithful
