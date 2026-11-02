import TetraStereo.OneCenter.ExactOfficialRuleMajorKey

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeRingSourceSparseOrdering

open TetraStereo.OneCenter

abbrev ExactLayer := List (OfficialSparseEntry DeclarativeCIP.ExactAtomicNumber)

def carbonRootLayer : ExactLayer := [([], .ofNat 6)]
def chlorinatedArmLayer : ExactLayer := [([0], .ofNat 17), ([1], .ofNat 6), ([2], .ofNat 1)]
def saturatedArmLayer : ExactLayer := [([0], .ofNat 6), ([1], .ofNat 1), ([2], .ofNat 1)]

/-- Independent source Rule-1a comparison: the two directly attached carbons tie, then Cl versus C
settles the sorted next sphere. All later layers, including ring-duplicate layers, are irrelevant
to this strict comparison. This coordinate theorem does not itself assert that a returned source
key has these coordinates; that physical projection remains a separate required join. -/
theorem chlorinated_arm_above_saturated (leftTail rightTail : List ExactLayer) :
    OfficialRuleMajorKey.compareSparseLayers ExactOfficialRuleMajorKey.compareExactAtomicNumber
      (carbonRootLayer :: chlorinatedArmLayer :: leftTail)
      (carbonRootLayer :: saturatedArmLayer :: rightTail) = Ordering.gt ∧
    OfficialRuleMajorKey.compareSparseLayers ExactOfficialRuleMajorKey.compareExactAtomicNumber
      (carbonRootLayer :: saturatedArmLayer :: rightTail)
      (carbonRootLayer :: chlorinatedArmLayer :: leftTail) = Ordering.lt := by
  have tied : ExactOfficialRuleMajorKey.compareExactAtomicNumber (.ofNat 6) (.ofNat 6) =
      Ordering.eq := by decide +kernel
  have forward := ExactOfficialRuleMajorKey.compareExactAtomicNumber_ofNat_gt
    (left := 17) (right := 6) (by decide)
  have reverse := ExactOfficialRuleMajorKey.compareExactAtomicNumber_ofNat_lt
    (left := 6) (right := 17) (by decide)
  constructor <;>
    simp [OfficialRuleMajorKey.compareSparseLayers, OfficialRuleMajorKey.compareSparseLayer,
      OfficialRuleMajorKey.compareSparseEntry, OfficialRuleMajorKey.compareNat,
      carbonRootLayer, chlorinatedArmLayer, saturatedArmLayer, List.compareLex, compareLex,
      Ordering.byKey, flip, tied, forward, reverse]

end TetraStereo.UniversalProof.NativeRingSourceSparseOrdering
