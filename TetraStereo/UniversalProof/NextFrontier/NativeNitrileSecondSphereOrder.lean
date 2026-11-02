import TetraStereo.UniversalProof.SecondSphereOwnSourceOrdering

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileSecondSphereOrder

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput

abbrev ExactLayer := List (OfficialSparseEntry DeclarativeCIP.ExactAtomicNumber)

def carbonRootLayer : ExactLayer := [([], .ofNat 6)]
def nitrileChildLayer : ExactLayer := [([0], .ofNat 7), ([1], .ofNat 7), ([2], .ofNat 7)]
def aminoalkylChildLayer : ExactLayer := [([0], .ofNat 7), ([1], .ofNat 6), ([2], .ofNat 1)]

/-- In the independent exact source representation, the first C ties and the first N ties.
The second N wins over C; arbitrary deeper layers cannot affect the result. Binding that second
entry to a generated multiple-bond duplicate is a separate physical projection obligation. -/
theorem second_sphere_sparse_both (nitrileTail aminoalkylTail : List ExactLayer) :
    OfficialRuleMajorKey.compareSparseLayers ExactOfficialRuleMajorKey.compareExactAtomicNumber
      (carbonRootLayer :: nitrileChildLayer :: nitrileTail)
      (carbonRootLayer :: aminoalkylChildLayer :: aminoalkylTail) = Ordering.gt ∧
    OfficialRuleMajorKey.compareSparseLayers ExactOfficialRuleMajorKey.compareExactAtomicNumber
      (carbonRootLayer :: aminoalkylChildLayer :: aminoalkylTail)
      (carbonRootLayer :: nitrileChildLayer :: nitrileTail) = Ordering.lt := by
  have carbonTie : ExactOfficialRuleMajorKey.compareExactAtomicNumber
      (.ofNat 6) (.ofNat 6) = Ordering.eq := by decide +kernel
  have nitrogenTie : ExactOfficialRuleMajorKey.compareExactAtomicNumber
      (.ofNat 7) (.ofNat 7) = Ordering.eq := by decide +kernel
  have nitrogenAbove := ExactOfficialRuleMajorKey.compareExactAtomicNumber_ofNat_gt
    (left := 7) (right := 6) (by decide)
  have carbonBelow := ExactOfficialRuleMajorKey.compareExactAtomicNumber_ofNat_lt
    (left := 6) (right := 7) (by decide)
  constructor <;>
    simp [OfficialRuleMajorKey.compareSparseLayers, OfficialRuleMajorKey.compareSparseLayer,
      OfficialRuleMajorKey.compareSparseEntry, OfficialRuleMajorKey.compareNat,
      carbonRootLayer, nitrileChildLayer, aminoalkylChildLayer, List.compareLex, compareLex,
      Ordering.byKey, flip, carbonTie, nitrogenTie, nitrogenAbove, carbonBelow]

/-- Generic coordinate transport for the real source-key comparator. These projection premises
are explicit local interfaces; they are not family assumptions or a final model theorem. -/
theorem second_sphere_source_keys_both (source : AuthoritativeChemicalInput)
    (nitrile aminoalkyl : source.AromaticCanonicalOccurrenceRule3Through5Key)
    (nitrileTail aminoalkylTail : List ExactLayer)
    (nitrileProjection : ExactOfficialRuleMajorKey.exactRule1aLayers
      source.molecule.toLocalizedMoleculeGraph nitrile.rule3.constitutional.sourceNodes =
      carbonRootLayer :: nitrileChildLayer :: nitrileTail)
    (aminoalkylProjection : ExactOfficialRuleMajorKey.exactRule1aLayers
      source.molecule.toLocalizedMoleculeGraph aminoalkyl.rule3.constitutional.sourceNodes =
      carbonRootLayer :: aminoalkylChildLayer :: aminoalkylTail) :
    source.compareAromaticCanonicalOccurrenceRule3Through5Keys nitrile aminoalkyl = Ordering.gt ∧
    source.compareAromaticCanonicalOccurrenceRule3Through5Keys aminoalkyl nitrile = Ordering.lt := by
  have strict := second_sphere_sparse_both nitrileTail aminoalkylTail
  constructor <;>
    simp [compareAromaticCanonicalOccurrenceRule3Through5Keys,
      compareAromaticCanonicalUncancelledRule3SpatialKeys,
      ExactOfficialRuleMajorKey.compare, ExactOfficialRuleMajorKey.compareAddressedSources,
      Ordering.byKey, compareLex, nitrileProjection, aminoalkylProjection, strict.1, strict.2]

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileSecondSphereOrder
