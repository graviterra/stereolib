import TetraStereo.Examples.SmilesTetrahedralKernelCyclicRank
import TetraStereo.Examples.SmilesTetrahedralKernelCyclicUnresolved
import TetraStereo.Examples.SmilesTetrahedralKernelCyclicTied

set_option autoImplicit false

namespace TetraStereo.Examples.SmilesTetrahedralKernelProof

open TetraStereo.OneCenter

theorem cyclicAutomorphism_fallback_none :
    cyclicAutomorphismExpanded.rankBranchPositionsWithSinglePairedFallback?
        (analysisFuel cyclicAutomorphismExpanded) 7
        (cyclicAutomorphismExpanded.ligandsWithLonePair 7) = none := by
  decide

theorem cyclicAutomorphism_outcome :
    cyclicAutomorphismExpanded.tetrahedralOutcome
        (analysisFuel cyclicAutomorphismExpanded) 7 =
      StereoOutcome.refused StereoRefusal.notStereogenic := by
  unfold RawMolecule.tetrahedralOutcome
  simp only [cyclicAutomorphism_rank_none, cyclicAutomorphism_fallback_none,
    cyclicAutomorphism_tied_true]
  rfl

theorem cyclicAutomorphism_parsed_none :
    parsedTetrahedralDescriptorAt? cyclicAutomorphismParsed 7 = none := by
  unfold parsedTetrahedralDescriptorAt?
  change expandedTetrahedralDescriptorAt? cyclicAutomorphismExpanded 7 = none
  unfold expandedTetrahedralDescriptorAt?
  have massesKnown : cyclicAutomorphismExpanded.rule2MassesKnown? = true := by
    decide
  simp [massesKnown, cyclicAutomorphism_outcome]

theorem cyclic_automorphism_refusal :
    (smilesTetrahedralDescriptorAt?
      "OC=1C=CC=CC1[C@H](C2=CC=CC=C2O)O" 7 = none) = true := by
  unfold smilesTetrahedralDescriptorAt?
  rw [cyclicAutomorphism_parse]
  apply propext
  constructor
  · intro _
    trivial
  · intro _
    exact cyclicAutomorphism_parsed_none

end TetraStereo.Examples.SmilesTetrahedralKernelProof
