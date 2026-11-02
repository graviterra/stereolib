import TetraStereo.Examples.SmilesTetrahedralKernelCyclicBase

set_option autoImplicit false

namespace TetraStereo.Examples.SmilesTetrahedralKernelProof

open TetraStereo.OneCenter

set_option maxHeartbeats 1000000 in
theorem cyclicAutomorphism_rank_none :
    cyclicAutomorphismExpanded.rankBranchPositions?
        (analysisFuel cyclicAutomorphismExpanded) 7
        (cyclicAutomorphismExpanded.ligandsWithLonePair 7) = none := by
  decide

end TetraStereo.Examples.SmilesTetrahedralKernelProof
