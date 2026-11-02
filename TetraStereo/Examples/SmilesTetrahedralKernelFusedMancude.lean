import TetraStereo.OneCenter.SmilesTetrahedral

set_option autoImplicit false

namespace TetraStereo.Examples.SmilesTetrahedralKernelProof

open TetraStereo.OneCenter

set_option maxHeartbeats 1000000 in
theorem fused_mancude_assignment :
    (smilesTetrahedralDescriptorAt? "C1=CC2=C([C@@]13N=CCO3)C=CC=C2" 4 =
      some RS.R) = true := by
  decide

end TetraStereo.Examples.SmilesTetrahedralKernelProof
