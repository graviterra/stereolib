import TetraStereo.OneCenter.SmilesTetrahedral

set_option autoImplicit false

namespace TetraStereo.Examples.SmilesTetrahedralKernelProof

open TetraStereo.OneCenter

set_option maxHeartbeats 1000000 in
theorem aromatic_parities_opposite :
    (match
        smilesTetrahedralDescriptorAt? "CC(C)Cc1ccc(cc1)[C@@H](C)C(=O)O" 10,
        smilesTetrahedralDescriptorAt? "CC(C)Cc1ccc(cc1)[C@H](C)C(=O)O" 10 with
      | some left, some right => left != right
      | _, _ => false) = true := by
  rfl

end TetraStereo.Examples.SmilesTetrahedralKernelProof
