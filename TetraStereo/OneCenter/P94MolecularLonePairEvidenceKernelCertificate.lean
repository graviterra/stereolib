import TetraStereo.OneCenter.P94MolecularLonePairEvidence
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
RED-first target for molecule-linked P-94 lone-pair evidence.  The certificate requires exact
finite lookup, raw-index boundedness, checked main-group electron balance, exact composition with
the graph-derived in/out premises, and downstream recovery of certified evidence from every
accepted lone-pair participant.
-/

assert_kernel_only BlueBookP94.P94MolecularLonePair.lonePairAt?_eq_true_iff
assert_kernel_only BlueBookP94.P94MolecularLonePair.hasLonePairAt_atom_bounded
assert_kernel_only BlueBookP94.P94MolecularLonePair.hasLonePairAt_mainGroupLewis
assert_kernel_only
  BlueBookP94.P94MolecularLonePair.graphElectronicPremises_bicyclicFramework_iff
assert_kernel_only
  BlueBookP94.P94MolecularLonePair.graphElectronicPremises_atomInFramework_iff
assert_kernel_only
  BlueBookP94.P94MolecularLonePair.graphElectronicPremises_lonePairAt_iff
assert_kernel_only
  BlueBookP94.P94MolecularLonePair.valid_lonePairParticipant_has_certified_evidence

end TetraStereo.OneCenter
