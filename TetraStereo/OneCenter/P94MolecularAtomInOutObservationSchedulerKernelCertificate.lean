import TetraStereo.OneCenter.P94MolecularAtomInOutObservationScheduler
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
RED-first target for exhaustive canonical P-94 atom-participant observation construction.  The
certificate requires exact enumeration of both theta bridgehead axes, every bounded molecular
atom at every supplied spatial state, automatic acquisition of the opposite-endpoint coordinate,
and all ordered observation pairs.  Its completeness theorem requires every accepted canonical
atom observation over a supplied state to occur in the generated ledger.
-/

assert_kernel_only
  BlueBookP94.P94MolecularAtomInOutObservationScheduler.mem_bridgeheadAxes_iff
assert_kernel_only
  BlueBookP94.P94MolecularAtomInOutObservationScheduler.mem_atomObservationsForAxis_iff
assert_kernel_only
  BlueBookP94.P94MolecularAtomInOutObservationScheduler.mem_scheduledAtomInOutObservations_iff
assert_kernel_only
  BlueBookP94.P94MolecularAtomInOutObservationScheduler.acceptedCanonicalAtomObservation_mem_scheduled
assert_kernel_only
  BlueBookP94.P94MolecularAtomInOutObservationScheduler.mem_scheduledAtomInOutInputs_iff

end TetraStereo.OneCenter
