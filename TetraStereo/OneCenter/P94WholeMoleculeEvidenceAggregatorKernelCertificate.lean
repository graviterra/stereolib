import TetraStereo.OneCenter.P94WholeMoleculeEvidenceAggregator
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
RED-first kernel target for the whole-molecule P-94 evidence aggregator.

The target requires one outcome for every scheduled ring request and every explicitly supplied
twist/in-out request, exact acceptance/refusal semantics, a sound independent assignment relation,
global duplicate freedom, and exact count-one/count-zero closure.  It deliberately does not claim
that molecular coordinates alone synthesize direct-rotation ledgers or bicyclic/electron premises.
-/

assert_kernel_only BlueBookP94.P94MolecularAggregator.analyzeRequest_outcome_request
assert_kernel_only BlueBookP94.P94MolecularAggregator.analyzeRequest_correct
assert_kernel_only BlueBookP94.P94MolecularAggregator.molecularOutcomes_map_request
assert_kernel_only BlueBookP94.P94MolecularAggregator.molecularOutcomes_all_correct
assert_kernel_only BlueBookP94.P94MolecularAggregator.molecularAssignments_mem_iff_independent
assert_kernel_only BlueBookP94.P94MolecularAggregator.molecularAssignments_nodup
assert_kernel_only BlueBookP94.P94MolecularAggregator.molecularAssignment_count_eq_one_iff
assert_kernel_only BlueBookP94.P94MolecularAggregator.molecularAssignment_count_eq_zero_iff

end TetraStereo.OneCenter
