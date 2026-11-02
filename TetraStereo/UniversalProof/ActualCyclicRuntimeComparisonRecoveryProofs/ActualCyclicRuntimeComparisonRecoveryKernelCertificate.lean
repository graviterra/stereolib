import TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery
import TetraStereo.KernelOnly

set_option autoImplicit false

























/- Both-cyclic is the exact complement of the acyclicity disjunction. -/
assert_kernel_only
  TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery.bothCyclic_iff_not_acyclicDisjunction

/- Gate is `false` at a tied constitutional result, with no acyclicity premise. -/
assert_kernel_only
  TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery.occurrenceRootsProvedAutomorphic_eq_false_of_compiled_eq

/- Retained sufficient condition: one acyclic endpoint refutes the gate. -/
assert_kernel_only
  TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery.occurrenceRootsProvedAutomorphic_eq_false_of_acyclic

/- Exact necessary condition: a `true` gate implies both endpoints cyclic. -/
assert_kernel_only
  TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery.occurrenceRootsProvedAutomorphic_eq_true_implies_bothCyclic

/- Exact necessary condition: a `true` gate implies a strict constitutional result. -/
assert_kernel_only
  TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery.occurrenceRootsProvedAutomorphic_eq_true_implies_compiled_ne_eq

/- Packaged necessary condition `GateCanFire`. -/
assert_kernel_only
  TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery.occurrenceRootsProvedAutomorphic_eq_true_implies_gateCanFire

/- General fast-stage factorization: successful raw comparison plus a `false` gate is returned. -/
assert_kernel_only
  TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery.certifiedConstitutionalStage?_eq_of_gate_false

/- General authoritative-stage factorization. -/
assert_kernel_only
  TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery.certifiedConstitutionalStageAuthoritative?_eq_of_gate_false

/- Tied-result pass-through on the fast path, arbitrary cyclicity. -/
assert_kernel_only
  TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery.certifiedConstitutionalStage?_eq_of_constitutional_eq

/- Tied-result pass-through on the uncapped authoritative path. -/
assert_kernel_only
  TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery.certifiedConstitutionalStageAuthoritative?_eq_of_constitutional_eq

/- The fast conservative stage cannot refuse at a successful raw Rule-2 tie. -/
assert_kernel_only
  TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery.certifiedConstitutionalStage?_ne_none_of_constitutional_eq

/- The uncapped authoritative stage cannot refuse at a successful raw Rule-2 tie. -/
assert_kernel_only
  TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery.certifiedConstitutionalStageAuthoritative?_ne_none_of_constitutional_eq

/- The witness ring has three atoms. -/
assert_kernel_only
  TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery.ringWitness_atomCount

/- The witness ring is well-formed. -/
assert_kernel_only
  TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery.ringWitness_wellFormed

/- The witness ring has unique unordered edge records. -/
assert_kernel_only
  TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery.ringWitness_bondRecordsUnique

/- The witness ring is admissible. -/
assert_kernel_only
  TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery.ringWitness_admissible

/- The witness written-neighbour view is exact. -/
assert_kernel_only
  TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery.ringWitness_writtenNeighborExact

/- The witness is stereochemically admissible. -/
assert_kernel_only
  TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery.ringWitness_stereochemicalAdmissible

/- The actual production runtime generator returns exactly the two ring-neighbour cursors. -/
assert_kernel_only
  TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery.ringWitness_runtime_roots

/- The left runtime cursor is real, bounded and an ordinary carbon. -/
assert_kernel_only
  TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery.ringWitness_left_meaning

/- The right runtime cursor is real, bounded and an ordinary carbon. -/
assert_kernel_only
  TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery.ringWitness_right_meaning

/- The actual incident-list of the left cursor atom is the ring. -/
assert_kernel_only
  TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery.ringWitness_incidentAtoms_left

/- The actual finite path search that witnesses the ring through the left atom. -/
assert_kernel_only
  TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery.ringWitness_reachable_avoiding_left

/- The actual `ringPairCount` of the left atom is one. -/
assert_kernel_only
  TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery.ringWitness_ringPairCount_left

/- The actual production cycle test is `true` for the left cursor atom at the stated fuel. -/
assert_kernel_only
  TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery.ringWitness_atomLiesInCycle_left

/- The actual production cycle test is `true` for the right cursor atom at the stated fuel. -/
assert_kernel_only
  TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery.ringWitness_atomLiesInCycle_right

/- The witness pair is both cyclic at the stated fuel. -/
assert_kernel_only
  TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery.ringWitness_bothCyclic

/- The witness pair is tied in actual atomic number. -/
assert_kernel_only
  TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery.ringWitness_atomZAt_tie

/- Both cursor masses are the frozen carbon Rule-2 lookup. -/
assert_kernel_only
  TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery.ringWitness_mass_frozen

/- The actual conservative gate is `false` at the tied compiled value for the witness pair. -/
assert_kernel_only
  TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery.ringWitness_gate_at_tie

/- The actual raw fast Rule-2 constitutional comparison of the witness pair ties. -/
assert_kernel_only
  TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery.ringWitness_raw_fast

/- The actual raw uncapped authoritative Rule-2 constitutional comparison ties. -/
assert_kernel_only
  TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery.ringWitness_raw_authoritative

/- Actual fast certified-stage result at the tied both-cyclic pair. -/
assert_kernel_only
  TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery.ringWitness_certifiedStage

/- Actual uncapped authoritative certified-stage result at the tied both-cyclic pair. -/
assert_kernel_only
  TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery.ringWitness_certifiedStageAuthoritative

/- The fast stage does not refuse at the witness pair. -/
assert_kernel_only
  TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery.ringWitness_certifiedStage_ne_none

/- The authoritative stage does not refuse at the witness pair. -/
assert_kernel_only
  TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery.ringWitness_certifiedStageAuthoritative_ne_none

/- Composed fast protocol outcome at the empty auxiliary descriptor state. -/
assert_kernel_only
  TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery.ringWitness_fast_protocol

/- Composed `fast`-then-`authoritative` protocol outcome at the empty auxiliary descriptor state. -/
assert_kernel_only
  TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery.ringWitness_complete_protocol

/- Precise actual API obstruction: the checked clean domain's generated neighbours are acyclic. -/
assert_kernel_only
  TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery.checked151_domain_excludes_cyclic_neighbors
