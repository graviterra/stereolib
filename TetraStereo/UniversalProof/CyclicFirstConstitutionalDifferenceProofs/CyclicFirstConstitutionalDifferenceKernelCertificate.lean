import TetraStereo.UniversalProof.CyclicFirstConstitutionalDifferenceProofs.CyclicFirstConstitutionalDifference
import TetraStereo.KernelOnly

set_option autoImplicit false



















open TetraStereo.UniversalProof.CyclicFirstConstitutionalDifferenceProofs.CyclicFirstConstitutionalDifference

/- Exact Rule-1a label at a real node. -/
assert_kernel_only canonicalRule1aLabel?_realAtom

/- Exact Rule-1a label at a production phantom padding node. -/
assert_kernel_only canonicalRule1aLabel?_phantom

/- The rational label comparator on integral labels is plain atomic-number comparison. -/
assert_kernel_only compareCIPAtomicLabel_unitValue

/- Equal-Z boundary: the checked Rule-1a atomic-difference bridge returns `eq` at tied roots. -/
assert_kernel_only rule1aRealTied_eq

/- Strict phantom-vs-real first-sphere label difference. -/
assert_kernel_only compareCIPAtomicLabel_phantom_lt_real

/- Production node comparator returns `lt` on a paired (phantom, real positive-Z) sphere. -/
assert_kernel_only compareCanonicalNodeRule?_rule1a_phantom_real

/- Cursor-sphere comparator returns `lt` on the phantom/real sphere. -/
assert_kernel_only compareCursorPairLabels_rule1a_phantom_real_single

/- Cursor rule returns `lt` on the phantom/real sphere at every step budget. -/
assert_kernel_only compareCursorRule_rule1a_single_phantom_real

/- The conflict gate is `false` when no exchanging symmetry exists around a shared frame. -/
assert_kernel_only occurrenceRootsProvedAutomorphic_eq_false_of_swapping_false

/- Conservative certified stage returns a gate-cleared strict result unchanged. -/
assert_kernel_only certifiedConstitutionalStage?_eq_of_gate_false

/- Conservative authoritative certified stage returns a gate-cleared strict result unchanged. -/
assert_kernel_only certifiedConstitutionalStageAuthoritative?_eq_of_gate_false

/- Fast occurrence protocol returns a strict certified stage verbatim. -/
assert_kernel_only compareOccurrenceBranches?_eq_of_constitutional

/- Authoritative occurrence protocol returns a strict certified stage verbatim. -/
assert_kernel_only compareOccurrenceBranchesAuthoritative?_eq_of_constitutional

/- Composed fast-then-authoritative path returns the fast decision unchanged. -/
assert_kernel_only compareOccurrenceBranchesComplete?_eq_of_fast


assert_kernel_only occurrenceFactAuthoritative?_eq_some_of_adjacent_strict

/- The equal-Z witness molecule has eleven atoms. -/
assert_kernel_only witness_atomCount

/- The equal-Z witness molecule is well-formed. -/
assert_kernel_only witness_wellFormed

/- The equal-Z witness molecule has unique unordered edge records. -/
assert_kernel_only witness_bondRecordsUnique

/- The equal-Z witness molecule is admissible. -/
assert_kernel_only witness_admissible

/- The equal-Z witness written-neighbour view is exact. -/
assert_kernel_only witness_writtenNeighborExact

/- The equal-Z witness is stereochemically admissible. -/
assert_kernel_only witness_stereochemicalAdmissible

/- The three-membered ring is an explicit closed bond path. -/
assert_kernel_only witness_threeRing_closed

/- The four-membered ring is an explicit closed bond path. -/
assert_kernel_only witness_fourRing_closed

/- The three-membered ring atoms lie within the source atom bound. -/
assert_kernel_only witness_threeRing_bounded

/- The four-membered ring atoms lie within the source atom bound. -/
assert_kernel_only witness_fourRing_bounded

/- The two arms are distinct lists of different lengths (different ring size). -/
assert_kernel_only witness_rings_distinct

/- The actual production generator returns exactly the four declared cursors. -/
assert_kernel_only witness_frame_generated

/- The actual production four-ligand frame is exactly those generated cursors. -/
assert_kernel_only witness_frame

/- The three-membered-arm cursor is a generated frame member. -/
assert_kernel_only witness_left_member

/- The four-membered-arm cursor is a generated frame member. -/
assert_kernel_only witness_right_member

/- The two generated roots carry distinct atoms. -/
assert_kernel_only witness_roots_distinct

/- Both cursors share one generated reference frame; both nodes are its generated siblings. -/
assert_kernel_only witness_shared_generated_frame

/- The three-membered-arm root carries atomic number 6. -/
assert_kernel_only witness_left_atomZAt

/- The four-membered-arm root carries atomic number 6. -/
assert_kernel_only witness_right_atomZAt

/- The two cyclic roots are atomic-number tied (the checked bridge does not apply). -/
assert_kernel_only witness_tiedZ

/- The actual cycle test is `true` for the three-membered-arm root. -/
assert_kernel_only witness_left_cyclic

/- The actual cycle test is `true` for the four-membered-arm root. -/
assert_kernel_only witness_right_cyclic

/- The shared centre is acyclic at the stated fuel. -/
assert_kernel_only witness_center_acyclic

/- Actual raw strict comparison, forward. -/
assert_kernel_only witness_raw_forward

/- Actual raw strict comparison, reverse. -/
assert_kernel_only witness_raw_reverse

/- Actual authoritative raw strict comparison, forward. -/
assert_kernel_only witness_authoritative_raw_forward

/- Actual authoritative raw strict comparison, reverse. -/
assert_kernel_only witness_authoritative_raw_reverse

/- The actual exhaustive symmetry search reports no exchanging bijection. -/
assert_kernel_only witness_no_swapping

/- The conflict gate is `false` on the equal-Z pair, forward. -/
assert_kernel_only witness_gate_false_forward

/- The conflict gate is `false` on the equal-Z pair, reverse. -/
assert_kernel_only witness_gate_false_reverse

/- Certified constitutional stage is strict, forward. -/
assert_kernel_only witness_certifiedStage_forward

/- Certified constitutional stage is strict, reverse. -/
assert_kernel_only witness_certifiedStage_reverse

/- Authoritative certified constitutional stage is strict, forward. -/
assert_kernel_only witness_authoritativeCertifiedStage_forward

/- Authoritative certified constitutional stage is strict, reverse. -/
assert_kernel_only witness_authoritativeCertifiedStage_reverse

/- Actual occurrence protocol is strict, forward. -/
assert_kernel_only witness_protocol_forward

/- Actual occurrence protocol is strict, reverse. -/
assert_kernel_only witness_protocol_reverse

/- Authoritative occurrence protocol is strict, forward. -/
assert_kernel_only witness_authoritativeProtocol_forward

/- Authoritative occurrence protocol is strict, reverse. -/
assert_kernel_only witness_authoritativeProtocol_reverse

/- Composed fast-then-authoritative protocol is strict, both directions. -/
assert_kernel_only witness_complete_protocol

/- The forward strict outcome is not a tie. -/
assert_kernel_only witness_protocol_forward_not_tie

/- The forward strict outcome is not a refusal. -/
assert_kernel_only witness_protocol_forward_ne_none

/- The actual four-root production sort returns the strict descending order. -/
assert_kernel_only witness_sort

/- The actual adjacent-comparison driver returns three strict decisions. -/
assert_kernel_only witness_adjacent_strict

/- The actual strictness guard value is `true`. -/
assert_kernel_only witness_adjacent_all_strict

/- The actual written-slot projection of the sorted frame. -/
assert_kernel_only witness_positions

/- The actual local production occurrence fact is produced. -/
assert_kernel_only witness_local_fact

/- The actual local production consumer does not refuse the equal-Z cyclic frame. -/
assert_kernel_only witness_local_fact_ne_none

/- The production sort consumes a strict equal-Z cyclic adjacent decision. -/
assert_kernel_only witness_sort_consumes_equalZ_pair

/- The finite independent structural domain, bundled from the source record alone. -/
assert_kernel_only witness_independent_domain

/- Bundled headline equal-Z cyclic first-difference deliverable. -/
assert_kernel_only witness_equalZ_cyclic_first_difference
