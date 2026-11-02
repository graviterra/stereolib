import TetraStereo.OneCenter.LocalizedGenericMarkedRecalculation
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Existing Rule-6 selection agrees with the generated three-way tied class

For a three-way tie above a unique fourth ligand, the production selector rotates the
three tied positions. It does not include the fourth ligand. The experimental constructor
selects the same class in its sorted order, and its three-result consensus is invariant
under that rotation. This concerns selection and consensus only: it does not remove the
production parity, topology, or local-reference gates, or justify a promotion schedule.
-/

namespace TetraStereo.OneCenter.OccurrenceRule6ReferenceSelectionAgreement

open LocalizedGenericMarkedRecalculation

theorem production_three_way_top (a b c d : Nat) :
    rule6EquivalentReferencePositions [a, b, c, d]
        [some Ordering.eq, some Ordering.eq, some Ordering.gt] = [b, c, a] := rfl

theorem generated_three_way_top (a b c d : Nat) :
    tiedPositions false [a, b, c, d]
        [some Ordering.eq, some Ordering.eq, some Ordering.gt] = [a, b, c] := rfl

theorem three_way_top_perm (a b c d : Nat) :
    (rule6EquivalentReferencePositions [a, b, c, d]
      [some Ordering.eq, some Ordering.eq, some Ordering.gt]).Perm
    (tiedPositions false [a, b, c, d]
      [some Ordering.eq, some Ordering.eq, some Ordering.gt]) := by
  exact (List.perm_append_comm : ([b, c] ++ [a]).Perm ([a] ++ [b, c]))

theorem consensus_rotate_three (a b c : Option RS) :
    consensus [b, c, a] = consensus [a, b, c] := by
  cases a <;> cases b <;> cases c <;> simp [consensus]
  all_goals split_ifs <;> simp_all [eq_comm]

/-- With the same reference evaluation, both orders of the three-way tied class have
exactly the same successful result or refusal. -/
theorem three_way_top_consensus (evaluate : Nat → Option RS) (a b c d : Nat) :
    consensus ((rule6EquivalentReferencePositions [a, b, c, d]
        [some Ordering.eq, some Ordering.eq, some Ordering.gt]).map evaluate) =
      consensus ((tiedPositions false [a, b, c, d]
        [some Ordering.eq, some Ordering.eq, some Ordering.gt]).map evaluate) := by
  exact consensus_rotate_three (evaluate a) (evaluate b) (evaluate c)

end TetraStereo.OneCenter.OccurrenceRule6ReferenceSelectionAgreement

assert_kernel_only TetraStereo.OneCenter.OccurrenceRule6ReferenceSelectionAgreement.production_three_way_top
assert_kernel_only TetraStereo.OneCenter.OccurrenceRule6ReferenceSelectionAgreement.three_way_top_perm
assert_kernel_only TetraStereo.OneCenter.OccurrenceRule6ReferenceSelectionAgreement.consensus_rotate_three
assert_kernel_only TetraStereo.OneCenter.OccurrenceRule6ReferenceSelectionAgreement.three_way_top_consensus
