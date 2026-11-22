import TetraStereo.OneCenter.LocalizedMarkedTerminalGaugeSwap

set_option autoImplicit false
namespace TetraStereo.Examples.RingNestedPolicyParity
open OneCenter LocalizedGenericMarkedRecalculation
open LocalizedMarkedTerminalGaugeSwap

/-- Two successful trial orders differing only in the last two slots can never
give a consensus, for arbitrary exact coordinates, including missing points. -/
theorem distal_pair_cancels (g : Geometry) (a b c d : Nat) :
    consensus [readback? g [a,b,c,d], readback? g [a,b,d,c]] = none := by
  rw [readback_swap34 g a b c d]
  cases readback? g [a,b,c,d] with
  | none => rfl
  | some value => cases value <;> rfl

theorem propellane_distal_trial_equality (g : Geometry) :
    consensus [readback? g [0,2,3,4], readback? g [0,2,4,3]] =
      consensus [none,none] :=
  distal_pair_cancels g 0 2 3 4

private theorem twice (x : Option RS) : (x.map RS.swap).map RS.swap = x := by
  cases x with
  | none => rfl
  | some value => cases value <;> rfl

/-- The three markings of a cyclically ordered triple yield the same actual
hand when their priority orders rotate the last three slots. -/
theorem cyclic_triple_reads (g : Geometry) (a b c d : Nat) :
    consensus [readback? g [a,b,c,d], readback? g [a,c,d,b], readback? g [a,d,b,c]] =
      readback? g [a,b,c,d] := by
  have left : readback? g [a,c,d,b] = readback? g [a,b,c,d] := by
    rw [readback_swap34 g a c b d, readback_swap23 g a b c d, twice]
  have right : readback? g [a,d,b,c] = readback? g [a,b,c,d] := by
    rw [readback_swap23 g a b d c, readback_swap34 g a b c d, twice]
  rw [left, right]
  cases readback? g [a,b,c,d] with
  | none => rfl
  | some value => cases value <;> rfl
end TetraStereo.Examples.RingNestedPolicyParity

assert_kernel_only TetraStereo.Examples.RingNestedPolicyParity.distal_pair_cancels
assert_kernel_only TetraStereo.Examples.RingNestedPolicyParity.propellane_distal_trial_equality
assert_kernel_only TetraStereo.Examples.RingNestedPolicyParity.cyclic_triple_reads
