import TetraStereo.OneCenter.RawFramedFailClosedFuelBase
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! # Fuel stability of the actual framed constitutional comparator

This module is the short endpoint built on `RawFramedFailClosedFuelBase`.

The actual comparator `FrameRuntime.compareBranch?` is *not* modified.  Instead:

* `RawFramedFailClosedFuelBase.failClosed_compareBranch_rule2_of_admitted_profile` gives a
  successful fail-closed candidate result at the explicit molecule-derived fuel bound
  `2 * mol.atomCount + 2`;
* `RawFramedFailClosedFuelBase.failClosed_success_mono` transports that result to every larger fuel;
* `RawFramedFailClosedFuelBase.failClosed_refines_main` identifies the transported candidate
  result with the actual `FrameRuntime.compareBranch?` result.

Combining the three facts yields the declared endpoint: under the actual admission hypotheses
(a well-formed molecule, the global P-92 bonding-number-six bound, an actually admitted shared
profile, and two actual ligand cursors of that center occurrence), there is a single ordering
`decision` that the **actual** comparator returns at *every* fuel at or above the bound.

The immediate corollary is exact Option equality of the actual comparator between any two fuels at
or above the bound.  No production comparator is redefined, no policy or chemistry premise is
added, and no totality/refinement fact is assumed.

## Scope

The hypotheses are exactly those of the existing closure/candidate endpoints: `mol.WellFormed`,
`∀ root, CanonicalCenterBondingNumberSix mol root`, an actually admitted
`profile? mol center = some profile`, and actual ligand-cursor membership in the generated center
occurrence.  The all-real character of the admitted profile is enforced by `profile?` itself, not
assumed here. -/

namespace TetraStereo.OneCenter

open TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.FrameRuntime
open TetraStereo.OneCenter.RawFramedConstitutionalFuelClosure
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.OneCenter.RawFramedFailClosedFuelBase

namespace RawFramedStructuralFuelAdequacy

/-- **Endpoint: stability of the actual Rule-2 comparator from fuel `2 * mol.atomCount + 2`.**

Starting only from a well-formed molecule, the global P-92 bonding-number-six admission, an
actually admitted profile `available : profile? mol center = some profile`, and two actual ligand
cursors of that center occurrence, the actual `FrameRuntime.compareBranch? mol profile true … .rule2`
returns one fixed `decision` at every fuel at or above `2 * mol.atomCount + 2`. -/
theorem compareBranch_rule2_stable_of_admitted_profile (mol : RawMolecule) (profile : Profile)
    {center : CanonicalBranchNode}
    (wellFormed : mol.WellFormed)
    (bonding : ∀ root, CanonicalCenterBondingNumberSix mol root)
    (available : profile? mol center = some profile)
    {left right : CanonicalRerootCursor}
    (leftMember : left ∈ occurrenceLigandCursors mol center)
    (rightMember : right ∈ occurrenceLigandCursors mol center) :
    ∃ decision, ∀ fuel, 2 * mol.atomCount + 2 ≤ fuel →
      FrameRuntime.compareBranch? mol profile true fuel .rule2 (.actual left) (.actual right) =
        some decision := by
  rcases failClosed_compareBranch_rule2_of_admitted_profile mol profile wellFormed bonding
    available leftMember rightMember with ⟨ordering, computed⟩
  refine ⟨ordering, ?_⟩
  intro fuel adequate
  exact failClosed_refines_main mol profile true .rule2 fuel (.actual left) (.actual right) ordering
    (failClosed_success_mono (mol := mol) (profile := profile) (authoritative := true)
      (stage := .rule2) (fuel := 2 * mol.atomCount + 2) (highFuel := fuel)
      (left := .actual left) (right := .actual right) (ordering := ordering) computed adequate)

/-- **Exact MAIN Option equality above the bound.**

For any two fuels `firstFuel` and `secondFuel` at or above `2 * mol.atomCount + 2`, the actual
`FrameRuntime.compareBranch? mol profile true … .rule2` returns the *same* `Option Ordering` at
both fuels.  This is the equality form of
`compareBranch_rule2_stable_of_admitted_profile`. -/
theorem compareBranch_rule2_option_eq_of_admitted_profile (mol : RawMolecule) (profile : Profile)
    {center : CanonicalBranchNode}
    (wellFormed : mol.WellFormed)
    (bonding : ∀ root, CanonicalCenterBondingNumberSix mol root)
    (available : profile? mol center = some profile)
    {left right : CanonicalRerootCursor}
    (leftMember : left ∈ occurrenceLigandCursors mol center)
    (rightMember : right ∈ occurrenceLigandCursors mol center)
    {firstFuel secondFuel : Nat}
    (firstBound : 2 * mol.atomCount + 2 ≤ firstFuel)
    (secondBound : 2 * mol.atomCount + 2 ≤ secondFuel) :
    FrameRuntime.compareBranch? mol profile true firstFuel .rule2 (.actual left) (.actual right) =
      FrameRuntime.compareBranch? mol profile true secondFuel .rule2 (.actual left) (.actual right) := by
  rcases compareBranch_rule2_stable_of_admitted_profile mol profile wellFormed bonding available
    leftMember rightMember with ⟨decision, stable⟩
  rw [stable firstFuel firstBound, stable secondFuel secondBound]

end RawFramedStructuralFuelAdequacy

end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only
  TetraStereo.OneCenter.RawFramedStructuralFuelAdequacy.compareBranch_rule2_stable_of_admitted_profile
assert_kernel_only
  TetraStereo.OneCenter.RawFramedStructuralFuelAdequacy.compareBranch_rule2_option_eq_of_admitted_profile
