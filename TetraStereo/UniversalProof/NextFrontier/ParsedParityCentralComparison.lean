import TetraStereo.UniversalProof.NextFrontier.ParsedParityCentralRule3
import TetraStereo.UniversalProof.NextFrontier.ParsedParityCentralRule45
import TetraStereo.UniversalProof.NextFrontier.ParsedParityCentralRoles
import TetraStereo.UniversalProof.NextFrontier.ParsedParityRoleSort

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-! Derives the complete actual central comparison table. H/Br and unequal atomic numbers
short-circuit ordinarily. The corresponding carbon arms tie through full Rule3, then actual
same-model compound Rule5 readings decide the sole possible pseudo comparison. -/

namespace TetraStereo.UniversalProof.NextFrontier.ParsedParityCentralComparison

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.UniversalProof.NativeOrdinarySourceInputProofs.SourceInputPremiseRecovery
open TetraStereo.UniversalProof.ParsedParitySourceIntake
open TetraStereo.UniversalProof.NextFrontier.ParsedParitySourceFrames
open TetraStereo.UniversalProof.NextFrontier.ParsedParityActualArmSource
open TetraStereo.UniversalProof.NextFrontier.ParsedParityCentralSourceLeaves
open TetraStereo.UniversalProof.NextFrontier.ParsedParityCentralRule3
open TetraStereo.UniversalProof.NextFrontier.ParsedParityCentralRule45
open TetraStereo.UniversalProof.NextFrontier.ParsedParityCentralRoles
open TetraStereo.UniversalProof.NextFrontier.ParsedParityRoleSort

private theorem spatial_tie_symmetric (source : AuthoritativeChemicalInput)
    (first second : source.AromaticCanonicalUncancelledRule3SpatialKey)
    (tied : source.compareAromaticCanonicalUncancelledRule3SpatialKeys first second = .eq) :
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys second first = .eq := by
  letI : Std.TransCmp source.compareAromaticCanonicalUncancelledRule3SpatialKeys :=
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys_transCmp
  rw [Std.OrientedCmp.eq_swap (cmp := source.compareAromaticCanonicalUncancelledRule3SpatialKeys)
    (a := second) (b := first), tied]
  rfl

private theorem spatial_tie_self (source : AuthoritativeChemicalInput)
    (key : source.AromaticCanonicalUncancelledRule3SpatialKey) :
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys key key = .eq := by
  letI : Std.TransCmp source.compareAromaticCanonicalUncancelledRule3SpatialKeys :=
    source.compareAromaticCanonicalUncancelledRule3SpatialKeys_transCmp
  exact Std.ReflCmp.compare_self

theorem source_frame_real (c l r : TetrahedralInputParity) :
    OccurrenceRootsReal (ownSource (raw c l r)) (sourceFrame c l r) := by
  intro slot
  obtain ⟨atom, _, current, real, _⟩ := source_slot_endpoint c l r slot
  exact ⟨atom, current, real⟩

theorem arm_pair_rule3_tie (c l r : TetrahedralInputParity) (first second : Bool) :
    (ownSource (raw c l r)).compareAromaticCanonicalUncancelledRule3SpatialKeys
      ((centralKeys c l r).keyAt (armSlot c l r first)).rule3
      ((centralKeys c l r).keyAt (armSlot c l r second)).rule3 = .eq := by
  cases first <;> cases second
  · exact spatial_tie_self (ownSource (raw c l r)) _
  · exact spatial_tie_symmetric (ownSource (raw c l r)) _ _ (central_arms_rule3_tie c l r)
  · exact central_arms_rule3_tie c l r
  · exact spatial_tie_self (ownSource (raw c l r)) _

private theorem arm_role_decision (l r : TetrahedralInputParity) (first second : Bool) :
    roleDecision (armReference l r true) (armReference l r false)
      (if first then 1 else 3) (if second then 1 else 3) =
      { ordering := referenceComparison .R (armReference l r first) (armReference l r second)
        pseudo := decide (armReference l r first ≠ armReference l r second) } := by
  cases l <;> cases r <;> cases first <;> cases second <;> decide +kernel

theorem arm_pair_callback (c l r : TetrahedralInputParity) (first second : Bool) :
    (ownSource (raw c l r)).compareAromaticCanonicalOccurrenceRule3Through5At (centralKeys c l r)
      (armSlot c l r first) (armSlot c l r second) =
      roleDecision (armReference l r true) (armReference l r false)
        (centralRoles c l r (armSlot c l r first)) (centralRoles c l r (armSlot c l r second)) := by
  rw [(ownSource (raw c l r)).compareAromaticCanonicalOccurrenceRule3Through5At_of_rule3_eq
    (centralKeys c l r) (armSlot c l r first) (armSlot c l r second)
    (arm_pair_rule3_tie c l r first second), arm_compound_comparison,
    central_arm_role, central_arm_role, arm_role_decision]

private theorem role_atomic_decision (leftLabel rightLabel : RS) (first second : Fin 4)
    (different : roleZ first ≠ roleZ second) :
    roleDecision leftLabel rightLabel first second =
      { ordering := compare (roleZ first) (roleZ second), pseudo := false } := by
  cases leftLabel <;> cases rightLabel <;> revert different first second <;> decide +kernel

private theorem distinct_equal_atomic_roles (first second : Fin 4)
    (different : first ≠ second) (sameZ : roleZ first = roleZ second) :
    (first = 1 ∧ second = 3) ∨ (first = 3 ∧ second = 1) := by
  revert sameZ different first second
  decide +kernel

/-- Complete off-diagonal callback table for the actual computed keys, with physical roles
read from their actual returned source-frame atom IDs. -/
theorem central_callback_table (c l r : TetrahedralInputParity) (first second : Fin 4)
    (different : first ≠ second) :
    (ownSource (raw c l r)).compareAromaticCanonicalOccurrenceRule3Through5At
      (centralKeys c l r) first second =
      roleDecision (armReference l r true) (armReference l r false)
        (centralRoles c l r first) (centralRoles c l r second) := by
  by_cases sameZ : roleZ (centralRoles c l r first) = roleZ (centralRoles c l r second)
  · have rolesDifferent : centralRoles c l r first ≠ centralRoles c l r second :=
      fun equal => different (centralRoles_injective c l r equal)
    rcases distinct_equal_atomic_roles _ _ rolesDifferent sameZ with forward | backward
    · have firstEq : first = armSlot c l r true := by
        apply centralRoles_injective c l r
        rw [forward.1, central_arm_role]
        rfl
      have secondEq : second = armSlot c l r false := by
        apply centralRoles_injective c l r
        rw [forward.2, central_arm_role]
        rfl
      subst first
      subst second
      exact arm_pair_callback c l r true false
    · have firstEq : first = armSlot c l r false := by
        apply centralRoles_injective c l r
        rw [backward.1, central_arm_role]
        rfl
      have secondEq : second = armSlot c l r true := by
        apply centralRoles_injective c l r
        rw [backward.2, central_arm_role]
        rfl
      subst first
      subst second
      exact arm_pair_callback c l r false true
  · rw [role_atomic_decision _ _ _ _ sameZ]
    rcases Nat.lt_or_gt_of_ne sameZ with lower | higher
    · rw [Nat.compare_eq_lt.mpr lower]
      apply occurrence_comparison_lt_of_atomic_priority (ownSource (raw c l r))
        (centralTarget c l r) (centralView c l r) 4 (sourceFrame c l r) (source_frame_real c l r)
        (centralKeys c l r) (central_keys_computed c l r) first second
      simpa only [central_role_priority] using lower
    · rw [Nat.compare_eq_gt.mpr higher]
      apply occurrence_comparison_gt_of_atomic_priority (ownSource (raw c l r))
        (centralTarget c l r) (centralView c l r) 4 (sourceFrame c l r) (source_frame_real c l r)
        (centralKeys c l r) (central_keys_computed c l r) first second
      simpa only [central_role_priority] using higher

end TetraStereo.UniversalProof.NextFrontier.ParsedParityCentralComparison
