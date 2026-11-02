import TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge
import TetraStereo.KernelOnly





assert_kernel_only TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge.observed_naturalHydrogen_element
assert_kernel_only TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge.observed_element_z
assert_kernel_only TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge.observed_naturalHydrogen_z
assert_kernel_only TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge.observed_naturalHydrogen_mass
assert_kernel_only TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge.originalParent_pathNode
assert_kernel_only TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge.pathNode_ne
assert_kernel_only TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge.actual_child_copies
assert_kernel_only TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge.actual_path_children
assert_kernel_only TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge.actual_terminal_children
assert_kernel_only TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge.carbon_z
assert_kernel_only TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge.hydrogen_z
assert_kernel_only TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge.generated_history_nodup
assert_kernel_only TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge.actual_hydrogen_fresh
assert_kernel_only TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge.actual_bridge_children
assert_kernel_only TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge.actual_methyl_children
assert_kernel_only TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge.methyl_terminal_star
assert_kernel_only TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge.actual_guards
assert_kernel_only TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge.physical_hydrogen_tie
assert_kernel_only TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge.physical_hydrogen_tie_authoritative
assert_kernel_only TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge.bridge_sibling_tie
assert_kernel_only TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge.methyl_sibling_tie
assert_kernel_only TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge.backbone_over_hydrogen
assert_kernel_only TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge.bridge_sibling_tie_authoritative
assert_kernel_only TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge.methyl_sibling_tie_authoritative
assert_kernel_only TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge.backbone_over_hydrogen_authoritative
assert_kernel_only TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge.actual_ranked_bridge
assert_kernel_only TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge.actual_ranked_methyl
assert_kernel_only TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge.actual_fast_raw_both
assert_kernel_only TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge.actual_ranked_bridge_authoritative
assert_kernel_only TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge.actual_ranked_methyl_authoritative
assert_kernel_only TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge.actual_authoritative_raw_both
assert_kernel_only TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge.actual_certified_both
assert_kernel_only TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge.actual_fast_protocol_both
assert_kernel_only TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge.actual_certified_authoritative_both
assert_kernel_only TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge.actual_authoritative_protocol_both
assert_kernel_only TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge.actual_complete_protocol_both
assert_kernel_only TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge.actual_complete_protocol_positive

/-! Six additive type-contract checks. The 37 original authority assertions above are retained.
The first three keep computed cursors and independently observed carbon Z domain-independent.
The final three require the intended physical/generated input domain explicitly. -/
namespace TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge.KernelContract

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking

example (raw : RawMolecule) (roles : Roles raw) (tail : List Nat) :
    CanonicalRerootCursor := bridgeCursor (roles := roles) (tail := tail)

example (raw : RawMolecule) (roles : Roles raw) (tail : List Nat) :
    CanonicalRerootCursor := methylCursor (roles := roles) (tail := tail)

example (raw : RawMolecule) (atom : Nat) (observed : ObservedElement raw atom Element.C) :
    raw.atomZAt atom = 6 := carbon_z atom observed

example (raw : RawMolecule) (roles : Roles raw) (root : Fin raw.atomCount) (tail : List Nat)
    (domain : InteriorDomain raw roles root tail) (fuel : Nat) (stage : CanonicalRuleStage) :
    compareCursorBranchAt raw (fuel + 1) stage (bridgeCursor (roles := roles) (tail := tail))
      (methylCursor (roles := roles) (tail := tail)) = some Ordering.gt ∧
    compareCursorBranchAt raw (fuel + 1) stage (methylCursor (roles := roles) (tail := tail))
      (bridgeCursor (roles := roles) (tail := tail)) = some Ordering.lt :=
  actual_fast_raw_both domain fuel stage

example (raw : RawMolecule) (roles : Roles raw) (root : Fin raw.atomCount) (tail : List Nat)
    (domain : InteriorDomain raw roles root tail) (fuel : Nat) (stage : CanonicalRuleStage) :
    compareCursorBranchAtAuthoritative? raw (fuel + 1) stage (bridgeCursor (roles := roles) (tail := tail))
      (methylCursor (roles := roles) (tail := tail)) = some Ordering.gt ∧
    compareCursorBranchAtAuthoritative? raw (fuel + 1) stage (methylCursor (roles := roles) (tail := tail))
      (bridgeCursor (roles := roles) (tail := tail)) = some Ordering.lt :=
  actual_authoritative_raw_both domain fuel stage

example (raw : RawMolecule) (roles : Roles raw) (root : Fin raw.atomCount) (tail : List Nat)
    (domain : InteriorDomain raw roles root tail) (state : OccurrenceAuxState) (fuel : Nat)
    (positive : 1 ≤ fuel) :
    compareOccurrenceBranchesComplete? raw state fuel (bridgeCursor (roles := roles) (tail := tail))
      (methylCursor (roles := roles) (tail := tail)) = some { ordering := Ordering.gt } ∧
    compareOccurrenceBranchesComplete? raw state fuel (methylCursor (roles := roles) (tail := tail))
      (bridgeCursor (roles := roles) (tail := tail)) = some { ordering := Ordering.lt } :=
  actual_complete_protocol_positive domain state fuel positive

end TetraStereo.UniversalProof.GeneralSecondSphereRuntimeBridge.KernelContract
