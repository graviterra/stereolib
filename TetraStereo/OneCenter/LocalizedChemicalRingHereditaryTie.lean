import TetraStereo.OneCenter.LocalizedChemicalRingCompoundReplay
import TetraStereo.OneCenter.LocalizedChemicalRingActualReferenceMatch
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! Complete actual comparison ties are hereditary up to a permutation of actual children.
Rebuilding uses the original target and dependency reader, with no acyclic or reference-count
restriction. Both successful child compound builds are derived at the carrier budget. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingHereditaryTie

open CertifiedLocalizedCIPInput LocalizedCumulativeDecoratedTree
open LocalizedChemicalRingDecodedRelation LocalizedChemicalRingStageReplay
open LocalizedChemicalRingCompoundReplay LocalizedChemicalRingActualFullLabelMatch

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}

noncomputable abbrev compiler (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (fuel : Nat) :
    input.RuleMajorCompoundStageCompiler carrierFuel :=
  fun stage => input.buildRuleMajorCumulativeWithRead? stage (input.localizedDependencyLabel target view) fuel

theorem compound_replay_of_observations
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    {treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realL : LocalizedCumulativeTreeRealizes input (input.localizedDependencyLabel target view) treeL)
    (realR : LocalizedCumulativeTreeRealizes input (input.localizedDependencyLabel target view) treeR)
    (same : observation treeL = observation treeR)
    (fuel : Nat) (x y : input.LocalizedRerootCursor carrierFuel)
    (related : ShapePositionCursorRelation (shape_eq_of_observation_eq treeL treeR same) x y)
    (left right : input.LocalizedRerootCompoundRule45Key)
    (builtL : input.buildRuleMajorCompoundRule45KeyWith? (compiler target view fuel) x = some left)
    (builtR : input.buildRuleMajorCompoundRule45KeyWith? (compiler target view fuel) y = some right) :
    input.compareLocalizedRerootCompoundThroughRule5 left right = ⟨.eq, false⟩ := by
  exact compound_replay (compiler target view fuel) (compiler target view fuel) x y
    (fun stage keyL keyR hl hr => replay_of_observations same _ _ realL realR stage fuel x y related
      keyL keyR hl hr)
    (fun keyL keyR hl hr => references_eq_of_observations target view realL realR same fuel x y related
      keyL keyR hl hr) left right builtL builtR

def RebuildMatch (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) (x y : input.LocalizedRerootCursor carrierFuel) : Prop :=
  ∃ left right,
    input.buildRuleMajorCompoundRule45KeyWith? (compiler target view (2 * (carrierFuel + 1))) x = some left ∧
    input.buildRuleMajorCompoundRule45KeyWith? (compiler target view (2 * (carrierFuel + 1))) y = some right ∧
    input.compareLocalizedRerootCompoundThroughRule5 left right = ⟨.eq, false⟩

theorem exists_rebuild_match_of_observations
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    {treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realL : LocalizedCumulativeTreeRealizes input (input.localizedDependencyLabel target view) treeL)
    (realR : LocalizedCumulativeTreeRealizes input (input.localizedDependencyLabel target view) treeR)
    (same : observation treeL = observation treeR)
    (x y : input.LocalizedRerootCursor carrierFuel)
    (related : ShapePositionCursorRelation (shape_eq_of_observation_eq treeL treeR same) x y)
    (validL : input.LocalizedRerootCursorValid x) (validR : input.LocalizedRerootCursorValid y) :
    RebuildMatch target view x y := by
  obtain ⟨left, builtL⟩ := input.buildRuleMajorCompoundRule45KeyWith?_total
    (compiler target view (2 * (carrierFuel + 1))) x
    (fun stage => input.exists_buildRuleMajorCumulativeWithRead_at_twice stage _ x validL)
  obtain ⟨right, builtR⟩ := input.buildRuleMajorCompoundRule45KeyWith?_total
    (compiler target view (2 * (carrierFuel + 1))) y
    (fun stage => input.exists_buildRuleMajorCumulativeWithRead_at_twice stage _ y validR)
  exact ⟨left, right, builtL, builtR,
    compound_replay_of_observations target view realL realR same _ x y related left right builtL builtR⟩

theorem forall₂_imp_mem {α β : Type*} {R S : α → β → Prop} {left : List α} {right : List β}
    (related : List.Forall₂ R left right)
    (step : ∀ x ∈ left, ∀ y ∈ right, R x y → S x y) : List.Forall₂ S left right := by
  induction related with
  | nil => exact .nil
  | @cons x y xs ys h _ ih =>
      exact .cons (step x (by simp) y (by simp) h)
        (ih (fun a ha b hb => step a (List.mem_cons_of_mem x ha) b (List.mem_cons_of_mem y hb)))

/-- An actual complete-key tie supplies a permutation of the actual child frame in which
every paired child successfully rebuilds and ties under the complete current comparator. -/
theorem full_tie_children
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (fuelL fuelR : Nat) (x y : input.LocalizedRerootCursor carrierFuel)
    (left right : input.LocalizedRerootCompoundRule45Key)
    (builtL : input.buildRuleMajorCompoundRule45KeyWith? (compiler target view fuelL) x = some left)
    (builtR : input.buildRuleMajorCompoundRule45KeyWith? (compiler target view fuelR) y = some right)
    (tie : (input.compareLocalizedRerootCompoundThroughRule5 left right).ordering = .eq) :
    ∃ frame, (input.executableLocalizedRerootChildren x).Perm frame ∧
      List.Forall₂ (RebuildMatch target view) frame (input.executableLocalizedRerootChildren y) := by
  obtain ⟨treeL, treeR, sourceL, sourceR, realL, realR, same⟩ :=
    full_tie_same_observations _ _ _ _ _ _ _ _ builtL builtR tie
  let hs := shape_eq_of_observation_eq treeL treeR same
  have roots := shapePositionCursorRelation_sources hs sourceL sourceR
  obtain ⟨frame, perm, related⟩ := shapePositionCursorRelation_children hs realL realR roots
  refine ⟨frame, perm, forall₂_imp_mem related ?_⟩
  intro a ha b hb pair
  exact exists_rebuild_match_of_observations target view realL realR same a b pair
    (input.localizedRerootChild_valid _ _ _ (input.executableLocalizedRerootChildren_declarative x)
      (perm.mem_iff.mpr ha))
    (input.localizedRerootChild_valid _ _ _ (input.executableLocalizedRerootChildren_declarative y) hb)

end TetraStereo.OneCenter.LocalizedChemicalRingHereditaryTie

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingHereditaryTie.compound_replay_of_observations
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingHereditaryTie.exists_rebuild_match_of_observations
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingHereditaryTie.full_tie_children
