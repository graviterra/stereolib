import TetraStereo.OneCenter.LocalizedChemicalRingHereditaryTie
import TetraStereo.OneCenter.LocalizedChemicalRingComparisonClasses
import TetraStereo.OneCenter.LocalizedChemicalRingReaddressedTree
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! A tied actual compound comparison matches children in any dense addressings which respect
the actual sibling order. The child correspondence retains the original target and reader.
In particular, promotion by a reference marker cannot disturb full-label matching. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingPromotedChildMatch

open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
open LocalizedCumulativeDecoratedTree LocalizedMarkedRetainedCanonicalMarker
open LocalizedMarkedRetainedPromotedKey LocalizedChemicalRingHereditaryTie
open LocalizedChemicalRingReaddressedTree LocalizedChemicalRingComparisonClasses
open LocalizedMarkedRetainedSubtreeContext

noncomputable section
open scoped Classical

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
  (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)

theorem through_tie_of_ordering_eq (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule45Key)
    (tie : (input.compareLocalizedRerootCompoundThroughRule5 left right).ordering = .eq) :
    input.compareLocalizedRerootCompoundThroughRule5 left right = ⟨.eq, false⟩ := by
  unfold compareLocalizedRerootCompoundThroughRule5 at tie ⊢
  dsimp only at tie ⊢
  split_ifs with prior
  · simp_all
  · cases h : input.compareLocalizedRerootCompoundRule5Readings .R left.rule5Readings right.rule5Readings <;>
      simp_all

def keyAt (fallback : input.LocalizedRerootCompoundRule45Key)
    (cursor : input.LocalizedRerootCursor carrierFuel) : input.LocalizedRerootCompoundRule45Key :=
  (input.buildRuleMajorCompoundRule45KeyWith? (compiler target view (2 * (carrierFuel + 1))) cursor).getD fallback

theorem keyAt_of_built (fallback key : input.LocalizedRerootCompoundRule45Key)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (built : input.buildRuleMajorCompoundRule45KeyWith?
      (compiler target view (2 * (carrierFuel + 1))) cursor = some key) :
    keyAt target view fallback cursor = key := by simp [keyAt, built]

theorem keyAt_built (fallback : input.LocalizedRerootCompoundRule45Key)
    (cursor : input.LocalizedRerootCursor carrierFuel) (valid : input.LocalizedRerootCursorValid cursor) :
    input.buildRuleMajorCompoundRule45KeyWith? (compiler target view (2 * (carrierFuel + 1))) cursor =
      some (keyAt target view fallback cursor) := by
  obtain ⟨key, built⟩ := input.buildRuleMajorCompoundRule45KeyWith?_total
    (compiler target view (2 * (carrierFuel + 1))) cursor
    (fun stage => input.exists_buildRuleMajorCumulativeWithRead_at_twice stage _ cursor valid)
  rw [keyAt_of_built target view fallback key cursor built]
  exact built

theorem keyAt_ordinary (fallback : input.LocalizedRerootCompoundRule45Key)
    (cursor : input.LocalizedRerootCursor carrierFuel) (valid : input.LocalizedRerootCursorValid cursor) :
    ordinaryKey? input target view cursor = some (keyAt target view fallback cursor) := by
  unfold ordinaryKey?
  rw [input.buildActualRuleMajorCompoundRule45KeyExec?_eq,
    input.buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor]
  exact keyAt_built target view fallback cursor valid

theorem keyAt_tie (fallback : input.LocalizedRerootCompoundRule45Key)
    {x y : input.LocalizedRerootCursor carrierFuel} (matched : RebuildMatch target view x y) :
    input.compareLocalizedRerootCompoundRule45Keys
      (keyAt target view fallback x) (keyAt target view fallback y) = .eq := by
  obtain ⟨left, right, builtL, builtR, tie⟩ := matched
  rw [keyAt_of_built target view fallback left x builtL, keyAt_of_built target view fallback right y builtR]
  exact (input.compareLocalizedRerootCompoundThroughRule5_ordering left right).symm.trans
    (congrArg ConstitutionalRule5Comparison.ordering tie)

theorem orderedChildren_sources_perm
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (realizes : LocalizedCumulativeTreeRealizes input (input.localizedDependencyLabel target view) tree)
    (addressing : (ruleMajorTreeGraph tree).Addressing) (dense : Dense addressing)
    (node : (ruleMajorTreeGraph tree).Node) :
    ((orderedChildren (ruleMajorTreeGraph tree) addressing dense node).map (nodeSource input tree)).Perm
      (input.executableLocalizedRerootChildren (nodeSource input tree node)) := by
  obtain ⟨sub, lookup⟩ := exists_local_subtree tree node
  obtain ⟨slots, perm, sources⟩ := slot_children input tree realizes node sub lookup
  rw [nodeSource_of_lookup input tree lookup]
  exact (((orderedChildren_perm _ addressing dense node).trans perm.symm).map _).trans sources

theorem orderedChildren_valid
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (realizes : LocalizedCumulativeTreeRealizes input (input.localizedDependencyLabel target view) tree)
    (addressing : (ruleMajorTreeGraph tree).Addressing) (dense : Dense addressing)
    (node child : (ruleMajorTreeGraph tree).Node)
    (member : child ∈ orderedChildren (ruleMajorTreeGraph tree) addressing dense node) :
    input.LocalizedRerootCursorValid (nodeSource input tree child) := by
  have memExec := (orderedChildren_sources_perm target view tree realizes addressing dense node).mem_iff.mp
    (List.mem_map.mpr ⟨child, member, rfl⟩)
  exact input.localizedRerootChild_valid _ _ _
    (input.executableLocalizedRerootChildren_declarative (nodeSource input tree node)) memExec

theorem orderedChildren_sorted
    (fallback : input.LocalizedRerootCompoundRule45Key)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (realizes : LocalizedCumulativeTreeRealizes input (input.localizedDependencyLabel target view) tree)
    {P : Type*} [LinearOrder P] (prior : (ruleMajorTreeGraph tree).Node → P)
    (agree : SiblingPriorAgreement input target view tree prior)
    (addressing : (ruleMajorTreeGraph tree).Addressing) (dense : Dense addressing)
    (sorted : KeySorted prior addressing) (node : (ruleMajorTreeGraph tree).Node) :
    ((orderedChildren (ruleMajorTreeGraph tree) addressing dense node).map
      (fun child => keyAt target view fallback (nodeSource input tree child))).Pairwise
        (fun a b => input.compareLocalizedRerootCompoundRule45Keys a b ≠ .lt) := by
  rw [List.pairwise_map, List.pairwise_iff_getElem]
  intro i j hi hj hij
  let children := orderedChildren (ruleMajorTreeGraph tree) addressing dense node
  have mi : children[i] ∈ children := List.getElem_mem hi
  have mj : children[j] ∈ children := List.getElem_mem hj
  have ai := (orderedChildren_get_iff _ addressing dense node children[i] i).mp
    (List.getElem?_eq_getElem hi)
  have aj := (orderedChildren_get_iff _ addressing dense node children[j] j).mp
    (List.getElem?_eq_getElem hj)
  have order := sorted node children[i] children[j] i j ai aj hij
  have comparison := agree node children[i] children[j]
    ((orderedChildren_mem _ addressing dense node _).mp mi)
    ((orderedChildren_mem _ addressing dense node _).mp mj) _ _
    (keyAt_ordinary target view fallback _ (orderedChildren_valid target view tree realizes addressing dense node _ mi))
    (keyAt_ordinary target view fallback _ (orderedChildren_valid target view tree realizes addressing dense node _ mj))
  rw [input.compareLocalizedRerootCompoundThroughRule5_ordering] at comparison
  rw [comparison]
  intro less
  exact (not_lt_of_ge order) (compare_lt_iff_lt.mp less)

/-- Full actual ties are retained at matching promoted child slots, rather than merely at
some independently chosen reading-tree correspondence. -/
theorem matched_orderedChildren
    (treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel)
    (realL : LocalizedCumulativeTreeRealizes input (input.localizedDependencyLabel target view) treeL)
    (realR : LocalizedCumulativeTreeRealizes input (input.localizedDependencyLabel target view) treeR)
    {P Q : Type*} [LinearOrder P] [LinearOrder Q]
    (priorL : (ruleMajorTreeGraph treeL).Node → P) (priorR : (ruleMajorTreeGraph treeR).Node → Q)
    (agreeL : SiblingPriorAgreement input target view treeL priorL)
    (agreeR : SiblingPriorAgreement input target view treeR priorR)
    (addressL : (ruleMajorTreeGraph treeL).Addressing) (addressR : (ruleMajorTreeGraph treeR).Addressing)
    (denseL : Dense addressL) (denseR : Dense addressR)
    (sortedL : KeySorted priorL addressL) (sortedR : KeySorted priorR addressR)
    (x : (ruleMajorTreeGraph treeL).Node) (y : (ruleMajorTreeGraph treeR).Node)
    (matched : RebuildMatch target view (nodeSource input treeL x) (nodeSource input treeR y)) :
    List.Forall₂ (fun a b => RebuildMatch target view (nodeSource input treeL a) (nodeSource input treeR b))
      (orderedChildren (ruleMajorTreeGraph treeL) addressL denseL x)
      (orderedChildren (ruleMajorTreeGraph treeR) addressR denseR y) := by
  obtain ⟨left, right, builtL, builtR, tie⟩ := matched
  obtain ⟨frame, perm, paired⟩ := full_tie_children target view _ _ _ _ left right builtL builtR
    (congrArg ConstitutionalRule5Comparison.ordering tie)
  let cmp := input.compareLocalizedRerootCompoundRule45Keys
  letI : Std.TransCmp cmp := input.compareLocalizedRerootCompoundRule45Keys_transCmp
  let key := keyAt target view left
  have leftPerm := ((orderedChildren_sources_perm target view treeL realL addressL denseL x).trans perm).map key
  have rightPerm := (orderedChildren_sources_perm target view treeR realR addressR denseR y).map key
  have keysPaired : List.Forall₂ (fun a b => cmp a b = .eq)
      (frame.map key) ((input.executableLocalizedRerootChildren (nodeSource input treeR y)).map key) := by
    simpa only [List.forall₂_map_left_iff, List.forall₂_map_right_iff] using
      paired.imp (fun _ _ pair => keyAt_tie target view left pair)
  have sortedKeys := sorted_ties_of_perms cmp leftPerm rightPerm keysPaired
    (by simpa only [List.map_map, Function.comp_def] using
      orderedChildren_sorted target view left treeL realL priorL agreeL addressL denseL sortedL x)
    (by simpa only [List.map_map, Function.comp_def] using
      orderedChildren_sorted target view left treeR realR priorR agreeR addressR denseR sortedR y)
  simp only [List.forall₂_map_left_iff, List.forall₂_map_right_iff] at sortedKeys
  refine forall₂_imp_mem sortedKeys ?_
  intro a ha b hb equal
  have buildA := keyAt_built target view left _ (orderedChildren_valid target view treeL realL addressL denseL x a ha)
  have buildB := keyAt_built target view left _ (orderedChildren_valid target view treeR realR addressR denseR y b hb)
  refine ⟨_, _, buildA, buildB, ?_⟩
  have eqOrder : (input.compareLocalizedRerootCompoundThroughRule5 _ _).ordering = .eq :=
    (input.compareLocalizedRerootCompoundThroughRule5_ordering _ _).trans equal
  exact through_tie_of_ordering_eq input _ _ eqOrder

end
end TetraStereo.OneCenter.LocalizedChemicalRingPromotedChildMatch

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedChildMatch.keyAt_built
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedChildMatch.orderedChildren_sorted
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedChildMatch.matched_orderedChildren
