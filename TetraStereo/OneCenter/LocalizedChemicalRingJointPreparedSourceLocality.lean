import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedDeepCutPrior
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Strict-descendant locality of the molecular-cut joint priorities.

Candidate maps need agree only beyond the target depth. The cutoff then agrees exactly;
the source priorities agree, and the actual deep priorities have the same sibling order
even though their compiled encodings and windows can differ. On a realized tree this
also identifies the full joint marker. This is a locality lemma for the auxiliary-model
construction, not an assertion that the candidates already have chemical meaning.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceLocality

open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
open LocalizedMarkedRetainedMolecularSelection (retainedCarrierFuel)
open LocalizedMarkedRetainedVirtualTarget LocalizedMarkedRetainedCanonicalFrame
open LocalizedChemicalRingJointPreparedDeepCutPrior
open LocalizedChemicalRingJointMarkerKey LocalizedCumulativeDecoratedTree

noncomputable section

variable {input : CertifiedLocalizedCIPInput}
  {first second : DescriptorMap (DetectedOccurrence input.moleculeGraph)}

/-- Equality of the cut maps is precisely agreement on strict descendant depths.
No agreement at the target or at any shallower occurrence is required. -/
theorem cutMap_eq_iff (bound : Nat) :
    cutMap first bound = cutMap second bound ↔
      ∀ unit, bound < unit.1.path.length → first unit = second unit := by
  constructor
  · intro same unit deeper
    have atUnit := congrFun same unit
    simpa only [cutMap, if_pos deeper] using atUnit
  · intro agree
    funext unit
    by_cases deeper : bound < unit.1.path.length
    · simp only [cutMap, if_pos deeper, agree unit deeper]
    · simp only [cutMap, if_neg deeper]

variable (single : input.moleculeGraph.SimpleBonded)
  (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
  (fallback : CompleteLigandRule5Key)
  (agree : ∀ unit, target.1.address.length < unit.1.path.length →
    first unit = second unit)

include single agree

/-- Every source-cut priority reads only the candidate labels beyond the target. -/
theorem sourceDeepKey_eq
    (parent child : input.LocalizedRerootCursor (retainedCarrierFuel input)) :
    sourceDeepKey input single first target fallback parent child =
      sourceDeepKey input single second target fallback parent child := by
  unfold sourceDeepKey
  rw [(cutMap_eq_iff target.1.address.length).mpr agree]

/-- Actual deep sibling comparisons, including ties, are insensitive to all excluded
candidate entries. Their compiled window sizes need not be equal. -/
theorem deepKey_orderAgrees
    (parent left right : input.LocalizedRerootCursor (retainedCarrierFuel input))
    (leftMember : left ∈ input.executableLocalizedRerootChildren parent)
    (rightMember : right ∈ input.executableLocalizedRerootChildren parent) :
    OrderAgrees (deepKey first target fallback parent left)
      (deepKey first target fallback parent right)
      (deepKey second target fallback parent left)
      (deepKey second target fallback parent right) := by
  have firstBridge := deepKey_orderAgrees_sourceDeepKey input single first target fallback
    parent left right leftMember rightMember
  have secondBridge := deepKey_orderAgrees_sourceDeepKey input single second target fallback
    parent left right leftMember rightMember
  rw [sourceDeepKey_eq single target fallback agree parent left,
    sourceDeepKey_eq single target fallback agree parent right] at firstBridge
  exact ⟨firstBridge.1.trans secondBridge.1.symm,
    firstBridge.2.trans secondBridge.2.symm⟩

/-- On a structural representation, the complete source-prior function is local. -/
theorem sourceDeepPrior_eq
    (tree : LocalizedCumulativeDecoratedTree input (retainedCarrierFuel input)) :
    sourceDeepPrior input single first target fallback tree =
      sourceDeepPrior input single second target fallback tree := by
  funext node
  exact sourceDeepKey_eq single target fallback agree _ _

/-- The complete ordered-reference marker has the same locality, at every node.
The tree may be realized by any reader; no desired label or comparator is assumed. -/
theorem jointMarkerKey_eq
    (tree : LocalizedCumulativeDecoratedTree input (retainedCarrierFuel input))
    {read : input.LocalizedRerootCursor (retainedCarrierFuel input) →
      Option LocalizedAuxiliaryLabel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (marks : (ruleMajorTreeGraph tree).Node → List Nat) (W D n : Nat)
    (node : (ruleMajorTreeGraph tree).Node) :
    jointMarkerKey (ruleMajorTreeGraph tree) (deepPrior first target fallback tree)
        marks W D n node =
      jointMarkerKey (ruleMajorTreeGraph tree) (deepPrior second target fallback tree)
        marks W D n node := by
  rw [jointMarkerKey_deepPrior_eq_source input single first target fallback tree realizes,
    jointMarkerKey_deepPrior_eq_source input single second target fallback tree realizes,
    sourceDeepPrior_eq single target fallback agree tree]

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceLocality

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceLocality.cutMap_eq_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceLocality.sourceDeepKey_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceLocality.deepKey_orderAgrees
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceLocality.sourceDeepPrior_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceLocality.jointMarkerKey_eq
