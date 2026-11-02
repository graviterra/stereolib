import TetraStereo.OneCenter.LocalizedRuleMajorBinaryPriorClasses
import TetraStereo.OneCenter.LocalizedRuleMajorActualSortCompleteness
import TetraStereo.OneCenter.DeclarativeCIPCompleteRootDescriptor
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Actual tracked flags count exactly the independent unordered pairs tied before Rule 5.
The binary-reference proof discharges the old max-two and cross-reading premises from actual
builder provenance. No independent physical graph-enantiomorphism claim is made here. -/

namespace TetraStereo.OneCenter.LocalizedRuleMajorReference
open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
noncomputable section
open scoped Classical

namespace GeneratedRuleMajorFullComparisonData
variable {input : Input} {center : input.certified.TetrahedralCenter}
  (data : GeneratedRuleMajorFullComparisonData input center)

theorem priorComparison (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic) (left right : Fin 4) :
    input.certified.compareLocalizedRerootCompoundRule4bcKeys
      (data.compounds left).prior (data.compounds right).prior =
      compare (ofLex (data.fullKey left)).1 (ofLex (data.fullKey right)).1 := by
  have built index : input.certified.buildActualRuleMajorCompoundRule45Key?
      (generatedTarget input center)
      (input.certified.molecularView (descriptorMap input) (generatedTarget input center))
      (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1))
      (input.certified.localizedLigandRootCursor center index) = some (data.compounds index) := by
    rw [molecularView_eq_generatedView input singleBonded acyclic]
    exact data.built index
  exact actual_ruleMajor_compound_prior_compare (descriptorMap input) (descriptorMap_tetrahedral input)
    (generatedTarget input center) (ActualReaderPhysicalBranchInverse.topTarget_root input center)
    (ActualReaderPhysicalBranchInverse.topTarget_address input center)
    singleBonded acyclic (data.stages left) (data.stages right)
    (data.widthBound left) (data.depthBound left) (data.widthBound right) (data.depthBound right)
    (built left) (built right)

end GeneratedRuleMajorFullComparisonData

namespace GeneratedRuleMajorFrameComparisonData
variable {input : Input} {center : input.certified.TetrahedralCenter}
  (frames : GeneratedRuleMajorFrameComparisonData input center)

def slotCompounds (slot : Fin 4) := frames.data.compounds (frames.ligandToSlot.symm slot)

theorem actualCallback_eq_compound : frames.actualCallback =
    compoundActualCompareAt input.certified frames.slotCompounds := by
  funext left right
  exact frames.callback_eq_compound left right

theorem slotCompounds_strict (distinct : Function.Injective frames.data.fullKey) :
    input.certified.CompoundKeyOffDiagonalStrict frames.slotCompounds := by
  intro left right different equal
  have ordering : (input.certified.compareLocalizedRerootCompoundThroughRule5
      (frames.slotCompounds left) (frames.slotCompounds right)).ordering = .eq := by
    rw [input.certified.compareLocalizedRerootCompoundThroughRule5_ordering]
    exact equal
  have keyEq := (frames.data.actualOrdering_eq_iff_fullKey_eq
    (frames.ligandToSlot.symm left) (frames.ligandToSlot.symm right)).mp ordering
  exact different (frames.ligandToSlot.symm.injective (distinct keyEq))

theorem slotPriorCount_eq_independent
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic) :
    sourceEnantiomorphicPairCount (compoundPriorTieRelation input.certified frames.slotCompounds) =
      completeRule5PairCount frames.data.fullKey := by
  have agree : ∀ left right,
      compoundPriorTieRelation input.certified frames.slotCompounds left right ↔
      CompletePriorPair frames.data.fullKey
        (frames.ligandToSlot.symm left) (frames.ligandToSlot.symm right) := by
    intro left right
    unfold compoundPriorTieRelation priorKeyTie slotCompounds CompletePriorPair
    rw [frames.data.priorComparison singleBonded acyclic,
      completeLigandPriorKey_compare_eq_iff]
    constructor
    · rintro ⟨different, equal⟩
      exact ⟨fun same => different (frames.ligandToSlot.symm.injective same), equal⟩
    · rintro ⟨different, equal⟩
      exact ⟨fun same => different (congrArg frames.ligandToSlot.symm same), equal⟩
  rw [sourceEnantiomorphicPairCount_congr_of_forall _ _ agree]
  exact sourceEnantiomorphicPairCount_perm (CompletePriorPair frames.data.fullKey)
    (fun _ _ pair => ⟨Ne.symm pair.1, pair.2.symm⟩) frames.ligandToSlot.symm

/-- The actual successful sort counts independent prior-tied pairs, without any supplied
maximum class size, mirror-reading relation, comparator strictness or pseudo-count premise. -/
theorem trackedCount_eq_independent
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (distinct : Function.Injective frames.data.fullKey)
    (tracked : TrackedLocalizedLigandOrder)
    (computed : safeTrackedOrderOrderedExecOf frames.actualCallback = some tracked) :
    tracked.pseudoComparisons = completeRule5PairCount frames.data.fullKey := by
  have strict := frames.slotCompounds_strict distinct
  have shapes : ∀ i, input.certified.RuleMajorReadingShape (frames.slotCompounds i) := by
    intro i
    exact frames.data.readingShape singleBonded acyclic (frames.ligandToSlot.symm i)
  obtain ⟨maxTwo, mirror⟩ := input.certified.ruleMajor_priorTie_dataCore frames.slotCompounds shapes strict
  obtain ⟨produced, sortComputed, _, _, count⟩ :=
    input.certified.sortFourLocalizedLigandsTracked_actualCompound_sourcePairFidelity
      frames.slotCompounds strict maxTwo mirror
  have same : produced = tracked := by
    rw [safeTrackedOrderOrderedExecOf_eq, frames.actualCallback_eq_compound] at computed
    unfold safeTrackedOrderOf at computed
    rw [sortComputed] at computed
    change (if orderCoherentOf (compoundActualCompareAt input.certified frames.slotCompounds)
      produced.highestFirst then some produced else none) = some tracked at computed
    split at computed
    · exact Option.some.inj computed
    · cases computed
  rw [← same, count, frames.slotPriorCount_eq_independent singleBonded acyclic]

end GeneratedRuleMajorFrameComparisonData
end
end TetraStereo.OneCenter.LocalizedRuleMajorReference

assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.GeneratedRuleMajorFullComparisonData.priorComparison
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.GeneratedRuleMajorFrameComparisonData.slotCompounds_strict
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.GeneratedRuleMajorFrameComparisonData.slotPriorCount_eq_independent
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.GeneratedRuleMajorFrameComparisonData.trackedCount_eq_independent
