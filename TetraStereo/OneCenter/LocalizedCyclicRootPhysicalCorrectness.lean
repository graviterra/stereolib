import TetraStereo.OneCenter.LocalizedCyclicRootPhysicalSetup
import TetraStereo.OneCenter.LocalizedCyclicPhysicalMirrorPriorTie
import TetraStereo.OneCenter.PhysicalEnantiomorphicPairCountReindexing
import TetraStereo.OneCenter.LocalizedRuleMajorBinaryPriorClasses
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0

/-!
# Physical correctness of the actual cyclic final-root keys

At the evaluator's own final root, in the physical domain of `CyclicRootPhysicalDomain`:

* physical proper distinguishability separates the actual compiled compounds
  (`compounds_offDiagonalStrict`), so the retained keys of the actual stage graphs and of the
  canonical predecessor cuts are injective;
* the builder's own reading shapes and the off-diagonal separation give the prior-tie class bound
  and the mirror readings (`compounds_dataCore`);
* every actual prior tie is a physical enantiomorphic pair of the detected ligand branches
  (`enantiomorphic_of_priorTie`, the accepted inverse).

Physical enantiomorphism also gives an actual prior tie, by the generated-reader mirror
transport on the canonical cuts. Thus both the retained and runtime prior-pair counts equal
the independent physical enantiomorphic pair count, reindexed through the actual frame alignment.
No comparison, selected-reference or reader-correspondence premise is supplied.
-/

namespace TetraStereo.OneCenter.LocalizedCyclicRootPhysicalCorrectness

open CertifiedLocalizedCIPInput
open LocalizedRuleMajorReference
open DeclarativeCIP
open RootedTetrahedralBranchSymmetry
open LocalizedCyclicMatchedReadingPhysicalTransport
open LocalizedCyclicRootPhysicalSetup

noncomputable section

variable {input : LocalizedRuleMajorReference.Input}
  {center : input.certified.TetrahedralCenter}
  {cfg : input.certified.detectedMultiCenterMolecule.Configuration}

/-! ## Separation and the data core -/

/-- **Physical distinguishability separates the actual compiled root compounds.** -/
theorem compounds_offDiagonalStrict (setup : CyclicRootPhysicalDomain input center cfg) :
    input.certified.CompoundKeyOffDiagonalStrict
      (finalRootFrames input setup.singleBonded center).compounds :=
  (finalRoot_physical_tie_classification input setup.singleBonded setup.charge center cfg
    setup.domain (properDistinct_slots setup.singleBonded center setup.properDistinct)).1

/-- The retained keys of the actual root stage graphs are injective. -/
theorem retainedKeys_injective (setup : CyclicRootPhysicalDomain input center cfg) :
    Function.Injective (finalRootFrames input setup.singleBonded center).retainedKeys := by
  intro i j equal
  by_contra different
  have full := (finalRootFrames input setup.singleBonded center).retainedActual_fullOrdering
    setup.singleBonded i j
  rw [CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundThroughRule5_ordering] at full
  have tie : compare ((finalRootFrames input setup.singleBonded center).retainedKeys i)
      ((finalRootFrames input setup.singleBonded center).retainedKeys j) = Ordering.eq :=
    (completeLigandRule5Key_compare_eq_iff _ _).mpr equal
  exact compounds_offDiagonalStrict setup i j different (full.trans tie)

/-- The retained keys of the canonical predecessor cuts are injective. -/
theorem canonicalCutKeys_injective (setup : CyclicRootPhysicalDomain input center cfg) :
    Function.Injective (retainedContextualFrameKeysAt input.certified.moleculeGraph
      (descriptorMap input) (finalCenterUnit input center)
      ((finalRootFrames input setup.singleBonded center).canonicalCutGraphs setup.singleBonded)
      (finalRootFrames input setup.singleBonded center).W
      (finalRootFrames input setup.singleBonded center).D) := by
  rw [canonicalCutKeys_eq_retainedKeys setup.singleBonded center]
  exact retainedKeys_injective setup

/-- The builder's own reading shapes, the prior-tie class bound and the mirror readings of the
actual root compounds. The shapes are the actual reference-count results of the compound builds. -/
theorem compounds_dataCore (setup : CyclicRootPhysicalDomain input center cfg) :
    (∀ slot, input.certified.RuleMajorReadingShape
      ((finalRootFrames input setup.singleBonded center).compounds slot)) ∧
    input.certified.PriorTieClassAtMostTwo
      (finalRootFrames input setup.singleBonded center).compounds ∧
    input.certified.PriorTieMirrorReadings
      (finalRootFrames input setup.singleBonded center).compounds := by
  have shaped := (finalRootFrames input setup.singleBonded center).retainedActual_readingShape
  obtain ⟨maxTwo, mirror⟩ := CertifiedLocalizedCIPInput.ruleMajor_priorTie_dataCore
    (finalRootFrames input setup.singleBonded center).compounds shaped
    (compounds_offDiagonalStrict setup)
  exact ⟨shaped, maxTwo, mirror⟩

/-! ## Prior ties and physical enantiomorphic pairs -/

/-- **Inverse.** An actual prior tie of two distinct root slots is a physical enantiomorphic pair
of the corresponding detected ligand branches. -/
theorem enantiomorphic_of_priorTie (setup : CyclicRootPhysicalDomain input center cfg)
    {i j : Fin 4} (distinct : i ≠ j)
    (priorTie : input.certified.compareLocalizedRerootCompoundRule4bcKeys
      ((finalRootFrames input setup.singleBonded center).compounds i).prior
      ((finalRootFrames input setup.singleBonded center).compounds j).prior = Ordering.eq) :
    Enantiomorphic input.certified.detectedMultiCenterMolecule cfg center
      ((finalRootFrames input setup.singleBonded center).detectedLigandPermutation i)
      ((finalRootFrames input setup.singleBonded center).detectedLigandPermutation j) :=
  (finalRoot_physical_tie_classification input setup.singleBonded setup.charge center cfg
    setup.domain (properDistinct_slots setup.singleBonded center setup.properDistinct)).2
      i j distinct priorTie

/-- **Converse physical prior-tie law at the final root.** Every physical enantiomorphic pair of
detected root ligand branches is an actual prior tie of the compiled compounds at the aligned
slots. The following theorem derives this law from the physical domain. -/
def FinalRootConversePriorTie (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (center : input.certified.TetrahedralCenter)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration) : Prop :=
  ∀ i j : Fin 4, i ≠ j →
    Enantiomorphic input.certified.detectedMultiCenterMolecule cfg center
        ((finalRootFrames input singleBonded center).detectedLigandPermutation i)
        ((finalRootFrames input singleBonded center).detectedLigandPermutation j) →
      input.certified.compareLocalizedRerootCompoundRule4bcKeys
        ((finalRootFrames input singleBonded center).compounds i).prior
        ((finalRootFrames input singleBonded center).compounds j).prior = Ordering.eq

/-- The physical prior-tie converse is a theorem of the actual physical domain. -/
theorem finalRootConversePriorTie_of_physicalDomain
    (setup : CyclicRootPhysicalDomain input center cfg) :
    FinalRootConversePriorTie input setup.singleBonded center cfg := by
  intro i j distinct physical
  exact LocalizedCyclicPhysicalMirrorPriorTie.finalRoot_priorTie_of_mirrorTransport
    input setup.singleBonded setup.charge center distinct cfg setup.domain physical.2.1

/-- Exact pointwise law at distinct slots: actual prior tie iff physical enantiomorphic pair. -/
theorem priorTie_iff_enantiomorphic (setup : CyclicRootPhysicalDomain input center cfg)
    {i j : Fin 4} (distinct : i ≠ j) :
    input.certified.compareLocalizedRerootCompoundRule4bcKeys
        ((finalRootFrames input setup.singleBonded center).compounds i).prior
        ((finalRootFrames input setup.singleBonded center).compounds j).prior = Ordering.eq ↔
      Enantiomorphic input.certified.detectedMultiCenterMolecule cfg center
        ((finalRootFrames input setup.singleBonded center).detectedLigandPermutation i)
        ((finalRootFrames input setup.singleBonded center).detectedLigandPermutation j) :=
  ⟨enantiomorphic_of_priorTie setup distinct, (finalRootConversePriorTie_of_physicalDomain setup) i j distinct⟩

/-- The independent retained prior pairs of the actual stage keys are exactly the physical
enantiomorphic pairs read through the frame alignment. -/
theorem completePriorPair_iff_enantiomorphic (setup : CyclicRootPhysicalDomain input center cfg)
    (i j : Fin 4) :
    CompletePriorPair (finalRootFrames input setup.singleBonded center).retainedKeys i j ↔
      Enantiomorphic input.certified.detectedMultiCenterMolecule cfg center
        ((finalRootFrames input setup.singleBonded center).detectedLigandPermutation i)
        ((finalRootFrames input setup.singleBonded center).detectedLigandPermutation j) := by
  constructor
  · rintro ⟨distinct, priorEq⟩
    have priorTie :=
      ((finalRootFrames input setup.singleBonded center).retainedActual_priorComparison
        setup.singleBonded i j).trans ((completeLigandPriorKey_compare_eq_iff _ _).mpr priorEq)
    exact enantiomorphic_of_priorTie setup distinct priorTie
  · intro pair
    have distinct : i ≠ j := fun same =>
      pair.1 (congrArg (finalRootFrames input setup.singleBonded center).detectedLigandPermutation
        same)
    refine ⟨distinct, (completeLigandPriorKey_compare_eq_iff _ _).mp ?_⟩
    exact ((finalRootFrames input setup.singleBonded center).retainedActual_priorComparison
      setup.singleBonded i j).symm.trans ((finalRootConversePriorTie_of_physicalDomain setup) i j distinct pair)

/-! ## The pair-count bijection -/

/-- **The retained prior-pair count is the physical enantiomorphic pair count**, reindexed through
the actual frame alignment to the detected physical ligands. -/
theorem retainedPairCount_eq_physicalCount (setup : CyclicRootPhysicalDomain input center cfg)
    :
    completeRule5PairCount (finalRootFrames input setup.singleBonded center).retainedKeys =
      physicalEnantiomorphicPairCount input.certified.detectedMultiCenterMolecule cfg center := by
  classical
  rw [← frameEnumeratedEnantiomorphicPairCount_eq input.certified.detectedMultiCenterMolecule cfg
    center (finalRootFrames input setup.singleBonded center).detectedLigandPermutation]
  unfold completeRule5PairCount frameEnumeratedEnantiomorphicPairCount
  exact sourceEnantiomorphicPairCount_congr _ _
    (fun i j _ => completePriorPair_iff_enantiomorphic setup i j)

/-- The same count on the canonical predecessor cuts. -/
theorem canonicalCutPairCount_eq_physicalCount (setup : CyclicRootPhysicalDomain input center cfg)
    :
    completeRule5PairCount (retainedContextualFrameKeysAt input.certified.moleculeGraph
        (descriptorMap input) (finalCenterUnit input center)
        ((finalRootFrames input setup.singleBonded center).canonicalCutGraphs setup.singleBonded)
        (finalRootFrames input setup.singleBonded center).W
        (finalRootFrames input setup.singleBonded center).D) =
      physicalEnantiomorphicPairCount input.certified.detectedMultiCenterMolecule cfg center := by
  rw [canonicalCutKeys_eq_retainedKeys setup.singleBonded center]
  exact retainedPairCount_eq_physicalCount setup

/-- The actual compound prior-tie relation, the one the runtime tracked sorter counts, has the
physical enantiomorphic pair count. -/
theorem compoundPriorTieCount_eq_physicalCount (setup : CyclicRootPhysicalDomain input center cfg)
    :
    sourceEnantiomorphicPairCount (compoundPriorTieRelation input.certified
        (finalRootFrames input setup.singleBonded center).compounds) =
      physicalEnantiomorphicPairCount input.certified.detectedMultiCenterMolecule cfg center := by
  classical
  rw [← frameEnumeratedEnantiomorphicPairCount_eq input.certified.detectedMultiCenterMolecule cfg
    center (finalRootFrames input setup.singleBonded center).detectedLigandPermutation]
  unfold frameEnumeratedEnantiomorphicPairCount
  refine sourceEnantiomorphicPairCount_congr _ _ (fun i j distinct => ?_)
  change i ≠ j ∧ input.certified.compareLocalizedRerootCompoundRule4bcKeys
      ((finalRootFrames input setup.singleBonded center).compounds i).prior
      ((finalRootFrames input setup.singleBonded center).compounds j).prior = Ordering.eq ↔ _
  rw [priorTie_iff_enantiomorphic setup distinct]
  exact ⟨fun pair => pair.2, fun pair => ⟨distinct, pair⟩⟩

end

end TetraStereo.OneCenter.LocalizedCyclicRootPhysicalCorrectness

assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootPhysicalCorrectness.compounds_offDiagonalStrict
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootPhysicalCorrectness.retainedKeys_injective
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootPhysicalCorrectness.canonicalCutKeys_injective
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootPhysicalCorrectness.compounds_dataCore
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootPhysicalCorrectness.enantiomorphic_of_priorTie
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootPhysicalCorrectness.FinalRootConversePriorTie
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootPhysicalCorrectness.priorTie_iff_enantiomorphic
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootPhysicalCorrectness.completePriorPair_iff_enantiomorphic
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootPhysicalCorrectness.retainedPairCount_eq_physicalCount
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootPhysicalCorrectness.canonicalCutPairCount_eq_physicalCount
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootPhysicalCorrectness.compoundPriorTieCount_eq_physicalCount

assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicRootPhysicalCorrectness.finalRootConversePriorTie_of_physicalDomain
