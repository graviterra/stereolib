import TetraStereo.OneCenter.LocalizedContextCompoundIndependentReadings
import TetraStereo.OneCenter.LocalizedContextCrossBranchReadingComparison
import TetraStereo.OneCenter.LocalizedContextRule4aComparison
import TetraStereo.OneCenter.LocalizedRuleMajorCompoundComparisonAlgebra
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Complete actual compound order through Rule4c at arbitrary generated auxiliary targets.
The reference population, alternative order, and all gated earlier-column ties are derived. -/

namespace TetraStereo.OneCenter.DeclarativeCIP
noncomputable section
universe u

private def unmaskedContextualPriorSignatureAt {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom) (W D : Nat) :
    CompletePriorSignature :=
  let selection := contextualReferenceSelection molecule descriptorMap unit graph
  let readings := contextualCompleteReadingsAt molecule descriptorMap unit graph W D
  toLex (selection.countPriority, toLex
    (readings.map (fun key => (ofLex key).1), readings.map (fun key => (ofLex key).2)))

private theorem compare_unmaskedContextualPriorSignature_eq
    {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (left right : RootedDigraph Atom) (W D : Nat) :
    compare (unmaskedContextualPriorSignatureAt molecule descriptorMap unit left W D)
        (unmaskedContextualPriorSignatureAt molecule descriptorMap unit right W D) =
      compare (contextualCompletePriorSignatureAt molecule descriptorMap unit left W D)
        (contextualCompletePriorSignatureAt molecule descriptorMap unit right W D) := by
  unfold unmaskedContextualPriorSignatureAt contextualCompletePriorSignatureAt
  cases hL : contextualReferenceSelection molecule descriptorMap unit left <;>
    cases hR : contextualReferenceSelection molecule descriptorMap unit right <;>
    simp only [ReferenceSelection.countPriority, reduceCtorEq, ↓reduceIte]
  all_goals first
    | rfl
    | (simp only [contextualCompleteReadingsAt, hL, hR, contextualCompleteReadingAt,
        List.map_cons, List.map_nil, ofLex_toLex]; rfl)

end
end TetraStereo.OneCenter.DeclarativeCIP

namespace TetraStereo.OneCenter.Rule4aTableBridge
open CertifiedLocalizedCIPInput LocalizedCumulativeDecoratedTree DeclarativeCIP
noncomputable section

section Algebra
variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
  {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
  {cursorL cursorR : input.LocalizedRerootCursor carrierFuel}
  (singleBonded : input.moleculeGraph.SimpleBonded)
  (leftStages : input.RuleMajorContextStages carrierFuel read cursorL)
  (rightStages : input.RuleMajorContextStages carrierFuel read cursorR)
  (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
  (unit : DetectedOccurrence input.moleculeGraph)
  (readL : RuleMajorContextReadingReadbacks leftStages descriptorMap unit)
  (readR : RuleMajorContextReadingReadbacks rightStages descriptorMap unit)
  (isoL : RuleMajorContextStageGraphIsoBundle leftStages)
  (isoR : RuleMajorContextStageGraphIsoBundle rightStages)
  {W D : Nat} (leftWidth : leftStages.widthBound ≤ W) (leftDepth : leftStages.depthBound ≤ D)
  (rightWidth : rightStages.widthBound ≤ W) (rightDepth : rightStages.depthBound ≤ D)
  {left right : input.LocalizedRerootCompoundRule45Key}

include singleBonded readL readR isoL isoR leftWidth leftDepth rightWidth rightDepth

private theorem reading_comparisons
    (dataL : ContextCompoundReadbackData leftStages descriptorMap unit left W D)
    (dataR : ContextCompoundReadbackData rightStages descriptorMap unit right W D)
    (aTie : input.compareLocalizedRerootCumulativeRule45Keys
      leftStages.a.key rightStages.a.key = .eq)
    (countTie : left.prior.referenceCountPriority = right.prior.referenceCountPriority)
    (l : input.LocalizedRerootRule4bcReading) (hl : l ∈ left.prior.readings)
    (r : input.LocalizedRerootRule4bcReading) (hr : r ∈ right.prior.readings) :
    let observedL := contextualCompleteReadingAt input.moleculeGraph descriptorMap unit
      (ruleMajorTreeGraph leftStages.a.tree) W D (l.reference?.map senseOf)
    let observedR := contextualCompleteReadingAt input.moleculeGraph descriptorMap unit
      (ruleMajorTreeGraph rightStages.a.tree) W D (r.reference?.map senseOf)
    input.compareLocalizedRerootRule4bcReadingsByRule4b l r =
        compare (ofLex observedL).1 (ofLex observedR).1 ∧
      (input.compareLocalizedRerootRule4bcReadingsByRule4b l r = .eq →
        OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
          l.rule4cKey.descriptor r.rule4cKey.descriptor =
            compare (ofLex observedL).2 (ofLex observedR).2) := by
  dsimp only
  have emptyIff := ReferenceSelection.empty_iff_of_countPriority_eq
    (dataL.count.symm.trans (countTie.trans dataR.count))
  have lp := dataL.readingStages l hl
  have rp := dataR.readingStages r hr
  cases hL : l.reference? with
  | none =>
      have rightNone := (dataR.readingEmpty r hr).mpr
        (emptyIff.mp ((dataL.readingEmpty l hl).mp hL))
      rw [hL] at lp
      rw [rightNone] at rp
      simp only [rightNone, Option.map_none]
      constructor
      · change OfficialRuleMajorKey.compareSparseLayers _ _ _ = compare ([] :
          Certificate.CanonicalSphereKey.Key StereoLabel) []
        dsimp only
        rw [lp.1, rp.1]
        exact (Ordering.then_eq_eq.mp aTie).2
      · intro _
        rw [lp.2, rp.2]
        exact contextCrossBranch_noReference_compare singleBonded leftStages rightStages descriptorMap unit readL readR isoL isoR
          aTie leftWidth leftDepth rightWidth rightDepth
  | some refL =>
      cases hR : r.reference? with
      | none =>
          have leftNone := (dataL.readingEmpty l hl).mpr
            (emptyIff.mpr ((dataR.readingEmpty r hr).mp hR))
          simp [hL] at leftNone
      | some refR =>
          rw [hL] at lp
          rw [hR] at rp
          simp only [Option.map_some]
          constructor
          · change OfficialRuleMajorKey.compareSparseLayers _ _ _ = _
            dsimp only
            rw [lp.1, rp.1]
            exact contextCrossBranch_selectedB_compare singleBonded leftStages rightStages descriptorMap unit readL readR isoL isoR
              refL refR aTie leftWidth leftDepth rightWidth rightDepth
          · intro bTie
            change OfficialRuleMajorKey.compareSparseLayers _
              l.rule4bKey.descriptor r.rule4bKey.descriptor = .eq at bTie
            rw [lp.1, rp.1] at bTie
            rw [lp.2, rp.2]
            exact contextCrossBranch_selectedC_compare singleBonded leftStages rightStages descriptorMap unit readL readR isoL isoR
              refL refR aTie bTie leftWidth leftDepth rightWidth rightDepth

private theorem compound_after4a_compare
    (dataL : ContextCompoundReadbackData leftStages descriptorMap unit left W D)
    (dataR : ContextCompoundReadbackData rightStages descriptorMap unit right W D)
    (aTie : input.compareLocalizedRerootCumulativeRule45Keys
      leftStages.a.key rightStages.a.key = .eq) :
    input.compareLocalizedRerootCompoundRule4bcAfterRule4a left.prior right.prior =
      compare (contextualCompletePriorSignatureAt input.moleculeGraph descriptorMap
        unit (ruleMajorTreeGraph leftStages.a.tree) W D)
        (contextualCompletePriorSignatureAt input.moleculeGraph descriptorMap
          unit (ruleMajorTreeGraph rightStages.a.tree) W D) := by
  rw [← compare_unmaskedContextualPriorSignature_eq]
  change (compare left.prior.referenceCountPriority right.prior.referenceCountPriority).then _ =
    (compare
      (contextualReferenceSelection input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph leftStages.a.tree)).countPriority
      (contextualReferenceSelection input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph rightStages.a.tree)).countPriority).then _
  rw [← dataL.count, ← dataR.count]
  apply then_congr
  intro countTie
  have countEq := compare_eq_iff_eq.mp countTie
  let observeL := fun reading : input.LocalizedRerootRule4bcReading =>
    contextualCompleteReadingAt input.moleculeGraph descriptorMap unit
      (ruleMajorTreeGraph leftStages.a.tree) W D (reading.reference?.map senseOf)
  let observeR := fun reading : input.LocalizedRerootRule4bcReading =>
    contextualCompleteReadingAt input.moleculeGraph descriptorMap unit
      (ruleMajorTreeGraph rightStages.a.tree) W D (reading.reference?.map senseOf)
  have agrees := reading_comparisons singleBonded leftStages rightStages descriptorMap unit readL readR isoL isoR leftWidth leftDepth rightWidth rightDepth
    dataL dataR aTie countEq
  have lists := compareLex_then_map_eq
    input.compareLocalizedRerootRule4bcReadingsByRule4b
    (fun l r => OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
      l.rule4cKey.descriptor r.rule4cKey.descriptor)
    compare compare (fun l => (ofLex (observeL l)).1) (fun r => (ofLex (observeR r)).1)
    (fun l => (ofLex (observeL l)).2) (fun r => (ofLex (observeR r)).2)
    left.prior.readings right.prior.readings
    (fun l hl r hr => (agrees l hl r hr).1)
    (fun l hl r hr => (agrees l hl r hr).2)
  have fstL := congrArg (List.map (fun key : CompleteReadingKey => (ofLex key).1)) dataL.observations
  have fstR := congrArg (List.map (fun key : CompleteReadingKey => (ofLex key).1)) dataR.observations
  have sndL := congrArg (List.map (fun key : CompleteReadingKey => (ofLex key).2)) dataL.observations
  have sndR := congrArg (List.map (fun key : CompleteReadingKey => (ofLex key).2)) dataR.observations
  simp only [List.map_map, Function.comp_def] at fstL fstR sndL sndR
  dsimp only [observeL, observeR] at lists
  rw [fstL, fstR, sndL, sndR] at lists
  exact lists

end Algebra

/-- Every actual generated compound pair agrees with the independent contextual priority
through Rule4c. The target path, depth, auxiliary label kinds and reference counts are unrestricted
on the finite acyclic single-bond domain. Stage and compound success are execution witnesses;
no reader, selected-reference, sorting, or desired comparison property is supplied. -/
theorem generatedContextCompound_prior_compare
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (target : input.certified.LocalizedRerootCursor
      (input.certified.certified.input.molecule.atomCount + 1))
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.occurrence.1 = unit.1)
    (cursorL cursorR : input.certified.LocalizedRerootCursor
      (input.certified.certified.input.molecule.atomCount + 1))
    (childL : cursorL ∈ input.certified.executableLocalizedRerootChildren target)
    (childR : cursorR ∈ input.certified.executableLocalizedRerootChildren target)
    (leftStages : input.certified.RuleMajorContextStages
      (input.certified.certified.input.molecule.atomCount + 1)
      (input.certified.localizedDependencyLabel target.occurrence
        (input.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState input) target.occurrence)) cursorL)
    (rightStages : input.certified.RuleMajorContextStages
      (input.certified.certified.input.molecule.atomCount + 1)
      (input.certified.localizedDependencyLabel target.occurrence
        (input.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState input) target.occurrence)) cursorR)
    {W D : Nat} (leftWidth : leftStages.widthBound ≤ W) (leftDepth : leftStages.depthBound ≤ D)
    (rightWidth : rightStages.widthBound ≤ W) (rightDepth : rightStages.depthBound ≤ D)
    {left right : input.certified.LocalizedRerootCompoundRule45Key}
    (builtL : input.certified.buildActualRuleMajorCompoundRule45KeyExec? target.occurrence
      (input.certified.localizedDependencyView
        (LocalizedRuleMajorReference.referenceState input) target.occurrence)
      (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1)) cursorL = some left)
    (builtR : input.certified.buildActualRuleMajorCompoundRule45KeyExec? target.occurrence
      (input.certified.localizedDependencyView
        (LocalizedRuleMajorReference.referenceState input) target.occurrence)
      (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1)) cursorR = some right) :
    input.certified.compareLocalizedRerootCompoundRule4bcKeys left.prior right.prior =
      compare
        (contextualCompleteLigandPriorKeyAt input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit
          (ruleMajorTreeGraph leftStages.a.tree) W D)
        (contextualCompleteLigandPriorKeyAt input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit
          (ruleMajorTreeGraph rightStages.a.tree) W D) := by
  have dataL := generatedContextCompound_independentReadback input singleBonded acyclic
    target unit targetUnit cursorL childL leftStages leftWidth leftDepth builtL
  have dataR := generatedContextCompound_independentReadback input singleBonded acyclic
    target unit targetUnit cursorR childR rightStages rightWidth rightDepth builtR
  let readL := ruleMajorContextReadingReadbacks_of_generatedActualChild input singleBonded acyclic
    target unit targetUnit cursorL childL leftStages
  let readR := ruleMajorContextReadingReadbacks_of_generatedActualChild input singleBonded acyclic
    target unit targetUnit cursorR childR rightStages
  let isoL := ruleMajorContextStageGraphIsoBundle_of_generatedActualChild input singleBonded acyclic
    target cursorL childL leftStages
  let isoR := ruleMajorContextStageGraphIsoBundle_of_generatedActualChild input singleBonded acyclic
    target cursorR childR rightStages
  have initialCompare := generatedContextTrees_rule4a_compare input singleBonded acyclic
    target unit targetUnit leftStages.a.tree rightStages.a.tree leftStages.a.trace rightStages.a.trace
    (by simpa only [leftStages.a.sourceEq] using childL)
    (by simpa only [rightStages.a.sourceEq] using childR)
    (leftStages.a_width_le.trans leftWidth) (rightStages.a_width_le.trans rightWidth)
    (leftStages.a_depth_le.trans leftDepth) (rightStages.a_depth_le.trans rightDepth)
  change (input.certified.compareLocalizedRerootCumulativeRule45Keys left.prior.rule4aKey
    right.prior.rule4aKey).then
      (input.certified.compareLocalizedRerootCompoundRule4bcAfterRule4a left.prior right.prior) =
    (compare
      (contextualMolecularRankPairAt input.certified.moleculeGraph
        (LocalizedRuleMajorReference.descriptorMap input) unit (ruleMajorTreeGraph leftStages.a.tree) W D)
      (contextualMolecularRankPairAt input.certified.moleculeGraph
        (LocalizedRuleMajorReference.descriptorMap input) unit (ruleMajorTreeGraph rightStages.a.tree) W D)).then _
  rw [dataL.aKey, dataR.aKey, ← initialCompare]
  exact then_congr (fun tied => compound_after4a_compare singleBonded leftStages rightStages
    (LocalizedRuleMajorReference.descriptorMap input) unit readL readR isoL isoR
    leftWidth leftDepth rightWidth rightDepth dataL dataR tied)

end
end TetraStereo.OneCenter.Rule4aTableBridge

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.generatedContextCompound_prior_compare
