import TetraStereo.OneCenter.LocalizedContextCompoundIndependentReadings
import TetraStereo.OneCenter.LocalizedContextRule5Comparison
import TetraStereo.OneCenter.LocalizedRuleMajorCompoundComparisonAlgebra
import TetraStereo.OneCenter.LocalizedRuleMajorRule5Observation
import TetraStereo.OneCenter.LocalizedActualRule4aTableBridge
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! Compare the actual Rule-5 output streams against the contextual independent streams at
arbitrary generated auxiliary targets. Exact stage readback and tag alignment are derived from
the successful compound builds; empty-reference readings retain their Rule-4c data. -/

namespace TetraStereo.OneCenter
namespace Rule4aTableBridge

open CertifiedLocalizedCIPInput DeclarativeCIP LocalizedCumulativeDecoratedTree
open Rule5ObservationBridge
noncomputable section

private theorem completeListTie_of_rule4b_rule4c_ties
    {input : CertifiedLocalizedCIPInput}
    (left right : List input.LocalizedRerootRule4bcReading)
    (rule4bTie : input.compareLocalizedRerootCompoundRule4bReadings left right = .eq)
    (rule4cTie : input.compareLocalizedRerootCompoundRule4cReadings left right = .eq) :
    List.compareLex input.compareRule4bcReadingsComplete left right = .eq := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons y ys =>
          change List.compareLex input.compareLocalizedRerootRule4bcReadingsByRule4b []
              (y :: ys) = .eq at rule4bTie
          have impossible := List.compareLex_nil_left_eq_eq.mp rule4bTie
          cases impossible
  | cons x xs ih =>
      cases right with
      | nil =>
          change List.compareLex input.compareLocalizedRerootRule4bcReadingsByRule4b
              (x :: xs) [] = .eq at rule4bTie
          have impossible := List.compareLex_nil_right_eq_eq.mp rule4bTie
          cases impossible
      | cons y ys =>
          simp only [compareLocalizedRerootCompoundRule4bReadings,
            compareLocalizedRerootCompoundRule4cReadings,
            List.compareLex_cons_cons, Ordering.then_eq_eq] at rule4bTie rule4cTie
          have cHead : OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
              x.rule4cKey.descriptor y.rule4cKey.descriptor = .eq := by
            simpa [Ordering.byKey] using rule4cTie.1
          have head : input.compareRule4bcReadingsComplete x y = .eq := by
            unfold compareRule4bcReadingsComplete
            rw [localizedCompareLex_eq_right_of_eq rule4bTie.1]
            exact cHead
          rw [List.compareLex_cons_cons, head, Ordering.eq_then]
          exact ih ys rule4bTie.2 rule4cTie.2

private theorem expectedRule5_descriptor
    {input : CertifiedLocalizedCIPInput} (common : RS)
    (reading : input.LocalizedRerootRule4bcReading) :
    input.localizedRerootRule5Descriptor common
        (input.ruleMajorExpectedRule5Reading reading) =
      (input.rule5LiftKey
        (match reading.reference? with
          | none => false
          | some own => common == own) reading.rule4cKey).descriptor := by
  cases common <;> cases ref : reading.reference? with
  | none => simp [ruleMajorExpectedRule5Reading, localizedRerootRule5Descriptor, ref]
  | some own => cases own <;>
      simp [ruleMajorExpectedRule5Reading, localizedRerootRule5Descriptor, ref]

private theorem contextRule5Pair_compare
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
    (readL : RuleMajorContextReadingReadbacks leftStages
      (LocalizedRuleMajorReference.descriptorMap input) unit)
    (readR : RuleMajorContextReadingReadbacks rightStages
      (LocalizedRuleMajorReference.descriptorMap input) unit)
    (isoL : RuleMajorContextStageGraphIsoBundle leftStages)
    (isoR : RuleMajorContextStageGraphIsoBundle rightStages)
    {W D : Nat}
    {left right : input.certified.LocalizedRerootCompoundRule45Key}
    (dataL : ContextCompoundReadbackData leftStages
      (LocalizedRuleMajorReference.descriptorMap input) unit left W D)
    (dataR : ContextCompoundReadbackData rightStages
      (LocalizedRuleMajorReference.descriptorMap input) unit right W D)
    (leftWidth : leftStages.widthBound ≤ W) (leftDepth : leftStages.depthBound ≤ D)
    (rightWidth : rightStages.widthBound ≤ W) (rightDepth : rightStages.depthBound ≤ D)
    (aTie : input.certified.compareLocalizedRerootCumulativeRule45Keys
      leftStages.a.key rightStages.a.key = .eq)
    (countEq : left.prior.referenceCountPriority = right.prior.referenceCountPriority)
    (common : RS)
    (x : input.certified.LocalizedRerootRule4bcReading) (hx : x ∈ left.prior.readings)
    (y : input.certified.LocalizedRerootRule4bcReading) (hy : y ∈ right.prior.readings)
    (priorEq : input.certified.compareRule4bcReadingsComplete x y = .eq) :
    Ordering.byKey
        (fun reading => input.certified.localizedRerootRule5Descriptor common
          (input.certified.ruleMajorExpectedRule5Reading reading))
        (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority)
        x y =
      compare
        (contextualCompleteRule5ReadingAt input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit
          (ruleMajorTreeGraph leftStages.a.tree) W D
          (x.reference?.map senseOf) (senseOf common))
        (contextualCompleteRule5ReadingAt input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit
          (ruleMajorTreeGraph rightStages.a.tree) W D
          (y.reference?.map senseOf) (senseOf common)) := by
  have countValues :
      (contextualReferenceSelection input.certified.moleculeGraph
        (LocalizedRuleMajorReference.descriptorMap input) unit
        (ruleMajorTreeGraph leftStages.a.tree)).countPriority =
      (contextualReferenceSelection input.certified.moleculeGraph
        (LocalizedRuleMajorReference.descriptorMap input) unit
        (ruleMajorTreeGraph rightStages.a.tree)).countPriority := by
    rw [← dataL.count, ← dataR.count]
    exact countEq
  have emptyIff := ReferenceSelection.empty_iff_of_countPriority_eq countValues
  have stagesL := dataL.readingStages x hx
  have stagesR := dataR.readingStages y hy
  have priorParts :
      input.certified.compareLocalizedRerootRule4bcReadingsByRule4b x y = .eq ∧
      OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        x.rule4cKey.descriptor y.rule4cKey.descriptor = .eq := by
    unfold compareRule4bcReadingsComplete at priorEq
    cases hB : input.certified.compareLocalizedRerootRule4bcReadingsByRule4b x y with
    | lt => simp [compareLex, hB] at priorEq
    | gt => simp [compareLex, hB] at priorEq
    | eq =>
        simp [compareLex, hB] at priorEq
        exact ⟨rfl, by simpa [Ordering.byKey, compareLex, hB] using priorEq⟩
  have compareDescriptor :
      OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        (input.certified.localizedRerootRule5Descriptor common
          (input.certified.ruleMajorExpectedRule5Reading x))
        (input.certified.localizedRerootRule5Descriptor common
          (input.certified.ruleMajorExpectedRule5Reading y)) =
      compare
        (contextualCompleteRule5ReadingAt input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit
          (ruleMajorTreeGraph leftStages.a.tree) W D
          (x.reference?.map senseOf) (senseOf common))
        (contextualCompleteRule5ReadingAt input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit
          (ruleMajorTreeGraph rightStages.a.tree) W D
          (y.reference?.map senseOf) (senseOf common)) := by
    cases hxRef : x.reference? with
    | none =>
        have leftEmpty := (dataL.readingEmpty x hx).mp hxRef
        have rightEmpty := emptyIff.mp leftEmpty
        have hyRef : y.reference? = none := (dataR.readingEmpty y hy).mpr rightEmpty
        simp [hxRef] at stagesL
        simp [hyRef] at stagesR
        have cTie : OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
            leftStages.noReference.key.descriptor rightStages.noReference.key.descriptor = .eq := by
          simpa [stagesL.2, stagesR.2] using priorParts.2
        have leftNoReference := stagesL.2
        have rightNoReference := stagesR.2
        have descriptorEq : leftStages.noReference.key.descriptor =
            rightStages.noReference.key.descriptor :=
          (compareSparseLayers_compareLocalizedCumulativeRule45Priority_eq_iff _ _).mp cTie
        have actualEq : OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
            (input.certified.rule5LiftKey false leftStages.noReference.key).descriptor
            (input.certified.rule5LiftKey false rightStages.noReference.key).descriptor = .eq := by
          rw [Rule5ObservationBridge.compare_lifts_eq_bits false false
            leftStages.noReference.key rightStages.noReference.key descriptorEq]
          have bitEq : Rule5ObservationBridge.bitTable false leftStages.noReference.key =
              Rule5ObservationBridge.bitTable false rightStages.noReference.key := by
            simp [Rule5ObservationBridge.bitTable, descriptorEq]
          rw [bitEq]
          exact CompilerProjectionFidelity.compareSparseLayers_self
            OfficialRuleMajorKey.compareNat CompilerProjectionFidelity.compareNat_self _
        have independentCompare := Rule4aTableBridge.contextCrossBranch_noReference_compare
          singleBonded leftStages rightStages
          (LocalizedRuleMajorReference.descriptorMap input) unit readL readR isoL isoR
          aTie leftWidth leftDepth rightWidth rightDepth
        have componentCompare :
            compare
              (ofLex (contextualCompleteReadingAt input.certified.moleculeGraph
                (LocalizedRuleMajorReference.descriptorMap input) unit
                (ruleMajorTreeGraph leftStages.a.tree) W D none)).2
              (ofLex (contextualCompleteReadingAt input.certified.moleculeGraph
                (LocalizedRuleMajorReference.descriptorMap input) unit
                (ruleMajorTreeGraph rightStages.a.tree) W D none)).2 = .eq :=
          independentCompare.symm.trans cTie
        have componentEq := (key_compare_eq_iff _ _).mp componentCompare
        have readingEq :
            contextualCompleteRule5ReadingAt input.certified.moleculeGraph
              (LocalizedRuleMajorReference.descriptorMap input) unit
              (ruleMajorTreeGraph leftStages.a.tree) W D none (senseOf common) =
            contextualCompleteRule5ReadingAt input.certified.moleculeGraph
              (LocalizedRuleMajorReference.descriptorMap input) unit
              (ruleMajorTreeGraph rightStages.a.tree) W D none (senseOf common) := by
          unfold contextualCompleteRule5ReadingAt
          rw [componentEq]
        have readingCompare : compare
            (contextualCompleteRule5ReadingAt input.certified.moleculeGraph
              (LocalizedRuleMajorReference.descriptorMap input) unit
              (ruleMajorTreeGraph leftStages.a.tree) W D none (senseOf common))
            (contextualCompleteRule5ReadingAt input.certified.moleculeGraph
              (LocalizedRuleMajorReference.descriptorMap input) unit
              (ruleMajorTreeGraph rightStages.a.tree) W D none (senseOf common)) = .eq := by
          rw [readingEq]
          exact Std.ReflCmp.compare_self
        rw [expectedRule5_descriptor common x, expectedRule5_descriptor common y,
          leftNoReference, rightNoReference, hxRef, hyRef]
        exact actualEq.trans readingCompare.symm
    | some ownL =>
        have rightNotEmpty :
            contextualReferenceSelection input.certified.moleculeGraph
              (LocalizedRuleMajorReference.descriptorMap input) unit
              (ruleMajorTreeGraph rightStages.a.tree) ≠ .empty := by
          intro hEmpty
          have leftEmpty := emptyIff.mpr hEmpty
          have leftReadingEmpty := (dataL.readingEmpty x hx).mpr leftEmpty
          simp [hxRef] at leftReadingEmpty
        cases hyRef : y.reference? with
        | none =>
            have rightEmpty := (dataR.readingEmpty y hy).mp hyRef
            exact (rightNotEmpty rightEmpty).elim
        | some ownR =>
            simp [hxRef] at stagesL
            simp [hyRef] at stagesR
            have cTie : OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
                (leftStages.c ownL).key.descriptor (rightStages.c ownR).key.descriptor = .eq := by
              simpa [stagesL.2, stagesR.2] using priorParts.2
            rw [expectedRule5_descriptor common x, expectedRule5_descriptor common y,
              stagesL.2, stagesR.2, hxRef, hyRef]
            simpa only [Option.map_some] using
              Rule5ObservationBridge.contextCrossBranch_selected_rule5_compare
                input singleBonded acyclic target unit targetUnit cursorL cursorR childL childR
                leftStages rightStages isoL isoR ownL ownR common
                leftWidth leftDepth rightWidth rightDepth aTie cTie
  simpa only [Ordering.byKey] using compareDescriptor

/-- Two successful actual context compounds with a complete Rule-4b/4c prior tie compare by
their full independent contextual Rule-5 streams. The caller supplies the fixed actual stages
and executable build equations; reference selection, stage readbacks, and graph isomorphisms are
derived from those equations and the actual child cursors. -/
theorem generatedContextCompound_rule5Readings_compare
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
    {W D : Nat}
    (leftWidth : leftStages.widthBound ≤ W) (leftDepth : leftStages.depthBound ≤ D)
    (rightWidth : rightStages.widthBound ≤ W) (rightDepth : rightStages.depthBound ≤ D)
    {left right : input.certified.LocalizedRerootCompoundRule45Key}
    (builtL : input.certified.buildActualRuleMajorCompoundRule45KeyExec? target.occurrence
      (input.certified.localizedDependencyView
        (LocalizedRuleMajorReference.referenceState input) target.occurrence)
      (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1)) cursorL = some left)
    (builtR : input.certified.buildActualRuleMajorCompoundRule45KeyExec? target.occurrence
      (input.certified.localizedDependencyView
        (LocalizedRuleMajorReference.referenceState input) target.occurrence)
      (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1)) cursorR = some right)
    (priorTie : input.certified.compareLocalizedRerootCompoundRule4bcKeys
      left.prior right.prior = .eq) (common : RS) :
    input.certified.compareLocalizedRerootCompoundRule5Readings common
        left.rule5Readings right.rule5Readings =
      compare
        (contextualCompleteRule5ReadingsAt input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit
          (ruleMajorTreeGraph leftStages.a.tree) W D (senseOf common))
        (contextualCompleteRule5ReadingsAt input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit
          (ruleMajorTreeGraph rightStages.a.tree) W D (senseOf common)) := by
  let view := input.certified.localizedDependencyView
    (LocalizedRuleMajorReference.referenceState input) target.occurrence
  let read := input.certified.localizedDependencyLabel target.occurrence view
  let fuel := 2 * (input.certified.certified.input.molecule.atomCount + 1 + 1)
  have uniformBuiltL : input.certified.buildRuleMajorCompoundRule45KeyWith?
      (fun stage position => input.certified.buildRuleMajorCumulativeWithRead? stage read fuel position)
      cursorL = some left := by
    rw [← input.certified.buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor]
    rw [← input.certified.buildActualRuleMajorCompoundRule45KeyExec?_eq]
    exact builtL
  have uniformBuiltR : input.certified.buildRuleMajorCompoundRule45KeyWith?
      (fun stage position => input.certified.buildRuleMajorCumulativeWithRead? stage read fuel position)
      cursorR = some right := by
    rw [← input.certified.buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor]
    rw [← input.certified.buildActualRuleMajorCompoundRule45KeyExec?_eq]
    exact builtR
  let dataL := generatedContextCompound_independentReadback input singleBonded acyclic
    target unit targetUnit cursorL childL leftStages leftWidth leftDepth builtL
  let dataR := generatedContextCompound_independentReadback input singleBonded acyclic
    target unit targetUnit cursorR childR rightStages rightWidth rightDepth builtR
  let readL := ruleMajorContextReadingReadbacks_of_generatedActualChild input singleBonded acyclic
    target unit targetUnit cursorL childL leftStages
  let readR := ruleMajorContextReadingReadbacks_of_generatedActualChild input singleBonded acyclic
    target unit targetUnit cursorR childR rightStages
  let isoL := ruleMajorContextStageGraphIsoBundle_of_generatedActualChild input singleBonded acyclic
    target cursorL childL leftStages
  let isoR := ruleMajorContextStageGraphIsoBundle_of_generatedActualChild input singleBonded acyclic
    target cursorR childR rightStages
  have tieFacts := (input.certified.compareLocalizedRerootCompoundRule4bcKeys_eq_eq_iff
    left.prior right.prior).mp priorTie
  have aTie : input.certified.compareLocalizedRerootCumulativeRule45Keys
      leftStages.a.key rightStages.a.key = .eq := by
    rw [← dataL.aKey, ← dataR.aKey]
    exact tieFacts.1
  have countTie : left.prior.referenceCountPriority = right.prior.referenceCountPriority :=
    compare_eq_iff_eq.mp tieFacts.2.1
  have priorListTie := completeListTie_of_rule4b_rule4c_ties
    left.prior.readings right.prior.readings tieFacts.2.2.1 tieFacts.2.2.2
  have rule5ReadbackL := input.certified.contextStages_compound_rule5Readings_eq_map
    leftStages uniformBuiltL
  have rule5ReadbackR := input.certified.contextStages_compound_rule5Readings_eq_map
    rightStages uniformBuiltR
  have priorTagsL : left.prior.readings.map
      (fun reading => reading.reference?.map senseOf) =
      contextualTaggedAlternativeReferencesAt input.certified.moleculeGraph
        (LocalizedRuleMajorReference.descriptorMap input) unit
        (ruleMajorTreeGraph leftStages.a.tree) W D := by
    calc
      _ = left.rule5Readings.map
          (fun reading => reading.prior.reference?.map senseOf) := by
            rw [rule5ReadbackL]
            simp [ruleMajorExpectedRule5Reading]
      _ = _ := dataL.tags
  have priorTagsR : right.prior.readings.map
      (fun reading => reading.reference?.map senseOf) =
      contextualTaggedAlternativeReferencesAt input.certified.moleculeGraph
        (LocalizedRuleMajorReference.descriptorMap input) unit
        (ruleMajorTreeGraph rightStages.a.tree) W D := by
    calc
      _ = right.rule5Readings.map
          (fun reading => reading.prior.reference?.map senseOf) := by
            rw [rule5ReadbackR]
            simp [ruleMajorExpectedRule5Reading]
      _ = _ := dataR.tags
  let expectedCmp := Ordering.byKey (fun reading => input.certified.localizedRerootRule5Descriptor common
      (input.certified.ruleMajorExpectedRule5Reading reading))
      (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority)
  let mappedCmp := Ordering.byKey (input.certified.localizedRerootRule5Descriptor common)
      (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority)
  have mappedExpected : List.compareLex mappedCmp
      (left.prior.readings.map input.certified.ruleMajorExpectedRule5Reading)
      (right.prior.readings.map input.certified.ruleMajorExpectedRule5Reading) =
      List.compareLex expectedCmp left.prior.readings right.prior.readings := by
    exact compareLex_map_rel expectedCmp mappedCmp input.certified.ruleMajorExpectedRule5Reading
      (by intro x y; rfl) _ _
  let observeL := fun reading : input.certified.LocalizedRerootRule4bcReading =>
    contextualCompleteRule5ReadingAt input.certified.moleculeGraph
      (LocalizedRuleMajorReference.descriptorMap input) unit
      (ruleMajorTreeGraph leftStages.a.tree) W D
      (reading.reference?.map senseOf) (senseOf common)
  let observeR := fun reading : input.certified.LocalizedRerootRule4bcReading =>
    contextualCompleteRule5ReadingAt input.certified.moleculeGraph
      (LocalizedRuleMajorReference.descriptorMap input) unit
      (ruleMajorTreeGraph rightStages.a.tree) W D
      (reading.reference?.map senseOf) (senseOf common)
  have tiedMap := Rule4aTableBridge.compareLex_map_eq_of_prior_tie
    input.certified.compareRule4bcReadingsComplete expectedCmp compare observeL observeR
    left.prior.readings right.prior.readings
    (fun x hx y hy priorEq => contextRule5Pair_compare input singleBonded acyclic
      target unit targetUnit cursorL cursorR childL childR leftStages rightStages readL readR
      isoL isoR dataL dataR leftWidth leftDepth rightWidth rightDepth aTie countTie common
      x hx y hy priorEq)
    priorListTie
  have mappedL : left.prior.readings.map observeL =
      contextualCompleteRule5ReadingsAt input.certified.moleculeGraph
        (LocalizedRuleMajorReference.descriptorMap input) unit
        (ruleMajorTreeGraph leftStages.a.tree) W D (senseOf common) := by
    unfold contextualCompleteRule5ReadingsAt
    rw [← priorTagsL]
    simp only [observeL, List.map_map, Function.comp_def]
  have mappedR : right.prior.readings.map observeR =
      contextualCompleteRule5ReadingsAt input.certified.moleculeGraph
        (LocalizedRuleMajorReference.descriptorMap input) unit
        (ruleMajorTreeGraph rightStages.a.tree) W D (senseOf common) := by
    unfold contextualCompleteRule5ReadingsAt
    rw [← priorTagsR]
    simp only [observeR, List.map_map, Function.comp_def]
  calc
    input.certified.compareLocalizedRerootCompoundRule5Readings common
        left.rule5Readings right.rule5Readings =
      List.compareLex mappedCmp
        (left.prior.readings.map input.certified.ruleMajorExpectedRule5Reading)
        (right.prior.readings.map input.certified.ruleMajorExpectedRule5Reading) := by
          rw [rule5ReadbackL, rule5ReadbackR]
          rfl
    _ = List.compareLex expectedCmp left.prior.readings right.prior.readings := mappedExpected
    _ = List.compareLex compare
        (left.prior.readings.map observeL) (right.prior.readings.map observeR) := tiedMap
    _ = compare
        (contextualCompleteRule5ReadingsAt input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit
          (ruleMajorTreeGraph leftStages.a.tree) W D (senseOf common))
        (contextualCompleteRule5ReadingsAt input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit
          (ruleMajorTreeGraph rightStages.a.tree) W D (senseOf common)) := by
            simp only [List.compare_eq_compareLex]
            rw [mappedL, mappedR]

end
end Rule4aTableBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.generatedContextCompound_rule5Readings_compare
