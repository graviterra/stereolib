/-
Copyright (c) 2026 TetraStereo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Later-rule neutrality of a physically unmarked final-root cut branch

This module eliminates Rules 4b, 4c and 5 from the actual production comparison of two final-root
frame slots whose incoming cut branches are *physically* unmarked under the accepted original
detected-frame general rigid/twin physical domain.

The substantive point is that the two `none`-only (empty) Rule-4b reference selections still
materialise padded zero priorities and one no-reference reading each, so a spurious later-rule
preference could in principle appear after a constitutional Rule-4a tie.  We prove it cannot: after
the physical emptiness the actual compound comparator collapses to the constitutional Rule-4a
comparison in both directions, and the `pseudo` flag is `false`.

Nothing here defines a new absolute-order spec, and no desired R/S label, reference list, all-`none`
label table, prior tie, reader covariance or key alignment is a final premise: each is derived from
the physical domain through the actual production builders.
-/

import TetraStereo.OneCenter.LocalizedActualPhysicalReferenceSelection
import TetraStereo.OneCenter.LocalizedGeneralRigidPhysicalKeySeparation
import TetraStereo.OneCenter.LocalizedEmptyRule4bReferenceDecoding
import TetraStereo.OneCenter.LocalizedPhysicalNearestRule4bReference
import TetraStereo.OneCenter.LocalizedDecodedTreeRule5Rereading
import TetraStereo.OneCenter.LocalizedPhysicalCompoundForwardTransport
import TetraStereo.OneCenter.LocalizedEmptyReferencePhysicalPriorInverse
import TetraStereo.OneCenter.LocalizedCumulativeTreeTableReconstruction
import TetraStereo.OneCenter.LocalizedCumulativeKeyObservableOrder
import TetraStereo.OneCenter.LocalizedSingleBondDescriptorModelBridge
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput
open LocalizedCumulativeDecoratedTree

noncomputable section









/-- **Actual empty references from a pure physical unmarkedness hypothesis.**  Keeping the original
detected-frame configuration `cfgPhys` as the physical witness: the actual ranked-label selection and
the actual production `prior` reference list are both empty, and the actual production `readings` is
one no-reference reading. -/
theorem unmarkedSlot_references_nil_of_physicalDomain
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfgPhys : input.certified.detectedMultiCenterMolecule.Configuration)
    (physicalDomain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfgPhys c)
    (oAtom : input.certified.Atom)
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    (unmarked : ∀ y : input.certified.Atom,
      y ∈ AcyclicCutBranchAutomorphism.CutBranch input.certified.moleculeGraph c.1 oAtom →
        ¬ PhysicalMarkedAtom input ⟨c.1, c.2⟩ y) :
    localizedRule4bReferencesFromRankedLabels
        (actualSlotCompoundKey input c frame frameComputed slot).prior.rule4aKey.rankedLabels = [] ∧
      (actualSlotCompoundKey input c frame frameComputed slot).prior.references = [] ∧
        ∃ reading : input.certified.LocalizedRerootRule4bcReading,
          (actualSlotCompoundKey input c frame frameComputed slot).prior.readings = [reading] ∧
            reading.reference? = none :=
  actualSlot_physicalBranchUnmarked_references_nil input c frame frameComputed slot
    singleBonded acyclic hcharge noDouble
    (input.certified.canonicalReindexConfiguration cfgPhys)
    (input.certified.actualGeneralRigidGlobalPhysicalDomain_of_actualGeneralRigidPhysicalDomain
      cfgPhys c physicalDomain)
    oAtom oObserved unmarked

/-! ## Two actual Rule-4a trees of equal erased shape from a constitutional tie -/

/-- **Realized actual Rule-4a trees of equal shape along the shared frame cursors.**

From only the two actual production Rule-4a builds and the all-`none` label tables derived from
physical emptiness, an actual constitutional tie yields two actually realized trees with the same
erased shape, whose shared generated reader is covariant along that shape's position
correspondence.  Nothing about the trees is assumed. -/
theorem unmarkedSlot_rule4aTreePair
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (left right : Fin 4)
    (leftAllNone : LocalizedLabelLayersAllNone
      (actualSlotCompoundKey input c frame frameComputed left).prior.rule4aKey.labels)
    (rightAllNone : LocalizedLabelLayersAllNone
      (actualSlotCompoundKey input c frame frameComputed right).prior.rule4aKey.labels)
    (constitutionalEq : OfficialRuleMajorKey.compare
      (actualSlotCompoundKey input c frame frameComputed left).prior.rule4aKey.constitutional
      (actualSlotCompoundKey input c frame frameComputed right).prior.rule4aKey.constitutional
      = Ordering.eq) :
    ∃ (tL tR : LocalizedCumulativeDecoratedTree input.certified
        (LocalizedUniversalReference.carrierFuel input))
      (hshape : shape tL = shape tR),
      (∀ x y, ShapePositionCursorRelation hshape x y →
        ActualReaderPhysicalBranchInverse.dependencyReader input c y =
          ActualReaderPhysicalBranchInverse.dependencyReader input c x) ∧
        (tL.source = frame.cursorAt left ∧ tR.source = frame.cursorAt right ∧
          LocalizedCumulativeTreeRealizes input.certified
            (ActualReaderPhysicalBranchInverse.dependencyReader input c) tL ∧
          LocalizedCumulativeTreeRealizes input.certified
            (ActualReaderPhysicalBranchInverse.dependencyReader input c) tR) := by
  classical
  -- actual realized trees with the four comparison-visible tables, from the production builds
  obtain ⟨tL, tLsource, tLmatch, tLlabel, tLrealizes⟩ :=
    exists_decoratedTree_of_buildLocalizedRerootCumulativeRule45Key? input.certified .rule4a
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (frame.cursorAt left)
      (actualSlotCompoundKey input c frame frameComputed left).prior.rule4aKey
      (actualSlotRule4aBuilt input c frame frameComputed left)
  obtain ⟨tR, tRsource, tRmatch, tRlabel, tRrealizes⟩ :=
    exists_decoratedTree_of_buildLocalizedRerootCumulativeRule45Key? input.certified .rule4a
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (frame.cursorAt right)
      (actualSlotCompoundKey input c frame frameComputed right).prior.rule4aKey
      (actualSlotRule4aBuilt input c frame frameComputed right)
  -- the three equal constitutional columns
  obtain ⟨rule1aEq, rule1bEq, rule2Eq⟩ :=
    (officialRuleMajorKey_compare_eq_iff _ _).mp constitutionalEq
  -- erased shape equality from the three constitutional columns only
  have hshape : shape tL = shape tR := by
    refine table_shape_eq_of_columns_eq .rule4a .rule4a tL tR ?_ ?_ ?_
    · exact tLmatch.1.trans (rule1aEq.trans tRmatch.1.symm)
    · exact tLmatch.2.1.trans (rule1bEq.trans tRmatch.2.1.symm)
    · exact tLmatch.2.2.1.trans (rule2Eq.trans tRmatch.2.2.1.symm)
  -- all-`none` label tables of the two actual trees
  have leftTableAllNone : LocalizedLabelLayersAllNone tL.labelTable := by
    rw [tLlabel]
    exact leftAllNone
  have rightTableAllNone : LocalizedLabelLayersAllNone tR.labelTable := by
    rw [tRlabel]
    exact rightAllNone
  -- reader covariance along the shared shape-position correspondence
  have readerCovariant : ∀ x y, ShapePositionCursorRelation hshape x y →
      ActualReaderPhysicalBranchInverse.dependencyReader input c y =
        ActualReaderPhysicalBranchInverse.dependencyReader input c x := by
    intro x y related
    have covariant := read_source_eq_of_shapePositionCursor
      (input := input.certified) (carrierFuel := LocalizedUniversalReference.carrierFuel input)
      hshape tLrealizes tRrealizes
      (id : Option LocalizedAuxiliaryLabel → Option LocalizedAuxiliaryLabel)
      (fun p => by
        have labelL := LocalizedEmptyReferencePhysicalPriorInverse.labelTable_allNone_node_label
          tL leftTableAllNone p.val (positionNode p) (positionNode_spec p)
        have labelR := LocalizedEmptyReferencePhysicalPriorInverse.labelTable_allNone_node_label
          tR rightTableAllNone (shapePositionEquiv hshape p).val
          (positionNode (shapePositionEquiv hshape p)) (positionNode_spec _)
        show (positionNode (shapePositionEquiv hshape p)).label =
          id ((positionNode p).label)
        rw [labelR, labelL]
        rfl)
      related
    simpa using covariant
  exact ⟨tL, tR, hshape, readerCovariant, tLsource, tRsource, tLrealizes, tRrealizes⟩

/-! ## The complete comparator on a prior tie with a tied common-`R` reading -/

/-- **On an actual prior tie with a tied common-`R` reading the through-Rule-5 comparison is the
constitutional tie with `pseudo = false`.**  This is the production definition, not a new
comparator: the prior branch is taken by its actual `eq` value and the common-`R` reading is the
production `match`. -/
theorem compareLocalizedRerootCompoundThroughRule5_eq_eq_of_priorTie
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule45Key)
    (priorEq : input.compareLocalizedRerootCompoundRule4bcKeys left.prior right.prior =
      Ordering.eq)
    (readingsEq : input.compareLocalizedRerootCompoundRule5Readings .R
      left.rule5Readings right.rule5Readings = Ordering.eq) :
    input.compareLocalizedRerootCompoundThroughRule5 left right =
      { ordering := Ordering.eq, pseudo := false } := by
  have orderingEq :
      (input.compareLocalizedRerootCompoundThroughRule5 left right).ordering = Ordering.eq := by
    rw [input.compareLocalizedRerootCompoundThroughRule5_ordering]
    show input.compareLocalizedRerootCompoundRule45Keys left right = Ordering.eq
    unfold CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundRule45Keys
    simp only [compareLex_eq_eq, Ordering.byKey]
    exact ⟨priorEq, readingsEq⟩
  have pseudoFalse :
      (input.compareLocalizedRerootCompoundThroughRule5 left right).pseudo = false := by
    cases pseudoCase : (input.compareLocalizedRerootCompoundThroughRule5 left right).pseudo with
    | false => rfl
    | true =>
        exact absurd readingsEq
          ((LocalizedRule5SwapAndSignal.compareLocalizedRerootCompoundThroughRule5_pseudo_eq_true_iff
            input left right).mp pseudoCase).2.1
  have etaEq : input.compareLocalizedRerootCompoundThroughRule5 left right =
      ⟨(input.compareLocalizedRerootCompoundThroughRule5 left right).ordering,
        (input.compareLocalizedRerootCompoundThroughRule5 left right).pseudo⟩ := rfl
  rw [etaEq, orderingEq, pseudoFalse]

/-! ## The physical endpoint -/

/-- **Later-rule neutrality for two physically unmarked actual final-root slots.**

Under the accepted original-detected-frame general rigid/twin physical domain, an acyclic
single-bond graph, explicit no-double-bond records, constant formal charge, and pure physical
unmarkedness of both incoming cut branches, the *actual production* through-Rule-5 compound
comparison of two actual frame slots equals the constitutional Rule-4a comparison with
`pseudo = false`, for all three possible constitutional outcomes and at arbitrary branch depth.

No reference list, label table, reading, prior tie, reader covariance or key alignment is assumed:
the empty selection is generated by the physical domain, and every sub-build used below is the
actual production build of the slot keys. -/
theorem actualSlots_unmarked_throughRule5_eq_constitutional
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (left right : Fin 4)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfgPhys : input.certified.detectedMultiCenterMolecule.Configuration)
    (physicalDomain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfgPhys c)
    (oAtomLeft : input.certified.Atom)
    (oObservedLeft : (frame.cursorAt left).occurrence.1.node.current? = some oAtomLeft)
    (oAtomRight : input.certified.Atom)
    (oObservedRight : (frame.cursorAt right).occurrence.1.node.current? = some oAtomRight)
    (unmarkedLeft : ∀ y : input.certified.Atom,
      y ∈ AcyclicCutBranchAutomorphism.CutBranch input.certified.moleculeGraph c.1 oAtomLeft →
        ¬ PhysicalMarkedAtom input ⟨c.1, c.2⟩ y)
    (unmarkedRight : ∀ y : input.certified.Atom,
      y ∈ AcyclicCutBranchAutomorphism.CutBranch input.certified.moleculeGraph c.1 oAtomRight →
        ¬ PhysicalMarkedAtom input ⟨c.1, c.2⟩ y) :
    input.certified.compareLocalizedRerootCompoundThroughRule5
        (actualSlotCompoundKey input c frame frameComputed left)
        (actualSlotCompoundKey input c frame frameComputed right) =
      { ordering := OfficialRuleMajorKey.compare
          (actualSlotCompoundKey input c frame frameComputed left).prior.rule4aKey.constitutional
          (actualSlotCompoundKey input c frame frameComputed right).prior.rule4aKey.constitutional
        pseudo := false } := by
  classical
  let fuel := localizedOccurrenceRerootEvaluationFuel
    (LocalizedUniversalReference.carrierFuel input)
  let keyL := actualSlotCompoundKey input c frame frameComputed left
  let keyR := actualSlotCompoundKey input c frame frameComputed right
  change input.certified.compareLocalizedRerootCompoundThroughRule5 keyL keyR =
    { ordering := OfficialRuleMajorKey.compare keyL.prior.rule4aKey.constitutional
        keyR.prior.rule4aKey.constitutional, pseudo := false }
  -- (1) physically empty actual references, one no-reference reading each
  obtain ⟨_selectionL, referencesL₀, readingL, readingsL₀, referenceNoneL⟩ :=
    unmarkedSlot_references_nil_of_physicalDomain input c frame frameComputed left
      singleBonded acyclic hcharge noDouble cfgPhys physicalDomain oAtomLeft oObservedLeft
      unmarkedLeft
  obtain ⟨_selectionR, referencesR₀, readingR, readingsR₀, referenceNoneR⟩ :=
    unmarkedSlot_references_nil_of_physicalDomain input c frame frameComputed right
      singleBonded acyclic hcharge noDouble cfgPhys physicalDomain oAtomRight oObservedRight
      unmarkedRight
  have referencesL : keyL.prior.references = [] := referencesL₀
  have referencesR : keyR.prior.references = [] := referencesR₀
  have readingsL : keyL.prior.readings = [readingL] := readingsL₀
  have readingsR : keyR.prior.readings = [readingR] := readingsR₀
  -- (2) the actual generated reader is sparse on every cursor
  have readerSparse : ∀ cursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input),
      LocalizedRule4bSparseLabel
        (input.certified.localizedDependencyLabel
          (ActualReaderPhysicalBranchInverse.topTarget input c)
          (referenceDependencyView input c) cursor) :=
    LocalizedGeneralRigidPhysicalKeySeparation.actualDependencyReader_sparse_of_physicalDomain
      input singleBonded acyclic hcharge noDouble cfgPhys c physicalDomain
  -- (3) all-`none` actual Rule-4a label tables
  have allNoneL : LocalizedLabelLayersAllNone keyL.prior.rule4aKey.labels :=
    input.certified.buildLocalizedRerootCompoundRule4bcKey?_rule4aKey_labels_allNone_of_references_eq_nil
      (ActualReaderPhysicalBranchInverse.topTarget input c) (referenceDependencyView input c)
      fuel (frame.cursorAt left) keyL.prior
      (actualSlotPriorBuilt input c frame frameComputed left) readerSparse referencesL
  have allNoneR : LocalizedLabelLayersAllNone keyR.prior.rule4aKey.labels :=
    input.certified.buildLocalizedRerootCompoundRule4bcKey?_rule4aKey_labels_allNone_of_references_eq_nil
      (ActualReaderPhysicalBranchInverse.topTarget input c) (referenceDependencyView input c)
      fuel (frame.cursorAt right) keyR.prior
      (actualSlotPriorBuilt input c frame frameComputed right) readerSparse referencesR
  -- (4) the actual read-parameterized production builds of both slots
  have keyBuiltL : input.certified.buildLocalizedRerootCompoundRule45KeyWithRead?
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel
      (frame.cursorAt left) = some keyL := by
    change input.certified.buildLocalizedRerootCompoundRule45KeyWithRead?
      (fun cursor => input.certified.localizedDependencyLabel
        (ActualReaderPhysicalBranchInverse.topTarget input c)
        (referenceDependencyView input c) cursor) fuel (frame.cursorAt left) = some keyL
    rw [input.certified.buildLocalizedRerootCompoundRule45KeyWithRead?_eq_localizedDependencyLabel
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c) fuel (frame.cursorAt left)]
    exact actualSlotCompoundBuilt input c frame frameComputed left
  have keyBuiltR : input.certified.buildLocalizedRerootCompoundRule45KeyWithRead?
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel
      (frame.cursorAt right) = some keyR := by
    change input.certified.buildLocalizedRerootCompoundRule45KeyWithRead?
      (fun cursor => input.certified.localizedDependencyLabel
        (ActualReaderPhysicalBranchInverse.topTarget input c)
        (referenceDependencyView input c) cursor) fuel (frame.cursorAt right) = some keyR
    rw [input.certified.buildLocalizedRerootCompoundRule45KeyWithRead?_eq_localizedDependencyLabel
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c) fuel (frame.cursorAt right)]
    exact actualSlotCompoundBuilt input c frame frameComputed right
  have priorWithReadL : input.certified.buildLocalizedRerootCompoundRule4bcKeyWithRead?
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel
      (frame.cursorAt left) = some keyL.prior :=
    (buildLocalizedRerootCompoundRule45KeyWithRead?_components input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel
      (frame.cursorAt left) keyL keyBuiltL).1
  have priorWithReadR : input.certified.buildLocalizedRerootCompoundRule4bcKeyWithRead?
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel
      (frame.cursorAt right) = some keyR.prior :=
    (buildLocalizedRerootCompoundRule45KeyWithRead?_components input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel
      (frame.cursorAt right) keyR keyBuiltR).1
  have rule4aBuiltL : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?
      .rule4a (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel
      (frame.cursorAt left) = some keyL.prior.rule4aKey := by
    change input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      (fun cursor => input.certified.localizedDependencyLabel
        (ActualReaderPhysicalBranchInverse.topTarget input c)
        (referenceDependencyView input c) cursor) fuel (frame.cursorAt left) =
      some keyL.prior.rule4aKey
    rw [input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
      .rule4a (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c) fuel (frame.cursorAt left)]
    exact actualSlotRule4aBuilt input c frame frameComputed left
  have rule4aBuiltR : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?
      .rule4a (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel
      (frame.cursorAt right) = some keyR.prior.rule4aKey := by
    change input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      (fun cursor => input.certified.localizedDependencyLabel
        (ActualReaderPhysicalBranchInverse.topTarget input c)
        (referenceDependencyView input c) cursor) fuel (frame.cursorAt right) =
      some keyR.prior.rule4aKey
    rw [input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
      .rule4a (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c) fuel (frame.cursorAt right)]
    exact actualSlotRule4aBuilt input c frame frameComputed right
  -- (5) the actual readings-list builds, inverted to the single no-reference reading
  have readingsBuildL : input.certified.buildLocalizedRerootRule4bcReadingsWithRead?
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel (frame.cursorAt left)
      (localizedRule4bcReferenceAlternatives keyL.prior.references) =
      some keyL.prior.readings :=
    (CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule4bcKeyWithRead?_components
      input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel
      (frame.cursorAt left) keyL.prior priorWithReadL).2.2.2
  have readingsBuildR : input.certified.buildLocalizedRerootRule4bcReadingsWithRead?
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel (frame.cursorAt right)
      (localizedRule4bcReferenceAlternatives keyR.prior.references) =
      some keyR.prior.readings :=
    (CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule4bcKeyWithRead?_components
      input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel
      (frame.cursorAt right) keyR.prior priorWithReadR).2.2.2
  have alternativeL : localizedRule4bcReferenceAlternatives keyL.prior.references = [none] := by
    rw [referencesL]
    rfl
  have alternativeR : localizedRule4bcReferenceAlternatives keyR.prior.references = [none] := by
    rw [referencesR]
    rfl
  obtain ⟨readingL', readingLEq, readingBuildL⟩ :=
    buildLocalizedRerootRule4bcReadingsWithRead?_singleton input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel (frame.cursorAt left)
      none keyL.prior.readings (by rw [← alternativeL]; exact readingsBuildL)
  obtain ⟨readingR', readingREq, readingBuildR⟩ :=
    buildLocalizedRerootRule4bcReadingsWithRead?_singleton input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel (frame.cursorAt right)
      none keyR.prior.readings (by rw [← alternativeR]; exact readingsBuildR)
  have readingL'Eq : readingL' = readingL :=
    (List.cons.inj (readingLEq.symm.trans readingsL)).1
  have readingR'Eq : readingR' = readingR :=
    (List.cons.inj (readingREq.symm.trans readingsR)).1
  have readingBuildL' : input.certified.buildLocalizedRerootRule4bcReadingWithRead?
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel (frame.cursorAt left)
      none = some readingL := by
    simpa [readingL'Eq] using readingBuildL
  have readingBuildR' : input.certified.buildLocalizedRerootRule4bcReadingWithRead?
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel (frame.cursorAt right)
      none = some readingR := by
    simpa [readingR'Eq] using readingBuildR
  -- (6) actual `.rule4cNoReference` builds and the `.rule4a` build of each reading
  have rule4cBuiltL : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?
      .rule4cNoReference (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel
      (frame.cursorAt left) = some readingL.rule4cKey := by
    have components := buildLocalizedRerootRule4bcReadingWithRead?_components input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel (frame.cursorAt left)
      none readingL readingBuildL'
    simpa [localizedRule4cOwnStage] using components.2.2
  have rule4cBuiltR : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?
      .rule4cNoReference (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel
      (frame.cursorAt right) = some readingR.rule4cKey := by
    have components := buildLocalizedRerootRule4bcReadingWithRead?_components input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel (frame.cursorAt right)
      none readingR readingBuildR'
    simpa [localizedRule4cOwnStage] using components.2.2
  have readingRule4bL : readingL.rule4bKey = keyL.prior.rule4aKey := by
    have components := buildLocalizedRerootRule4bcReadingWithRead?_components input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel (frame.cursorAt left)
      none readingL readingBuildL'
    have built : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?
        .rule4a (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel
        (frame.cursorAt left) = some readingL.rule4bKey := by
      simpa [localizedRule4bOwnStageOf] using components.2.1
    exact Option.some.inj (built.symm.trans rule4aBuiltL)
  have readingRule4bR : readingR.rule4bKey = keyR.prior.rule4aKey := by
    have components := buildLocalizedRerootRule4bcReadingWithRead?_components input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel (frame.cursorAt right)
      none readingR readingBuildR'
    have built : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?
        .rule4a (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel
        (frame.cursorAt right) = some readingR.rule4bKey := by
      simpa [localizedRule4bOwnStageOf] using components.2.1
    exact Option.some.inj (built.symm.trans rule4aBuiltR)
  -- the actual Rule-5 readings, and their common-`R` component builds
  have readingsBuild5L : input.certified.buildLocalizedRerootRule5ReadingsWithRead?
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel (frame.cursorAt left)
      keyL.prior.readings = some keyL.rule5Readings :=
    (buildLocalizedRerootCompoundRule45KeyWithRead?_components input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel
      (frame.cursorAt left) keyL keyBuiltL).2
  have readingsBuild5R : input.certified.buildLocalizedRerootRule5ReadingsWithRead?
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel (frame.cursorAt right)
      keyR.prior.readings = some keyR.rule5Readings :=
    (buildLocalizedRerootCompoundRule45KeyWithRead?_components input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel
      (frame.cursorAt right) keyR keyBuiltR).2
  obtain ⟨rule5L, rule5LEq, rule5BuildL⟩ :=
    buildLocalizedRerootRule5ReadingsWithRead?_singleton input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel (frame.cursorAt left)
      readingL keyL.rule5Readings (by rw [← readingsL]; exact readingsBuild5L)
  obtain ⟨rule5R, rule5REq, rule5BuildR⟩ :=
    buildLocalizedRerootRule5ReadingsWithRead?_singleton input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel (frame.cursorAt right)
      readingR keyR.rule5Readings (by rw [← readingsR]; exact readingsBuild5R)
  have commonRL : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (.rule5NoRule4bReference .R)
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel (frame.cursorAt left) =
      some rule5L.commonR := by
    have components := buildLocalizedRerootRule5ReadingWithRead?_components input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel (frame.cursorAt left)
      readingL rule5L rule5BuildL
    simpa [localizedRule5StageFor, referenceNoneL] using components.2.1
  have commonRR : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (.rule5NoRule4bReference .R)
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel (frame.cursorAt right) =
      some rule5R.commonR := by
    have components := buildLocalizedRerootRule5ReadingWithRead?_components input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel (frame.cursorAt right)
      readingR rule5R rule5BuildR
    simpa [localizedRule5StageFor, referenceNoneR] using components.2.1
  -- reference-count priorities are equal actual zero priorities
  have countL : keyL.prior.referenceCountPriority =
      constitutionalRule4bReferenceCountPriority ([] : List RS) :=
    (buildLocalizedRerootCompoundRule4bcKey?_sound input.certified
      (ActualReaderPhysicalBranchInverse.topTarget input c) (referenceDependencyView input c)
      fuel (frame.cursorAt left) keyL.prior
      (actualSlotPriorBuilt input c frame frameComputed left)).2.2.1.trans
      (by rw [referencesL])
  have countR : keyR.prior.referenceCountPriority =
      constitutionalRule4bReferenceCountPriority ([] : List RS) :=
    (buildLocalizedRerootCompoundRule4bcKey?_sound input.certified
      (ActualReaderPhysicalBranchInverse.topTarget input c) (referenceDependencyView input c)
      fuel (frame.cursorAt right) keyR.prior
      (actualSlotPriorBuilt input c frame frameComputed right)).2.2.1.trans
      (by rw [referencesR])
  -- (7) split on the actual constitutional comparison
  by_cases constitutionalTie : OfficialRuleMajorKey.compare
      keyL.prior.rule4aKey.constitutional keyR.prior.rule4aKey.constitutional = Ordering.eq
  · -- constitutional tie: every later rule must tie as well
    obtain ⟨tL, tR, hshape, readerCovariant, tLsource, tRsource, tLrealizes, tRrealizes⟩ :=
      unmarkedSlot_rule4aTreePair input c frame frameComputed left right allNoneL allNoneR
        constitutionalTie
    have related : ShapePositionCursorRelation hshape (frame.cursorAt left) (frame.cursorAt right) :=
      shapePositionCursorRelation_sources hshape tLsource tRsource
    have rule4aDescriptorEq :
        keyL.prior.rule4aKey.descriptor = keyR.prior.rule4aKey.descriptor :=
      descriptor_eq_of_shapePositionCursor_sameReader_builds (input := input.certified)
        (carrierFuel := LocalizedUniversalReference.carrierFuel input)
        singleBonded acyclic hshape
        (ActualReaderPhysicalBranchInverse.dependencyReader input c)
        tLrealizes tRrealizes readerCovariant .rule4a fuel related rule4aBuiltL rule4aBuiltR
    have rule4cDescriptorEq : readingL.rule4cKey.descriptor = readingR.rule4cKey.descriptor :=
      descriptor_eq_of_shapePositionCursor_sameReader_builds (input := input.certified)
        (carrierFuel := LocalizedUniversalReference.carrierFuel input)
        singleBonded acyclic hshape
        (ActualReaderPhysicalBranchInverse.dependencyReader input c)
        tLrealizes tRrealizes readerCovariant .rule4cNoReference fuel related
        rule4cBuiltL rule4cBuiltR
    have commonRDescriptorEq : rule5L.commonR.descriptor = rule5R.commonR.descriptor :=
      descriptor_eq_of_shapePositionCursor_sameReader_builds (input := input.certified)
        (carrierFuel := LocalizedUniversalReference.carrierFuel input)
        singleBonded acyclic hshape
        (ActualReaderPhysicalBranchInverse.dependencyReader input c)
        tLrealizes tRrealizes readerCovariant (.rule5NoRule4bReference .R) fuel related
        commonRL commonRR
    -- the cumulative Rule-4a keys tie
    have cumulativeTie : input.certified.compareLocalizedRerootCumulativeRule45Keys
        keyL.prior.rule4aKey keyR.prior.rule4aKey = Ordering.eq := by
      unfold CertifiedLocalizedCIPInput.compareLocalizedRerootCumulativeRule45Keys
      simp only [compareLex_eq_eq, Ordering.byKey]
      exact ⟨constitutionalTie,
        (compareSparseLayers_compareLocalizedCumulativeRule45Priority_eq_iff _ _).mpr
          rule4aDescriptorEq⟩
    -- the compound prior ties
    have priorTie : input.certified.compareLocalizedRerootCompoundRule4bcKeys
        keyL.prior keyR.prior = Ordering.eq := by
      rw [input.certified.compareLocalizedRerootCompoundRule4bcKeys_eq_afterRule4a_of_tie
        keyL.prior keyR.prior cumulativeTie]
      unfold CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundRule4bcAfterRule4a
      simp only [compareLex_eq_eq, Ordering.byKey]
      refine ⟨?_, ?_, ?_⟩
      · rw [countL, countR]
        exact Nat.compare_eq_eq.mpr rfl
      · rw [readingsL, readingsR]
        exact (compareLocalizedRerootCompoundRule4bReadings_singleton_eq input.certified
          readingL readingR).mpr
          ((compareSparseLayers_compareLocalizedCumulativeRule45Priority_eq_iff _ _).mpr
            (by rw [readingRule4bL, readingRule4bR]; exact rule4aDescriptorEq))
      · rw [readingsL, readingsR]
        simpa only [CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundRule4cReadings,
          List.compareLex_cons_cons, Ordering.byKey, Ordering.then_eq_eq,
          List.compareLex_nil_nil, and_true] using
          (compareSparseLayers_compareLocalizedCumulativeRule45Priority_eq_iff _ _).mpr
            rule4cDescriptorEq
    -- the common-`R` Rule-5 reading comparison ties
    have commonRTie : input.certified.compareLocalizedRerootCompoundRule5Readings .R
        keyL.rule5Readings keyR.rule5Readings = Ordering.eq := by
      rw [rule5LEq, rule5REq]
      simpa only [CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundRule5Readings,
        CertifiedLocalizedCIPInput.localizedRerootRule5Descriptor,
        List.compareLex_cons_cons, Ordering.byKey, Ordering.then_eq_eq,
        List.compareLex_nil_nil, and_true] using
        (compareSparseLayers_compareLocalizedCumulativeRule45Priority_eq_iff _ _).mpr
          commonRDescriptorEq
    rw [compareLocalizedRerootCompoundThroughRule5_eq_eq_of_priorTie input.certified keyL keyR
      priorTie commonRTie, constitutionalTie]
  · -- strict constitutional decision: the cumulative and compound comparisons inherit it
    have cumulativeStrict : input.certified.compareLocalizedRerootCumulativeRule45Keys
        keyL.prior.rule4aKey keyR.prior.rule4aKey =
        OfficialRuleMajorKey.compare keyL.prior.rule4aKey.constitutional
          keyR.prior.rule4aKey.constitutional :=
      compareLocalizedRerootCumulativeRule45Keys_eq_of_constitutional_ne input.certified
        keyL.prior.rule4aKey keyR.prior.rule4aKey constitutionalTie
    have rule4aNe : input.certified.compareLocalizedRerootCumulativeRule45Keys
        keyL.prior.rule4aKey keyR.prior.rule4aKey ≠ Ordering.eq := by
      rw [cumulativeStrict]
      exact constitutionalTie
    have priorStrict : input.certified.compareLocalizedRerootCompoundRule4bcKeys
        keyL.prior keyR.prior =
        OfficialRuleMajorKey.compare keyL.prior.rule4aKey.constitutional
          keyR.prior.rule4aKey.constitutional := by
      rw [input.certified.compareLocalizedRerootCompoundRule4bcKeys_eq_rule4a_of_ne
        keyL.prior keyR.prior rule4aNe, cumulativeStrict]
    have priorNe : input.certified.compareLocalizedRerootCompoundRule4bcKeys
        keyL.prior keyR.prior ≠ Ordering.eq := by
      rw [priorStrict]
      exact constitutionalTie
    rw [compareLocalizedRerootCompoundThroughRule5_eq_of_prior_ne input.certified keyL keyR
      priorNe, priorStrict]

/-! ## The exported ordering projection -/

/-- **The actual through-Rule-5 key comparator on two physically unmarked slots equals the
constitutional Rule-4a comparison.**  Same physical premises as
`actualSlots_unmarked_throughRule5_eq_constitutional`; this is its `ordering` projection onto the
production key comparator, so no `pseudo` signal can remain. -/
theorem actualSlots_unmarked_rule45Keys_eq_constitutional
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (left right : Fin 4)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfgPhys : input.certified.detectedMultiCenterMolecule.Configuration)
    (physicalDomain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfgPhys c)
    (oAtomLeft : input.certified.Atom)
    (oObservedLeft : (frame.cursorAt left).occurrence.1.node.current? = some oAtomLeft)
    (oAtomRight : input.certified.Atom)
    (oObservedRight : (frame.cursorAt right).occurrence.1.node.current? = some oAtomRight)
    (unmarkedLeft : ∀ y : input.certified.Atom,
      y ∈ AcyclicCutBranchAutomorphism.CutBranch input.certified.moleculeGraph c.1 oAtomLeft →
        ¬ PhysicalMarkedAtom input ⟨c.1, c.2⟩ y)
    (unmarkedRight : ∀ y : input.certified.Atom,
      y ∈ AcyclicCutBranchAutomorphism.CutBranch input.certified.moleculeGraph c.1 oAtomRight →
        ¬ PhysicalMarkedAtom input ⟨c.1, c.2⟩ y) :
    input.certified.compareLocalizedRerootCompoundRule45Keys
        (actualSlotCompoundKey input c frame frameComputed left)
        (actualSlotCompoundKey input c frame frameComputed right) =
      OfficialRuleMajorKey.compare
        (actualSlotCompoundKey input c frame frameComputed left).prior.rule4aKey.constitutional
        (actualSlotCompoundKey input c frame frameComputed right).prior.rule4aKey.constitutional := by
  rw [← input.certified.compareLocalizedRerootCompoundThroughRule5_ordering]
  rw [actualSlots_unmarked_throughRule5_eq_constitutional input c frame frameComputed left right
    singleBonded acyclic hcharge noDouble cfgPhys physicalDomain oAtomLeft oObservedLeft
    oAtomRight oObservedRight unmarkedLeft unmarkedRight]

assert_kernel_only TetraStereo.OneCenter.unmarkedSlot_references_nil_of_physicalDomain
assert_kernel_only TetraStereo.OneCenter.unmarkedSlot_rule4aTreePair
assert_kernel_only TetraStereo.OneCenter.compareLocalizedRerootCompoundThroughRule5_eq_eq_of_priorTie
assert_kernel_only TetraStereo.OneCenter.actualSlots_unmarked_throughRule5_eq_constitutional
assert_kernel_only TetraStereo.OneCenter.actualSlots_unmarked_rule45Keys_eq_constitutional

end

end TetraStereo.OneCenter
