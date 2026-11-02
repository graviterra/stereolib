import TetraStereo.OneCenter.LocalizedOrderedRigidPhysicalDescriptor
import TetraStereo.OneCenter.DeclarativeCIPFinalTetrahedralAssignment
import TetraStereo.OneCenter.DeclarativeCIPMultiReferenceProblem
import TetraStereo.OneCenter.LocalizedActualLigandRootSlotCursor
import TetraStereo.OneCenter.LocalizedActualCanonicalConstitutionalRefinement
import TetraStereo.OneCenter.LocalizedActualRigidFrameCompleteness
import TetraStereo.OneCenter.LocalizedIndependentAuxiliaryRS
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-!
# Final-root independent descriptors from the ordered physical evaluator

At a constitutionally rigid calibrated centre, the actual ordered evaluator supplies a strict
physical order at its own fixed-point view. This module turns that order into a ranking for the
independent eight-rule problem, for an arbitrary auxiliary descriptor map. Since distinct ligands
are already separated by constitutional Rules 1a--2, later-rule ties are impossible and the
independent Rule-5 pair count is zero.

This is a final-root theorem. It does not assert a simultaneous all-occurrence `CIPSpec`.
-/

namespace TetraStereo.OneCenter

open DeclarativeCIP
open CertifiedLocalizedCIPInput
open LocalizedUniversalReference
open AcyclicCutBranchAutomorphism

noncomputable section
open scoped Classical

private theorem finRangeMapPermFourFinal (e : Equiv.Perm (Fin 4)) :
    ((List.finRange 4).map e).Perm (List.finRange 4) := by
  have nd : ((List.finRange 4).map e).Nodup := (List.nodup_finRange 4).map e.injective
  apply List.perm_of_nodup_nodup_toFinset_eq nd (List.nodup_finRange 4)
  have h₁ : ((List.finRange 4).map e).toFinset = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [List.toFinset_card_of_nodup nd]; simp)
  have h₂ : (List.finRange 4).toFinset = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [List.toFinset_card_of_nodup (List.nodup_finRange 4)]; simp)
  rw [h₁, h₂]

def finalRootDescriptorMap (input : CertifiedLocalizedCIPInput)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)) :
    DescriptorMap input.TetrahedralCenter :=
  fun center => descriptorMap (input.topUnit center)

private noncomputable def finalRootArm (input : CertifiedLocalizedCIPInput)
    (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
    (view : input.LocalizedDependencyView target) (center : input.TetrahedralCenter)
    (index : Fin 4) :
    input.OriginalRootArm center index .rule4a
      (fun cursor => input.localizedDependencyLabel target view cursor) :=
  Classical.choice (input.exists_originalRootArm center index .rule4a
    (fun cursor => input.localizedDependencyLabel target view cursor))

private theorem finalRootArm_constitutional_eq_frameKey
    (input : CertifiedLocalizedCIPInput)
    (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
    (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedOccurrenceFourLigandFrame
      (input.certified.input.molecule.atomCount + 1))
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (center : input.TetrahedralCenter) (slot index : Fin 4)
    (cursorEq : frame.cursorAt slot = input.localizedLigandRootCursor center index) :
    (finalRootArm input target view center index).key.constitutional =
      (frame.compoundKeyAt input target view derived slot).prior.rule4aKey.constitutional := by
  let arm := finalRootArm input target view center index
  have armBuilt := arm.built
  have frameBuilt := frame.compoundKeyAt_built input target view derived slot
  have framePrior := buildLocalizedRerootCompoundRule45Key?_prior_built input
    target view (localizedOccurrenceRerootEvaluationFuel
      (input.certified.input.molecule.atomCount + 1)) (frame.cursorAt slot)
    (frame.compoundKeyAt input target view derived slot) frameBuilt
  have frameRule4a := buildLocalizedRerootCompoundRule4bcKey?_rule4aKey input
    target view (localizedOccurrenceRerootEvaluationFuel
      (input.certified.input.molecule.atomCount + 1)) (frame.cursorAt slot)
    ((frame.compoundKeyAt input target view derived slot).prior) framePrior.1
  have frameRead : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      (fun cursor => input.localizedDependencyLabel target view cursor)
      (2 * (input.certified.input.molecule.atomCount + 1 + 1))
      (input.localizedLigandRootCursor center index) =
      some ((frame.compoundKeyAt input target view derived slot).prior.rule4aKey) := by
    rw [input.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
      .rule4a target view]
    have hfuel : localizedOccurrenceRerootEvaluationFuel
        (input.certified.input.molecule.atomCount + 1) =
          2 * (input.certified.input.molecule.atomCount + 1 + 1) := rfl
    rw [← cursorEq, ← hfuel]
    exact frameRule4a
  have keyEq : arm.key =
      (frame.compoundKeyAt input target view derived slot).prior.rule4aKey :=
    Option.some.inj (armBuilt.symm.trans frameRead)
  exact congrArg (fun key : input.LocalizedRerootCumulativeRule45Key => key.constitutional)
    keyEq

private theorem finalRootFrameSlot_eq_ligandRootCursor
    (input : LocalizedUniversalReference.Input)
    (center : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input center) = some frame)
    (alpha : Equiv.Perm (Fin 4))
    (ligandLink : ∀ slot, (frame.cursorAt slot).occurrence.1.node.current? =
      some (input.certified.canonicalLigandAtom ⟨center.1, center.2⟩ (alpha slot)))
    (slot : Fin 4) :
    frame.cursorAt slot = input.certified.localizedLigandRootCursor
      ⟨center.1, center.2⟩ (alpha slot) := by
  let tc : input.certified.TetrahedralCenter := ⟨center.1, center.2⟩
  obtain ⟨other, otherEq⟩ := exists_cursorAt_eq_localizedLigandRootCursor input center
    frame frameComputed tc rfl (alpha slot)
  have currentOther : (frame.cursorAt other).occurrence.1.node.current? =
      some (input.certified.canonicalLigandAtom tc (alpha slot)) := by
    rw [otherEq]
    simp [tc, localizedLigandRootNode, OfficialCIPNode.extend]
  have atomEq : input.certified.canonicalLigandAtom tc (alpha other) =
      input.certified.canonicalLigandAtom tc (alpha slot) :=
    Option.some.inj ((ligandLink other).symm.trans currentOther)
  have alphaEq : alpha other = alpha slot :=
    input.certified.canonicalLigandAtom_injective tc atomEq
  have slotEq : other = slot := alpha.injective alphaEq
  subst other
  exact otherEq

theorem localizedConstitutionalRuleOutcome_iff_multiReferenceRuleOutcome
    (input : CertifiedLocalizedCIPInput)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (center : input.TetrahedralCenter) (rule : ConstitutionalRule)
    (left right : Fin 4) (outcome : Ordering) :
    (input.localizedConstitutionalProblemData.withCanonicalAddressing.toProblem).RuleOutcome
      (finalRootDescriptorMap input descriptorMap) rule.toSequenceRule center left right outcome ↔
    (multiReferenceProblem input.moleculeGraph input.localizedDetectedFrame
      input.geometricOrientation).RuleOutcome descriptorMap rule.toSequenceRule
        (input.topUnit center) left right outcome := by
  cases rule <;>
    simp only [Problem.RuleOutcome, Problem.OutcomeOnGraphs,
      DeclarativeCIP.ConstitutionalProblemData.toProblem,
      DeclarativeCIP.ConstitutionalProblemData.CanonicalOutcome,
      DeclarativeCIP.ConstitutionalProblemData.withCanonicalAddressing,
      multiReferenceProblem, MultiReferenceJudgment, ConstitutionalCanonical,
      localizedConstitutionalProblemData,
      ConstitutionalRule.toSequenceRule] <;>
    rw [input.localizedDetectedFrame_ligand_topUnit center left,
      input.localizedDetectedFrame_ligand_topUnit center right] <;>
    simp [topUnit, OccurrenceUnit.atom]

private theorem constitutionalHigher_to_finalProblemHigher
    (input : CertifiedLocalizedCIPInput)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (center : input.TetrahedralCenter) (left right : Fin 4)
    (higher :
      Problem.ConstitutionalHigher
        (input.localizedConstitutionalProblemData.withCanonicalAddressing.toProblem)
        (finalRootDescriptorMap input descriptorMap) center left right) :
      (multiReferenceProblem input.moleculeGraph input.localizedDetectedFrame
        input.geometricOrientation).Higher descriptorMap (input.topUnit center) left right := by
  rcases higher with ⟨rule, earlierTie, decisive⟩
  refine ⟨rule.toSequenceRule, ?_, ?_⟩
  · intro earlier before
    cases earlier with
    | rule1aAtomicNumber =>
        have hbefore : ruleIndex .rule1aAtomicNumber < ruleIndex rule := by
          cases rule <;> simp [SequenceRule.Before, SequenceRule.rank,
            ConstitutionalRule.toSequenceRule, ruleIndex] at before ⊢
        exact (localizedConstitutionalRuleOutcome_iff_multiReferenceRuleOutcome input descriptorMap
          center .rule1aAtomicNumber left right Ordering.eq).mp
          (earlierTie .rule1aAtomicNumber hbefore)
    | rule1bDuplicateNodeProximity =>
        have hbefore : ruleIndex .rule1bDuplicateNodeProximity < ruleIndex rule := by
          cases rule <;> simp [SequenceRule.Before, SequenceRule.rank,
            ConstitutionalRule.toSequenceRule, ruleIndex] at before ⊢
        exact (localizedConstitutionalRuleOutcome_iff_multiReferenceRuleOutcome input descriptorMap
          center .rule1bDuplicateNodeProximity left right Ordering.eq).mp
          (earlierTie .rule1bDuplicateNodeProximity hbefore)
    | rule2AtomicMass =>
        have hbefore : ruleIndex .rule2AtomicMass < ruleIndex rule := by
          cases rule <;> simp [SequenceRule.Before, SequenceRule.rank,
            ConstitutionalRule.toSequenceRule] at before ⊢
        exact (localizedConstitutionalRuleOutcome_iff_multiReferenceRuleOutcome input descriptorMap
          center .rule2AtomicMass left right Ordering.eq).mp
          (earlierTie .rule2AtomicMass hbefore)
    | rule3DoubleBondGeometry =>
        cases rule <;> simp_all [SequenceRule.Before, SequenceRule.rank,
          ConstitutionalRule.toSequenceRule]
    | rule4aStereogenicUnitKind =>
        cases rule <;> simp_all [SequenceRule.Before, SequenceRule.rank,
          ConstitutionalRule.toSequenceRule]
    | rule4bLikeUnlikeDescriptorPairs =>
        cases rule <;> simp_all [SequenceRule.Before, SequenceRule.rank,
          ConstitutionalRule.toSequenceRule]
    | rule4cPseudoasymmetricDescriptor =>
        cases rule <;> simp_all [SequenceRule.Before, SequenceRule.rank,
          ConstitutionalRule.toSequenceRule]
    | rule5EnantiomorphicDescriptor =>
        cases rule <;> simp_all [SequenceRule.Before, SequenceRule.rank,
          ConstitutionalRule.toSequenceRule]
    | rule6ReferencePromotion =>
        cases rule <;> simp_all [SequenceRule.Before, SequenceRule.rank,
          ConstitutionalRule.toSequenceRule]
  · exact (localizedConstitutionalRuleOutcome_iff_multiReferenceRuleOutcome input descriptorMap
      center rule left right Ordering.gt).mp decisive

private theorem finalRootProblemHigher_iff_frameKeyGt
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : ConstantFormalCharge input.certified.moleculeGraph)
    (center : input.certified.detectedMultiCenterMolecule.Center)
    (target : input.certified.LocalizedCIPOccurrence
      (LocalizedUniversalReference.carrierFuel input))
    (view : input.certified.LocalizedDependencyView target)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame? target = some frame)
    (targetEq : target = ActualReaderPhysicalBranchInverse.topTarget input center)
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (alpha : Equiv.Perm (Fin 4))
    (ligandLink : ∀ slot, (frame.cursorAt slot).occurrence.1.node.current? =
      some (input.certified.canonicalLigandAtom ⟨center.1, center.2⟩ (alpha slot)))
    (centerReal : input.certified.RealTetrahedralCenterNode target.1.node ⟨center.1, center.2⟩)
    (rigid : ConstitutionallyRigidGraphAt input.certified.moleculeGraph center.1)
    (enough : input.certified.certified.input.molecule.atomCount ≤
      LocalizedUniversalReference.carrierFuel input)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.certified.moleculeGraph))
    (left right : Fin 4) (different : left ≠ right) :
    (multiReferenceProblem input.certified.moleculeGraph input.certified.localizedDetectedFrame
      input.certified.geometricOrientation).Higher descriptorMap
        (input.certified.topUnit ⟨center.1, center.2⟩) left right ↔
      OfficialRuleMajorKey.compare
        ((frame.compoundKeyAt input.certified target view derived (alpha.symm left)).prior.rule4aKey.constitutional)
        ((frame.compoundKeyAt input.certified target view derived (alpha.symm right)).prior.rule4aKey.constitutional) =
        Ordering.gt := by
  let tc : input.certified.TetrahedralCenter := ⟨center.1, center.2⟩
  let leftSlot := alpha.symm left
  let rightSlot := alpha.symm right
  have frameComputedTop : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input center) = some frame := by
    rw [← targetEq]
    exact frameComputed
  have slotsDifferent : leftSlot ≠ rightSlot := by
    intro same
    apply different
    exact alpha.symm.injective same
  let leftArm := finalRootArm input.certified target view tc left
  let rightArm := finalRootArm input.certified target view tc right
  have leftCursor0 := finalRootFrameSlot_eq_ligandRootCursor input center frame frameComputedTop
    alpha ligandLink leftSlot
  have leftCursor : frame.cursorAt leftSlot =
      input.certified.localizedLigandRootCursor tc left := by
    rw [leftCursor0, Equiv.apply_symm_apply]
  have rightCursor0 := finalRootFrameSlot_eq_ligandRootCursor input center frame frameComputedTop
    alpha ligandLink rightSlot
  have rightCursor : frame.cursorAt rightSlot =
      input.certified.localizedLigandRootCursor tc right := by
    rw [rightCursor0, Equiv.apply_symm_apply]
  have leftKey := finalRootArm_constitutional_eq_frameKey input.certified target view frame
    derived tc leftSlot left leftCursor
  have rightKey := finalRootArm_constitutional_eq_frameKey input.certified target view frame
    derived tc rightSlot right rightCursor
  have frameKeyNe := constitutionalCompare_ne_at_actualFrame_of_graphRigid_derived input.certified
    target view frame derived tc centerReal rigid acyclic singleBonded hcharge enough
    leftSlot rightSlot slotsDifferent
  have centerMap := finalRootDescriptorMap input.certified descriptorMap
  have physicalCompareNe : OfficialRuleMajorKey.compare leftArm.key.constitutional
      rightArm.key.constitutional ≠ Ordering.eq := by
    intro same
    have frameTie : OfficialRuleMajorKey.compare
        ((frame.compoundKeyAt input.certified target view derived leftSlot).prior.rule4aKey.constitutional)
        ((frame.compoundKeyAt input.certified target view derived rightSlot).prior.rule4aKey.constitutional) =
        Ordering.eq := by
      simpa only [leftKey, rightKey, leftArm, rightArm] using same
    exact frameKeyNe frameTie
  constructor
  · intro higher
    rcases higher with ⟨rule, earlierTie, decisive⟩
    cases rule with
    | rule1aAtomicNumber =>
        have decisiveC :=
          (localizedConstitutionalRuleOutcome_iff_multiReferenceRuleOutcome input.certified
            descriptorMap tc .rule1aAtomicNumber left right Ordering.gt).mpr decisive
        have higherC : Problem.ConstitutionalHigher
            (input.certified.localizedConstitutionalProblemData.withCanonicalAddressing.toProblem)
            centerMap tc left right := by
          refine ⟨.rule1aAtomicNumber, ?_, decisiveC⟩
          intro earlier before
          cases earlier <;> simp_all [ruleIndex]
        have compared := (leftArm.compare_eq_gt_iff_constitutionalHigher rightArm centerMap).2
          higherC
        rw [leftKey, rightKey] at compared
        exact compared
    | rule1bDuplicateNodeProximity =>
        have tie1a := earlierTie .rule1aAtomicNumber
          (by simp [SequenceRule.Before, SequenceRule.rank])
        have tie1aC :=
          (localizedConstitutionalRuleOutcome_iff_multiReferenceRuleOutcome input.certified
            descriptorMap tc .rule1aAtomicNumber left right Ordering.eq).mpr tie1a
        have decisiveC :=
          (localizedConstitutionalRuleOutcome_iff_multiReferenceRuleOutcome input.certified
            descriptorMap tc .rule1bDuplicateNodeProximity left right Ordering.gt).mpr decisive
        have higherC : Problem.ConstitutionalHigher
            (input.certified.localizedConstitutionalProblemData.withCanonicalAddressing.toProblem)
            centerMap tc left right := by
          refine ⟨.rule1bDuplicateNodeProximity, ?_, decisiveC⟩
          intro earlier before
          cases earlier with
          | rule1aAtomicNumber => exact tie1aC
          | rule1bDuplicateNodeProximity => simp [ruleIndex] at before
          | rule2AtomicMass => simp [ruleIndex] at before
        have compared := (leftArm.compare_eq_gt_iff_constitutionalHigher rightArm centerMap).2
          higherC
        rw [leftKey, rightKey] at compared
        exact compared
    | rule2AtomicMass =>
        have tie1a := earlierTie .rule1aAtomicNumber
          (by simp [SequenceRule.Before, SequenceRule.rank])
        have tie1b := earlierTie .rule1bDuplicateNodeProximity
          (by simp [SequenceRule.Before, SequenceRule.rank])
        have tie1aC :=
          (localizedConstitutionalRuleOutcome_iff_multiReferenceRuleOutcome input.certified
            descriptorMap tc .rule1aAtomicNumber left right Ordering.eq).mpr tie1a
        have tie1bC :=
          (localizedConstitutionalRuleOutcome_iff_multiReferenceRuleOutcome input.certified
            descriptorMap tc .rule1bDuplicateNodeProximity left right Ordering.eq).mpr tie1b
        have decisiveC :=
          (localizedConstitutionalRuleOutcome_iff_multiReferenceRuleOutcome input.certified
            descriptorMap tc .rule2AtomicMass left right Ordering.gt).mpr decisive
        have higherC : Problem.ConstitutionalHigher
            (input.certified.localizedConstitutionalProblemData.withCanonicalAddressing.toProblem)
            centerMap tc left right := by
          refine ⟨.rule2AtomicMass, ?_, decisiveC⟩
          intro earlier before
          cases earlier with
          | rule1aAtomicNumber => exact tie1aC
          | rule1bDuplicateNodeProximity => exact tie1bC
          | rule2AtomicMass => simp [ruleIndex] at before
        have compared := (leftArm.compare_eq_gt_iff_constitutionalHigher rightArm centerMap).2
          higherC
        rw [leftKey, rightKey] at compared
        exact compared
    | rule3DoubleBondGeometry | rule4aStereogenicUnitKind |
      rule4bLikeUnlikeDescriptorPairs | rule4cPseudoasymmetricDescriptor |
      rule5EnantiomorphicDescriptor | rule6ReferencePromotion =>
        have tiedC : Problem.ConstitutionalTied
            (input.certified.localizedConstitutionalProblemData.withCanonicalAddressing.toProblem)
            centerMap tc left right := by
          intro earlier
          have tied := earlierTie earlier.toSequenceRule (by
            cases earlier <;> simp [SequenceRule.Before, SequenceRule.rank,
              ConstitutionalRule.toSequenceRule])
          exact (localizedConstitutionalRuleOutcome_iff_multiReferenceRuleOutcome input.certified
            descriptorMap tc earlier left right Ordering.eq).mpr tied
        have compared :=
          (leftArm.compare_eq_eq_iff_constitutionalTied rightArm centerMap).2 tiedC
        exact (physicalCompareNe compared).elim
  · intro compared
    have armCompared : OfficialRuleMajorKey.compare leftArm.key.constitutional
        rightArm.key.constitutional = Ordering.gt := by
      rw [leftKey, rightKey]
      exact compared
    exact constitutionalHigher_to_finalProblemHigher input.certified descriptorMap tc left right
      ((leftArm.compare_eq_gt_iff_constitutionalHigher rightArm centerMap).1 armCompared)

private theorem compare_gt_not_both {α : Type*} (cmp : α → α → Ordering)
    [Std.OrientedCmp cmp] (left right : α)
    (forward : cmp left right = Ordering.gt)
    (backward : cmp right left = Ordering.gt) : False := by
  have oriented := Std.OrientedCmp.eq_swap (cmp := cmp) (a := left) (b := right)
  rw [forward, backward] at oriented
  cases oriented

/-- The whole-ligand comparison of a rigid final-root pair is decided by its independent
constitutional comparison, even though later rules in the problem can mention an arbitrary map. -/
private theorem finalRootFramePhysical_gt_implies_Higher
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : ConstantFormalCharge input.certified.moleculeGraph)
    (center : input.certified.detectedMultiCenterMolecule.Center)
    (target : input.certified.LocalizedCIPOccurrence
      (LocalizedUniversalReference.carrierFuel input))
    (view : input.certified.LocalizedDependencyView target)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame? target = some frame)
    (targetEq : target = ActualReaderPhysicalBranchInverse.topTarget input center)
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (alpha : Equiv.Perm (Fin 4))
    (ligandLink : ∀ slot, (frame.cursorAt slot).occurrence.1.node.current? =
      some (input.certified.canonicalLigandAtom ⟨center.1, center.2⟩ (alpha slot)))
    (centerReal : input.certified.RealTetrahedralCenterNode target.1.node ⟨center.1, center.2⟩)
    (rigid : ConstitutionallyRigidGraphAt input.certified.moleculeGraph center.1)
    (enough : input.certified.certified.input.molecule.atomCount ≤
      LocalizedUniversalReference.carrierFuel input)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.certified.moleculeGraph))
    (left right : Fin 4) (different : left ≠ right)
    (higher : frameSlotPhysicalOutcome input.certified target view frame derived
      singleBonded acyclic target.1.root left right Ordering.gt) :
    (multiReferenceProblem input.certified.moleculeGraph input.certified.localizedDetectedFrame
      input.certified.geometricOrientation).Higher descriptorMap
        (input.certified.topUnit ⟨center.1, center.2⟩) (alpha left) (alpha right) := by
  have cmp := (frameSlotPhysicalOutcome_iff_constitutionalCompare input.certified
    target view frame derived singleBonded acyclic left right Ordering.gt).2 higher
  have mapped := (finalRootProblemHigher_iff_frameKeyGt input singleBonded acyclic hcharge
    center target view frame frameComputed targetEq derived alpha ligandLink centerReal rigid enough
    descriptorMap (alpha left) (alpha right) (fun h => different (alpha.injective h))).2
  have cmp' : OfficialRuleMajorKey.compare
      ((frame.compoundKeyAt input.certified target view derived
          (alpha.symm (alpha left))).prior.rule4aKey.constitutional)
      ((frame.compoundKeyAt input.certified target view derived
          (alpha.symm (alpha right))).prior.rule4aKey.constitutional) = Ordering.gt := by
    simpa only [Equiv.symm_apply_apply] using cmp
  exact mapped cmp'

/-- Arbitrary-map final-root theorem. The runtime label, independent eight-rule judgment, zero
Rule-5 tie count, and uniqueness of the final assignment are all about the same actual final
occurrence. The only per-center hypotheses are the physical calibrated-center assumptions and
simple/acyclic/constant-charge chemistry; there is no global physical-domain or Z-injectivity
premise. -/
theorem orderedTop_finalTetrahedralAssignment_of_physicalCalibratedCenter
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : ConstantFormalCharge input.certified.moleculeGraph)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (center : input.certified.detectedMultiCenterMolecule.Center)
    (calibrated : ActualPhysicalGeneralRigidCalibratedCenter input.certified
      input.certified.detectedMultiCenterMolecule cfg center)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.certified.moleculeGraph)) :
    ∃ rs : RS,
      input.certified.orderedReferenceState (LocalizedUniversalReference.carrierFuel input)
          (ActualReaderPhysicalBranchInverse.topTarget input center) = some (.chiral rs) ∧
      FinalTetrahedralAssignment
        (multiReferenceProblem input.certified.moleculeGraph input.certified.localizedDetectedFrame
          input.certified.geometricOrientation)
        descriptorMap (input.certified.topUnit ⟨center.1, center.2⟩) (.chiral rs) ∧
      finalRule5PairCount
        (multiReferenceProblem input.certified.moleculeGraph input.certified.localizedDetectedFrame
          input.certified.geometricOrientation)
        descriptorMap (input.certified.topUnit ⟨center.1, center.2⟩) = 0 ∧
      ∀ label, FinalTetrahedralAssignment
        (multiReferenceProblem input.certified.moleculeGraph input.certified.localizedDetectedFrame
          input.certified.geometricOrientation)
        descriptorMap (input.certified.topUnit ⟨center.1, center.2⟩) label → label = .chiral rs := by
  let tc : input.certified.TetrahedralCenter := ⟨center.1, center.2⟩
  let target := ActualReaderPhysicalBranchInverse.topTarget input center
  let view := input.certified.localizedDependencyView
    (input.certified.orderedReferenceState (LocalizedUniversalReference.carrierFuel input)) target
  let problem := multiReferenceProblem input.certified.moleculeGraph
    input.certified.localizedDetectedFrame input.certified.geometricOrientation
  let unit := input.certified.topUnit tc
  obtain ⟨frame, alpha, pointsAt, order, frameComputed, ligandLink, observed,
    independent, iffGeometry⟩ :=
    orderedTop_eq_chiral_iff_independentPhysicalGeometry_of_physicalCalibratedCenter input
      singleBonded acyclic hcharge cfg center calibrated
  have derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame target frame :=
    input.certified.localizedOccurrenceFourLigandFrame?_sound target frame frameComputed
  have targetCurrent : target.1.node.current? = some center.1 :=
    ActualReaderPhysicalBranchInverse.topTarget_current input center
  have centerReal : input.certified.RealTetrahedralCenterNode target.1.node tc :=
    ⟨input.certified.carrierOccurrence_provenance_real singleBonded acyclic target,
      targetCurrent⟩
  have rigid : ConstitutionallyRigidGraphAt input.certified.moleculeGraph center.1 :=
    constitutionallyRigidGraphAt_of_constitutionallyRigid_detected input.certified center
      calibrated.1
  have enough : input.certified.certified.input.molecule.atomCount ≤
      LocalizedUniversalReference.carrierFuel input := by
    exact globalCarrierFuel_adequate input
  let canonicalOrder : List (Fin 4) := order.map alpha
  have canonicalOrderPerm : canonicalOrder.Perm (List.finRange 4) := by
    exact (independent.1.map alpha).trans (finRangeMapPermFourFinal alpha)
  have canonicalOrderHigher : canonicalOrder.Pairwise
      (fun left right => problem.Higher descriptorMap unit left right) := by
    apply List.pairwise_map.mpr
    apply independent.2.imp
    intro left right physical
    have different : left ≠ right := by
      intro same
      subst right
      have compared := (frameSlotPhysicalOutcome_iff_constitutionalCompare input.certified
        target view frame derived singleBonded acyclic left left Ordering.gt).2 physical
      have self : OfficialRuleMajorKey.compare
          ((frame.compoundKeyAt input.certified target view derived left).prior.rule4aKey.constitutional)
          ((frame.compoundKeyAt input.certified target view derived left).prior.rule4aKey.constitutional) =
          Ordering.eq := CompilerProjectionFidelity.compare_eq_eq_of_sameConstitution
            ⟨rfl, rfl, rfl, rfl⟩
      rw [self] at compared
      cases compared
    exact finalRootFramePhysical_gt_implies_Higher input singleBonded acyclic hcharge center
      target view frame frameComputed rfl derived alpha ligandLink centerReal rigid enough
      descriptorMap left right different physical
  have nd : canonicalOrder.Nodup := canonicalOrderPerm.nodup_iff.2 (List.nodup_finRange 4)
  have hlen : canonicalOrder.length = 4 := by
    rw [canonicalOrderPerm.length_eq, List.length_finRange]
  have hmem : ∀ x, x ∈ canonicalOrder := fun x =>
    canonicalOrderPerm.mem_iff.2 (List.mem_finRange x)
  let ranking : Equiv.Perm (Fin 4) :=
    (finCongr hlen.symm).trans
      (List.Nodup.getEquivOfForallMemList canonicalOrder nd hmem)
  have ranking_apply : ∀ k, ranking k = canonicalOrder.get (Fin.cast hlen.symm k) :=
    fun _ => rfl
  have ranks : problem.Ranks descriptorMap unit ranking := by
    intro first second before
    have before' : Fin.cast hlen.symm first < Fin.cast hlen.symm second := before
    have higher := (List.pairwise_iff_get.1 canonicalOrderHigher _ _ before')
    rw [ranking_apply, ranking_apply]
    exact higher
  have hmapRanking : (List.finRange 4).map ranking = canonicalOrder := by
    apply List.ext_getElem
    · rw [List.length_map, List.length_finRange, hlen]
    · intro n hn1 hn2
      rw [List.getElem_map, List.getElem_finRange, ranking_apply]
      rfl
  have hpoints : (List.finRange 4).map (fun k => pointsAt (ranking k)) =
      canonicalOrder.map pointsAt := by
    have hcomp : (fun k => pointsAt (ranking k)) = pointsAt ∘ ranking := rfl
    rw [hcomp, ← List.map_map, hmapRanking]
  rcases calibrated with ⟨_calibratedRigid, physicalPoints, physicalObserved,
    physicalNonzero, _calibrationSign⟩
  let beta := input.certified.canonicalLigandReindex center
  have pointsEq : pointsAt = fun i => physicalPoints (beta.symm i) := by
    funext i
    have atomEq : input.certified.detectedMultiCenterMolecule.ligandAtomAt center (beta.symm i) =
        input.certified.canonicalLigandAtom tc i := by
      simpa [beta, tc] using
        input.certified.canonicalLigandReindex_spec center (beta.symm i)
    have physicalAtCanonical : input.certified.spatialPointAt?
        (input.certified.canonicalLigandAtom tc i) = some (physicalPoints (beta.symm i)) := by
      rw [← atomEq]
      exact physicalObserved (beta.symm i)
    exact Option.some.inj ((observed i).symm.trans physicalAtCanonical)
  have nonzeroCanonical : CartesianPoint3.orientedVolume
      (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) ≠ 0 := by
    rw [pointsEq]
    exact cartesianOrientedVolume_perm_ne_zero physicalPoints beta.symm physicalNonzero
  obtain ⟨rs, rationalCanonical⟩ :=
    rationalTetrahedralDescriptor_exists_of_permutation pointsAt canonicalOrder
      canonicalOrderPerm nonzeroCanonical
  have rationalOrdered : RationalTetrahedralDescriptor
      (order.map fun i => pointsAt (alpha i)) rs := by
    simpa [canonicalOrder, List.map_map] using rationalCanonical
  have stateEq := (iffGeometry rs).2 rationalOrdered
  have orientation : input.certified.geometricOrientation unit ranking (rsDescriptor rs) := by
    refine ⟨pointsAt, rs, ?_, ?_, rfl⟩
    · intro i
      rw [localizedDetectedFrame_ligand_topUnit]
      exact observed i
    · rw [hpoints]
      exact rationalCanonical
  have judgment : problem.DescriptorJudgment descriptorMap unit (rsDescriptor rs) :=
    ⟨ranking, ranks, orientation⟩
  have noEarlierTie : ∀ i j : Fin 4, i ≠ j →
      ¬ problem.EarlierRulesTie descriptorMap .rule5EnantiomorphicDescriptor unit i j := by
    intro i j different hties
    let leftSlot := alpha.symm i
    let rightSlot := alpha.symm j
    have slotsDifferent : leftSlot ≠ rightSlot := by
      intro same
      exact different (alpha.symm.injective same)
    have frameKeyNe := constitutionalCompare_ne_at_actualFrame_of_graphRigid_derived input.certified
      target view frame derived tc centerReal rigid acyclic singleBonded hcharge enough
      leftSlot rightSlot slotsDifferent
    let leftArm := finalRootArm input.certified target view tc i
    let rightArm := finalRootArm input.certified target view tc j
    have leftCursor0 := finalRootFrameSlot_eq_ligandRootCursor input center frame frameComputed
      alpha ligandLink leftSlot
    have leftCursor : frame.cursorAt leftSlot =
        input.certified.localizedLigandRootCursor tc i := by
      rw [leftCursor0, Equiv.apply_symm_apply]
    have rightCursor0 := finalRootFrameSlot_eq_ligandRootCursor input center frame frameComputed
      alpha ligandLink rightSlot
    have rightCursor : frame.cursorAt rightSlot =
        input.certified.localizedLigandRootCursor tc j := by
      rw [rightCursor0, Equiv.apply_symm_apply]
    have leftKey := finalRootArm_constitutional_eq_frameKey input.certified target view frame
      derived tc leftSlot i leftCursor
    have rightKey := finalRootArm_constitutional_eq_frameKey input.certified target view frame
      derived tc rightSlot j rightCursor
    have tiedC :
        Problem.ConstitutionalTied
          (input.certified.localizedConstitutionalProblemData.withCanonicalAddressing.toProblem)
          (finalRootDescriptorMap input.certified descriptorMap) tc i j := by
      intro rule
      have tied := hties rule.toSequenceRule (by cases rule <;>
        simp [SequenceRule.Before, SequenceRule.rank, ConstitutionalRule.toSequenceRule])
      exact (localizedConstitutionalRuleOutcome_iff_multiReferenceRuleOutcome input.certified
        descriptorMap tc rule i j Ordering.eq).mpr tied
    have compared :=
      (leftArm.compare_eq_eq_iff_constitutionalTied rightArm
        (finalRootDescriptorMap input.certified descriptorMap)).2 tiedC
    have frameTie : OfficialRuleMajorKey.compare
        ((frame.compoundKeyAt input.certified target view derived leftSlot).prior.rule4aKey.constitutional)
        ((frame.compoundKeyAt input.certified target view derived rightSlot).prior.rule4aKey.constitutional) =
        Ordering.eq := by
      simpa only [leftKey, rightKey, leftArm, rightArm] using compared
    exact frameKeyNe frameTie
  have countZero : finalRule5PairCount problem descriptorMap unit = 0 :=
    finalRule5PairCount_eq_zero_of_noEarlierTie problem descriptorMap unit noEarlierTie
  have assignment : FinalTetrahedralAssignment problem descriptorMap unit (.chiral rs) :=
    finalTetrahedralAssignment_chiral_of_count_zero problem descriptorMap unit rs judgment countZero
  have ranksUnique : ∀ first second : Equiv.Perm (Fin 4),
      problem.Ranks descriptorMap unit first → problem.Ranks descriptorMap unit second →
        first = second := by
    intro first second firstRanks secondRanks
    haveI : Std.OrientedCmp OfficialRuleMajorKey.compareNat := by
      unfold OfficialRuleMajorKey.compareNat
      infer_instance
    haveI : Std.OrientedCmp OfficialRuleMajorKey.compareRule1b := by
      unfold OfficialRuleMajorKey.compareRule1b
      infer_instance
    haveI : Std.OrientedCmp (@OfficialRuleMajorKey.compare input.certified.Atom) := by
      unfold OfficialRuleMajorKey.compare OfficialRuleMajorKey.compareSparseLayers
        OfficialRuleMajorKey.compareSparseLayer OfficialRuleMajorKey.compareSparseEntry
      infer_instance
    let reindex : Equiv.Perm (Fin 4) := first.trans second.symm
    have monotone : StrictMono reindex := by
      intro i j before
      by_contra notBefore
      have le : reindex j ≤ reindex i := le_of_not_gt notBefore
      have ne : reindex j ≠ reindex i := by
        intro same
        exact (ne_of_lt before) (reindex.injective (Eq.symm same))
      have reverseBefore : reindex j < reindex i := lt_of_le_of_ne le ne
      have forwardHigher := firstRanks i j before
      have reverseHigher : problem.Higher descriptorMap unit (first j) (first i) := by
        simpa [reindex] using secondRanks (reindex j) (reindex i) reverseBefore
      have different : first i ≠ first j := fun same =>
        (ne_of_lt before) (first.injective same)
      have cmpForward :=
        (finalRootProblemHigher_iff_frameKeyGt input singleBonded acyclic hcharge center target
          view frame frameComputed rfl derived alpha ligandLink centerReal rigid enough descriptorMap
          (first i) (first j) different).1 forwardHigher
      have cmpReverse :=
        (finalRootProblemHigher_iff_frameKeyGt input singleBonded acyclic hcharge center target
          view frame frameComputed rfl derived alpha ligandLink centerReal rigid enough descriptorMap
          (first j) (first i) different.symm).1 reverseHigher
      exact compare_gt_not_both (@OfficialRuleMajorKey.compare input.certified.Atom)
        ((frame.compoundKeyAt input.certified target view derived (alpha.symm (first i))).prior.rule4aKey.constitutional)
        ((frame.compoundKeyAt input.certified target view derived (alpha.symm (first j))).prior.rule4aKey.constitutional)
        cmpForward cmpReverse
    apply Equiv.ext
    intro i
    have identity : reindex i = i := le_antisymm (monotone.le_id i) (monotone.id_le i)
    have equality := congrArg second identity
    simpa [reindex] using equality
  have descriptorUnique : ∀ descriptor, problem.DescriptorJudgment descriptorMap unit descriptor →
      descriptor = rsDescriptor rs := by
    intro descriptor descriptorJudgment
    rcases descriptorJudgment with ⟨otherRanking, otherRanks, otherOrientation⟩
    have rankingEq := ranksUnique ranking otherRanking ranks otherRanks
    subst otherRanking
    exact (input.certified.geometricOrientation_functional orientation otherOrientation).symm
  refine ⟨rs, stateEq, assignment, countZero, ?_⟩
  intro label assigned
  rcases assigned with ⟨otherRS, otherJudgment, labelEq⟩
  have descriptorEq := descriptorUnique (rsDescriptor otherRS) otherJudgment
  have rsEq := rsDescriptor_injective descriptorEq
  subst otherRS
  have labelEq' : label = classifyTetrahedralRSPseudo rs
      (finalRule5PairCount problem descriptorMap unit) := by
    simpa [problem, unit, tc] using labelEq
  rw [countZero] at labelEq'
  simpa using labelEq'

end
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.orderedTop_finalTetrahedralAssignment_of_physicalCalibratedCenter
