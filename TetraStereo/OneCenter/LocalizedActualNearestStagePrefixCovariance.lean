import TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction
import TetraStereo.OneCenter.LocalizedRealizedTreeCutIsomorphism
import TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism
import TetraStereo.OneCenter.LocalizedActualTableAddressOrder
import TetraStereo.OneCenter.LocalizedRealizedTreePhysicalDistance
import TetraStereo.OneCenter.LocalizedGeneralRigidCalibratedRootReader
import TetraStereo.OneCenter.LocalizedParametricCumulativeLabels
import TetraStereo.OneCenter.LocalizedConstitutionalObservable
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput








































namespace LocalizedActualNearestStagePrefixCovariance

/-! ## A. Actual production builds as parametric WithRead builds -/

/-- The actual production build of one stage at the frame cursor is exactly the parametric WithRead
build with the actual generated dependency reader: specializing the parametric builder's callback to
`localizedDependencyLabel` over the reference dependency view reproduces the production builder. -/
theorem withReadBuild_eq_of_actualStage_built
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (_frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    (stage : LocalizedCumulativeRule45Stage)
    {key : input.certified.LocalizedRerootCumulativeRule45Key}
    (built : input.certified.buildLocalizedRerootCumulativeRule45Key? stage
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (2 * (LocalizedUniversalReference.carrierFuel input + 1))
      (frame.cursorAt slot) = some key) :
    input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? stage
        (ActualReaderPhysicalBranchInverse.dependencyReader input c)
        (2 * (LocalizedUniversalReference.carrierFuel input + 1))
        (frame.cursorAt slot) = some key := by
  have asPlain : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? stage
      (fun cursor => input.certified.localizedDependencyLabel
        (ActualReaderPhysicalBranchInverse.topTarget input c)
        (input.certified.localizedDependencyView
          (LocalizedUniversalReference.referenceState input)
          (ActualReaderPhysicalBranchInverse.topTarget input c)) cursor)
      (2 * (LocalizedUniversalReference.carrierFuel input + 1))
      (frame.cursorAt slot) =
    input.certified.buildLocalizedRerootCumulativeRule45Key? stage
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (input.certified.localizedDependencyView
        (LocalizedUniversalReference.referenceState input)
        (ActualReaderPhysicalBranchInverse.topTarget input c))
      (2 * (LocalizedUniversalReference.carrierFuel input + 1))
      (frame.cursorAt slot) :=
    buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
      input.certified stage (ActualReaderPhysicalBranchInverse.topTarget input c)
      (input.certified.localizedDependencyView
        (LocalizedUniversalReference.referenceState input)
        (ActualReaderPhysicalBranchInverse.topTarget input c))
      (2 * (LocalizedUniversalReference.carrierFuel input + 1))
      (frame.cursorAt slot)
  change input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? stage
      (fun cursor => input.certified.localizedDependencyLabel
        (ActualReaderPhysicalBranchInverse.topTarget input c)
        (input.certified.localizedDependencyView
          (LocalizedUniversalReference.referenceState input)
          (ActualReaderPhysicalBranchInverse.topTarget input c)) cursor)
      (2 * (LocalizedUniversalReference.carrierFuel input + 1))
      (frame.cursorAt slot) = some key
  rw [asPlain]
  exact built

/-! ## B. Constitutional coherence at the shared actual cursor -/

/-- The two actual production stage builds at one frame cursor carry **equal constitutional
observables**: each actual build admits the independent declarative Rule-1/2 derivation at the same
cursor (through the parametric WithRead compiler), and independent derivations at one cursor agree.
No equality of keys, labels, readers or recursion budgets is assumed. -/
theorem sameCursor_constitutionalObservable_eq_of_actualStage_built
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    (own : Option RS)
    {keyR keyS : input.certified.LocalizedRerootCumulativeRule45Key}
    (builtR : input.certified.buildLocalizedRerootCumulativeRule45Key?
      (localizedRule5StageFor own .R)
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (2 * (LocalizedUniversalReference.carrierFuel input + 1))
      (frame.cursorAt slot) = some keyR)
    (builtS : input.certified.buildLocalizedRerootCumulativeRule45Key?
      (localizedRule5StageFor own .S)
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (2 * (LocalizedUniversalReference.carrierFuel input + 1))
      (frame.cursorAt slot) = some keyS) :
    constitutionalObservable keyR.constitutional =
      constitutionalObservable keyS.constitutional := by
  have withReadR := withReadBuild_eq_of_actualStage_built input c frame frameComputed slot
    (localizedRule5StageFor own .R) builtR
  have withReadS := withReadBuild_eq_of_actualStage_built input c frame frameComputed slot
    (localizedRule5StageFor own .S) builtS
  have declarativeR := buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_declarative
    input.certified (localizedRule5StageFor own .R)
    (ActualReaderPhysicalBranchInverse.dependencyReader input c)
    (2 * (LocalizedUniversalReference.carrierFuel input + 1))
    (frame.cursorAt slot) keyR withReadR
  have declarativeS := buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_declarative
    input.certified (localizedRule5StageFor own .S)
    (ActualReaderPhysicalBranchInverse.dependencyReader input c)
    (2 * (LocalizedUniversalReference.carrierFuel input + 1))
    (frame.cursorAt slot) keyS withReadS
  exact declarative_constitutional_observable_unique input.certified
    (carrierFuel := LocalizedUniversalReference.carrierFuel input)
    (2 * (LocalizedUniversalReference.carrierFuel input + 1))
    (2 * (LocalizedUniversalReference.carrierFuel input + 1))
    (frame.cursorAt slot) keyR.constitutional keyS.constitutional declarativeR declarativeS

/-! ## C. Literal constitutional column equalities of the two actual trees -/

/-- The literal Rule-1a column of the two actual stage trees is the same list of addressed rows. -/
theorem rule1a_eq_of_actualStage_built
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    (own : Option RS)
    {keyR keyS : input.certified.LocalizedRerootCumulativeRule45Key}
    {treeR treeS : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input)}
    (builtR : input.certified.buildLocalizedRerootCumulativeRule45Key?
      (localizedRule5StageFor own .R)
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (2 * (LocalizedUniversalReference.carrierFuel input + 1))
      (frame.cursorAt slot) = some keyR)
    (builtS : input.certified.buildLocalizedRerootCumulativeRule45Key?
      (localizedRule5StageFor own .S)
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (2 * (LocalizedUniversalReference.carrierFuel input + 1))
      (frame.cursorAt slot) = some keyS)
    (tableMatchR : LocalizedCumulativeTreeTableMatch
      (localizedRule5StageFor own .R) treeR keyR)
    (tableMatchS : LocalizedCumulativeTreeTableMatch
      (localizedRule5StageFor own .S) treeS keyS) :
    (LocalizedCumulativeDecoratedTree.tables (localizedRule5StageFor own .R) treeR).rule1a =
      (LocalizedCumulativeDecoratedTree.tables (localizedRule5StageFor own .S) treeS).rule1a := by
  have observableEq :=
    sameCursor_constitutionalObservable_eq_of_actualStage_built input c frame frameComputed
      slot own builtR builtS
  have keyEq : keyR.constitutional.rule1a = keyS.constitutional.rule1a :=
    congrArg LocalizedConstitutionalObservable.rule1a observableEq
  exact tableMatchR.1.trans (keyEq.trans tableMatchS.1.symm)

/-- The literal Rule-1b column of the two actual stage trees is the same list of addressed rows. -/
theorem rule1b_eq_of_actualStage_built
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    (own : Option RS)
    {keyR keyS : input.certified.LocalizedRerootCumulativeRule45Key}
    {treeR treeS : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input)}
    (builtR : input.certified.buildLocalizedRerootCumulativeRule45Key?
      (localizedRule5StageFor own .R)
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (2 * (LocalizedUniversalReference.carrierFuel input + 1))
      (frame.cursorAt slot) = some keyR)
    (builtS : input.certified.buildLocalizedRerootCumulativeRule45Key?
      (localizedRule5StageFor own .S)
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (2 * (LocalizedUniversalReference.carrierFuel input + 1))
      (frame.cursorAt slot) = some keyS)
    (tableMatchR : LocalizedCumulativeTreeTableMatch
      (localizedRule5StageFor own .R) treeR keyR)
    (tableMatchS : LocalizedCumulativeTreeTableMatch
      (localizedRule5StageFor own .S) treeS keyS) :
    (LocalizedCumulativeDecoratedTree.tables (localizedRule5StageFor own .R) treeR).rule1b =
      (LocalizedCumulativeDecoratedTree.tables (localizedRule5StageFor own .S) treeS).rule1b := by
  have observableEq :=
    sameCursor_constitutionalObservable_eq_of_actualStage_built input c frame frameComputed
      slot own builtR builtS
  have keyEq : keyR.constitutional.rule1b = keyS.constitutional.rule1b :=
    congrArg LocalizedConstitutionalObservable.rule1b observableEq
  exact tableMatchR.2.1.trans (keyEq.trans tableMatchS.2.1.symm)

/-- The literal Rule-2 column of the two actual stage trees is the same list of addressed rows. -/
theorem rule2_eq_of_actualStage_built
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    (own : Option RS)
    {keyR keyS : input.certified.LocalizedRerootCumulativeRule45Key}
    {treeR treeS : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input)}
    (builtR : input.certified.buildLocalizedRerootCumulativeRule45Key?
      (localizedRule5StageFor own .R)
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (2 * (LocalizedUniversalReference.carrierFuel input + 1))
      (frame.cursorAt slot) = some keyR)
    (builtS : input.certified.buildLocalizedRerootCumulativeRule45Key?
      (localizedRule5StageFor own .S)
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (2 * (LocalizedUniversalReference.carrierFuel input + 1))
      (frame.cursorAt slot) = some keyS)
    (tableMatchR : LocalizedCumulativeTreeTableMatch
      (localizedRule5StageFor own .R) treeR keyR)
    (tableMatchS : LocalizedCumulativeTreeTableMatch
      (localizedRule5StageFor own .S) treeS keyS) :
    (LocalizedCumulativeDecoratedTree.tables (localizedRule5StageFor own .R) treeR).rule2 =
      (LocalizedCumulativeDecoratedTree.tables (localizedRule5StageFor own .S) treeS).rule2 := by
  have observableEq :=
    sameCursor_constitutionalObservable_eq_of_actualStage_built input c frame frameComputed
      slot own builtR builtS
  have keyEq : keyR.constitutional.rule2 = keyS.constitutional.rule2 :=
    congrArg LocalizedConstitutionalObservable.rule2 observableEq
  exact tableMatchR.2.2.1.trans (keyEq.trans tableMatchS.2.2.1.symm)

/-! ## D. Equal erased shape of the two actual trees -/

/-- **The two actual stage trees at one frame cursor have the same erased shape.**  The three
constitutional columns are literal equal lists and the descriptor column is not read: this is the
stage-free reconstruction theorem. -/
theorem shape_eq_of_actualStage_built
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    (own : Option RS)
    {keyR keyS : input.certified.LocalizedRerootCumulativeRule45Key}
    {treeR treeS : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input)}
    (builtR : input.certified.buildLocalizedRerootCumulativeRule45Key?
      (localizedRule5StageFor own .R)
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (2 * (LocalizedUniversalReference.carrierFuel input + 1))
      (frame.cursorAt slot) = some keyR)
    (builtS : input.certified.buildLocalizedRerootCumulativeRule45Key?
      (localizedRule5StageFor own .S)
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (2 * (LocalizedUniversalReference.carrierFuel input + 1))
      (frame.cursorAt slot) = some keyS)
    (tableMatchR : LocalizedCumulativeTreeTableMatch
      (localizedRule5StageFor own .R) treeR keyR)
    (tableMatchS : LocalizedCumulativeTreeTableMatch
      (localizedRule5StageFor own .S) treeS keyS) :
    LocalizedCumulativeDecoratedTree.shape treeR =
      LocalizedCumulativeDecoratedTree.shape treeS := by
  exact LocalizedCumulativeDecoratedTree.table_shape_eq_of_columns_eq
    (localizedRule5StageFor own .R) (localizedRule5StageFor own .S) treeR treeS
    (rule1a_eq_of_actualStage_built input c frame frameComputed slot own builtR builtS
      tableMatchR tableMatchS)
    (rule1b_eq_of_actualStage_built input c frame frameComputed slot own builtR builtS
      tableMatchR tableMatchS)
    (rule2_eq_of_actualStage_built input c frame frameComputed slot own builtR builtS
      tableMatchR tableMatchS)

/-! ## E. The actual shape self-isomorphism of the incoming cut branch -/





noncomputable def actualStage_selfIso
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    {oAtom : input.certified.Atom}
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    {treeR treeS : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input)}
    (sourceEqR : treeR.source = frame.cursorAt slot)
    (sourceEqS : treeS.source = frame.cursorAt slot)
    (realizesR : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) treeR)
    (realizesS : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) treeS)
    (hshape : LocalizedCumulativeDecoratedTree.shape treeR =
      LocalizedCumulativeDecoratedTree.shape treeS) :
    AcyclicCutBranchAutomorphism.RootedCutBranchIso input.certified.moleculeGraph c.1 oAtom oAtom :=
  rootedCutBranchIso_of_shapeMatch (input := input.certified)
    (carrierFuel := LocalizedUniversalReference.carrierFuel input)
    (singleBonded := singleBonded) (acyclic := acyclic)
    (globalCarrierFuel_adequate input) hshape realizesR realizesS
    (LocalizedUniqueNearestRule5Direction.actualTree_previousEq_of_source
      input c frame frameComputed slot sourceEqR)
    (LocalizedUniqueNearestRule5Direction.actualTree_valid_of_source
      input c frame frameComputed slot sourceEqR)
    (LocalizedUniqueNearestRule5Direction.actualTree_sameRoot_of_source
      input c frame frameComputed slot sourceEqR)
    (LocalizedUniqueNearestRule5Direction.actualTree_previousEq_of_source
      input c frame frameComputed slot sourceEqS)
    (LocalizedUniqueNearestRule5Direction.actualTree_valid_of_source
      input c frame frameComputed slot sourceEqS)
    (LocalizedUniqueNearestRule5Direction.actualTree_sameRoot_of_source
      input c frame frameComputed slot sourceEqS)
    (LocalizedUniqueNearestRule5Direction.actualTree_oObserved_of_source
      input c frame frameComputed slot sourceEqR oObserved)
    (ActualReaderPhysicalBranchInverse.topTarget_current input c)
    (LocalizedUniqueNearestRule5Direction.actualTree_oObserved_of_source
      input c frame frameComputed slot sourceEqS oObserved)
    (ActualReaderPhysicalBranchInverse.topTarget_current input c)
    (actualSlot_incomingEdge input c frame frameComputed slot oObserved)
    (actualSlot_incomingEdge input c frame frameComputed slot oObserved)




theorem actualStage_selfIso_fixes_center
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
    {oAtom : input.certified.Atom}
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    {treeR treeS : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input)}
    (sourceEqR : treeR.source = frame.cursorAt slot)
    (sourceEqS : treeS.source = frame.cursorAt slot)
    (realizesR : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) treeR)
    (realizesS : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) treeS)
    (hshape : LocalizedCumulativeDecoratedTree.shape treeR =
      LocalizedCumulativeDecoratedTree.shape treeS)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom center distance) :
    ((actualStage_selfIso input c frame frameComputed slot singleBonded acyclic oObserved
        sourceEqR sourceEqS realizesR realizesS hshape).toEquiv ⟨center, unique.1⟩ :
      input.certified.Atom) = center := by
  exact LocalizedCutBranchSelfAutomorphism.rootedCutBranchIso_fixes_physicalBranchUniqueNearest_center
    (input := input) (singleBonded := singleBonded) (acyclic := acyclic)
    (hcharge := hcharge) (c := c) (u := oAtom)
    (hcu := actualSlot_incomingEdge input c frame frameComputed slot oObserved)
    (φ := actualStage_selfIso input c frame frameComputed slot singleBonded acyclic oObserved
      sourceEqR sourceEqS realizesR realizesS hshape)
    (nearest := unique)

/-- **Centre positions are preserved by the equal-shape correspondence.**  A left position whose
physical atom is the unique nearest centre matches a right position whose physical atom is again
the centre.  The forward map is the concrete isomorphism action (`toEquiv_apply`), and the fixed
centre forces the image to be the centre cut-branch point. -/
theorem shapePositionEquiv_atom_center_of_center_of_actualStage
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
    {oAtom : input.certified.Atom}
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    {treeR treeS : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input)}
    (sourceEqR : treeR.source = frame.cursorAt slot)
    (sourceEqS : treeS.source = frame.cursorAt slot)
    (realizesR : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) treeR)
    (realizesS : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) treeS)
    (hshape : LocalizedCumulativeDecoratedTree.shape treeR =
      LocalizedCumulativeDecoratedTree.shape treeS)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom center distance)
    (p : Position treeR)
    (pCenter : positionAtom singleBonded acyclic p = center) :
    positionAtom singleBonded acyclic (shapePositionEquiv hshape p) = center := by
  have prevEqR := LocalizedUniqueNearestRule5Direction.actualTree_previousEq_of_source
    input c frame frameComputed slot sourceEqR
  have prevEqS := LocalizedUniqueNearestRule5Direction.actualTree_previousEq_of_source
    input c frame frameComputed slot sourceEqS
  have validR := LocalizedUniqueNearestRule5Direction.actualTree_valid_of_source
    input c frame frameComputed slot sourceEqR
  have validS := LocalizedUniqueNearestRule5Direction.actualTree_valid_of_source
    input c frame frameComputed slot sourceEqS
  have sameRootR := LocalizedUniqueNearestRule5Direction.actualTree_sameRoot_of_source
    input c frame frameComputed slot sourceEqR
  have sameRootS := LocalizedUniqueNearestRule5Direction.actualTree_sameRoot_of_source
    input c frame frameComputed slot sourceEqS
  have obsR := LocalizedUniqueNearestRule5Direction.actualTree_oObserved_of_source
    input c frame frameComputed slot sourceEqR oObserved
  have obsS := LocalizedUniqueNearestRule5Direction.actualTree_oObserved_of_source
    input c frame frameComputed slot sourceEqS oObserved
  have cutPointCenter : (positionCutEquiv singleBonded acyclic
      (globalCarrierFuel_adequate input) realizesR
      (ActualReaderPhysicalBranchInverse.topTarget input c) prevEqR validR sameRootR obsR
      (ActualReaderPhysicalBranchInverse.topTarget_current input c)
      (actualSlot_incomingEdge input c frame frameComputed slot oObserved) p :
      input.certified.Atom) = center := by
    simpa only [positionCutEquiv_apply_coe] using pCenter
  have applyEq : (((actualStage_selfIso input c frame frameComputed slot singleBonded acyclic
          oObserved sourceEqR sourceEqS realizesR realizesS hshape).toEquiv
            (positionCutEquiv singleBonded acyclic (globalCarrierFuel_adequate input) realizesR
              (ActualReaderPhysicalBranchInverse.topTarget input c) prevEqR validR sameRootR obsR
              (ActualReaderPhysicalBranchInverse.topTarget_current input c)
              (actualSlot_incomingEdge input c frame frameComputed slot oObserved) p) :
          AcyclicCutBranchAutomorphism.CutBranch input.certified.moleculeGraph c.1 oAtom) :
        input.certified.Atom) =
      positionAtom singleBonded acyclic (shapePositionEquiv hshape p) := by
    simpa only [actualStage_selfIso] using
      (rootedCutBranchIso_of_shapeMatch_toEquiv_apply (input := input.certified)
        (carrierFuel := LocalizedUniversalReference.carrierFuel input)
        (singleBonded := singleBonded) (acyclic := acyclic)
        (globalCarrierFuel_adequate input) hshape realizesR realizesS prevEqR validR sameRootR
        prevEqS validS sameRootS obsR
        (ActualReaderPhysicalBranchInverse.topTarget_current input c) obsS
        (ActualReaderPhysicalBranchInverse.topTarget_current input c)
        (actualSlot_incomingEdge input c frame frameComputed slot oObserved)
        (actualSlot_incomingEdge input c frame frameComputed slot oObserved) p)
  have fixCenter := actualStage_selfIso_fixes_center input c frame frameComputed slot
    singleBonded acyclic hcharge oObserved sourceEqR sourceEqS realizesR realizesS hshape unique
  have mappedCenter : (((actualStage_selfIso input c frame frameComputed slot singleBonded acyclic
        oObserved sourceEqR sourceEqS realizesR realizesS hshape).toEquiv
          (positionCutEquiv singleBonded acyclic (globalCarrierFuel_adequate input) realizesR
            (ActualReaderPhysicalBranchInverse.topTarget input c) prevEqR validR sameRootR obsR
            (ActualReaderPhysicalBranchInverse.topTarget_current input c)
            (actualSlot_incomingEdge input c frame frameComputed slot oObserved) p) :
        AcyclicCutBranchAutomorphism.CutBranch input.certified.moleculeGraph c.1 oAtom) :
      input.certified.Atom) = center := by
    have cutPointEq : positionCutEquiv singleBonded acyclic
        (globalCarrierFuel_adequate input) realizesR
        (ActualReaderPhysicalBranchInverse.topTarget input c) prevEqR validR sameRootR obsR
        (ActualReaderPhysicalBranchInverse.topTarget_current input c)
        (actualSlot_incomingEdge input c frame frameComputed slot oObserved) p =
        (⟨center, unique.1⟩ :
          AcyclicCutBranchAutomorphism.CutBranch
            input.certified.moleculeGraph c.1 oAtom) :=
      Subtype.ext cutPointCenter
    calc (((actualStage_selfIso input c frame frameComputed slot singleBonded acyclic
            oObserved sourceEqR sourceEqS realizesR realizesS hshape).toEquiv
              (positionCutEquiv singleBonded acyclic (globalCarrierFuel_adequate input) realizesR
                (ActualReaderPhysicalBranchInverse.topTarget input c) prevEqR validR sameRootR
                obsR (ActualReaderPhysicalBranchInverse.topTarget_current input c)
                (actualSlot_incomingEdge input c frame frameComputed slot oObserved) p) :
          AcyclicCutBranchAutomorphism.CutBranch input.certified.moleculeGraph c.1 oAtom) :
        input.certified.Atom)
        = ((actualStage_selfIso input c frame frameComputed slot singleBonded acyclic oObserved
            sourceEqR sourceEqS realizesR realizesS hshape).toEquiv ⟨center, unique.1⟩ :
          input.certified.Atom) := by
          rw [cutPointEq]
      _ = center := fixCenter
  exact applyEq.symm.trans mappedCenter

/-- **Being the centre is preserved and reflected by the equal-shape correspondence.**  Both
directions follow from the one-way preservation theorem applied to the pair and to the reversed
pair; the reversed shape equality is `hshape.symm`. -/
theorem shapePositionEquiv_center_iff_of_actualStage
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
    {oAtom : input.certified.Atom}
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    {treeR treeS : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input)}
    (sourceEqR : treeR.source = frame.cursorAt slot)
    (sourceEqS : treeS.source = frame.cursorAt slot)
    (realizesR : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) treeR)
    (realizesS : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) treeS)
    (hshape : LocalizedCumulativeDecoratedTree.shape treeR =
      LocalizedCumulativeDecoratedTree.shape treeS)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom center distance)
    (p : Position treeR) :
    positionAtom singleBonded acyclic p = center ↔
      positionAtom singleBonded acyclic (shapePositionEquiv hshape p) = center := by
  constructor
  · intro pCenter
    exact shapePositionEquiv_atom_center_of_center_of_actualStage
      (input := input) (c := c) (frame := frame) (frameComputed := frameComputed) (slot := slot)
      (singleBonded := singleBonded) (acyclic := acyclic) (hcharge := hcharge)
      (oAtom := oAtom) (oObserved := oObserved) (sourceEqR := sourceEqR) (sourceEqS := sourceEqS)
      (realizesR := realizesR) (realizesS := realizesS) (hshape := hshape) (unique := unique)
      (p := p) pCenter
  · intro shapeCenter
    have back := shapePositionEquiv_atom_center_of_center_of_actualStage
      (input := input) (c := c) (frame := frame) (frameComputed := frameComputed) (slot := slot)
      (singleBonded := singleBonded) (acyclic := acyclic) (hcharge := hcharge)
      (oAtom := oAtom) (oObserved := oObserved) (treeR := treeS) (treeS := treeR)
      (sourceEqR := sourceEqS) (sourceEqS := sourceEqR) (realizesR := realizesS)
      (realizesS := realizesR) (hshape := hshape.symm) (unique := unique)
      (p := shapePositionEquiv hshape p) shapeCenter
    have posEq : shapePositionEquiv hshape.symm (shapePositionEquiv hshape p) = p :=
      position_ext (by simp only [shapePositionEquiv_val])
    rwa [posEq] at back

/-! ## F. The centre carries the same raw address in both actual trees -/

/-- **Same centre address.**  Positions of the two actual trees whose physical atom is the unique
nearest centre have the same raw sibling-slot address: the equal-shape image of the left centre
position is a centre position (preservation), and the position injectivity of the right actual
tree identifies it with the right centre position.  The shape equivalence preserves the address
exactly, so both trees observe the centre at the same address. -/
theorem sameCenterAddress_of_actualStage
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
    {oAtom : input.certified.Atom}
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    {treeR treeS : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input)}
    (sourceEqR : treeR.source = frame.cursorAt slot)
    (sourceEqS : treeS.source = frame.cursorAt slot)
    (realizesR : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) treeR)
    (realizesS : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) treeS)
    (hshape : LocalizedCumulativeDecoratedTree.shape treeR =
      LocalizedCumulativeDecoratedTree.shape treeS)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom center distance)
    {pR : Position treeR} {pS : Position treeS}
    (pRAtom : positionAtom singleBonded acyclic pR = center)
    (pSAtom : positionAtom singleBonded acyclic pS = center) :
    pR.val = pS.val := by
  have shapeAtom : positionAtom singleBonded acyclic (shapePositionEquiv hshape pR) = center :=
    shapePositionEquiv_atom_center_of_center_of_actualStage
      (input := input) (c := c) (frame := frame) (frameComputed := frameComputed) (slot := slot)
      (singleBonded := singleBonded) (acyclic := acyclic) (hcharge := hcharge)
      (oAtom := oAtom) (oObserved := oObserved) (sourceEqR := sourceEqR) (sourceEqS := sourceEqS)
      (realizesR := realizesR) (realizesS := realizesS) (hshape := hshape) (unique := unique)
      (p := pR) pRAtom
  have posEq : shapePositionEquiv hshape pR = pS :=
    positionAtom_injective singleBonded acyclic (globalCarrierFuel_adequate input) realizesS
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (LocalizedUniqueNearestRule5Direction.actualTree_previousEq_of_source
        input c frame frameComputed slot sourceEqS)
      (LocalizedUniqueNearestRule5Direction.actualTree_sameRoot_of_source
        input c frame frameComputed slot sourceEqS)
      (LocalizedUniqueNearestRule5Direction.actualTree_oObserved_of_source
        input c frame frameComputed slot sourceEqS oObserved)
      (ActualReaderPhysicalBranchInverse.topTarget_current input c)
      (shapePositionEquiv hshape pR) pS (shapeAtom.trans pSAtom.symm)
  exact (shapePositionEquiv_val hshape pR).trans
    (congrArg Subtype.val posEq)

/-! ## G. Per-tree actual label machinery from the production pipeline -/

/-- Lifting a position of an actual child to the parent tree by prepending the sibling slot. -/
private def liftPosition {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (i : Nat) (bound : i < tree.children.length)
    (p : Position (tree.children[i])) : Position tree :=
  ⟨i :: p.val, by
    rw [subtreeAt?_cons]
    simp [List.getElem?_eq_getElem bound, positionNode_spec p]⟩

/-- The lifted position carries the same decorated node as the original child position. -/
private theorem liftPosition_node {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (i : Nat) (bound : i < tree.children.length)
    (p : Position (tree.children[i])) :
    positionNode (liftPosition i bound p) = positionNode p := by
  have h₁ := positionNode_spec (liftPosition i bound p)
  have h₂ : subtreeAt? tree (i :: p.val) = some (positionNode p) := by
    rw [subtreeAt?_cons]
    simp [List.getElem?_eq_getElem bound, positionNode_spec p]
  exact Option.some.inj (h₁.symm.trans h₂)

/-- Congruence of `flatMap` from pointwise `map` equality. -/
private theorem flatMap_congr {α β : Type*} {f g : α → List β} {l₁ l₂ : List α}
    (h : l₁.map f = l₂.map g) : l₁.flatMap f = l₂.flatMap g := by
  induction l₁ generalizing l₂ with
  | nil =>
      cases l₂ with
      | nil => rfl
      | cons head tail => simp at h
  | cons head tail ih =>
      cases l₂ with
      | nil => simp at h
      | cons head₂ tail₂ =>
          simp only [List.flatMap_cons, List.map_cons] at h ⊢
          have headEq : f head = g head₂ :=
            Option.some.inj (congrArg (α := List (List β))
              (a₁ := f head :: tail.map f) (a₂ := g head₂ :: tail₂.map g) List.head? h)
          have tailEq : tail.map f = tail₂.map g := congrArg List.tail h
          exact congrArg₂ (· ++ ·) headEq (ih tailEq)

/-- A nonempty `getD` sphere forces its depth below the list length. -/
private theorem getD_ne_nil_imp_lt_length {β : Type*} : ∀ (list : List (List β)) (n : Nat),
    list.getD n [] ≠ [] → n < list.length
  | [], n, nonNil => by simp at nonNil
  | _head :: tail, 0, _nonNil => by simp
  | _head :: tail, n + 1, nonNil => by
      have tailNonNil : tail.getD n [] ≠ [] := by
        intro tailNil
        apply nonNil
        simpa using tailNil
      exact Nat.succ_lt_succ (getD_ne_nil_imp_lt_length tail n tailNonNil)

/-- **The actual node label is the actual whole reference state at the position's actual
occurrence.**  The realized tree was built with the actual restricted dependency reader, so its
root was reached strictly outward from the dependency target; the whole-state agreement of the
restricted and unrestricted readers transfers the production state to the tree label.  No reader
law is supplied. -/
theorem position_label_eq_referenceState_of_actualStage
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    {oAtom : input.certified.Atom}
    (_oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    {tree : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input)}
    (sourceEq : tree.source = frame.cursorAt slot)
    (realizes : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) tree)
    (p : Position tree) :
    (positionNode p).label =
      LocalizedUniversalReference.referenceState input (positionSource p).occurrence := by
  have previousEq := LocalizedUniqueNearestRule5Direction.actualTree_previousEq_of_source
    input c frame frameComputed slot sourceEq
  have valid := LocalizedUniqueNearestRule5Direction.actualTree_valid_of_source
    input c frame frameComputed slot sourceEq
  have previousShorter := LocalizedUniqueNearestRule5Direction.actualTree_previousShorter_of_source
    input c frame frameComputed slot sourceEq
  have realizesState : LocalizedCumulativeTreeRealizes input.certified
      (fun cursor => input.certified.localizedDependencyLabel
        (ActualReaderPhysicalBranchInverse.topTarget input c)
        (input.certified.localizedDependencyView
          (LocalizedUniversalReference.referenceState input)
          (ActualReaderPhysicalBranchInverse.topTarget input c)) cursor) tree := by
    simpa only [ActualReaderPhysicalBranchInverse.dependencyReader] using realizes
  exact positionNode_label_eq_state_of_outward (input := input.certified)
    (carrierFuel := LocalizedUniversalReference.carrierFuel input)
    (target := ActualReaderPhysicalBranchInverse.topTarget input c)
    (state := LocalizedUniversalReference.referenceState input)
    (tree := tree) (realizes := realizesState) (valid := valid)
    (previous := ActualReaderPhysicalBranchInverse.topTarget input c)
    (previousEq := previousEq) (previousShorter := previousShorter) (targetEq := rfl) (p := p)

/-- **Sparse actual reader classification at every tree position.**  The whole reference state at
a position's actual occurrence is either `none` or an actual uppercase chiral descriptor.  The
occurrence is a strict depth dependency of the final target by actual child reachability through
the actual frame cursor, so the general-rigid reader classification applies; no eligibility or
twin premise is supplied. -/
theorem position_referenceState_sparse_of_actualStage
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidGlobalPhysicalDomain input.certified cfg ⟨c.1, c.2⟩)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    {oAtom : input.certified.Atom}
    (_oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    {tree : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input)}
    (sourceEq : tree.source = frame.cursorAt slot)
    (realizes : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) tree)
    (p : Position tree) :
    LocalizedUniversalReference.referenceState input (positionSource p).occurrence = none ∨
      ∃ rs : RS,
        LocalizedUniversalReference.referenceState input (positionSource p).occurrence =
          some (.chiral rs) := by
  have reachable : input.certified.ActualChildReachable tree.source (positionSource p) :=
    actualChildReachable_positionSource realizes p
  have reachableStart : input.certified.ActualChildReachable
      (frame.cursorAt slot) (positionSource p) := by
    rw [sourceEq] at reachable
    exact reachable
  have present : frame.cursorAt slot ∈ frame.cursors := by
    unfold LocalizedOccurrenceFourLigandFrame.cursorAt
    exact List.get_mem _ _
  have firstChild : frame.cursorAt slot ∈
      input.certified.executableLocalizedRerootChildren
        ({ occurrence := ActualReaderPhysicalBranchInverse.topTarget input c, previous? := none } :
          input.certified.LocalizedRerootCursor
            (LocalizedUniversalReference.carrierFuel input)) :=
    ActualReaderPhysicalBranchInverse.mem_executableLocalizedRerootChildren_of_frame
      input.certified (ActualReaderPhysicalBranchInverse.topTarget input c) frame frameComputed
      (frame.cursorAt slot) present
  have firstDeeper : (ActualReaderPhysicalBranchInverse.topTarget input c).1.address.length <
      (frame.cursorAt slot).occurrence.1.address.length :=
    ActualReaderPhysicalBranchInverse.frame_cursor_strictlyDeeper_of_target_address_nil
      input.certified (ActualReaderPhysicalBranchInverse.topTarget input c) frame frameComputed
      (ActualReaderPhysicalBranchInverse.topTarget_address input c)
      (frame.cursorAt slot) present
  have facts := outward_reachable_dependency input.certified
    (ActualReaderPhysicalBranchInverse.topTarget input c)
    (frame.cursorAt slot) (positionSource p) firstChild firstDeeper reachableStart
  exact actualStrictDependency_referenceState_none_or_chiral_generalRigid
    (input := input) (singleBonded := singleBonded) (acyclic := acyclic) (hcharge := hcharge)
    (noDouble := noDouble) (cfg := cfg) (root := ⟨c.1, c.2⟩) (domain := domain)
    (topCenter := ⟨c.1, c.2⟩) (topAt := rfl) (cursor := positionSource p) (dependency := facts.1)

/-! ## H. Label sparseness at non-centres and the centre descriptor -/

/-- **A non-centre position inside the nearest sphere reads `none`.**  If the position's physical
atom is not the unique nearest centre and its address has length at most the nearest radius, its
label is `none`.  A chiral label would produce a physical mark, hence an actual simple physical
walk of the address length from the incoming atom; at strictly smaller length that contradicts the
nearest predicate's no-earlier clause, at exactly the nearest radius it contradicts the
uniqueness clause together with non-centredness. -/
theorem label_none_of_noncenter_le_distance_of_actualStage
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
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidGlobalPhysicalDomain input.certified cfg ⟨c.1, c.2⟩)
    {oAtom : input.certified.Atom}
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    {tree : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input)}
    (sourceEq : tree.source = frame.cursorAt slot)
    (realizes : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) tree)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom center distance)
    (p : Position tree) (pLe : p.val.length ≤ distance)
    (notCenter : positionAtom singleBonded acyclic p ≠ center) :
    (positionNode p).label = none := by
  have labelEq := position_label_eq_referenceState_of_actualStage input c frame frameComputed
    slot oObserved sourceEq realizes p
  by_cases nonChiral : LocalizedUniversalReference.referenceState input
      (positionSource p).occurrence = none
  · rw [labelEq, nonChiral]
  · have chiralOr : ∃ rs : RS, LocalizedUniversalReference.referenceState input
        (positionSource p).occurrence = some (.chiral rs) := by
      rcases position_referenceState_sparse_of_actualStage
        (input := input) (singleBonded := singleBonded) (acyclic := acyclic)
        (hcharge := hcharge) (noDouble := noDouble) (cfg := cfg) (domain := domain) (c := c)
        (frame := frame) (frameComputed := frameComputed) (slot := slot) (_oObserved := oObserved)
        (sourceEq := sourceEq) (realizes := realizes) (p := p) with noneEq | someEq
      · exact (nonChiral noneEq).elim
      · exact someEq
    obtain ⟨descriptor, stateEq⟩ := chiralOr
    have labelChiral : (positionNode p).label = some (.chiral descriptor) := by
      rw [labelEq, stateEq]
    have previousEq := LocalizedUniqueNearestRule5Direction.actualTree_previousEq_of_source
      input c frame frameComputed slot sourceEq
    have valid := LocalizedUniqueNearestRule5Direction.actualTree_valid_of_source
      input c frame frameComputed slot sourceEq
    have previousShorter := LocalizedUniqueNearestRule5Direction.actualTree_previousShorter_of_source
      input c frame frameComputed slot sourceEq
    have sameRoot := LocalizedUniqueNearestRule5Direction.actualTree_sameRoot_of_source
      input c frame frameComputed slot sourceEq
    have oObservedTree := LocalizedUniqueNearestRule5Direction.actualTree_oObserved_of_source
      input c frame frameComputed slot sourceEq oObserved
    have incomingEdge := actualSlot_incomingEdge input c frame frameComputed slot oObserved
    have markSome := (LocalizedUniqueNearestRule5Direction.actualTreeMark_reader input c frame
      frameComputed slot singleBonded acyclic realizes previousEq valid previousShorter sameRoot
      oObservedTree incomingEdge p descriptor).mp labelChiral
    have marked :=
      LocalizedUniqueNearestRule5Direction.physicalMarkedAtom_of_actualTreeMark_eq_some
        input c frame frameComputed slot singleBonded acyclic hcharge noDouble cfg domain
        oObserved sourceEq realizes markSome
    have cutMember : positionAtom singleBonded acyclic p ∈
        AcyclicCutBranchAutomorphism.CutBranch input.certified.moleculeGraph c.1 oAtom :=
      positionAtom_mem_cutBranch (input := input.certified)
        (carrierFuel := LocalizedUniversalReference.carrierFuel input)
        (read := ActualReaderPhysicalBranchInverse.dependencyReader input c)
        (singleBonded := singleBonded) (acyclic := acyclic)
        (enough := globalCarrierFuel_adequate input) (tree := tree) (realizes := realizes)
        (previous := ActualReaderPhysicalBranchInverse.topTarget input c)
        (previousEq := previousEq) (valid := valid)
        (oObserved := oObservedTree)
        (pObserved := ActualReaderPhysicalBranchInverse.topTarget_current input c)
        (incomingEdge := incomingEdge) (p := p)
    obtain ⟨walk, walkPath, walkLen⟩ := exists_positionPath
      (input := input.certified) (carrierFuel := LocalizedUniversalReference.carrierFuel input)
      (read := ActualReaderPhysicalBranchInverse.dependencyReader input c)
      (singleBonded := singleBonded) (acyclic := acyclic)
      (enough := globalCarrierFuel_adequate input) (tree := tree) (realizes := realizes)
      (previous := ActualReaderPhysicalBranchInverse.topTarget input c) (previousEq := previousEq)
      (valid := valid) (sameRoot := sameRoot) (oObserved := oObservedTree)
      (pObserved := ActualReaderPhysicalBranchInverse.topTarget_current input c)
      (incomingEdge := incomingEdge) (p := p)
    by_cases eqDistance : p.val.length = distance
    · exact absurd (unique.2.2.2.2 (positionAtom singleBonded acyclic p) cutMember marked walk
        walkPath (by rw [walkLen]; exact eqDistance)) notCenter
    · exact (unique.2.2.2.1 (positionAtom singleBonded acyclic p) cutMember marked walk walkPath
        (by rw [walkLen]; exact Nat.lt_of_le_of_ne pLe eqDistance)).elim

/-- **The centre position reads the nearest descriptor, and the derived mark agrees.**  At a
position whose physical atom is the unique nearest centre, the actual tree label is the upper-case
chiral descriptor certified by the nearest physical predicate, and the tree's derived mark of the
centre is exactly that descriptor. -/
theorem label_mark_of_center_of_actualStage
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
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidGlobalPhysicalDomain input.certified cfg ⟨c.1, c.2⟩)
    {oAtom : input.certified.Atom}
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    {tree : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input)}
    (sourceEq : tree.source = frame.cursorAt slot)
    (realizes : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) tree)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom center distance)
    (p : Position tree)
    (pCenter : positionAtom singleBonded acyclic p = center) :
    ∃ descriptor : RS,
      (positionNode p).label = some (.chiral descriptor) ∧
        LocalizedUniqueNearestRule5Direction.actualTreeMark input singleBonded acyclic tree
          center = some descriptor := by
  obtain ⟨descriptor, _earlier, _uniqueObs, markSome⟩ :=
    LocalizedUniqueNearestRule5Direction.tree_observations_of_physicalBranchUniqueNearest
      input c frame frameComputed slot singleBonded acyclic hcharge noDouble cfg domain
      oObserved sourceEq realizes unique
  have previousEq := LocalizedUniqueNearestRule5Direction.actualTree_previousEq_of_source
    input c frame frameComputed slot sourceEq
  have valid := LocalizedUniqueNearestRule5Direction.actualTree_valid_of_source
    input c frame frameComputed slot sourceEq
  have previousShorter := LocalizedUniqueNearestRule5Direction.actualTree_previousShorter_of_source
    input c frame frameComputed slot sourceEq
  have sameRoot := LocalizedUniqueNearestRule5Direction.actualTree_sameRoot_of_source
    input c frame frameComputed slot sourceEq
  have oObservedTree := LocalizedUniqueNearestRule5Direction.actualTree_oObserved_of_source
    input c frame frameComputed slot sourceEq oObserved
  have incomingEdge := actualSlot_incomingEdge input c frame frameComputed slot oObserved
  have reader := LocalizedUniqueNearestRule5Direction.actualTreeMark_reader input c frame
    frameComputed slot singleBonded acyclic realizes previousEq valid previousShorter sameRoot
    oObservedTree incomingEdge
  have pMark : LocalizedUniqueNearestRule5Direction.actualTreeMark input singleBonded acyclic
      tree (positionAtom singleBonded acyclic p) = some descriptor := by
    rw [pCenter]
    exact markSome
  exact ⟨descriptor, (reader p descriptor).mpr pMark, markSome⟩

/-! ## I. Equal labels at equal addresses through the nearest sphere -/

/-- **Equal labels at equal addresses through the nearest sphere.**  For matching addresses of the
two actual trees, the labels at the two positions are equal whenever the address length is at most
the nearest radius.  At the centre address both labels are the same certified upper-case chiral
descriptor (the fixed centre is preserved by the equal-shape correspondence, and the two derived
marks agree by fixed-root carrier injectivity); at any other address inside the sphere both labels
are `none` (a chiral label would produce a physical walk contradicting nearestness).  Labels below
the sphere are not constrained. -/
theorem position_label_eq_of_actualStage_le_distance
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
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidGlobalPhysicalDomain input.certified cfg ⟨c.1, c.2⟩)
    {oAtom : input.certified.Atom}
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    (own : Option RS)
    {keyR keyS : input.certified.LocalizedRerootCumulativeRule45Key}
    {treeR treeS : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input)}
    (builtR : input.certified.buildLocalizedRerootCumulativeRule45Key?
      (localizedRule5StageFor own .R)
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (2 * (LocalizedUniversalReference.carrierFuel input + 1))
      (frame.cursorAt slot) = some keyR)
    (builtS : input.certified.buildLocalizedRerootCumulativeRule45Key?
      (localizedRule5StageFor own .S)
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (2 * (LocalizedUniversalReference.carrierFuel input + 1))
      (frame.cursorAt slot) = some keyS)
    (tableMatchR : LocalizedCumulativeTreeTableMatch
      (localizedRule5StageFor own .R) treeR keyR)
    (tableMatchS : LocalizedCumulativeTreeTableMatch
      (localizedRule5StageFor own .S) treeS keyS)
    (sourceEqR : treeR.source = frame.cursorAt slot)
    (sourceEqS : treeS.source = frame.cursorAt slot)
    (realizesR : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) treeR)
    (realizesS : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) treeS)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom center distance)
    {pR : Position treeR} {pS : Position treeS}
    (addressEq : pR.val = pS.val)
    (pLe : pR.val.length ≤ distance) :
    (positionNode pR).label = (positionNode pS).label := by
  have hshape := shape_eq_of_actualStage_built input c frame frameComputed slot own
    builtR builtS tableMatchR tableMatchS
  by_cases centerCase : positionAtom singleBonded acyclic pR = center
  · have pSCenter : positionAtom singleBonded acyclic pS = center := by
      have centerIff := shapePositionEquiv_center_iff_of_actualStage
        (input := input) (c := c) (frame := frame) (frameComputed := frameComputed) (slot := slot)
        (singleBonded := singleBonded) (acyclic := acyclic) (hcharge := hcharge)
        (oAtom := oAtom) (oObserved := oObserved) (treeR := treeR) (treeS := treeS)
        (sourceEqR := sourceEqR) (sourceEqS := sourceEqS) (realizesR := realizesR)
        (realizesS := realizesS) (hshape := hshape) (unique := unique) (p := pR)
      have shapePS : shapePositionEquiv hshape pR = pS :=
        position_ext (by rw [shapePositionEquiv_val, addressEq])
      have centerShape := centerIff.mp centerCase
      rwa [shapePS] at centerShape
    obtain ⟨descriptorR, labelR, markR⟩ :=
      label_mark_of_center_of_actualStage
        (input := input) (c := c) (frame := frame) (frameComputed := frameComputed) (slot := slot)
        (singleBonded := singleBonded) (acyclic := acyclic) (hcharge := hcharge)
        (noDouble := noDouble) (cfg := cfg) (domain := domain) (oAtom := oAtom)
        (oObserved := oObserved) (sourceEq := sourceEqR) (realizes := realizesR)
        (unique := unique) (p := pR) (pCenter := centerCase)
    obtain ⟨descriptorS, labelS, markS⟩ :=
      label_mark_of_center_of_actualStage
        (input := input) (c := c) (frame := frame) (frameComputed := frameComputed) (slot := slot)
        (singleBonded := singleBonded) (acyclic := acyclic) (hcharge := hcharge)
        (noDouble := noDouble) (cfg := cfg) (domain := domain) (oAtom := oAtom)
        (oObserved := oObserved) (sourceEq := sourceEqS) (realizes := realizesS)
        (unique := unique) (p := pS) (pCenter := pSCenter)
    have marksEq := LocalizedUniqueNearestRule5Direction.actualTreeMark_eq_of_marks_some
      input c frame frameComputed slot singleBonded acyclic sourceEqR sourceEqS realizesR
      realizesS oObserved (actualSlot_incomingEdge input c frame frameComputed slot oObserved)
      markR markS
    have descriptorEq : descriptorR = descriptorS :=
      Option.some.inj (by simpa [markR, markS] using marksEq)
    subst descriptorS
    exact labelR.trans labelS.symm
  · have pSNotCenter : positionAtom singleBonded acyclic pS ≠ center := by
      intro pSCenter
      apply centerCase
      have centerIff := shapePositionEquiv_center_iff_of_actualStage
        (input := input) (c := c) (frame := frame) (frameComputed := frameComputed) (slot := slot)
        (singleBonded := singleBonded) (acyclic := acyclic) (hcharge := hcharge)
        (oAtom := oAtom) (oObserved := oObserved) (treeR := treeR) (treeS := treeS)
        (sourceEqR := sourceEqR) (sourceEqS := sourceEqS) (realizesR := realizesR)
        (realizesS := realizesS) (hshape := hshape) (unique := unique) (p := pR)
      have shapePS : shapePositionEquiv hshape pR = pS :=
        position_ext (by rw [shapePositionEquiv_val, addressEq])
      rw [shapePS.symm] at pSCenter
      exact centerIff.mpr pSCenter
    have noneR := label_none_of_noncenter_le_distance_of_actualStage
      (input := input) (c := c) (frame := frame) (frameComputed := frameComputed) (slot := slot)
      (singleBonded := singleBonded) (acyclic := acyclic) (hcharge := hcharge)
      (noDouble := noDouble) (cfg := cfg) (domain := domain) (oAtom := oAtom)
      (oObserved := oObserved) (sourceEq := sourceEqR) (realizes := realizesR)
      (unique := unique) (p := pR) (pLe := pLe) (notCenter := centerCase)
    have noneS := label_none_of_noncenter_le_distance_of_actualStage
      (input := input) (c := c) (frame := frame) (frameComputed := frameComputed) (slot := slot)
      (singleBonded := singleBonded) (acyclic := acyclic) (hcharge := hcharge)
      (noDouble := noDouble) (cfg := cfg) (domain := domain) (oAtom := oAtom)
      (oObserved := oObserved) (sourceEq := sourceEqS) (realizes := realizesS)
      (unique := unique) (p := pS) (pLe := by rw [← addressEq]; exact pLe)
      (notCenter := pSNotCenter)
    exact noneR.trans noneS.symm

/-! ## J. Observation-layer equality from equal shape and equal bounded labels -/

/-- **Structural observation equality from equal shape and equal bounded labels.**  This is plain
table algebra over the shared coordinate system: if two decorated trees have the same erased shape
(so children correspond indexwise) and positionwise equal observations at every pair of matching
addresses of length at most `radius`, then every observation sphere at depth at most `radius` is
equal.  No physical premise is used. -/
private theorem observationsAtDepth_eq_aux
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat} {α : Type*}
    {observeL observeR : LocalizedCumulativeDecoratedTree input carrierFuel → α}
    (leftTree rightTree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    ∀ depth,
      LocalizedCumulativeDecoratedTree.shape leftTree =
        LocalizedCumulativeDecoratedTree.shape rightTree →
      (∀ {pL : Position leftTree} {pR : Position rightTree},
        pL.val = pR.val → pL.val.length ≤ depth →
          observeL (positionNode pL) = observeR (positionNode pR)) →
      LocalizedCumulativeDecoratedTree.observationsAtDepth observeL depth leftTree =
        LocalizedCumulativeDecoratedTree.observationsAtDepth observeR depth rightTree := by
  intro depth
  induction depth generalizing leftTree rightTree with
  | zero =>
      intro _hshape labelEq
      rw [LocalizedCumulativeDecoratedTree.observationsAtDepth,
        LocalizedCumulativeDecoratedTree.observationsAtDepth]
      exact congrArg (fun value => [value])
        (by simpa only [positionNode_rootPosition] using
          (labelEq (pL := rootPosition leftTree) (pR := rootPosition rightTree) rfl (by simp)))
  | succ depth ih =>
      intro hshape labelEq
      rw [LocalizedCumulativeDecoratedTree.observationsAtDepth,
        LocalizedCumulativeDecoratedTree.observationsAtDepth]
      have childrenShapeEq : leftTree.children.map LocalizedCumulativeDecoratedTree.shape =
          rightTree.children.map LocalizedCumulativeDecoratedTree.shape := by
        have childrenShapeListEq : LocalizedCumulativeDecoratedTree.shapeList leftTree.children =
            LocalizedCumulativeDecoratedTree.shapeList rightTree.children := by
          cases leftTree with
          | mk sL aL dL mL lL chL =>
              cases rightTree with
              | mk sR aR dR mR lR chR =>
                  have hshape' := hshape
                  rw [LocalizedCumulativeDecoratedTree.table_shape_mk,
                    LocalizedCumulativeDecoratedTree.table_shape_mk] at hshape'
                  exact congrArg (fun (s : LocalizedCumulativeBranchShape) => s.children)
                    hshape'
        simpa only [LocalizedCumulativeDecoratedTree.table_shapeList_eq_map] using
          childrenShapeListEq
      have countEq : leftTree.children.length = rightTree.children.length := by
        simpa using (congrArg (α := List LocalizedCumulativeBranchShape) List.length
          childrenShapeEq)
      have mapEq : leftTree.children.map
          (fun child => LocalizedCumulativeDecoratedTree.observationsAtDepth observeL depth child) =
        rightTree.children.map
          (fun child => LocalizedCumulativeDecoratedTree.observationsAtDepth observeR depth
            child) := by
        apply List.ext_getElem (by simpa using countEq)
        intro i inFirst inSecond
        rw [List.getElem_map, List.getElem_map]
        have leftBound : i < leftTree.children.length := by simpa using inFirst
        have rightBound : i < rightTree.children.length := by simpa using inSecond
        have childShapeEq : LocalizedCumulativeDecoratedTree.shape
            (leftTree.children[i]'leftBound) =
          LocalizedCumulativeDecoratedTree.shape (rightTree.children[i]'rightBound) := by
          have leftGet : (leftTree.children.map LocalizedCumulativeDecoratedTree.shape)[i]? =
              some (LocalizedCumulativeDecoratedTree.shape
                (leftTree.children[i]'leftBound)) := by
            rw [List.getElem?_map]
            simp [List.getElem?_eq_getElem leftBound]
          have rightGet : (rightTree.children.map LocalizedCumulativeDecoratedTree.shape)[i]? =
              some (LocalizedCumulativeDecoratedTree.shape
                (rightTree.children[i]'rightBound)) := by
            rw [List.getElem?_map]
            simp [List.getElem?_eq_getElem rightBound]
          rw [childrenShapeEq] at leftGet
          exact Option.some.inj (leftGet.symm.trans rightGet)
        exact ih (leftTree := leftTree.children[i]'leftBound)
          (rightTree := rightTree.children[i]'rightBound) childShapeEq
          (fun {pL pR} h childLe =>
            by
              simpa only [liftPosition_node] using
                (labelEq (pL := liftPosition i leftBound pL) (pR := liftPosition i rightBound pR)
                  (by change i :: pL.val = i :: pR.val; rw [h])
                  (by
                    change (i :: pL.val).length ≤ depth + 1
                    simp only [List.length_cons]
                    exact Nat.succ_le_succ childLe)))
      exact flatMap_congr mapEq

/-- The bounded-label wrapper: an address of length at most `depth ≤ radius` is one of length at
most `radius`, so the depth-tied recursion transfers the given radius-bounded label equality to
every observation sphere through `radius`. -/
theorem observationsAtDepth_eq_of_shape_eq_of_labelEq_le
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat} {α : Type*}
    {observeL observeR : LocalizedCumulativeDecoratedTree input carrierFuel → α}
    {leftTree rightTree : LocalizedCumulativeDecoratedTree input carrierFuel} {radius : Nat}
    (hshape : LocalizedCumulativeDecoratedTree.shape leftTree =
      LocalizedCumulativeDecoratedTree.shape rightTree)
    (labelEq : ∀ {pL : Position leftTree} {pR : Position rightTree},
      pL.val = pR.val → pL.val.length ≤ radius →
        observeL (positionNode pL) = observeR (positionNode pR)) :
    ∀ depth, depth ≤ radius →
      LocalizedCumulativeDecoratedTree.observationsAtDepth observeL depth leftTree =
        LocalizedCumulativeDecoratedTree.observationsAtDepth observeR depth rightTree := by
  intro depth depthLe
  exact observationsAtDepth_eq_aux (leftTree := leftTree) (rightTree := rightTree) depth hshape
    (fun {pL pR} h childLe => labelEq h (le_trans childLe depthLe))

/-- **Equal label observations through the nearest sphere for the two actual trees.**  The actual
stage trees share their erased shape and their positionwise labels through the sphere, so their
label observation spheres agree at every depth at most the nearest radius.  Deeper spheres are
unrestricted. -/
theorem observationsAtDepth_eq_of_actualStage_le_distance
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
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidGlobalPhysicalDomain input.certified cfg ⟨c.1, c.2⟩)
    {oAtom : input.certified.Atom}
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    (own : Option RS)
    {keyR keyS : input.certified.LocalizedRerootCumulativeRule45Key}
    {treeR treeS : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input)}
    (builtR : input.certified.buildLocalizedRerootCumulativeRule45Key?
      (localizedRule5StageFor own .R)
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (2 * (LocalizedUniversalReference.carrierFuel input + 1))
      (frame.cursorAt slot) = some keyR)
    (builtS : input.certified.buildLocalizedRerootCumulativeRule45Key?
      (localizedRule5StageFor own .S)
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (2 * (LocalizedUniversalReference.carrierFuel input + 1))
      (frame.cursorAt slot) = some keyS)
    (tableMatchR : LocalizedCumulativeTreeTableMatch
      (localizedRule5StageFor own .R) treeR keyR)
    (tableMatchS : LocalizedCumulativeTreeTableMatch
      (localizedRule5StageFor own .S) treeS keyS)
    (sourceEqR : treeR.source = frame.cursorAt slot)
    (sourceEqS : treeS.source = frame.cursorAt slot)
    (realizesR : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) treeR)
    (realizesS : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) treeS)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom center distance) :
    ∀ depth, depth ≤ distance →
      LocalizedCumulativeDecoratedTree.observationsAtDepth (fun node => node.label) depth treeR =
        LocalizedCumulativeDecoratedTree.observationsAtDepth (fun node => node.label) depth treeS := by
  exact observationsAtDepth_eq_of_shape_eq_of_labelEq_le
    (input := input.certified) (carrierFuel := LocalizedUniversalReference.carrierFuel input)
    (observeL := fun node => node.label) (observeR := fun node => node.label)
    (radius := distance)
    (hshape := shape_eq_of_actualStage_built input c frame frameComputed slot own
      builtR builtS tableMatchR tableMatchS)
    (labelEq := fun {pL pR} addressEq lengthLe =>
      position_label_eq_of_actualStage_le_distance
        (input := input) (c := c) (frame := frame) (frameComputed := frameComputed) (slot := slot)
        (singleBonded := singleBonded) (acyclic := acyclic) (hcharge := hcharge)
        (noDouble := noDouble) (cfg := cfg) (domain := domain) (oAtom := oAtom)
        (oObserved := oObserved) (own := own) (builtR := builtR) (builtS := builtS)
        (tableMatchR := tableMatchR) (tableMatchS := tableMatchS) (sourceEqR := sourceEqR)
        (sourceEqS := sourceEqS) (realizesR := realizesR) (realizesS := realizesS)
        (unique := unique) (pR := pL) (pS := pR) (addressEq := addressEq) (pLe := lengthLe))

/-! ## K. Table length, address rows and sphere existence across the two actual trees -/





private theorem addressRows_components_of_actualStage
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    (own : Option RS)
    {keyR keyS : input.certified.LocalizedRerootCumulativeRule45Key}
    {treeR treeS : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input)}
    (builtR : input.certified.buildLocalizedRerootCumulativeRule45Key?
      (localizedRule5StageFor own .R)
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (2 * (LocalizedUniversalReference.carrierFuel input + 1))
      (frame.cursorAt slot) = some keyR)
    (builtS : input.certified.buildLocalizedRerootCumulativeRule45Key?
      (localizedRule5StageFor own .S)
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (2 * (LocalizedUniversalReference.carrierFuel input + 1))
      (frame.cursorAt slot) = some keyS)
    (tableMatchR : LocalizedCumulativeTreeTableMatch
      (localizedRule5StageFor own .R) treeR keyR)
    (tableMatchS : LocalizedCumulativeTreeTableMatch
      (localizedRule5StageFor own .S) treeS keyS) :
    SparseSupportAlignment.SameAddressRows
        (LocalizedCumulativeDecoratedTree.table
          (fun node => localizedCumulativeRule45Priority (localizedRule5StageFor own .R)
            node.label) treeR)
        (LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) treeR) ∧
      SparseSupportAlignment.SameAddressRows
        (LocalizedCumulativeDecoratedTree.table
          (fun node => localizedCumulativeRule45Priority (localizedRule5StageFor own .S)
            node.label) treeS)
        (LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) treeS) ∧
      LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) treeR =
        LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) treeS := by
  have sarR : SparseSupportAlignment.SameAddressRows
      (LocalizedCumulativeDecoratedTree.table
        (fun node => localizedCumulativeRule45Priority (localizedRule5StageFor own .R) node.label)
        treeR)
      (LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) treeR) :=
    LocalizedActualTableAddressOrder.SameAddressRows_table
      (fun node => localizedCumulativeRule45Priority (localizedRule5StageFor own .R) node.label)
      (fun node => node.atomicNumber) treeR
  have sarS : SparseSupportAlignment.SameAddressRows
      (LocalizedCumulativeDecoratedTree.table
        (fun node => localizedCumulativeRule45Priority (localizedRule5StageFor own .S) node.label)
        treeS)
      (LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) treeS) :=
    LocalizedActualTableAddressOrder.SameAddressRows_table
      (fun node => localizedCumulativeRule45Priority (localizedRule5StageFor own .S) node.label)
      (fun node => node.atomicNumber) treeS
  have bridge : LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) treeR =
      LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) treeS := by
    simpa only [LocalizedCumulativeDecoratedTree.tables_rule1a] using
      (rule1a_eq_of_actualStage_built input c frame frameComputed slot own
        builtR builtS tableMatchR tableMatchS)
  exact ⟨sarR, sarS, bridge⟩

/-- **Equal descriptor-table lengths of the two actual stage trees.** -/
theorem table_length_eq_of_actualStage
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    (own : Option RS)
    {keyR keyS : input.certified.LocalizedRerootCumulativeRule45Key}
    {treeR treeS : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input)}
    (builtR : input.certified.buildLocalizedRerootCumulativeRule45Key?
      (localizedRule5StageFor own .R)
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (2 * (LocalizedUniversalReference.carrierFuel input + 1))
      (frame.cursorAt slot) = some keyR)
    (builtS : input.certified.buildLocalizedRerootCumulativeRule45Key?
      (localizedRule5StageFor own .S)
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (2 * (LocalizedUniversalReference.carrierFuel input + 1))
      (frame.cursorAt slot) = some keyS)
    (tableMatchR : LocalizedCumulativeTreeTableMatch
      (localizedRule5StageFor own .R) treeR keyR)
    (tableMatchS : LocalizedCumulativeTreeTableMatch
      (localizedRule5StageFor own .S) treeS keyS) :
    (LocalizedCumulativeDecoratedTree.table
      (fun node => localizedCumulativeRule45Priority (localizedRule5StageFor own .R) node.label)
      treeR).length =
    (LocalizedCumulativeDecoratedTree.table
      (fun node => localizedCumulativeRule45Priority (localizedRule5StageFor own .S) node.label)
      treeS).length := by
  obtain ⟨sarR, sarS, bridge⟩ := addressRows_components_of_actualStage
    input c frame frameComputed slot own builtR builtS tableMatchR tableMatchS
  have bridgeLen : (LocalizedCumulativeDecoratedTree.table
      (fun node => node.atomicNumber) treeR).length =
    (LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) treeS).length :=
    congrArg (α := List (List (OfficialSparseEntry ℕ))) List.length bridge
  exact sarR.lengthEq.trans (bridgeLen.trans sarS.lengthEq.symm)

/-- **Equal address rows at every depth of the two actual descriptor tables.** -/
theorem table_addresses_eq_of_actualStage
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    (own : Option RS)
    {keyR keyS : input.certified.LocalizedRerootCumulativeRule45Key}
    {treeR treeS : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input)}
    (builtR : input.certified.buildLocalizedRerootCumulativeRule45Key?
      (localizedRule5StageFor own .R)
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (2 * (LocalizedUniversalReference.carrierFuel input + 1))
      (frame.cursorAt slot) = some keyR)
    (builtS : input.certified.buildLocalizedRerootCumulativeRule45Key?
      (localizedRule5StageFor own .S)
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (2 * (LocalizedUniversalReference.carrierFuel input + 1))
      (frame.cursorAt slot) = some keyS)
    (tableMatchR : LocalizedCumulativeTreeTableMatch
      (localizedRule5StageFor own .R) treeR keyR)
    (tableMatchS : LocalizedCumulativeTreeTableMatch
      (localizedRule5StageFor own .S) treeS keyS) :
    ∀ depth,
      ((LocalizedCumulativeDecoratedTree.table
        (fun node => localizedCumulativeRule45Priority (localizedRule5StageFor own .R) node.label)
        treeR).getD depth []).map Prod.fst =
      ((LocalizedCumulativeDecoratedTree.table
        (fun node => localizedCumulativeRule45Priority (localizedRule5StageFor own .S) node.label)
        treeS).getD depth []).map Prod.fst := by
  obtain ⟨sarR, sarS, bridge⟩ := addressRows_components_of_actualStage
    input c frame frameComputed slot own builtR builtS tableMatchR tableMatchS
  intro depth
  have middle : ((LocalizedCumulativeDecoratedTree.table
      (fun node => node.atomicNumber) treeR).getD depth []).map Prod.fst =
    ((LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber)
      treeS).getD depth []).map Prod.fst := by
    rw [bridge]
  exact (sarR.rows depth).trans (middle.trans (sarS.rows depth).symm)

/-- **The nearest sphere exists in the actual R-stage table.**  The R-tree's observations at the
nearest radius are the singleton nearest descriptor (a nonempty sphere), and the descriptor column
of the R-stage table maps that sphere onto the priority image; hence the sphere is below the table
length. -/
theorem depthLt_of_actualStage
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
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidGlobalPhysicalDomain input.certified cfg ⟨c.1, c.2⟩)
    {oAtom : input.certified.Atom}
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    (own : Option RS)
    {tree : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input)}
    (sourceEq : tree.source = frame.cursorAt slot)
    (realizes : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) tree)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom center distance) :
    distance < (LocalizedCumulativeDecoratedTree.table
      (fun node => localizedCumulativeRule45Priority (localizedRule5StageFor own .R) node.label)
      tree).length := by
  obtain ⟨descriptor, _earlier, uniqueObs, _mark⟩ :=
    LocalizedUniqueNearestRule5Direction.tree_observations_of_physicalBranchUniqueNearest
      input c frame frameComputed slot singleBonded acyclic hcharge noDouble cfg domain
      oObserved sourceEq realizes unique
  have obsNonNil : LocalizedCumulativeDecoratedTree.observationsAtDepth
      (fun node => node.label) distance tree ≠ [] := by
    intro obsNil
    have uniqueObsNil : LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
        [] = [descriptor] := by
      simpa only [obsNil] using uniqueObs
    have impossible : [descriptor] = [] :=
      uniqueObsNil.symm.trans (by rfl)
    cases impossible
  have getDNonNil : (LocalizedCumulativeDecoratedTree.table
      (fun node => localizedCumulativeRule45Priority (localizedRule5StageFor own .R) node.label)
      tree).getD distance [] ≠ [] := by
    intro getDNil
    have mappedNil : (LocalizedCumulativeDecoratedTree.observationsAtDepth
        (fun node => node.label) distance tree).map
        (localizedCumulativeRule45Priority (localizedRule5StageFor own .R)) = [] := by
      rw [← LocalizedUniqueNearestRule5Direction.descriptorTable_getD_map_snd
        (localizedRule5StageFor own .R) tree distance]
      simp only [getDNil, List.map_nil]
    apply obsNonNil
    cases h : LocalizedCumulativeDecoratedTree.observationsAtDepth
        (fun node => node.label) distance tree with
    | nil => rfl
    | cons head tail =>
        have bad : localizedCumulativeRule45Priority (localizedRule5StageFor own .R) head ::
            tail.map (localizedCumulativeRule45Priority (localizedRule5StageFor own .R)) = [] := by
          simpa only [h, List.map_cons] using mappedNil
        cases bad
  exact getD_ne_nil_imp_lt_length
    (LocalizedCumulativeDecoratedTree.table
      (fun node => localizedCumulativeRule45Priority (localizedRule5StageFor own .R) node.label)
      tree) distance getDNonNil

/-! ## L. The complete actual shared-prefix bundle at the physically unique nearest centre -/














theorem actualStage_sharedThroughNearest_of_physicalBranchUniqueNearest
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
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidGlobalPhysicalDomain input.certified cfg ⟨c.1, c.2⟩)
    {oAtom : input.certified.Atom}
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    (own : Option RS)
    {keyR keyS : input.certified.LocalizedRerootCumulativeRule45Key}
    {treeR treeS : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input)}
    (builtR : input.certified.buildLocalizedRerootCumulativeRule45Key?
      (localizedRule5StageFor own .R)
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (2 * (LocalizedUniversalReference.carrierFuel input + 1))
      (frame.cursorAt slot) = some keyR)
    (builtS : input.certified.buildLocalizedRerootCumulativeRule45Key?
      (localizedRule5StageFor own .S)
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (2 * (LocalizedUniversalReference.carrierFuel input + 1))
      (frame.cursorAt slot) = some keyS)
    (tableMatchR : LocalizedCumulativeTreeTableMatch
      (localizedRule5StageFor own .R) treeR keyR)
    (tableMatchS : LocalizedCumulativeTreeTableMatch
      (localizedRule5StageFor own .S) treeS keyS)
    (sourceEqR : treeR.source = frame.cursorAt slot)
    (sourceEqS : treeS.source = frame.cursorAt slot)
    (realizesR : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) treeR)
    (realizesS : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) treeS)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom center distance) :
    ∃ descriptor : RS,
      (∀ earlier < distance,
        LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
          (LocalizedCumulativeDecoratedTree.observationsAtDepth
            (fun node => node.label) earlier treeR) = []) ∧
      LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
        (LocalizedCumulativeDecoratedTree.observationsAtDepth
          (fun node => node.label) distance treeR) = [descriptor] ∧
      LocalizedUniqueNearestRule5Direction.actualTreeMark input singleBonded acyclic treeR
        center = some descriptor ∧
      LocalizedUniqueNearestRule5Direction.actualTreeMark input singleBonded acyclic treeS
        center = some descriptor ∧
      (LocalizedCumulativeDecoratedTree.table
        (fun node => localizedCumulativeRule45Priority (localizedRule5StageFor own .R) node.label)
        treeR).length =
      (LocalizedCumulativeDecoratedTree.table
        (fun node => localizedCumulativeRule45Priority (localizedRule5StageFor own .S) node.label)
        treeS).length ∧
      distance < (LocalizedCumulativeDecoratedTree.table
        (fun node => localizedCumulativeRule45Priority (localizedRule5StageFor own .R) node.label)
        treeR).length ∧
      (∀ depth, depth ≤ distance →
        ((LocalizedCumulativeDecoratedTree.table
          (fun node => localizedCumulativeRule45Priority (localizedRule5StageFor own .R) node.label)
          treeR).getD depth []).map Prod.fst =
        ((LocalizedCumulativeDecoratedTree.table
          (fun node => localizedCumulativeRule45Priority (localizedRule5StageFor own .S) node.label)
          treeS).getD depth []).map Prod.fst) ∧
      (∀ depth, depth ≤ distance →
        LocalizedCumulativeDecoratedTree.observationsAtDepth (fun node => node.label) depth treeR =
          LocalizedCumulativeDecoratedTree.observationsAtDepth (fun node => node.label) depth
            treeS) := by
  obtain ⟨descriptor, earlier, uniqueObs, markR⟩ :=
    LocalizedUniqueNearestRule5Direction.tree_observations_of_physicalBranchUniqueNearest
      input c frame frameComputed slot singleBonded acyclic hcharge noDouble cfg domain
      oObserved sourceEqR realizesR unique
  obtain ⟨descriptorS, _earlierS, _uniqueObsS, markS⟩ :=
    LocalizedUniqueNearestRule5Direction.tree_observations_of_physicalBranchUniqueNearest
      input c frame frameComputed slot singleBonded acyclic hcharge noDouble cfg domain
      oObserved sourceEqS realizesS unique
  have marksEq := LocalizedUniqueNearestRule5Direction.actualTreeMark_eq_of_marks_some
    input c frame frameComputed slot singleBonded acyclic sourceEqR sourceEqS realizesR
    realizesS oObserved (actualSlot_incomingEdge input c frame frameComputed slot oObserved)
    markR markS
  have descriptorEq : descriptor = descriptorS :=
    Option.some.inj (by simpa [markR, markS] using marksEq)
  subst descriptorS
  refine ⟨descriptor, earlier, uniqueObs, markR, markS, ?_, ?_, ?_, ?_⟩
  · exact table_length_eq_of_actualStage input c frame frameComputed slot own
      builtR builtS tableMatchR tableMatchS
  · exact depthLt_of_actualStage
      (input := input) (c := c) (frame := frame) (frameComputed := frameComputed) (slot := slot)
      (singleBonded := singleBonded) (acyclic := acyclic) (hcharge := hcharge)
      (noDouble := noDouble) (cfg := cfg) (domain := domain) (oAtom := oAtom)
      (oObserved := oObserved) (own := own) (sourceEq := sourceEqR) (realizes := realizesR)
      (unique := unique)
  · intro depth _
    exact table_addresses_eq_of_actualStage input c frame frameComputed slot own
      builtR builtS tableMatchR tableMatchS depth
  · exact observationsAtDepth_eq_of_actualStage_le_distance
      (input := input) (c := c) (frame := frame) (frameComputed := frameComputed) (slot := slot)
      (singleBonded := singleBonded) (acyclic := acyclic) (hcharge := hcharge)
      (noDouble := noDouble) (cfg := cfg) (domain := domain) (oAtom := oAtom)
      (oObserved := oObserved) (own := own) (builtR := builtR) (builtS := builtS)
      (tableMatchR := tableMatchR) (tableMatchS := tableMatchS) (sourceEqR := sourceEqR)
      (sourceEqS := sourceEqS) (realizesR := realizesR) (realizesS := realizesS)
      (unique := unique)

/-- **The production wrapper.**  From the pure physical nearest predicate at one actual frame
slot, there exist the two actual production stage builds, their matched realized trees, and the
full shared-prefix bundle: certified no-earlier and singleton-nearest observations, equal centre
marks on both trees, equal table lengths, a real nearest sphere, equal address rows, and equal
label observations through the nearest radius.  Every key, tree, match, realization and label fact
is produced by the actual pipeline; nothing is assumed. -/
theorem exists_actualStage_sharedThroughNearest_of_physicalBranchUniqueNearest
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
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidGlobalPhysicalDomain input.certified cfg ⟨c.1, c.2⟩)
    {oAtom : input.certified.Atom}
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    (own : Option RS)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom center distance) :
    ∃ descriptor : RS,
      ∃ (keyR keyS : input.certified.LocalizedRerootCumulativeRule45Key)
        (treeR treeS : LocalizedCumulativeDecoratedTree input.certified
          (LocalizedUniversalReference.carrierFuel input)),
        input.certified.buildLocalizedRerootCumulativeRule45Key?
            (localizedRule5StageFor own .R)
            (ActualReaderPhysicalBranchInverse.topTarget input c)
            (referenceDependencyView input c)
            (2 * (LocalizedUniversalReference.carrierFuel input + 1))
            (frame.cursorAt slot) = some keyR ∧
        input.certified.buildLocalizedRerootCumulativeRule45Key?
            (localizedRule5StageFor own .S)
            (ActualReaderPhysicalBranchInverse.topTarget input c)
            (referenceDependencyView input c)
            (2 * (LocalizedUniversalReference.carrierFuel input + 1))
            (frame.cursorAt slot) = some keyS ∧
        LocalizedCumulativeTreeTableMatch (localizedRule5StageFor own .R) treeR keyR ∧
        LocalizedCumulativeTreeTableMatch (localizedRule5StageFor own .S) treeS keyS ∧
        treeR.source = frame.cursorAt slot ∧
        treeS.source = frame.cursorAt slot ∧
        LocalizedCumulativeTreeRealizes input.certified
          (ActualReaderPhysicalBranchInverse.dependencyReader input c) treeR ∧
        LocalizedCumulativeTreeRealizes input.certified
          (ActualReaderPhysicalBranchInverse.dependencyReader input c) treeS ∧
        (∀ earlier < distance,
          LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
            (LocalizedCumulativeDecoratedTree.observationsAtDepth
              (fun node => node.label) earlier treeR) = []) ∧
        LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
          (LocalizedCumulativeDecoratedTree.observationsAtDepth
            (fun node => node.label) distance treeR) = [descriptor] ∧
        LocalizedUniqueNearestRule5Direction.actualTreeMark input singleBonded acyclic treeR
          center = some descriptor ∧
        LocalizedUniqueNearestRule5Direction.actualTreeMark input singleBonded acyclic treeS
          center = some descriptor ∧
        (LocalizedCumulativeDecoratedTree.table
          (fun node => localizedCumulativeRule45Priority (localizedRule5StageFor own .R)
            node.label) treeR).length =
        (LocalizedCumulativeDecoratedTree.table
          (fun node => localizedCumulativeRule45Priority (localizedRule5StageFor own .S)
            node.label) treeS).length ∧
        distance < (LocalizedCumulativeDecoratedTree.table
          (fun node => localizedCumulativeRule45Priority (localizedRule5StageFor own .R)
            node.label) treeR).length ∧
        (∀ depth, depth ≤ distance →
          ((LocalizedCumulativeDecoratedTree.table
            (fun node => localizedCumulativeRule45Priority (localizedRule5StageFor own .R)
              node.label) treeR).getD depth []).map Prod.fst =
          ((LocalizedCumulativeDecoratedTree.table
            (fun node => localizedCumulativeRule45Priority (localizedRule5StageFor own .S)
              node.label) treeS).getD depth []).map Prod.fst) ∧
        (∀ depth, depth ≤ distance →
          LocalizedCumulativeDecoratedTree.observationsAtDepth
            (fun node => node.label) depth treeR =
          LocalizedCumulativeDecoratedTree.observationsAtDepth
            (fun node => node.label) depth treeS) := by
  obtain ⟨keyR, keyS, treeR, treeS, builtR, builtS, sourceEqR, sourceEqS, tableMatchR,
      tableMatchS, realizesR, realizesS⟩ :=
    LocalizedUniqueNearestRule5Direction.exists_actualSlot_stageFor_builds_and_trees
      input c frame frameComputed slot own
  obtain ⟨descriptor, earlier, uniqueObs, markR, markS, lengthEq, depthLt, addresses,
      observations⟩ :=
    actualStage_sharedThroughNearest_of_physicalBranchUniqueNearest
      (input := input) (c := c) (frame := frame) (frameComputed := frameComputed) (slot := slot)
      (singleBonded := singleBonded) (acyclic := acyclic) (hcharge := hcharge)
      (noDouble := noDouble) (cfg := cfg) (domain := domain) (oAtom := oAtom)
      (oObserved := oObserved) (own := own) (builtR := builtR) (builtS := builtS)
      (tableMatchR := tableMatchR) (tableMatchS := tableMatchS) (sourceEqR := sourceEqR)
      (sourceEqS := sourceEqS) (realizesR := realizesR) (realizesS := realizesS)
      (unique := unique)
  exact ⟨descriptor, keyR, keyS, treeR, treeS, builtR, builtS, tableMatchR, tableMatchS,
    sourceEqR, sourceEqS, realizesR, realizesS, earlier, uniqueObs, markR, markS, lengthEq,
    depthLt, addresses, observations⟩

/-! ## M. The direct actual-key label prefix for the signed consumer -/

/-- Row equality of addressed sparse tables from equality of the address and value projections.
This is plain list algebra over `OfficialSparseEntry` pairs; no alignment or physical premise is
used. -/
private theorem rows_eq_of_fst_snd_eq {α : Type*} : ∀ (left right : List (List ℕ × α)),
    left.map Prod.fst = right.map Prod.fst →
    left.map Prod.snd = right.map Prod.snd → left = right
  | [], [], _fstEq, _sndEq => rfl
  | [], _head :: _tail, fstEq, _sndEq => by simp at fstEq
  | _head :: _tail, [], fstEq, _sndEq => by simp at fstEq
  | head :: tail, head₂ :: tail₂, fstEq, sndEq => by
      have headFst : head.1 = head₂.1 :=
        Option.some.inj (congrArg (α := List (List ℕ))
          (a₁ := head.1 :: tail.map Prod.fst) (a₂ := head₂.1 :: tail₂.map Prod.fst)
          List.head? fstEq)
      have headSnd : head.2 = head₂.2 :=
        Option.some.inj (congrArg (α := List α)
          (a₁ := head.2 :: tail.map Prod.snd) (a₂ := head₂.2 :: tail₂.map Prod.snd)
          List.head? sndEq)
      have tailFst : tail.map Prod.fst = tail₂.map Prod.fst := congrArg List.tail fstEq
      have tailSnd : tail.map Prod.snd = tail₂.map Prod.snd := congrArg List.tail sndEq
      rw [Prod.ext headFst headSnd]
      exact congrArg (fun t => head₂ :: t) (rows_eq_of_fst_snd_eq tail tail₂ tailFst tailSnd)












theorem actualKey_labels_prefix_of_physicalBranchUniqueNearest
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
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (domain : ActualGeneralRigidGlobalPhysicalDomain input.certified cfg ⟨c.1, c.2⟩)
    {oAtom : input.certified.Atom}
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    (own : Option RS)
    {keyR keyS : input.certified.LocalizedRerootCumulativeRule45Key}
    (builtR : input.certified.buildLocalizedRerootCumulativeRule45Key?
      (localizedRule5StageFor own .R)
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (2 * (LocalizedUniversalReference.carrierFuel input + 1))
      (frame.cursorAt slot) = some keyR)
    (builtS : input.certified.buildLocalizedRerootCumulativeRule45Key?
      (localizedRule5StageFor own .S)
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (2 * (LocalizedUniversalReference.carrierFuel input + 1))
      (frame.cursorAt slot) = some keyS)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom center distance) :
    keyR.labels.length = keyS.labels.length ∧
      ∀ depth, depth ≤ distance → keyR.labels.getD depth [] = keyS.labels.getD depth [] := by
  obtain ⟨treeR, sourceEqR, tableMatchR, labelTableEqR, realizesR'⟩ :=
    exists_decoratedTree_of_buildLocalizedRerootCumulativeRule45Key?
      input.certified (localizedRule5StageFor own .R)
      (ActualReaderPhysicalBranchInverse.topTarget input c) (referenceDependencyView input c)
      (2 * (LocalizedUniversalReference.carrierFuel input + 1)) (frame.cursorAt slot) keyR builtR
  obtain ⟨treeS, sourceEqS, tableMatchS, labelTableEqS, realizesS'⟩ :=
    exists_decoratedTree_of_buildLocalizedRerootCumulativeRule45Key?
      input.certified (localizedRule5StageFor own .S)
      (ActualReaderPhysicalBranchInverse.topTarget input c) (referenceDependencyView input c)
      (2 * (LocalizedUniversalReference.carrierFuel input + 1)) (frame.cursorAt slot) keyS builtS
  have realizesR : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) treeR :=
    realizesR'
  have realizesS : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) treeS :=
    realizesS'
  obtain ⟨_descriptor, _earlier, _uniqueObs, _markR, _markS, lengthEq, _depthLt, _addresses,
      observations⟩ :=
    actualStage_sharedThroughNearest_of_physicalBranchUniqueNearest
      (input := input) (c := c) (frame := frame) (frameComputed := frameComputed) (slot := slot)
      (singleBonded := singleBonded) (acyclic := acyclic) (hcharge := hcharge)
      (noDouble := noDouble) (cfg := cfg) (domain := domain) (oAtom := oAtom)
      (oObserved := oObserved) (own := own) (keyR := keyR) (keyS := keyS) (treeR := treeR)
      (treeS := treeS) (builtR := builtR) (builtS := builtS) (tableMatchR := tableMatchR)
      (tableMatchS := tableMatchS) (sourceEqR := sourceEqR) (sourceEqS := sourceEqS)
      (realizesR := realizesR) (realizesS := realizesS) (center := center)
      (distance := distance) (unique := unique)
  have rule1aEq : LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) treeR =
      LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) treeS := by
    simpa only [LocalizedCumulativeDecoratedTree.tables_rule1a] using
      (rule1a_eq_of_actualStage_built input c frame frameComputed slot own builtR builtS
        tableMatchR tableMatchS)
  have labelTableLenEq :
      (LocalizedCumulativeDecoratedTree.table (fun node => node.label) treeR).length =
        (LocalizedCumulativeDecoratedTree.table (fun node => node.label) treeS).length := by
    simpa only [LocalizedCumulativeDecoratedTree.table_length_eq_height] using lengthEq
  have labelRowsEq : ∀ depth, depth ≤ distance →
      (LocalizedCumulativeDecoratedTree.table (fun node => node.label) treeR).getD depth [] =
        (LocalizedCumulativeDecoratedTree.table (fun node => node.label) treeS).getD depth [] := by
    intro depth depthLe
    have fstEq :
        ((LocalizedCumulativeDecoratedTree.table (fun node => node.label) treeR).getD
          depth []).map Prod.fst =
        ((LocalizedCumulativeDecoratedTree.table (fun node => node.label) treeS).getD
          depth []).map Prod.fst := by
      have middle :
          ((LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) treeR).getD
            depth []).map Prod.fst =
          ((LocalizedCumulativeDecoratedTree.table (fun node => node.atomicNumber) treeS).getD
            depth []).map Prod.fst := by
        rw [rule1aEq]
      exact ((LocalizedActualTableAddressOrder.SameAddressRows_table
          (fun node => node.label) (fun node => node.atomicNumber) treeR).rows depth).trans
        (middle.trans ((LocalizedActualTableAddressOrder.SameAddressRows_table
          (fun node => node.label) (fun node => node.atomicNumber) treeS).rows depth).symm)
    have sndEq :
        ((LocalizedCumulativeDecoratedTree.table (fun node => node.label) treeR).getD
          depth []).map Prod.snd =
        ((LocalizedCumulativeDecoratedTree.table (fun node => node.label) treeS).getD
          depth []).map Prod.snd := by
      rw [LocalizedCumulativeDecoratedTree.table_getD_map_snd,
        LocalizedCumulativeDecoratedTree.table_getD_map_snd]
      exact observations depth depthLe
    exact rows_eq_of_fst_snd_eq
      ((LocalizedCumulativeDecoratedTree.table (fun node => node.label) treeR).getD depth [])
      ((LocalizedCumulativeDecoratedTree.table (fun node => node.label) treeS).getD depth [])
      fstEq sndEq
  constructor
  · have keyLenR : keyR.labels.length =
        (LocalizedCumulativeDecoratedTree.table (fun node => node.label) treeR).length := by
      rw [← labelTableEqR, LocalizedCumulativeDecoratedTree.labelTable_eq_table]
    have keyLenS : keyS.labels.length =
        (LocalizedCumulativeDecoratedTree.table (fun node => node.label) treeS).length := by
      rw [← labelTableEqS, LocalizedCumulativeDecoratedTree.labelTable_eq_table]
    exact keyLenR.trans (labelTableLenEq.trans keyLenS.symm)
  · intro depth depthLe
    have rowR : keyR.labels.getD depth [] =
        (LocalizedCumulativeDecoratedTree.table (fun node => node.label) treeR).getD depth [] := by
      rw [← labelTableEqR, LocalizedCumulativeDecoratedTree.labelTable_eq_table]
    have rowS : keyS.labels.getD depth [] =
        (LocalizedCumulativeDecoratedTree.table (fun node => node.label) treeS).getD depth [] := by
      rw [← labelTableEqS, LocalizedCumulativeDecoratedTree.labelTable_eq_table]
    exact rowR.trans ((labelRowsEq depth depthLe).trans rowS.symm)

end LocalizedActualNearestStagePrefixCovariance

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.LocalizedActualNearestStagePrefixCovariance.withReadBuild_eq_of_actualStage_built
assert_kernel_only TetraStereo.OneCenter.LocalizedActualNearestStagePrefixCovariance.sameCursor_constitutionalObservable_eq_of_actualStage_built
assert_kernel_only TetraStereo.OneCenter.LocalizedActualNearestStagePrefixCovariance.rule1a_eq_of_actualStage_built
assert_kernel_only TetraStereo.OneCenter.LocalizedActualNearestStagePrefixCovariance.rule1b_eq_of_actualStage_built
assert_kernel_only TetraStereo.OneCenter.LocalizedActualNearestStagePrefixCovariance.rule2_eq_of_actualStage_built
assert_kernel_only TetraStereo.OneCenter.LocalizedActualNearestStagePrefixCovariance.shape_eq_of_actualStage_built
assert_kernel_only TetraStereo.OneCenter.LocalizedActualNearestStagePrefixCovariance.actualStage_selfIso
assert_kernel_only TetraStereo.OneCenter.LocalizedActualNearestStagePrefixCovariance.actualStage_selfIso_fixes_center
assert_kernel_only TetraStereo.OneCenter.LocalizedActualNearestStagePrefixCovariance.shapePositionEquiv_atom_center_of_center_of_actualStage
assert_kernel_only TetraStereo.OneCenter.LocalizedActualNearestStagePrefixCovariance.shapePositionEquiv_center_iff_of_actualStage
assert_kernel_only TetraStereo.OneCenter.LocalizedActualNearestStagePrefixCovariance.sameCenterAddress_of_actualStage
assert_kernel_only TetraStereo.OneCenter.LocalizedActualNearestStagePrefixCovariance.position_label_eq_referenceState_of_actualStage
assert_kernel_only TetraStereo.OneCenter.LocalizedActualNearestStagePrefixCovariance.position_referenceState_sparse_of_actualStage
assert_kernel_only TetraStereo.OneCenter.LocalizedActualNearestStagePrefixCovariance.label_none_of_noncenter_le_distance_of_actualStage
assert_kernel_only TetraStereo.OneCenter.LocalizedActualNearestStagePrefixCovariance.label_mark_of_center_of_actualStage
assert_kernel_only TetraStereo.OneCenter.LocalizedActualNearestStagePrefixCovariance.position_label_eq_of_actualStage_le_distance
assert_kernel_only TetraStereo.OneCenter.LocalizedActualNearestStagePrefixCovariance.observationsAtDepth_eq_of_shape_eq_of_labelEq_le
assert_kernel_only TetraStereo.OneCenter.LocalizedActualNearestStagePrefixCovariance.observationsAtDepth_eq_of_actualStage_le_distance
assert_kernel_only TetraStereo.OneCenter.LocalizedActualNearestStagePrefixCovariance.table_length_eq_of_actualStage
assert_kernel_only TetraStereo.OneCenter.LocalizedActualNearestStagePrefixCovariance.table_addresses_eq_of_actualStage
assert_kernel_only TetraStereo.OneCenter.LocalizedActualNearestStagePrefixCovariance.depthLt_of_actualStage
assert_kernel_only TetraStereo.OneCenter.LocalizedActualNearestStagePrefixCovariance.actualStage_sharedThroughNearest_of_physicalBranchUniqueNearest
assert_kernel_only TetraStereo.OneCenter.LocalizedActualNearestStagePrefixCovariance.exists_actualStage_sharedThroughNearest_of_physicalBranchUniqueNearest
assert_kernel_only TetraStereo.OneCenter.LocalizedActualNearestStagePrefixCovariance.actualKey_labels_prefix_of_physicalBranchUniqueNearest
