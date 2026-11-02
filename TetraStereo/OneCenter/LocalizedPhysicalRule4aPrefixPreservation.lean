import TetraStereo.OneCenter.LocalizedPhysicalStageExtensionClosure
import TetraStereo.OneCenter.LocalizedActualSiblingPhysicalKind
import TetraStereo.OneCenter.LocalizedActualNearestStagePrefixCovariance
import TetraStereo.OneCenter.LocalizedRealizedTreeCutIsomorphism
import TetraStereo.OneCenter.LocalizedRerootFuelCompleteness
import TetraStereo.OneCenter.LocalizedCumulativeConstitutionalCoherence
import TetraStereo.OneCenter.LocalizedActualMolecularEvidenceRefinement
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput
open LocalizedCumulativeDecoratedTree






































/-! ## Addressed-table projection algebra

The algebra below is independent of stages, labels, readers and physical data: it is the exact
commutation of the addressed sparse-table recursion with a fixed payload projection. -/

/-- Apply a function to the payload of an addressed sparse entry, keeping the raw sibling-slot
address untouched. -/
private def sparseEntryMap {α β : Type*} (project : α → β)
    (entry : OfficialSparseEntry α) : OfficialSparseEntry β :=
  (entry.1, project entry.2)

/-- The payload map on a pair-form entry. -/
private theorem sparseEntryMap_mk {α β : Type*} (project : α → β)
    (address : List Nat) (value : α) :
    sparseEntryMap project (address, value) = (address, project value) := rfl

/-- Prefixing a raw sibling slot commutes with the entry payload map. -/
private theorem prefixLayer_sparseEntryMap {α β : Type*} (project : α → β)
    (slot : Nat) (layer : List (OfficialSparseEntry α)) :
    (OfficialRuleMajorKey.prefixLayer slot layer).map (sparseEntryMap project) =
      OfficialRuleMajorKey.prefixLayer slot (layer.map (sparseEntryMap project)) := by
  induction layer with
  | nil => rfl
  | cons entry rest inductionHypothesis =>
      simp only [OfficialRuleMajorKey.prefixLayer, List.map_cons, sparseEntryMap] at inductionHypothesis ⊢
      rw [inductionHypothesis]

/-- A slot-indexed merge commutes with the entry payload map: the projected merge is the merge of
the projected blocks, at every raw address. -/
private theorem mergePairs_sparseEntryMap {α β γ : Type*} (project : α → β)
    (pairs : List (γ × Nat)) (block : γ → List (OfficialSparseEntry α)) :
    (SparseAddress.mergePairs pairs block).map (sparseEntryMap project) =
      SparseAddress.mergePairs pairs
        (fun value => (block value).map (sparseEntryMap project)) := by
  induction pairs with
  | nil => rfl
  | cons pair rest inductionHypothesis =>
      show (OfficialRuleMajorKey.prefixLayer pair.2 (block pair.1) ++
          SparseAddress.mergePairs rest block).map (sparseEntryMap project) =
        OfficialRuleMajorKey.prefixLayer pair.2 ((block pair.1).map (sparseEntryMap project)) ++
          SparseAddress.mergePairs rest (fun value => (block value).map (sparseEntryMap project))
      rw [List.map_append, prefixLayer_sparseEntryMap, inductionHypothesis]

/-- Reading one sphere out of a projected layer list is the projection of the sphere read out of
the original list. -/
private theorem getD_map_sparseEntryMap {α β : Type*} (project : α → β)
    (layers : List (List (OfficialSparseEntry α))) (depth : Nat) :
    ((layers.map (List.map (sparseEntryMap project))).getD depth []) =
      (layers.getD depth []).map (sparseEntryMap project) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases layers[depth]? with
  | none => rfl
  | some layer => rfl

/-- The row count of a layer list is unchanged by the entry payload map. -/
private theorem localizedTreeChildLayerCount_sparseEntryMap {α β : Type*} (project : α → β)
    (tables : List (List (List (OfficialSparseEntry α)))) :
    localizedTreeChildLayerCount (tables.map (List.map (List.map (sparseEntryMap project)))) =
      localizedTreeChildLayerCount tables := by
  simp only [localizedTreeChildLayerCount, List.foldl_map, List.length_map]

/-- The addressed child merge commutes with the entry payload map, preserving the sphere count and
every raw address. -/
private theorem mergeLocalizedTreeChildTables_sparseEntryMap {α β : Type*} (project : α → β)
    (tables : List (List (List (OfficialSparseEntry α)))) :
    (mergeLocalizedTreeChildTables tables).map (List.map (sparseEntryMap project)) =
      mergeLocalizedTreeChildTables (tables.map (List.map (List.map (sparseEntryMap project)))) := by
  unfold mergeLocalizedTreeChildTables
  rw [mergePairTable_zipIdx_map_gen]
  rw [localizedTreeChildLayerCount_sparseEntryMap]
  simp only [SparseAddress.mergePairTable, List.map_map]
  apply List.map_congr_left
  intro depth _
  rw [Function.comp_apply, mergePairs_sparseEntryMap]
  congr 1
  funext value
  exact (getD_map_sparseEntryMap project value depth).symm

/-- **Whole addressed-table projection from pointwise agreement.**  If two decorated trees have the
same erased shape and the projected right observation at every raw sibling-slot address equals the
left observation at the same address, then the whole addressed right table, projected entrywise,
is the whole addressed left table.  Both nested list levels are preserved and no sphere, address or
child order is discarded. -/
private theorem table_map_eq_of_address_agree
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat} {α β : Type*}
    (observeL : LocalizedCumulativeDecoratedTree input carrierFuel → α)
    (observeR : LocalizedCumulativeDecoratedTree input carrierFuel → β)
    (project : β → α) (tL tR : LocalizedCumulativeDecoratedTree input carrierFuel)
    (hshape : shape tL = shape tR)
    (agree : ∀ (addr : List Nat)
      (nodeL nodeR : LocalizedCumulativeDecoratedTree input carrierFuel),
      subtreeAt? tL addr = some nodeL → subtreeAt? tR addr = some nodeR →
        project (observeR nodeR) = observeL nodeL) :
    (table observeR tR).map (List.map (sparseEntryMap project)) = table observeL tL := by
  have main : ∀ n : Nat, ∀ tL : LocalizedCumulativeDecoratedTree input carrierFuel,
      LocalizedCumulativeDecoratedTree.height tL ≤ n →
      ∀ tR : LocalizedCumulativeDecoratedTree input carrierFuel, shape tL = shape tR →
      (∀ (addr : List Nat)
        (nodeL nodeR : LocalizedCumulativeDecoratedTree input carrierFuel),
        subtreeAt? tL addr = some nodeL → subtreeAt? tR addr = some nodeR →
          project (observeR nodeR) = observeL nodeL) →
      (table observeR tR).map (List.map (sparseEntryMap project)) = table observeL tL := by
    intro n
    refine Nat.strong_induction_on n ?_
    intro k inductionHypothesis tL bound tR hshape agree
    cases tL with
    | mk sourceL atomicL distL massL labelL childrenL =>
      cases tR with
      | mk sourceR atomicR distR massR labelR childrenR =>
        have rootAgree : project (observeR
            ⟨sourceR, atomicR, distR, massR, labelR, childrenR⟩) =
            observeL ⟨sourceL, atomicL, distL, massL, labelL, childrenL⟩ :=
          agree [] _ _ (by rw [subtreeAt?_nil]) (by rw [subtreeAt?_nil])
        have matched : RealizedTreeMatch
            (⟨sourceL, atomicL, distL, massL, labelL, childrenL⟩ :
              LocalizedCumulativeDecoratedTree input carrierFuel)
            ⟨sourceR, atomicR, distR, massR, labelR, childrenR⟩ :=
          realizedTreeMatch_of_shape_eq hshape
        have lengthEq : childrenL.length = childrenR.length :=
          realizedTreeMatch_children_length_eq matched
        have childAgree : ∀ (slot : Nat)
            (childL : LocalizedCumulativeDecoratedTree input carrierFuel),
            childrenL[slot]? = some childL →
            ∃ childR : LocalizedCumulativeDecoratedTree input carrierFuel,
              childrenR[slot]? = some childR ∧
                (table observeR childR).map (List.map (sparseEntryMap project)) =
                  table observeL childL := by
          intro slot childL atL
          obtain ⟨childR, atR, childMatch⟩ :=
            realizedTreeMatch_children_getElem? matched atL
          refine ⟨childR, atR, ?_⟩
          refine inductionHypothesis
            (LocalizedCumulativeDecoratedTree.height childL) ?_ childL le_rfl childR
            (shape_eq_of_realizedTreeMatch childMatch) ?_
          · have smaller := height_lt_height_of_mem
              (⟨sourceL, atomicL, distL, massL, labelL, childrenL⟩ :
                LocalizedCumulativeDecoratedTree input carrierFuel)
              (List.mem_of_getElem? atL)
            omega
          · intro addr nodeL nodeR atNodeL atNodeR
            exact agree (slot :: addr) nodeL nodeR
              (by
                rw [subtreeAt?_cons, atL]
                simpa only [Option.bind_some] using atNodeL)
              (by
                rw [subtreeAt?_cons, atR]
                simpa only [Option.bind_some] using atNodeR)
        have layersEq : (childrenR.map (table observeR)).map
            (List.map (List.map (sparseEntryMap project))) =
            childrenL.map (table observeL) := by
          rw [List.map_map]
          apply List.ext_getElem?
          intro slot
          rw [List.getElem?_map, List.getElem?_map]
          cases atL : childrenL[slot]? with
          | none =>
              have atR : childrenR[slot]? = none := by
                rw [List.getElem?_eq_none_iff] at atL ⊢
                omega
              rw [atR]
              rfl
          | some childL =>
              obtain ⟨childR, atR, tableEq⟩ := childAgree slot childL atL
              rw [atR]
              exact congrArg some tableEq
        rw [table_eq_root_merge observeR
            ⟨sourceR, atomicR, distR, massR, labelR, childrenR⟩,
          table_eq_root_merge observeL
            ⟨sourceL, atomicL, distL, massL, labelL, childrenL⟩,
          List.map_append,
          mergeLocalizedTreeChildTables_sparseEntryMap]
        rw [layersEq]
        simp only [List.map_cons, List.map_nil, sparseEntryMap_mk, rootAgree]
  exact main (LocalizedCumulativeDecoratedTree.height tL) tL le_rfl tR hshape agree

/-! ## Kind algebra of the cumulative priority vectors -/

/-- Every cumulative priority vector starts with the Rule-4a kind observation, so its scalar
first-component projection `getD 0 0` is the Rule-4a kind of its label, independent of the stage. -/
private theorem cumulativePriority_getD_zero_eq_kind
    (stage : LocalizedCumulativeRule45Stage)
    (label : Option LocalizedAuxiliaryLabel) :
    (localizedCumulativeRule45Priority stage label).getD 0 0 =
      localizedRule4aPriority label := by
  cases stage <;> simp only [localizedCumulativeRule45Priority, List.getD_cons_zero]

/-- Every cumulative priority vector starts with the Rule-4a kind observation.  Taking the first
component of any stage vector therefore recovers the first component of any other stage vector as
soon as the two labels have the same Rule-4a kind. -/
private theorem cumulativePriority_take_one_of_kind_eq
    (stageL stageR : LocalizedCumulativeRule45Stage)
    {labelL labelR : Option LocalizedAuxiliaryLabel}
    (kindEq : localizedRule4aPriority labelL = localizedRule4aPriority labelR) :
    (localizedCumulativeRule45Priority stageR labelR).take 1 =
      (localizedCumulativeRule45Priority stageL labelL).take 1 := by
  cases stageL <;> cases stageR <;>
    simp only [localizedCumulativeRule45Priority, List.take_succ_cons, List.take_zero, kindEq]

/-- The scalar first-column projection `getD 0 0` agrees between any two cumulative stages at
labels of equal Rule-4a kind. -/
private theorem cumulativePriority_getD_zero_of_kind_eq
    (stageL stageR : LocalizedCumulativeRule45Stage)
    {labelL labelR : Option LocalizedAuxiliaryLabel}
    (kindEq : localizedRule4aPriority labelL = localizedRule4aPriority labelR) :
    (localizedCumulativeRule45Priority stageR labelR).getD 0 0 =
      (localizedCumulativeRule45Priority stageL labelL).getD 0 0 := by
  cases stageL <;> cases stageR <;>
    simp only [localizedCumulativeRule45Priority, List.getD_cons_zero, kindEq]

/-! ## Scalar projection of the addressed table -/

/-- Projecting every addressed entry of a table onto component `0` is exactly compiling the same
tree with the scalar observation `fun node => (observe node).getD 0 0`.  Every sphere and every raw
sibling-slot address is preserved. -/
private theorem projectCumulative_zero_table
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (observe : LocalizedCumulativeDecoratedTree input carrierFuel → List Nat)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    projectCumulative 0 (table observe tree) =
      table (fun node => (observe node).getD 0 0) tree := by
  show (table observe tree).map
      (List.map (sparseEntryMap (fun values : List Nat => values.getD 0 0))) =
    table (fun node => (observe node).getD 0 0) tree
  exact table_map_eq_of_address_agree
    (observeL := fun node => (observe node).getD 0 0) (observeR := observe)
    (project := fun values : List Nat => values.getD 0 0) tree tree rfl
    (fun addr nodeL nodeR atL atR => by
      have same : nodeL = nodeR := Option.some.inj (atL.symm.trans atR)
      rw [same])











/-- **Actual same-cursor physical stage kind.**  For two successful actual builds at the actual
frame cursor `setup.frame.cursorAt setup.slot`, driven by the actual generated dependency reader and
the actual production target/view, the two realized trees have equal erased shape, and at every raw
sibling-slot address where both trees have a node the first components (`take 1`) and the scalar
first components (`getD 0 0`) of the stage priority vectors agree.  No common prefix, child-order
alignment, label covariance, reference value or source-bearing key equality is assumed. -/
theorem exists_actualSameCursor_physicalStageKind
    {input : LocalizedUniversalReference.Input}
    (setup : ActualSlotPhysicalSetup input)
    (stageL stageR : LocalizedCumulativeRule45Stage)
    (fuelL fuelR : Nat)
    (keyL keyR : input.certified.LocalizedRerootCumulativeRule45Key)
    (builtL : input.certified.buildLocalizedRerootCumulativeRule45Key?
      stageL
      (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
      (referenceDependencyView input setup.c) fuelL
      (setup.frame.cursorAt setup.slot) = some keyL)
    (builtR : input.certified.buildLocalizedRerootCumulativeRule45Key?
      stageR
      (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
      (referenceDependencyView input setup.c) fuelR
      (setup.frame.cursorAt setup.slot) = some keyR) :
    ∃ (tL tR : LocalizedCumulativeDecoratedTree input.certified
          (LocalizedUniversalReference.carrierFuel input))
      (hshape : LocalizedCumulativeDecoratedTree.shape tL =
        LocalizedCumulativeDecoratedTree.shape tR)
      (_sourceL : tL.source = setup.frame.cursorAt setup.slot)
      (_sourceR : tR.source = setup.frame.cursorAt setup.slot)
      (_matchL : LocalizedCumulativeTreeTableMatch stageL tL keyL)
      (_matchR : LocalizedCumulativeTreeTableMatch stageR tR keyR)
      (_realizesL : LocalizedCumulativeTreeRealizes input.certified
        (ActualReaderPhysicalBranchInverse.dependencyReader input setup.c) tL)
      (_realizesR : LocalizedCumulativeTreeRealizes input.certified
        (ActualReaderPhysicalBranchInverse.dependencyReader input setup.c) tR),
      (∀ pL : Position tL,
        localizedRule4aPriority (positionNode pL).label =
          localizedRule4aPriority (positionNode (shapePositionEquiv hshape pL)).label) ∧
      (∀ (addr : List Nat)
        (nodeL nodeR : LocalizedCumulativeDecoratedTree input.certified
          (LocalizedUniversalReference.carrierFuel input)),
        subtreeAt? tL addr = some nodeL →
          subtreeAt? tR addr = some nodeR →
            (localizedCumulativeRule45Priority stageR nodeR.label).take 1 =
              (localizedCumulativeRule45Priority stageL nodeL.label).take 1) ∧
      (∀ (addr : List Nat)
        (nodeL nodeR : LocalizedCumulativeDecoratedTree input.certified
          (LocalizedUniversalReference.carrierFuel input)),
        subtreeAt? tL addr = some nodeL →
          subtreeAt? tR addr = some nodeR →
            (localizedCumulativeRule45Priority stageR nodeR.label).getD 0 0 =
              (localizedCumulativeRule45Priority stageL nodeL.label).getD 0 0) := by
  have builtWithReadL : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? stageL
      (ActualReaderPhysicalBranchInverse.dependencyReader input setup.c) fuelL
      (setup.frame.cursorAt setup.slot) = some keyL := by
    rw [buildWithRead_dependencyReader_eq_build setup stageL fuelL
      (setup.frame.cursorAt setup.slot)]
    exact builtL
  have builtWithReadR : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? stageR
      (ActualReaderPhysicalBranchInverse.dependencyReader input setup.c) fuelR
      (setup.frame.cursorAt setup.slot) = some keyR := by
    rw [buildWithRead_dependencyReader_eq_build setup stageR fuelR
      (setup.frame.cursorAt setup.slot)]
    exact builtR
  have observableEq := cumulative_builds_constitutional_observable_equal
    (input := input.certified)
    (carrierFuel := LocalizedUniversalReference.carrierFuel input)
    (cursor := setup.frame.cursorAt setup.slot) builtL builtR
  have rule1aEq : keyL.constitutional.rule1a = keyR.constitutional.rule1a := by
    have columnEq := congrArg
      (fun observable : LocalizedConstitutionalObservable => observable.rule1a) observableEq
    simpa only [constitutionalObservable] using columnEq
  have rule1bEq : keyL.constitutional.rule1b = keyR.constitutional.rule1b := by
    have columnEq := congrArg
      (fun observable : LocalizedConstitutionalObservable => observable.rule1b) observableEq
    simpa only [constitutionalObservable] using columnEq
  have rule2Eq : keyL.constitutional.rule2 = keyR.constitutional.rule2 := by
    have columnEq := congrArg
      (fun observable : LocalizedConstitutionalObservable => observable.rule2) observableEq
    simpa only [constitutionalObservable] using columnEq
  obtain ⟨tL, tR, sourceL, sourceR, matchL, matchR, realizesL, realizesR, hshape, _matched⟩ :=
    exists_matchedTrees_of_buildWithRead input.certified stageL stageR
      (ActualReaderPhysicalBranchInverse.dependencyReader input setup.c)
      (ActualReaderPhysicalBranchInverse.dependencyReader input setup.c)
      fuelL fuelR
      (setup.frame.cursorAt setup.slot) (setup.frame.cursorAt setup.slot)
      keyL keyR builtWithReadL builtWithReadR rule1aEq rule1bEq rule2Eq
  have prevEqL := LocalizedUniqueNearestRule5Direction.actualTree_previousEq_of_source
    input setup.c setup.frame setup.frameComputed setup.slot sourceL
  have validL := LocalizedUniqueNearestRule5Direction.actualTree_valid_of_source
    input setup.c setup.frame setup.frameComputed setup.slot sourceL
  have sameRootL := LocalizedUniqueNearestRule5Direction.actualTree_sameRoot_of_source
    input setup.c setup.frame setup.frameComputed setup.slot sourceL
  have obsL := LocalizedUniqueNearestRule5Direction.actualTree_oObserved_of_source
    input setup.c setup.frame setup.frameComputed setup.slot sourceL setup.oObserved
  have prevEqR := LocalizedUniqueNearestRule5Direction.actualTree_previousEq_of_source
    input setup.c setup.frame setup.frameComputed setup.slot sourceR
  have validR := LocalizedUniqueNearestRule5Direction.actualTree_valid_of_source
    input setup.c setup.frame setup.frameComputed setup.slot sourceR
  have sameRootR := LocalizedUniqueNearestRule5Direction.actualTree_sameRoot_of_source
    input setup.c setup.frame setup.frameComputed setup.slot sourceR
  have obsR := LocalizedUniqueNearestRule5Direction.actualTree_oObserved_of_source
    input setup.c setup.frame setup.frameComputed setup.slot sourceR setup.oObserved
  let φ : AcyclicCutBranchAutomorphism.RootedCutBranchIso input.certified.moleculeGraph
      setup.c.1 setup.oAtom setup.oAtom :=
    LocalizedActualNearestStagePrefixCovariance.actualStage_selfIso input setup.c setup.frame
      setup.frameComputed setup.slot setup.singleBonded setup.acyclic setup.oObserved
      sourceL sourceR realizesL realizesR hshape
  let e := LocalizedCutBranchSelfAutomorphism.detectedCutBranchSelfAut
    input.certified.moleculeGraph setup.c.1 setup.oAtom setup.acyclic setup.incomingEdge
    setup.singleBonded setup.hcharge φ
  have eApplyRoot : (e : Equiv.Perm input.certified.Atom) setup.root.1 = setup.root.1 :=
    LocalizedCutBranchSelfAutomorphism.detectedCutBranchSelfAut_apply_center
      input.certified.moleculeGraph setup.c.1 setup.oAtom setup.acyclic setup.incomingEdge
      setup.singleBonded setup.hcharge φ
  have hcenter :
      input.certified.detectedMultiCenterMolecule.centerPerm e setup.root = setup.root :=
    LocalizedCutBranchSelfAutomorphism.centerPerm_eq_self_of_apply_eq
      input.certified.detectedMultiCenterMolecule e setup.root eApplyRoot
  have reachableL : input.certified.ActualChildReachable setup.tree.source tL.source := by
    rw [sourceL, ← setup.tree_source]
    exact actualChildReachable_iff_reflTransGen.mpr Relation.ReflTransGen.refl
  have reachableR : input.certified.ActualChildReachable setup.tree.source tR.source := by
    rw [sourceR, ← setup.tree_source]
    exact actualChildReachable_iff_reflTransGen.mpr Relation.ReflTransGen.refl
  have imageAt : ∀ q : Position tL,
      (e : Equiv.Perm input.certified.Atom)
          (positionAtom setup.singleBonded setup.acyclic q) =
        positionAtom setup.singleBonded setup.acyclic (shapePositionEquiv hshape q) := by
    intro q
    have mem : positionAtom setup.singleBonded setup.acyclic q ∈
        AcyclicCutBranchAutomorphism.CutBranch input.certified.moleculeGraph setup.c.1
          setup.oAtom :=
      reachable_position_atom_mem_slotBranch setup realizesL reachableL q
    have cutEq :
        (⟨positionAtom setup.singleBonded setup.acyclic q, mem⟩ :
            AcyclicCutBranchAutomorphism.CutBranch input.certified.moleculeGraph setup.c.1
              setup.oAtom) =
          positionCutEquiv setup.singleBonded setup.acyclic (globalCarrierFuel_adequate input)
            realizesL (ActualReaderPhysicalBranchInverse.topTarget input setup.c) prevEqL validL
            sameRootL obsL (ActualReaderPhysicalBranchInverse.topTarget_current input setup.c)
            setup.incomingEdge q :=
      Subtype.ext (by rw [positionCutEquiv_apply_coe])
    have applyEq :
        (((LocalizedActualNearestStagePrefixCovariance.actualStage_selfIso input setup.c
            setup.frame setup.frameComputed setup.slot setup.singleBonded setup.acyclic
            setup.oObserved sourceL sourceR realizesL realizesR hshape).toEquiv
          (positionCutEquiv setup.singleBonded setup.acyclic
            (globalCarrierFuel_adequate input) realizesL
            (ActualReaderPhysicalBranchInverse.topTarget input setup.c) prevEqL validL sameRootL
            obsL (ActualReaderPhysicalBranchInverse.topTarget_current input setup.c)
            setup.incomingEdge q) :
              AcyclicCutBranchAutomorphism.CutBranch input.certified.moleculeGraph setup.c.1
                setup.oAtom) : input.certified.Atom) =
          positionAtom setup.singleBonded setup.acyclic (shapePositionEquiv hshape q) := by
      simpa only [LocalizedActualNearestStagePrefixCovariance.actualStage_selfIso] using
        (rootedCutBranchIso_of_shapeMatch_toEquiv_apply (input := input.certified)
          (carrierFuel := LocalizedUniversalReference.carrierFuel input)
          (singleBonded := setup.singleBonded) (acyclic := setup.acyclic)
          (globalCarrierFuel_adequate input) hshape realizesL realizesR
          prevEqL validL sameRootL prevEqR validR sameRootR obsL
          (ActualReaderPhysicalBranchInverse.topTarget_current input setup.c) obsR
          (ActualReaderPhysicalBranchInverse.topTarget_current input setup.c)
          setup.incomingEdge setup.incomingEdge q)
    calc (e : Equiv.Perm input.certified.Atom)
          (positionAtom setup.singleBonded setup.acyclic q)
        = (φ.toEquiv ⟨positionAtom setup.singleBonded setup.acyclic q, mem⟩ :
            input.certified.Atom) :=
          LocalizedCutBranchSelfAutomorphism.detectedCutBranchSelfAut_apply_of_mem
            input.certified.moleculeGraph setup.c.1 setup.oAtom setup.acyclic setup.incomingEdge
            setup.singleBonded setup.hcharge φ mem
      _ = (φ.toEquiv (positionCutEquiv setup.singleBonded setup.acyclic
            (globalCarrierFuel_adequate input) realizesL
            (ActualReaderPhysicalBranchInverse.topTarget input setup.c) prevEqL validL sameRootL
            obsL (ActualReaderPhysicalBranchInverse.topTarget_current input setup.c)
            setup.incomingEdge q) : input.certified.Atom) := by
          rw [cutEq]
      _ = positionAtom setup.singleBonded setup.acyclic (shapePositionEquiv hshape q) := applyEq
  have markedAt : ∀ q : Position tL,
      PhysicalMarkedAtom input setup.root
          (positionAtom setup.singleBonded setup.acyclic q) ↔
        PhysicalMarkedAtom input setup.root
          (positionAtom setup.singleBonded setup.acyclic
            (shapePositionEquiv hshape q)) := by
    intro q
    have transport := LocalizedPhysicalReferenceCovariance.physicalBranchMarked_transport
      input.certified input.certified.detectedMultiCenterMolecule e hcenter
      (positionAtom setup.singleBonded setup.acyclic q)
    rw [imageAt q] at transport
    exact (LocalizedPhysicalReferenceCovariance.physicalBranchMarked_iff_physicalMarkedAtom
        input setup.root (positionAtom setup.singleBonded setup.acyclic q)).symm.trans
      (transport.symm.trans
        (LocalizedPhysicalReferenceCovariance.physicalBranchMarked_iff_physicalMarkedAtom
          input setup.root
          (positionAtom setup.singleBonded setup.acyclic
            (shapePositionEquiv hshape q))))
  have kindEq : ∀ pL : Position tL,
      localizedRule4aPriority (positionNode pL).label =
        localizedRule4aPriority (positionNode (shapePositionEquiv hshape pL)).label := by
    intro pL
    have stateL := reachable_position_label_eq_state setup realizesL reachableL pL
    have stateR := reachable_position_label_eq_state setup realizesR reachableR
      (shapePositionEquiv hshape pL)
    have sparseL := reachable_position_sparse setup realizesL reachableL pL
    have sparseR := reachable_position_sparse setup realizesR reachableR
      (shapePositionEquiv hshape pL)
    have chiralL := reachable_position_chiral_iff_marked setup realizesL reachableL pL
    have chiralR := reachable_position_chiral_iff_marked setup realizesR reachableR
      (shapePositionEquiv hshape pL)
    rw [stateL, stateR]
    exact localizedRule4aPriority_eq_of_sparse sparseL sparseR
      ((option_none_iff_not_exists_chiral_of_sparse sparseL).trans
        ((not_iff_not.mpr (chiralL.trans ((markedAt pL).trans chiralR.symm))).trans
          (option_none_iff_not_exists_chiral_of_sparse sparseR).symm))
  have addressedTake : ∀ (addr : List Nat)
      (nodeL nodeR : LocalizedCumulativeDecoratedTree input.certified
        (LocalizedUniversalReference.carrierFuel input)),
      subtreeAt? tL addr = some nodeL →
        subtreeAt? tR addr = some nodeR →
          (localizedCumulativeRule45Priority stageR nodeR.label).take 1 =
            (localizedCumulativeRule45Priority stageL nodeL.label).take 1 := by
    intro addr nodeL nodeR atL atR
    let pL : Position tL := ⟨addr, by rw [atL]; rfl⟩
    have nodeEqL : positionNode pL = nodeL := by
      have spec := positionNode_spec pL
      rw [show pL.val = addr from rfl] at spec
      rw [atL] at spec
      exact (Option.some.inj spec).symm
    have nodeEqR : positionNode (shapePositionEquiv hshape pL) = nodeR := by
      have spec := positionNode_spec (shapePositionEquiv hshape pL)
      rw [show (shapePositionEquiv hshape pL).val = addr from rfl] at spec
      rw [atR] at spec
      exact (Option.some.inj spec).symm
    have hkind := kindEq pL
    rw [nodeEqR, nodeEqL] at hkind
    exact cumulativePriority_take_one_of_kind_eq stageL stageR hkind
  have addressedGetD : ∀ (addr : List Nat)
      (nodeL nodeR : LocalizedCumulativeDecoratedTree input.certified
        (LocalizedUniversalReference.carrierFuel input)),
      subtreeAt? tL addr = some nodeL →
        subtreeAt? tR addr = some nodeR →
          (localizedCumulativeRule45Priority stageR nodeR.label).getD 0 0 =
            (localizedCumulativeRule45Priority stageL nodeL.label).getD 0 0 := by
    intro addr nodeL nodeR atL atR
    let pL : Position tL := ⟨addr, by rw [atL]; rfl⟩
    have nodeEqL : positionNode pL = nodeL := by
      have spec := positionNode_spec pL
      rw [show pL.val = addr from rfl] at spec
      rw [atL] at spec
      exact (Option.some.inj spec).symm
    have nodeEqR : positionNode (shapePositionEquiv hshape pL) = nodeR := by
      have spec := positionNode_spec (shapePositionEquiv hshape pL)
      rw [show (shapePositionEquiv hshape pL).val = addr from rfl] at spec
      rw [atR] at spec
      exact (Option.some.inj spec).symm
    have hkind := kindEq pL
    rw [nodeEqR, nodeEqL] at hkind
    exact cumulativePriority_getD_zero_of_kind_eq stageL stageR hkind
  exact ⟨tL, tR, hshape, sourceL, sourceR, matchL, matchR, realizesL, realizesR,
    kindEq, addressedTake, addressedGetD⟩

/-! ## The literal whole-descriptor-table identity at stage Rule-4b -/

/-- **Actual physical Rule-4a prefix preservation at stage Rule-4b.**  For the actual same frame
cursor `setup.frame.cursorAt setup.slot`, an arbitrary reference `rb : RS`, and any successful
actual `.rule4a` and `.rule4b rb` production builds at that cursor, projecting every entry of the
stage-`.rule4b rb` descriptor table onto its first component — at every sphere and every raw
sibling-slot address, at arbitrary molecular depth — is exactly the whole stage-`.rule4a` descriptor
table.  No common prefix, child-order alignment, label covariance, reference value or source-bearing
key equality is assumed. -/
theorem actualPhysical_rule4b_descriptor_prefix
    {input : LocalizedUniversalReference.Input}
    (setup : ActualSlotPhysicalSetup input)
    (reference : RS)
    (fuel4a fuel4b : Nat)
    (key4a key4b : input.certified.LocalizedRerootCumulativeRule45Key)
    (built4a : input.certified.buildLocalizedRerootCumulativeRule45Key?
      .rule4a
      (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
      (referenceDependencyView input setup.c) fuel4a
      (setup.frame.cursorAt setup.slot) = some key4a)
    (built4b : input.certified.buildLocalizedRerootCumulativeRule45Key?
      (.rule4b reference)
      (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
      (referenceDependencyView input setup.c) fuel4b
      (setup.frame.cursorAt setup.slot) = some key4b) :
    key4b.descriptor.map (fun row => row.map (fun entry => (entry.1, entry.2.take 1))) =
      key4a.descriptor := by
  obtain ⟨tL, tR, hshape, _sourceL, _sourceR, matchL, matchR, _realizesL, _realizesR,
    _kindEq, addressedTake, _addressedGetD⟩ :=
    exists_actualSameCursor_physicalStageKind setup .rule4a (.rule4b reference)
      fuel4a fuel4b key4a key4b built4a built4b
  have match4a : (tL.tables .rule4a).descriptor = key4a.descriptor := matchL.2.2.2
  have match4b : (tR.tables (.rule4b reference)).descriptor = key4b.descriptor := matchR.2.2.2
  have tableEq : (table (fun node =>
        localizedCumulativeRule45Priority (.rule4b reference) node.label) tR).map
      (List.map (sparseEntryMap (fun values : List Nat => values.take 1))) =
        table (fun node =>
          localizedCumulativeRule45Priority .rule4a node.label) tL :=
    table_map_eq_of_address_agree
      (observeL := fun node => localizedCumulativeRule45Priority .rule4a node.label)
      (observeR := fun node =>
        localizedCumulativeRule45Priority (.rule4b reference) node.label)
      (project := fun values : List Nat => values.take 1) tL tR hshape addressedTake
  have projectionEq :
      (fun row : List (OfficialSparseEntry (List Nat)) =>
          row.map (fun entry => (entry.1, entry.2.take 1))) =
        List.map (sparseEntryMap (fun values : List Nat => values.take 1)) := by
    funext row
    rfl
  calc key4b.descriptor.map (fun row => row.map (fun entry => (entry.1, entry.2.take 1)))
      = key4b.descriptor.map
          (List.map (sparseEntryMap (fun values : List Nat => values.take 1))) := by
        rw [projectionEq]
    _ = ((tR.tables (.rule4b reference)).descriptor).map
          (List.map (sparseEntryMap (fun values : List Nat => values.take 1))) := by
        rw [← match4b]
    _ = (tL.tables .rule4a).descriptor := by
        simpa only [tables_descriptor] using tableEq
    _ = key4a.descriptor := match4a

/-- **Scalar first-column corollary.**  The same actual data, projected to the scalar first
component of every addressed entry (`projectCumulative 0`), gives the literal scalar descriptor
equality of the whole nested sparse tables. -/
theorem actualPhysical_rule4b_first_column
    {input : LocalizedUniversalReference.Input}
    (setup : ActualSlotPhysicalSetup input)
    (reference : RS)
    (fuel4a fuel4b : Nat)
    (key4a key4b : input.certified.LocalizedRerootCumulativeRule45Key)
    (built4a : input.certified.buildLocalizedRerootCumulativeRule45Key?
      .rule4a
      (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
      (referenceDependencyView input setup.c) fuel4a
      (setup.frame.cursorAt setup.slot) = some key4a)
    (built4b : input.certified.buildLocalizedRerootCumulativeRule45Key?
      (.rule4b reference)
      (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
      (referenceDependencyView input setup.c) fuel4b
      (setup.frame.cursorAt setup.slot) = some key4b) :
    projectCumulative 0 key4b.descriptor = projectCumulative 0 key4a.descriptor := by
  obtain ⟨tL, tR, hshape, _sourceL, _sourceR, matchL, matchR, _realizesL, _realizesR,
    _kindEq, _addressedTake, addressedGetD⟩ :=
    exists_actualSameCursor_physicalStageKind setup .rule4a (.rule4b reference)
      fuel4a fuel4b key4a key4b built4a built4b
  have match4a : (tL.tables .rule4a).descriptor = key4a.descriptor := matchL.2.2.2
  have match4b : (tR.tables (.rule4b reference)).descriptor = key4b.descriptor := matchR.2.2.2
  have scalarEq :
      (table (fun node =>
          localizedCumulativeRule45Priority (.rule4b reference) node.label) tR).map
        (List.map (sparseEntryMap (fun values : List Nat => values.getD 0 0))) =
          table (fun node =>
            (localizedCumulativeRule45Priority .rule4a node.label).getD 0 0) tL :=
    table_map_eq_of_address_agree
      (observeL := fun node =>
        (localizedCumulativeRule45Priority .rule4a node.label).getD 0 0)
      (observeR := fun node =>
        localizedCumulativeRule45Priority (.rule4b reference) node.label)
      (project := fun values : List Nat => values.getD 0 0) tL tR hshape addressedGetD
  calc projectCumulative 0 key4b.descriptor
      = projectCumulative 0 ((tR.tables (.rule4b reference)).descriptor) := by
        rw [← match4b]
    _ = projectCumulative 0 (table (fun node =>
          localizedCumulativeRule45Priority (.rule4b reference) node.label) tR) := by
        rw [tables_descriptor]
    _ = (table (fun node =>
          localizedCumulativeRule45Priority (.rule4b reference) node.label) tR).map
          (List.map (sparseEntryMap (fun values : List Nat => values.getD 0 0))) := rfl
    _ = table (fun node =>
          (localizedCumulativeRule45Priority .rule4a node.label).getD 0 0) tL := scalarEq
    _ = projectCumulative 0 (table (fun node =>
          localizedCumulativeRule45Priority .rule4a node.label) tL) :=
        (projectCumulative_zero_table _ tL).symm
    _ = projectCumulative 0 ((tL.tables .rule4a).descriptor) := by
        rw [tables_descriptor]
    _ = projectCumulative 0 key4a.descriptor := by
        rw [← match4a]

/-! ## Physical-only adequate-fuel producers -/

/-- **Adequate-fuel producer without new build-success assumptions.**  At the actual frame cursor,
the proved reroot budget `2 * (carrierFuel + 1)` suffices for the stage-`.rule4b reference` build,
and the resulting actual key satisfies the whole descriptor-table prefix identity.  The caller
supplies only the physical slot setup, an arbitrary reference, and nothing else. -/
theorem exists_actualSameCursor_rule4b_descriptor_prefix
    {input : LocalizedUniversalReference.Input}
    (setup : ActualSlotPhysicalSetup input)
    (reference : RS) :
    ∃ key4b : input.certified.LocalizedRerootCumulativeRule45Key,
      input.certified.buildLocalizedRerootCumulativeRule45Key?
          (.rule4b reference)
          (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
          (referenceDependencyView input setup.c)
          (2 * (LocalizedUniversalReference.carrierFuel input + 1))
          (setup.frame.cursorAt setup.slot) = some key4b ∧
        key4b.descriptor.map (fun row => row.map (fun entry => (entry.1, entry.2.take 1))) =
          setup.key.prior.rule4aKey.descriptor := by
  obtain ⟨key4b, built4b⟩ :=
    exists_buildLocalizedRerootCumulativeRule45Key?_at_twice input.certified
      (.rule4b reference)
      (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
      (referenceDependencyView input setup.c)
      (setup.frame.cursorAt setup.slot)
      (setup.tree_source ▸ setup.tree_valid)
  exact ⟨key4b, built4b,
    actualPhysical_rule4b_descriptor_prefix setup reference
      (localizedOccurrenceRerootEvaluationFuel (LocalizedUniversalReference.carrierFuel input))
      (2 * (LocalizedUniversalReference.carrierFuel input + 1))
      setup.key.prior.rule4aKey key4b setup.rule4aBuilt built4b⟩

/-- **Adequate-fuel scalar first-column producer.**  The scalar `projectCumulative 0` form of the
whole-table identity, with the same physical-only success guarantee. -/
theorem exists_actualSameCursor_rule4b_first_column
    {input : LocalizedUniversalReference.Input}
    (setup : ActualSlotPhysicalSetup input)
    (reference : RS) :
    ∃ key4b : input.certified.LocalizedRerootCumulativeRule45Key,
      input.certified.buildLocalizedRerootCumulativeRule45Key?
          (.rule4b reference)
          (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
          (referenceDependencyView input setup.c)
          (2 * (LocalizedUniversalReference.carrierFuel input + 1))
          (setup.frame.cursorAt setup.slot) = some key4b ∧
        projectCumulative 0 key4b.descriptor =
          projectCumulative 0 setup.key.prior.rule4aKey.descriptor := by
  obtain ⟨key4b, built4b, _prefix⟩ :=
    exists_actualSameCursor_rule4b_descriptor_prefix setup reference
  exact ⟨key4b, built4b,
    actualPhysical_rule4b_first_column setup reference
      (localizedOccurrenceRerootEvaluationFuel (LocalizedUniversalReference.carrierFuel input))
      (2 * (LocalizedUniversalReference.carrierFuel input + 1))
      setup.key.prior.rule4aKey key4b setup.rule4aBuilt built4b⟩

/-- **Original-input facade.**  From the certified graph facts, the original configuration, the
original physical general-rigid / physical-terminal-twin domain at the detected centre, and an atom
actually bonded to that centre, an indexed actual slot setup exists, and at its own derived frame
cursor the adequate-fuel stage-`.rule4b reference` build satisfies the whole descriptor-table
prefix identity against the actual Rule-4a key.  The frame, slot and observation are derived; no
frame-success, desired-letter or nearest-selection premise is added. -/
theorem exists_actualSlotPhysicalSetup_rule4b_descriptor_prefix
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (physicalDomain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (oAtom : input.certified.Atom)
    (adjacent : input.certified.moleculeGraph.Adj c.1 oAtom)
    (reference : RS) :
    ∃ setupOf : ActualSlotPhysicalSetupOf input c cfg physicalDomain oAtom,
      ∃ key4b : input.certified.LocalizedRerootCumulativeRule45Key,
        input.certified.buildLocalizedRerootCumulativeRule45Key?
            (.rule4b reference)
            (ActualReaderPhysicalBranchInverse.topTarget input c)
            (referenceDependencyView input c)
            (2 * (LocalizedUniversalReference.carrierFuel input + 1))
            (setupOf.toSetup.frame.cursorAt setupOf.toSetup.slot) = some key4b ∧
          key4b.descriptor.map
              (fun row => row.map (fun entry => (entry.1, entry.2.take 1))) =
            setupOf.toSetup.key.prior.rule4aKey.descriptor := by
  obtain ⟨setupOf⟩ := exists_actualSlotPhysicalSetupOf input c singleBonded acyclic hcharge
    noDouble cfg physicalDomain oAtom adjacent
  obtain ⟨key4b, built4b, prefixEq⟩ :=
    exists_actualSameCursor_rule4b_descriptor_prefix setupOf.toSetup reference
  exact ⟨setupOf, key4b, built4b, prefixEq⟩

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.exists_actualSameCursor_physicalStageKind
assert_kernel_only TetraStereo.OneCenter.actualPhysical_rule4b_descriptor_prefix
assert_kernel_only TetraStereo.OneCenter.actualPhysical_rule4b_first_column
assert_kernel_only TetraStereo.OneCenter.exists_actualSameCursor_rule4b_descriptor_prefix
assert_kernel_only TetraStereo.OneCenter.exists_actualSameCursor_rule4b_first_column
assert_kernel_only TetraStereo.OneCenter.exists_actualSlotPhysicalSetup_rule4b_descriptor_prefix
