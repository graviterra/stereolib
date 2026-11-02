import TetraStereo.OneCenter.LocalizedActualPhysicalKeySeparation
import TetraStereo.OneCenter.LocalizedEmptyRule4bReferenceDecoding
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput
open LocalizedCumulativeDecoratedTree
open LocalizedActualPhysicalKeySeparation





































namespace LocalizedEmptyReferencePhysicalPriorInverse

/-! ## All-`none` label layers survive the sparse child reconstruction -/

/-- The tail of an all-`none` list of addressed label layers is all-`none`. -/
theorem localizedLabelLayersAllNone_tail
    {layers : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))}
    (allNone : LocalizedLabelLayersAllNone layers) :
    LocalizedLabelLayersAllNone layers.tail := by
  intro layer layerPresent
  exact allNone layer (List.mem_of_mem_tail layerPresent)

/-- A `takeWhile` prefix of an all-`none` list of layers is all-`none`. -/
theorem localizedLabelLayersAllNone_takeWhile
    (predicate : List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)) → Bool)
    (layers : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))))
    (allNone : LocalizedLabelLayersAllNone layers) :
    LocalizedLabelLayersAllNone (layers.takeWhile predicate) := by
  induction layers with
  | nil =>
      intro layer layerPresent
      cases layerPresent
  | cons head tail inductionHypothesis =>
      rw [List.takeWhile_cons]
      by_cases keep : predicate head
      · rw [if_pos keep]
        intro layer layerPresent
        rcases List.mem_cons.mp layerPresent with same | tailPresent
        · subst layer
          exact allNone head (List.mem_cons_self)
        · exact inductionHypothesis
            (fun layer layerPresent =>
              allNone layer (List.mem_cons_of_mem head layerPresent))
            layer tailPresent
      · rw [if_neg keep]
        intro layer layerPresent
        cases layerPresent

/-- Dropping the leading slot from every entry of an all-`none` layer leaves it all-`none`. -/
theorem localizedLabelLayersAllNone_dropAddressHeadLayer
    {layer : List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))}
    (allNone : ∀ entry, entry ∈ layer → entry.2 = none) :
    ∀ entry, entry ∈ SparseAddress.dropAddressHeadLayer layer → entry.2 = none := by
  intro entry present
  obtain ⟨source, sourcePresent, same⟩ := List.mem_map.mp present
  rw [← same]
  simpa [SparseAddress.dropAddressHead] using allNone source sourcePresent

/-- Selecting the entries whose address begins with one slot preserves all-`none`. -/
theorem localizedLabelLayersAllNone_entriesAtSlot
    (slot : Nat)
    {layer : List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel))}
    (allNone : ∀ entry, entry ∈ layer → entry.2 = none) :
    ∀ entry, entry ∈ SparseAddress.entriesAtSlot slot layer → entry.2 = none := by
  intro entry present
  have inLayer : entry ∈ layer := by
    simpa [SparseAddress.entriesAtSlot] using (List.mem_filter.mp present).1
  exact allNone entry inLayer

/-- The normalized child table of an all-`none` label table is all-`none`.  This is the sparse
inverse that lets a whole-table label statement descend to every actual child slot. -/
theorem localizedLabelLayersAllNone_normalizedChildTable
    (slot : Nat)
    {layers : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))}
    (allNone : LocalizedLabelLayersAllNone layers) :
    LocalizedLabelLayersAllNone (SparseAddress.normalizedChildTable slot layers) := by
  unfold SparseAddress.normalizedChildTable
  apply localizedLabelLayersAllNone_takeWhile
  intro layer layerPresent entry entryPresent
  obtain ⟨original, originalPresent, same⟩ := List.mem_map.mp layerPresent
  rw [← same] at entryPresent
  exact localizedLabelLayersAllNone_dropAddressHeadLayer
    (localizedLabelLayersAllNone_entriesAtSlot slot
      (fun member memberPresent => allNone original originalPresent member memberPresent))
    entry entryPresent

/-! ## Every node of an actually realised tree with an all-`none` label table has label `none` -/

/-- Sphere zero of a table is the singleton root entry, so a layer list whose `getD 0` is a
singleton contains a layer containing that value. -/
theorem exists_mem_layer_of_getD_zero_eq_singleton {α : Type*}
    {layers : List (List α)} {value : α}
    (equal : layers.getD 0 [] = [value]) :
    ∃ layer, layer ∈ layers ∧ value ∈ layer := by
  cases layers with
  | nil => simp at equal
  | cons layer rest =>
      refine ⟨layer, List.mem_cons_self, ?_⟩
      have layerEq : layer = [value] := by
        simpa only [List.getD_cons_zero] using equal
      rw [layerEq]
      exact List.mem_singleton_self value

/-- If every entry of the exact-label table carries `none`, then every actual node of the tree
has label `none`.  The root is read from sphere zero; a slot step descends through the normalized
child table, whose all-`none` property is preserved by the sparse inverse. -/
theorem labelTable_allNone_node_label {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat} :
    ∀ (tree : LocalizedCumulativeDecoratedTree input carrierFuel),
      LocalizedLabelLayersAllNone tree.labelTable →
      ∀ (path : List Nat) (node : LocalizedCumulativeDecoratedTree input carrierFuel),
        subtreeAt? tree path = some node → node.label = none := by
  intro tree allNone path
  revert allNone
  revert tree
  induction path with
  | nil =>
      intro tree allNone node lookup
      rw [subtreeAt?_nil] at lookup
      have nodeEq : node = tree := (Option.some.inj lookup).symm
      subst node
      have rootTable : tree.labelTable.getD 0 [] =
          [(([], tree.label) : OfficialSparseEntry (Option LocalizedAuxiliaryLabel))] := by
        simpa using table_getD_zero (fun node => node.label) tree
      obtain ⟨layer, layerPresent, entryPresent⟩ :=
        exists_mem_layer_of_getD_zero_eq_singleton rootTable
      simpa using allNone layer layerPresent ([], tree.label) entryPresent
  | cons slot rest inductionHypothesis =>
      intro tree allNone node lookup
      rw [subtreeAt?_cons_eq_some_iff] at lookup
      obtain ⟨child, atSlot, restLookup⟩ := lookup
      have childTable : child.labelTable =
          SparseAddress.normalizedChildTable slot tree.labelTable.tail :=
        (LocalizedCumulativeDecoratedTree.normalizedChildTable_tail_eq_table
          (fun node => node.label) tree slot child atSlot).symm
      have childAllNone : LocalizedLabelLayersAllNone child.labelTable := by
        rw [childTable]
        exact localizedLabelLayersAllNone_normalizedChildTable slot
          (localizedLabelLayersAllNone_tail allNone)
      exact inductionHypothesis child childAllNone node restLookup

/-! ## Count priorities of the actual slot priors -/

/-- The stored reference-count priority of an actual slot prior is the constitutional priority
of its actual reference list.  This is the count half of builder soundness, used below to compare
empty and singleton selections by actual values rather than by an abstract selector. -/
theorem frameSlotKey_prior_referenceCountPriority
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame)
    (index : Fin 4) :
    (frameSlotKey input c frame derived index).prior.referenceCountPriority =
      constitutionalRule4bReferenceCountPriority
        (frameSlotKey input c frame derived index).prior.references := by
  have priorBuilt : input.certified.buildLocalizedRerootCompoundRule4bcKey?
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (actualPhysicalView input c)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (frame.cursorAt index) = some (frameSlotKey input c frame derived index).prior :=
    (buildLocalizedRerootCompoundRule45Key?_prior_built input.certified
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (actualPhysicalView input c)
      (localizedOccurrenceRerootEvaluationFuel
        (LocalizedUniversalReference.carrierFuel input))
      (frame.cursorAt index)
      (frameSlotKey input c frame derived index)
      (frameSlotKey_built input c frame derived index)).1
  exact (input.certified.buildLocalizedRerootCompoundRule4bcKey?_sound
    (ActualReaderPhysicalBranchInverse.topTarget input c)
    (actualPhysicalView input c)
    (localizedOccurrenceRerootEvaluationFuel
      (LocalizedUniversalReference.carrierFuel input))
    (frame.cursorAt index)
    (frameSlotKey input c frame derived index).prior priorBuilt).2.2.1

/-! ## Empty/empty prior ties are physical proper transports -/











theorem actualFrame_empty_priorTie_properTransport
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slotSpec : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c (alpha index)))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame)
    (left right : Fin 4) (different : left ≠ right)
    (leftReferences : (frameSlotKey input c frame derived left).prior.references = [])
    (rightReferences : (frameSlotKey input c frame derived right).prior.references = [])
    (priorTie : input.certified.compareLocalizedRerootCompoundRule4bcKeys
      (frameSlotKey input c frame derived left).prior
      (frameSlotKey input c frame derived right).prior = Ordering.eq) :
    RootedTetrahedralBranchSymmetry.ProperTransport
      input.certified.detectedMultiCenterMolecule cfg c (alpha left) (alpha right) := by
  classical
  let fuel := localizedOccurrenceRerootEvaluationFuel
    (LocalizedUniversalReference.carrierFuel input)
  -- Actual production compound Rules-4b/4c builds of both slot priors.
  have leftPriorBuilt : input.certified.buildLocalizedRerootCompoundRule4bcKey?
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (actualPhysicalView input c) fuel (frame.cursorAt left) =
      some (frameSlotKey input c frame derived left).prior :=
    (buildLocalizedRerootCompoundRule45Key?_prior_built input.certified
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (actualPhysicalView input c) fuel (frame.cursorAt left)
      (frameSlotKey input c frame derived left)
      (frameSlotKey_built input c frame derived left)).1
  have rightPriorBuilt : input.certified.buildLocalizedRerootCompoundRule4bcKey?
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (actualPhysicalView input c) fuel (frame.cursorAt right) =
      some (frameSlotKey input c frame derived right).prior :=
    (buildLocalizedRerootCompoundRule45Key?_prior_built input.certified
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (actualPhysicalView input c) fuel (frame.cursorAt right)
      (frameSlotKey input c frame derived right)
      (frameSlotKey_built input c frame derived right)).1
  -- The generated dependency reader is sparse in the global physical domain.
  have readerSparse : ∀ cursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input),
      LocalizedRule4bSparseLabel
        (input.certified.localizedDependencyLabel
          (ActualReaderPhysicalBranchInverse.topTarget input c)
          (actualPhysicalView input c) cursor) := by
    intro cursor
    simpa [ActualReaderPhysicalBranchInverse.dependencyReader, actualPhysicalView] using
      actualDependencyReader_sparse input singleBonded acyclic noDouble cfg c domain cursor
  -- Empty references force all actual Rule-4a labels to be `none`.
  have leftAllNone : LocalizedLabelLayersAllNone
      (frameSlotKey input c frame derived left).prior.rule4aKey.labels :=
    input.certified.buildLocalizedRerootCompoundRule4bcKey?_rule4aKey_labels_allNone_of_references_eq_nil
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (actualPhysicalView input c) fuel (frame.cursorAt left)
      (frameSlotKey input c frame derived left).prior leftPriorBuilt readerSparse
      leftReferences
  have rightAllNone : LocalizedLabelLayersAllNone
      (frameSlotKey input c frame derived right).prior.rule4aKey.labels :=
    input.certified.buildLocalizedRerootCompoundRule4bcKey?_rule4aKey_labels_allNone_of_references_eq_nil
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (actualPhysicalView input c) fuel (frame.cursorAt right)
      (frameSlotKey input c frame derived right).prior rightPriorBuilt readerSparse
      rightReferences
  -- The Rule-4a half of the prior tie.
  have rule4aTie : input.certified.compareLocalizedRerootCumulativeRule45Keys
      (frameSlotKey input c frame derived left).prior.rule4aKey
      (frameSlotKey input c frame derived right).prior.rule4aKey = Ordering.eq :=
    ((input.certified.compareLocalizedRerootCompoundRule4bcKeys_eq_eq_iff
      (frameSlotKey input c frame derived left).prior
      (frameSlotKey input c frame derived right).prior).mp priorTie).1
  -- Actual realised trees of the Rule-4a builds, at the generated dependency reader.
  have leftRule4aWithRead :
      input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
        (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel
        (frame.cursorAt left) =
      some (frameSlotKey input c frame derived left).prior.rule4aKey :=
    input.certified.buildLocalizedRerootCompoundRule45KeyWithRead?_prior_rule4aKey
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel
      (frame.cursorAt left) (frameSlotKey input c frame derived left)
      (frameSlotKey_withRead_built input c frame derived left)
  have rightRule4aWithRead :
      input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
        (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel
        (frame.cursorAt right) =
      some (frameSlotKey input c frame derived right).prior.rule4aKey :=
    input.certified.buildLocalizedRerootCompoundRule45KeyWithRead?_prior_rule4aKey
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel
      (frame.cursorAt right) (frameSlotKey input c frame derived right)
      (frameSlotKey_withRead_built input c frame derived right)
  obtain ⟨tL, tLsource, tLmatch, tLrealizes, _⟩ :=
    exists_decoratedTree_of_buildWithRead_fullMatch input.certified .rule4a
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel
      (frame.cursorAt left) (frameSlotKey input c frame derived left).prior.rule4aKey
      leftRule4aWithRead
  obtain ⟨tR, tRsource, tRmatch, tRrealizes, _⟩ :=
    exists_decoratedTree_of_buildWithRead_fullMatch input.certified .rule4a
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) fuel
      (frame.cursorAt right) (frameSlotKey input c frame derived right).prior.rule4aKey
      rightRule4aWithRead
  -- The Rule-4a tie is equality of the two actual tree tables, hence of the erased shapes.
  have tablesEq : tL.tables .rule4a = tR.tables .rule4a :=
    (compareLocalizedRerootCumulativeRule45Keys_eq_iff_treeTables_eq input.certified .rule4a
      (frameSlotKey input c frame derived left).prior.rule4aKey
      (frameSlotKey input c frame derived right).prior.rule4aKey
      tL tR tLmatch.tableMatch tRmatch.tableMatch).mp rule4aTie
  have hshape : LocalizedCumulativeDecoratedTree.shape tL =
      LocalizedCumulativeDecoratedTree.shape tR :=
    table_shape_eq_of_tables_eq .rule4a tL tR tablesEq
  -- The exact-label tables are all-`none`, so node labels agree under the identity mirror.
  have leftAllNoneTable : LocalizedLabelLayersAllNone tL.labelTable := by
    rw [labelTable_eq_labels_of_fullMatch tLmatch]
    exact leftAllNone
  have rightAllNoneTable : LocalizedLabelLayersAllNone tR.labelTable := by
    rw [labelTable_eq_labels_of_fullMatch tRmatch]
    exact rightAllNone
  have labelsSame : ∀ (path : List Nat)
      (nodeL nodeR : LocalizedCumulativeDecoratedTree input.certified
        (LocalizedUniversalReference.carrierFuel input)),
      subtreeAt? tL path = some nodeL →
        subtreeAt? tR path = some nodeR →
          nodeR.label = labelMirror false nodeL.label := by
    intro path nodeL nodeR foundL foundR
    rw [labelTable_allNone_node_label tL leftAllNoneTable path nodeL foundL,
      labelTable_allNone_node_label tR rightAllNoneTable path nodeR foundR]
    simp
  have sourceL : tL.source = frame.cursorAt (alpha.symm (alpha left)) := by
    rw [tLsource]
    rw [Equiv.symm_apply_apply]
  have sourceR : tR.source = frame.cursorAt (alpha.symm (alpha right)) := by
    rw [tRsource]
    rw [Equiv.symm_apply_apply]
  have hij : alpha left ≠ alpha right :=
    fun equality => different (alpha.injective equality)
  exact ActualReaderPhysicalBranchInverse.actualReaderPhysicalBranchTransport
    input noDouble singleBonded acyclic charge cfg c (alpha left) (alpha right) hij
    domain frame alpha frameComputed slotSpec tL tR sourceL sourceR tLrealizes tRrealizes
    hshape false labelsSame

/-! ## Mixed empty/singleton prior ties are impossible -/

/-- **Empty left against singleton right: the actual prior cannot tie.**  The compound
Rules-4b/4c comparator compares the stored count priorities, which builder soundness identifies
with the constitutional priorities of the actual reference lists.  These are `0` for `[]` and `2`
for `[r]`, so the count gate is strict and the prior is not `eq`. -/
theorem actualFrame_empty_left_singleton_right_prior_notTie
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame)
    (left right : Fin 4) (rightReference : RS)
    (leftReferences : (frameSlotKey input c frame derived left).prior.references = [])
    (rightReferences : (frameSlotKey input c frame derived right).prior.references =
      [rightReference]) :
    input.certified.compareLocalizedRerootCompoundRule4bcKeys
      (frameSlotKey input c frame derived left).prior
      (frameSlotKey input c frame derived right).prior ≠ Ordering.eq := by
  intro priorTie
  have countTie : compare
      (frameSlotKey input c frame derived left).prior.referenceCountPriority
      (frameSlotKey input c frame derived right).prior.referenceCountPriority =
      Ordering.eq :=
    ((input.certified.compareLocalizedRerootCompoundRule4bcKeys_eq_eq_iff
      (frameSlotKey input c frame derived left).prior
      (frameSlotKey input c frame derived right).prior).mp priorTie).2.1
  rw [frameSlotKey_prior_referenceCountPriority input c frame derived left,
    frameSlotKey_prior_referenceCountPriority input c frame derived right,
    leftReferences, rightReferences] at countTie
  simp [constitutionalRule4bReferenceCountPriority] at countTie

/-- **Singleton left against empty right: the actual prior cannot tie.**  The mirrored
orientation of `actualFrame_empty_left_singleton_right_prior_notTie`; the count gate compares `2`
with `0`, which is `gt`, never `eq`. -/
theorem actualFrame_singleton_left_empty_right_prior_notTie
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame)
    (left right : Fin 4) (leftReference : RS)
    (leftReferences : (frameSlotKey input c frame derived left).prior.references =
      [leftReference])
    (rightReferences : (frameSlotKey input c frame derived right).prior.references = []) :
    input.certified.compareLocalizedRerootCompoundRule4bcKeys
      (frameSlotKey input c frame derived left).prior
      (frameSlotKey input c frame derived right).prior ≠ Ordering.eq := by
  intro priorTie
  have countTie : compare
      (frameSlotKey input c frame derived left).prior.referenceCountPriority
      (frameSlotKey input c frame derived right).prior.referenceCountPriority =
      Ordering.eq :=
    ((input.certified.compareLocalizedRerootCompoundRule4bcKeys_eq_eq_iff
      (frameSlotKey input c frame derived left).prior
      (frameSlotKey input c frame derived right).prior).mp priorTie).2.1
  rw [frameSlotKey_prior_referenceCountPriority input c frame derived left,
    frameSlotKey_prior_referenceCountPriority input c frame derived right,
    leftReferences, rightReferences] at countTie
  simp [constitutionalRule4bReferenceCountPriority] at countTie

/-! ## Zero-or-one selections with a tied prior are both singleton -/

/-- **Zero-or-one classification of a tied actual prior.**  If every actual slot key has either
no own reference or exactly one, and the priors of two distinct slots tie, then both selections
are singleton.  The empty/empty case is excluded by physical root proper-distinguishability (it
would build a proper transport), and the mixed cases are excluded by the count gate. -/
theorem actualFrame_zeroOrOne_priorTie_singletons
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (distinct : ∀ i j : Fin 4, i ≠ j →
      ¬ RootedTetrahedralBranchSymmetry.ProperTransport
        input.certified.detectedMultiCenterMolecule cfg c i j)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slotSpec : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c (alpha index)))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame)
    (left right : Fin 4) (different : left ≠ right)
    (zeroOrOne : ∀ index : Fin 4,
      (frameSlotKey input c frame derived index).prior.references = [] ∨
        ∃ reference : RS,
          (frameSlotKey input c frame derived index).prior.references = [reference])
    (priorTie : input.certified.compareLocalizedRerootCompoundRule4bcKeys
      (frameSlotKey input c frame derived left).prior
      (frameSlotKey input c frame derived right).prior = Ordering.eq) :
    (∃ leftReference : RS,
        (frameSlotKey input c frame derived left).prior.references = [leftReference]) ∧
      (∃ rightReference : RS,
        (frameSlotKey input c frame derived right).prior.references = [rightReference]) := by
  have hij : alpha left ≠ alpha right :=
    fun equality => different (alpha.injective equality)
  constructor
  · rcases zeroOrOne left with leftEmpty | leftSingleton
    · rcases zeroOrOne right with rightEmpty | rightSingleton
      · exfalso
        exact distinct (alpha left) (alpha right) hij
          (actualFrame_empty_priorTie_properTransport input noDouble singleBonded acyclic
            charge cfg c domain frame alpha frameComputed slotSpec derived left right
            different leftEmpty rightEmpty priorTie)
      · exfalso
        obtain ⟨rightReference, rightReferences⟩ := rightSingleton
        exact absurd priorTie
          (actualFrame_empty_left_singleton_right_prior_notTie input c frame derived
            left right rightReference leftEmpty rightReferences)
    · exact leftSingleton
  · rcases zeroOrOne right with rightEmpty | rightSingleton
    · rcases zeroOrOne left with leftEmpty | leftSingleton
      · exfalso
        exact distinct (alpha left) (alpha right) hij
          (actualFrame_empty_priorTie_properTransport input noDouble singleBonded acyclic
            charge cfg c domain frame alpha frameComputed slotSpec derived left right
            different leftEmpty rightEmpty priorTie)
      · exfalso
        obtain ⟨leftReference, leftReferences⟩ := leftSingleton
        exact absurd priorTie
          (actualFrame_singleton_left_empty_right_prior_notTie input c frame derived
            left right leftReference leftReferences rightEmpty)
    · exact rightSingleton

/-! ## The final zero-or-one enantiomorphism theorem -/












theorem actualFrame_zeroOrOne_priorTie_enantiomorphic_of_physicalDistinct
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge
      input.certified.moleculeGraph)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (distinct : ∀ i j : Fin 4, i ≠ j →
      ¬ RootedTetrahedralBranchSymmetry.ProperTransport
        input.certified.detectedMultiCenterMolecule cfg c i j)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slotSpec : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c (alpha index)))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame)
    (left right : Fin 4) (different : left ≠ right)
    (zeroOrOne : ∀ index : Fin 4,
      (frameSlotKey input c frame derived index).prior.references = [] ∨
        ∃ reference : RS,
          (frameSlotKey input c frame derived index).prior.references = [reference])
    (priorTie : input.certified.compareLocalizedRerootCompoundRule4bcKeys
      (frameSlotKey input c frame derived left).prior
      (frameSlotKey input c frame derived right).prior = Ordering.eq) :
    RootedTetrahedralBranchSymmetry.Enantiomorphic
      input.certified.detectedMultiCenterMolecule cfg c (alpha left) (alpha right) := by
  obtain ⟨leftSingleton, rightSingleton⟩ :=
    actualFrame_zeroOrOne_priorTie_singletons input noDouble singleBonded acyclic charge cfg c
      domain distinct frame alpha frameComputed slotSpec derived left right different zeroOrOne
      priorTie
  obtain ⟨leftReference, leftReferences⟩ := leftSingleton
  obtain ⟨rightReference, rightReferences⟩ := rightSingleton
  exact actualFrame_singleton_priorTie_enantiomorphic_of_physicalDistinct input noDouble
    singleBonded acyclic charge cfg c domain distinct frame alpha frameComputed slotSpec
    derived left right different leftReference rightReference leftReferences rightReferences
    priorTie

end LocalizedEmptyReferencePhysicalPriorInverse

/-! ## Kernel-authority guards -/

assert_kernel_only
  TetraStereo.OneCenter.LocalizedEmptyReferencePhysicalPriorInverse.localizedLabelLayersAllNone_tail
assert_kernel_only
  TetraStereo.OneCenter.LocalizedEmptyReferencePhysicalPriorInverse.localizedLabelLayersAllNone_takeWhile
assert_kernel_only
  TetraStereo.OneCenter.LocalizedEmptyReferencePhysicalPriorInverse.localizedLabelLayersAllNone_dropAddressHeadLayer
assert_kernel_only
  TetraStereo.OneCenter.LocalizedEmptyReferencePhysicalPriorInverse.localizedLabelLayersAllNone_entriesAtSlot
assert_kernel_only
  TetraStereo.OneCenter.LocalizedEmptyReferencePhysicalPriorInverse.localizedLabelLayersAllNone_normalizedChildTable
assert_kernel_only
  TetraStereo.OneCenter.LocalizedEmptyReferencePhysicalPriorInverse.exists_mem_layer_of_getD_zero_eq_singleton
assert_kernel_only
  TetraStereo.OneCenter.LocalizedEmptyReferencePhysicalPriorInverse.labelTable_allNone_node_label
assert_kernel_only
  TetraStereo.OneCenter.LocalizedEmptyReferencePhysicalPriorInverse.frameSlotKey_prior_referenceCountPriority
assert_kernel_only
  TetraStereo.OneCenter.LocalizedEmptyReferencePhysicalPriorInverse.actualFrame_empty_priorTie_properTransport
assert_kernel_only
  TetraStereo.OneCenter.LocalizedEmptyReferencePhysicalPriorInverse.actualFrame_empty_left_singleton_right_prior_notTie
assert_kernel_only
  TetraStereo.OneCenter.LocalizedEmptyReferencePhysicalPriorInverse.actualFrame_singleton_left_empty_right_prior_notTie
assert_kernel_only
  TetraStereo.OneCenter.LocalizedEmptyReferencePhysicalPriorInverse.actualFrame_zeroOrOne_priorTie_singletons
assert_kernel_only
  TetraStereo.OneCenter.LocalizedEmptyReferencePhysicalPriorInverse.actualFrame_zeroOrOne_priorTie_enantiomorphic_of_physicalDistinct

end TetraStereo.OneCenter
