import TetraStereo.OneCenter.LocalizedPhysicalNearestRule4bReference
import TetraStereo.OneCenter.LocalizedCumulativeKeyObservableOrder
import TetraStereo.OneCenter.Rule4c5SparseSourceDecisionFidelity
import TetraStereo.OneCenter.LocalizedRule5SwapAndSignal
import TetraStereo.OneCenter.LocalizedActualPhysicalReferenceSelection
import TetraStereo.OneCenter.LocalizedAcyclicCarrierInjectivity
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput

























































































namespace LocalizedUniqueNearestRule5Direction

/-! ## A. Observation plumbing -/

/-- Mapping a decoration through a function commutes with flat-mapping a list of blocks. -/
private theorem flatMap_map_eq_map_flatMap {α β γ : Type*}
    (values : List α) (blocks : α → List β) (map : β → γ) :
    values.flatMap (fun value => (blocks value).map map) =
      (values.flatMap blocks).map map := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.flatMap_cons, List.map_append, inductionHypothesis]

/-- The stage priority observation at one tree depth is the priority vector of the label
observation at that depth, in the same left-to-right order. -/
theorem observationsAtDepth_priority
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage) (depth : Nat)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) :
    LocalizedCumulativeDecoratedTree.observationsAtDepth
        (fun node => localizedCumulativeRule45Priority stage node.label) depth tree =
      (LocalizedCumulativeDecoratedTree.observationsAtDepth
        (fun node => node.label) depth tree).map
        (localizedCumulativeRule45Priority stage) := by
  induction depth generalizing tree with
  | zero => rfl
  | succ depth inductionHypothesis =>
      simp only [LocalizedCumulativeDecoratedTree.observationsAtDepth]
      rw [List.flatMap_congr (fun child _ => inductionHypothesis child)]
      exact flatMap_map_eq_map_flatMap tree.children
        (fun child => LocalizedCumulativeDecoratedTree.observationsAtDepth
          (fun node => node.label) depth child)
        (localizedCumulativeRule45Priority stage)

/-- The value projection of a descriptor table sphere is the priority observation list at that
depth. -/
theorem descriptorTable_getD_map_snd
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel) (depth : Nat) :
    ((LocalizedCumulativeDecoratedTree.table
        (fun node => localizedCumulativeRule45Priority stage node.label) tree).getD depth []).map
        Prod.snd =
      (LocalizedCumulativeDecoratedTree.observationsAtDepth
        (fun node => node.label) depth tree).map
        (localizedCumulativeRule45Priority stage) := by
  rw [LocalizedCumulativeDecoratedTree.table_getD_map_snd, observationsAtDepth_priority]

/-! ## B. The final Rule-5 component of an actual cumulative vector -/

/-- The last component of an actual cumulative priority vector.  For every stage carrying a
Rule-5 component this is exactly the Rule-5 bit
(`stageFinalRule5Value_eq_of_probe`); the definition is deliberately total so that the
component sum below is available for both stages of a pair. -/
def stageFinalRule5Value (stage : LocalizedCumulativeRule45Stage)
    (label : Option LocalizedAuxiliaryLabel) : Nat :=
  (localizedCumulativeRule45Priority stage label).reverse.headD 0

/-- Unfolding equation for `stageFinalRule5Value`. -/
theorem stageFinalRule5Value_def (stage : LocalizedCumulativeRule45Stage)
    (label : Option LocalizedAuxiliaryLabel) :
    stageFinalRule5Value stage label =
      (localizedCumulativeRule45Priority stage label).reverse.headD 0 := rfl

/-- In every stage that actually carries a Rule-5 probe, the final cumulative component is that
probe's Rule-5 bit. -/
theorem stageFinalRule5Value_eq_of_probe
    (stage : LocalizedCumulativeRule45Stage) (probe : RS)
    (probeEq : Rule4c5SourceDecision.stageRule5Probe? stage = some probe)
    (label : Option LocalizedAuxiliaryLabel) :
    stageFinalRule5Value stage label = localizedRule5Priority probe label := by
  rw [stageFinalRule5Value_def,
    Rule4c5SourceDecision.cumulativePriority_eq_prefix_append_rule5 stage probe probeEq label]
  simp

/-- Reassociating the final-component map as a map of the priority vectors. -/
private theorem map_stageFinalRule5Value_eq
    (stage : LocalizedCumulativeRule45Stage)
    (labels : List (Option LocalizedAuxiliaryLabel)) :
    labels.map (stageFinalRule5Value stage) =
      (labels.map (localizedCumulativeRule45Priority stage)).map
        (fun vector : List Nat => vector.reverse.headD 0) := by
  rw [List.map_map]
  rfl

/-- Equal lists of actual cumulative priority vectors have equal sums of their final Rule-5
components.  This is the permutation-invariant observable used below: it never mentions an
address or a sibling order. -/
theorem sum_stageFinalRule5Value_eq_of_map_eq
    {stageL stageR : LocalizedCumulativeRule45Stage}
    {labelsL labelsR : List (Option LocalizedAuxiliaryLabel)}
    (vectorsEq : labelsL.map (localizedCumulativeRule45Priority stageL) =
      labelsR.map (localizedCumulativeRule45Priority stageR)) :
    (labelsL.map (stageFinalRule5Value stageL)).sum =
      (labelsR.map (stageFinalRule5Value stageR)).sum := by
  rw [map_stageFinalRule5Value_eq, map_stageFinalRule5Value_eq, vectorsEq]

/-- Sum of the Rule-5 bits of a list of labels under one probe reference. -/
def rule5BitSum (probe : RS) (labels : List (Option LocalizedAuxiliaryLabel)) : Nat :=
  (labels.map (localizedRule5Priority probe)).sum

/-- The Rule-5 bit sum only counts uppercase chiral observations; every other label contributes
zero. -/
theorem rule5BitSum_eq_chiralDescriptors_sum (probe : RS)
    (labels : List (Option LocalizedAuxiliaryLabel)) :
    rule5BitSum probe labels =
      ((LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations labels).map
        (fun descriptor => if descriptor == probe then 1 else 0)).sum := by
  -- The `==` spelling is kept so that the induction hypothesis rewrites syntactically.
  induction labels with
  | nil => rfl
  | cons head rest inductionHypothesis =>
      cases head with
      | none =>
          simpa [rule5BitSum, localizedRule5Priority,
            LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations]
            using inductionHypothesis
      | some label =>
          cases label with
          | pseudoasymmetric descriptor =>
              simpa [rule5BitSum, localizedRule5Priority,
                LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations]
                using inductionHypothesis
          | chiral descriptor =>
              simp only [rule5BitSum, List.map_cons, List.sum_cons, localizedRule5Priority,
                LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations]
              change (if descriptor == probe then 1 else 0) + rule5BitSum probe rest =
                (if descriptor == probe then 1 else 0) +
                  ((LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations rest).map
                    (fun descriptor => if descriptor == probe then 1 else 0)).sum
              rw [inductionHypothesis]

/-- A unique chiral descriptor at one depth fixes the Rule-5 bit sum of the whole sphere to that
descriptor's like/unlike bit. -/
theorem rule5BitSum_eq_bit_of_chiralDescriptors_singleton
    (probe descriptor : RS) (labels : List (Option LocalizedAuxiliaryLabel))
    (unique : LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations labels =
      [descriptor]) :
    rule5BitSum probe labels = if descriptor == probe then 1 else 0 := by
  rw [rule5BitSum_eq_chiralDescriptors_sum, unique]
  simp

/-- With the same unique chiral descriptor at the observed depth, the common-`R` bit sum and the
common-`S` bit sum differ.  This is the entire content of the strictness argument, and it holds
irrespective of the remaining labels and of their sibling order.  Note that the depth sphere is
**not** assumed to be a single table entry: other `none`/pseudoasymmetric observations remain,
and they only contribute zero to the sum. -/
theorem rule5BitSum_R_ne_S_of_same_chiral
    (labelsR labelsS : List (Option LocalizedAuxiliaryLabel)) (descriptor : RS)
    (uniqueR : LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations labelsR =
      [descriptor])
    (uniqueS : LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations labelsS =
      [descriptor]) :
    rule5BitSum .R labelsR ≠ rule5BitSum .S labelsS := by
  rw [rule5BitSum_eq_bit_of_chiralDescriptors_singleton .R descriptor labelsR uniqueR,
    rule5BitSum_eq_bit_of_chiralDescriptors_singleton .S descriptor labelsS uniqueS]
  cases descriptor <;> decide

/-! ## C. Stage pairing at a unique nearest centre -/

/-- The two common-reference stages selected for the same ligand's own Rule-4b reference have
the same earlier-priority prefix; they differ only in the Rule-5 probe. -/
theorem stagePriorityPrefix_stageFor_eq
    (own : Option RS) (probeR probeS : RS)
    (label : Option LocalizedAuxiliaryLabel) :
    Rule4c5SourceDecision.stagePriorityPrefix
        (localizedRule5StageFor own probeR) label =
      Rule4c5SourceDecision.stagePriorityPrefix
        (localizedRule5StageFor own probeS) label := by
  cases own <;> rfl

/-- The two stages selected for one ligand are both Rule-5 stages, with probes `R` and `S`. -/
theorem stageRule5Probe_stageFor_R (own : Option RS) :
    Rule4c5SourceDecision.stageRule5Probe? (localizedRule5StageFor own .R) = some .R := by
  cases own <;> rfl

theorem stageRule5Probe_stageFor_S (own : Option RS) :
    Rule4c5SourceDecision.stageRule5Probe? (localizedRule5StageFor own .S) = some .S := by
  cases own <;> rfl

/-- **Signed one-observation direction.**  At a single shared address, the same uppercase chiral
descriptor read under the common-`R` stage is strictly senior to its common-`S` reading: a
descriptor `R` gives `gt`, an `S` gives `lt`.  The earlier-priority tie is derived from the
stage pairing, not assumed. -/
theorem comparePriority_stageFor_R_S_chiral
    (own : Option RS) (descriptor : RS) :
    compareLocalizedCumulativeRule45Priority
        (localizedCumulativeRule45Priority (localizedRule5StageFor own .R)
          (some (.chiral descriptor)))
        (localizedCumulativeRule45Priority (localizedRule5StageFor own .S)
          (some (.chiral descriptor))) =
      if descriptor = RS.R then Ordering.gt else Ordering.lt := by
  have prefixEq := stagePriorityPrefix_stageFor_eq own .R .S (some (.chiral descriptor))
  rw [Rule4c5SourceDecision.cumulativePriority_eq_prefix_append_rule5
        (localizedRule5StageFor own .R) .R (stageRule5Probe_stageFor_R own)
        (some (.chiral descriptor)),
    Rule4c5SourceDecision.cumulativePriority_eq_prefix_append_rule5
        (localizedRule5StageFor own .S) .S (stageRule5Probe_stageFor_S own)
        (some (.chiral descriptor)),
    ← prefixEq]
  unfold compareLocalizedCumulativeRule45Priority
  rw [Rule4c5SourceDecision.compareLex_compareNat_append_singleton]
  cases descriptor <;> rfl

/-- The absolute `R`-over-`S` orientation at one shared address, for every selection of the
ligand's own Rule-4b reference. -/
theorem comparePriority_stageFor_R_S_chiral_R (own : Option RS) :
    compareLocalizedCumulativeRule45Priority
        (localizedCumulativeRule45Priority (localizedRule5StageFor own .R)
          (some (.chiral .R)))
        (localizedCumulativeRule45Priority (localizedRule5StageFor own .S)
          (some (.chiral .R))) = Ordering.gt := by
  rw [comparePriority_stageFor_R_S_chiral]
  rfl

/-- The sparse addressed form of the signed one-observation direction: one shared address, one
observed uppercase `R` label, common-`R` stage versus common-`S` stage, gives `gt`. -/
theorem compareSparseLayers_stageFor_R_S_chiral_R
    (own : Option RS) (address : List Nat) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        (Rule4c5SourceDecision.actualStageObservation (localizedRule5StageFor own .R)
          address (some (.chiral .R)))
        (Rule4c5SourceDecision.actualStageObservation (localizedRule5StageFor own .S)
          address (some (.chiral .R))) = Ordering.gt := by
  unfold Rule4c5SourceDecision.actualStageObservation
  rw [Rule4c5SourceDecision.compareSparseLayers_liftSparseObservation,
    Rule4c5SourceDecision.sourcePathDecision_self]
  exact comparePriority_stageFor_R_S_chiral_R own

/-! ## D. Full descriptor-table strictness at a unique nearest depth -/

/-- **Strict descriptor-table difference from one unique chiral depth.**

The two descriptor tables use the two common-reference stages.  If each tree has a unique chiral
label `descriptor` at the same tree depth (and that is the only chiral observation used), then
the two compiled descriptor tables are different.  No address stability, no shared skeleton and
no sibling-order alignment is assumed: the argument projects to the permutation-invariant value
list at that depth.  Other `none` entries in the same row are irrelevant to the sum. -/
theorem descriptor_ne_of_unique_chiral_at_depth
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (stageR stageS : LocalizedCumulativeRule45Stage)
    (probeEqR : Rule4c5SourceDecision.stageRule5Probe? stageR = some .R)
    (probeEqS : Rule4c5SourceDecision.stageRule5Probe? stageS = some .S)
    (treeR treeS : LocalizedCumulativeDecoratedTree input carrierFuel)
    (depth : Nat) (descriptor : RS)
    (uniqueR : LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
      (LocalizedCumulativeDecoratedTree.observationsAtDepth
        (fun node => node.label) depth treeR) = [descriptor])
    (uniqueS : LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
      (LocalizedCumulativeDecoratedTree.observationsAtDepth
        (fun node => node.label) depth treeS) = [descriptor]) :
    LocalizedCumulativeDecoratedTree.table
        (fun node => localizedCumulativeRule45Priority stageR node.label) treeR ≠
      LocalizedCumulativeDecoratedTree.table
        (fun node => localizedCumulativeRule45Priority stageS node.label) treeS := by
  intro tablesEq
  have rowsEq :
      ((LocalizedCumulativeDecoratedTree.table
          (fun node => localizedCumulativeRule45Priority stageR node.label) treeR).getD
            depth []).map Prod.snd =
        ((LocalizedCumulativeDecoratedTree.table
          (fun node => localizedCumulativeRule45Priority stageS node.label) treeS).getD
            depth []).map Prod.snd := by
    rw [tablesEq]
  rw [descriptorTable_getD_map_snd, descriptorTable_getD_map_snd] at rowsEq
  have sumsEq := sum_stageFinalRule5Value_eq_of_map_eq rowsEq
  have leftEq :
      ((LocalizedCumulativeDecoratedTree.observationsAtDepth
          (fun node => node.label) depth treeR).map
            (stageFinalRule5Value stageR)).sum =
        rule5BitSum .R
          (LocalizedCumulativeDecoratedTree.observationsAtDepth
            (fun node => node.label) depth treeR) := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro label _
    exact stageFinalRule5Value_eq_of_probe stageR .R probeEqR label
  have rightEq :
      ((LocalizedCumulativeDecoratedTree.observationsAtDepth
          (fun node => node.label) depth treeS).map
            (stageFinalRule5Value stageS)).sum =
        rule5BitSum .S
          (LocalizedCumulativeDecoratedTree.observationsAtDepth
            (fun node => node.label) depth treeS) := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro label _
    exact stageFinalRule5Value_eq_of_probe stageS .S probeEqS label
  rw [leftEq, rightEq] at sumsEq
  exact rule5BitSum_R_ne_S_of_same_chiral
    (LocalizedCumulativeDecoratedTree.observationsAtDepth (fun node => node.label) depth treeR)
    (LocalizedCumulativeDecoratedTree.observationsAtDepth (fun node => node.label) depth treeS)
    descriptor uniqueR uniqueS sumsEq

/-- The same strict difference at the level of the actual compiled keys, transported through
the actual tree/table match of the production builder. -/
theorem key_descriptor_ne_of_unique_chiral_at_depth
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (stageR stageS : LocalizedCumulativeRule45Stage)
    (probeEqR : Rule4c5SourceDecision.stageRule5Probe? stageR = some .R)
    (probeEqS : Rule4c5SourceDecision.stageRule5Probe? stageS = some .S)
    (treeR treeS : LocalizedCumulativeDecoratedTree input carrierFuel)
    (keyR keyS : input.LocalizedRerootCumulativeRule45Key)
    (tableMatchR : LocalizedCumulativeTreeTableMatch stageR treeR keyR)
    (tableMatchS : LocalizedCumulativeTreeTableMatch stageS treeS keyS)
    (depth : Nat) (descriptor : RS)
    (uniqueR : LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
      (LocalizedCumulativeDecoratedTree.observationsAtDepth
        (fun node => node.label) depth treeR) = [descriptor])
    (uniqueS : LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
      (LocalizedCumulativeDecoratedTree.observationsAtDepth
        (fun node => node.label) depth treeS) = [descriptor]) :
    keyR.descriptor ≠ keyS.descriptor := by
  intro descriptorsEq
  refine descriptor_ne_of_unique_chiral_at_depth stageR stageS probeEqR probeEqS treeR treeS
    depth descriptor uniqueR uniqueS ?_
  show (treeR.tables stageR).descriptor = (treeS.tables stageS).descriptor
  rw [tableMatchR.2.2.2, tableMatchS.2.2.2, descriptorsEq]

/-! ## E. The derived actual read mark

The mark below is *not* a hypothesis.  It is computed from the actual final reference state at
the unique actual position that carries the atom.  The reader correspondence is proved from the
actual realization of the generated dependency reader.  This is exactly the repair of the
former binder, which quantified over all decorated trees with the same source and was therefore
inconsistent (a decorated root label is free). -/

/-- The actual read mark of an actually realized production tree.  At an atom of the tree it is
the upper-case chiral descriptor of the actual final reference state at the actual position
source; atoms with no position are unmarked. -/
noncomputable def actualTreeMark
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (tree : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input))
    (atom : input.certified.Atom) : Option RS := by
  classical
  exact
    if hex : ∃ p : Position tree, positionAtom singleBonded acyclic p = atom then
      chiralDescriptorOfLabel
        (LocalizedUniversalReference.referenceState input
          (positionSource (Classical.choose hex)).occurrence)
    else none

/-- The source facts of a realized tree at an actual frame cursor.  These are derived from the
frame, not assumed. -/
theorem actualTree_previousEq_of_source
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    {tree : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input)}
    (sourceEq : tree.source = frame.cursorAt slot) :
    tree.source.previous? = some (ActualReaderPhysicalBranchInverse.topTarget input c) := by
  rw [sourceEq]
  exact input.certified.localizedOccurrenceFourLigandFrame_cursor_previous
    (ActualReaderPhysicalBranchInverse.topTarget input c) frame frameComputed
    (frame.cursorAt slot) (List.get_mem frame.cursors _)

/-- A realized tree at an actual frame cursor keeps the final root. -/
theorem actualTree_sameRoot_of_source
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    {tree : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input)}
    (sourceEq : tree.source = frame.cursorAt slot) :
    tree.source.occurrence.1.root =
      (ActualReaderPhysicalBranchInverse.topTarget input c).1.root := by
  rw [sourceEq]
  exact input.certified.localizedOccurrenceFourLigandFrame_cursor_root
    (ActualReaderPhysicalBranchInverse.topTarget input c) frame frameComputed
    (frame.cursorAt slot) (List.get_mem frame.cursors _)

/-- A realized tree at an actual frame cursor is path-valid. -/
theorem actualTree_valid_of_source
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    {tree : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input)}
    (sourceEq : tree.source = frame.cursorAt slot) :
    input.certified.LocalizedRerootCursorValid tree.source := by
  rw [sourceEq]
  exact input.certified.localizedOccurrenceFourLigandFrame_cursor_valid
    (ActualReaderPhysicalBranchInverse.topTarget input c) frame frameComputed
    (frame.cursorAt slot) (List.get_mem frame.cursors _)

/-- A realized tree at an actual frame cursor is strictly deeper than the final target. -/
theorem actualTree_previousShorter_of_source
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    {tree : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input)}
    (sourceEq : tree.source = frame.cursorAt slot) :
    (ActualReaderPhysicalBranchInverse.topTarget input c).1.address.length <
      tree.source.occurrence.1.address.length := by
  rw [sourceEq]
  exact actualSlot_cursor_previousShorter input c frame frameComputed slot

/-- A realized tree at an actual frame cursor observes the slot atom. -/
theorem actualTree_oObserved_of_source
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (_frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    {tree : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input)}
    (sourceEq : tree.source = frame.cursorAt slot)
    {oAtom : input.certified.Atom}
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom) :
    tree.source.occurrence.1.node.current? = some oAtom := by
  rw [sourceEq]
  exact oObserved

/-- **Mark membership through an actual position.**  The derived mark is `some descriptor`
exactly when some actual position carries that atom and the actual reference state at that
position is the corresponding chiral label.  Position injectivity makes the choice in the
definition irrelevant. -/
theorem actualTreeMark_eq_some_iff
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    {tree : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input)}
    (realizes : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) tree)
    (previousEq : tree.source.previous? =
      some (ActualReaderPhysicalBranchInverse.topTarget input c))
    (sameRoot : tree.source.occurrence.1.root =
      (ActualReaderPhysicalBranchInverse.topTarget input c).1.root)
    {oAtom : input.certified.Atom}
    (oObserved : tree.source.occurrence.1.node.current? = some oAtom)
    (_incomingEdge : input.certified.moleculeGraph.Adj c.1 oAtom)
    (atom : input.certified.Atom) (descriptor : RS) :
    actualTreeMark input singleBonded acyclic tree atom = some descriptor ↔
      ∃ p : Position tree,
        positionAtom singleBonded acyclic p = atom ∧
          LocalizedUniversalReference.referenceState input
            (positionSource p).occurrence = some (.chiral descriptor) := by
  classical
  unfold actualTreeMark
  by_cases hex : ∃ p : Position tree, positionAtom singleBonded acyclic p = atom
  · rw [dif_pos hex]
    constructor
    · intro markSome
      exact ⟨Classical.choose hex, Classical.choose_spec hex,
        (chiralDescriptorOfLabel_eq_some_iff _ descriptor).mp markSome⟩
    · rintro ⟨p, pAtom, pState⟩
      have chooseEq : Classical.choose hex = p := by
        apply positionAtom_injective
          (input := input.certified)
          (carrierFuel := LocalizedUniversalReference.carrierFuel input)
          (read := ActualReaderPhysicalBranchInverse.dependencyReader input c)
          (tree := tree)
          (singleBonded := singleBonded)
          (acyclic := acyclic)
          (enough := globalCarrierFuel_adequate input)
          (realizes := realizes)
          (previous := ActualReaderPhysicalBranchInverse.topTarget input c)
          (previousEq := previousEq)
          (sameRoot := sameRoot)
          (oObserved := oObserved)
          (pObserved := ActualReaderPhysicalBranchInverse.topTarget_current input c)
        rw [Classical.choose_spec hex, pAtom]
      rw [chooseEq]
      exact (chiralDescriptorOfLabel_eq_some_iff _ descriptor).mpr pState
  · rw [dif_neg hex]
    constructor
    · intro markNone
      cases markNone
    · rintro ⟨p, pAtom, _⟩
      exact absurd ⟨p, pAtom⟩ hex

/-- **The derived reader correspondence.**  For every position of the actual realized tree, the
actual label is an upper-case chiral descriptor exactly when the derived actual mark of the
position's atom is that descriptor.  This is proved from the actual realization and the actual
whole reference state; it is not a supplied reader law. -/
theorem actualTreeMark_reader
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (_frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (_slot : Fin 4)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    {tree : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input)}
    (realizes : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) tree)
    (previousEq : tree.source.previous? =
      some (ActualReaderPhysicalBranchInverse.topTarget input c))
    (valid : input.certified.LocalizedRerootCursorValid tree.source)
    (previousShorter : (ActualReaderPhysicalBranchInverse.topTarget input c).1.address.length <
      tree.source.occurrence.1.address.length)
    (sameRoot : tree.source.occurrence.1.root =
      (ActualReaderPhysicalBranchInverse.topTarget input c).1.root)
    {oAtom : input.certified.Atom}
    (oObserved : tree.source.occurrence.1.node.current? = some oAtom)
    (incomingEdge : input.certified.moleculeGraph.Adj c.1 oAtom)
    (p : Position tree) (descriptor : RS) :
    (positionNode p).label = some (.chiral descriptor) ↔
      actualTreeMark input singleBonded acyclic tree
        (positionAtom singleBonded acyclic p) = some descriptor := by
  have realizesState : LocalizedCumulativeTreeRealizes input.certified
      (fun cursor => input.certified.localizedDependencyLabel
        (ActualReaderPhysicalBranchInverse.topTarget input c)
        (input.certified.localizedDependencyView
          (LocalizedUniversalReference.referenceState input)
          (ActualReaderPhysicalBranchInverse.topTarget input c)) cursor) tree := by
    simpa only [ActualReaderPhysicalBranchInverse.dependencyReader] using realizes
  have stateEq := positionNode_label_eq_state_of_outward
    (input := input.certified)
    (carrierFuel := LocalizedUniversalReference.carrierFuel input)
    (target := ActualReaderPhysicalBranchInverse.topTarget input c)
    (state := LocalizedUniversalReference.referenceState input)
    (tree := tree)
    (realizes := realizesState)
    (valid := valid)
    (previous := ActualReaderPhysicalBranchInverse.topTarget input c)
    (previousEq := previousEq)
    (previousShorter := previousShorter)
    (targetEq := rfl)
    (p := p)
  constructor
  · intro labelChiral
    have stateChiral : LocalizedUniversalReference.referenceState input
        (positionSource p).occurrence = some (.chiral descriptor) := by
      rw [← stateEq]
      exact labelChiral
    exact (actualTreeMark_eq_some_iff input c singleBonded acyclic realizes previousEq
      sameRoot oObserved incomingEdge (positionAtom singleBonded acyclic p) descriptor).mpr
      ⟨p, rfl, stateChiral⟩
  · intro markSome
    obtain ⟨q, qAtom, qState⟩ :=
      (actualTreeMark_eq_some_iff input c singleBonded acyclic realizes previousEq
        sameRoot oObserved incomingEdge (positionAtom singleBonded acyclic p) descriptor).mp
        markSome
    have qEq : q = p := positionAtom_injective
      (input := input.certified)
      (carrierFuel := LocalizedUniversalReference.carrierFuel input)
      (read := ActualReaderPhysicalBranchInverse.dependencyReader input c)
      (tree := tree)
      (singleBonded := singleBonded)
      (acyclic := acyclic)
      (enough := globalCarrierFuel_adequate input)
      (realizes := realizes)
      (previous := ActualReaderPhysicalBranchInverse.topTarget input c)
      (previousEq := previousEq)
      (sameRoot := sameRoot)
      (oObserved := oObserved)
      (pObserved := ActualReaderPhysicalBranchInverse.topTarget_current input c)
      (p := q) (q := p) (atomEq := qAtom)
    rw [qEq] at qState
    rw [stateEq, qState]




theorem physicalMarkedAtom_of_actualTreeMark_eq_some
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
    {atom : input.certified.Atom} {descriptor : RS}
    (mark : actualTreeMark input singleBonded acyclic tree atom = some descriptor) :
    PhysicalMarkedAtom input ⟨c.1, c.2⟩ atom := by
  have previousEq := actualTree_previousEq_of_source input c frame frameComputed slot sourceEq
  have sameRoot := actualTree_sameRoot_of_source input c frame frameComputed slot sourceEq
  have oObservedTree :=
    actualTree_oObserved_of_source input c frame frameComputed slot sourceEq oObserved
  obtain ⟨p, pAtom, pState⟩ :=
    (actualTreeMark_eq_some_iff input c singleBonded acyclic realizes previousEq sameRoot
      oObservedTree (actualSlot_incomingEdge input c frame frameComputed slot oObserved)
      atom descriptor).mp mark
  have treeRoot : tree.source.occurrence.1.root = c.1 := by
    rw [sameRoot, ActualReaderPhysicalBranchInverse.topTarget_root]
  have rootEq : (positionSource p).occurrence.1.root = c.1 := by
    rw [positionSource_root_eq_of_realized realizes p, treeRoot]
  rw [← pAtom]
  exact (referenceState_chiral_iff_physicalMarked input singleBonded acyclic hcharge noDouble
    cfg c domain
    (actualSlot_incomingEdge input c frame frameComputed slot oObserved)
    (positionSource p).occurrence rootEq
    (positionAtom_spec singleBonded acyclic p)
    (positionAtom_mem_cutBranch
      (input := input.certified)
      (carrierFuel := LocalizedUniversalReference.carrierFuel input)
      (read := ActualReaderPhysicalBranchInverse.dependencyReader input c)
      (tree := tree)
      (singleBonded := singleBonded)
      (acyclic := acyclic)
      (enough := globalCarrierFuel_adequate input)
      (realizes := realizes)
      (previous := ActualReaderPhysicalBranchInverse.topTarget input c)
      (previousEq := previousEq)
      (valid := actualTree_valid_of_source input c frame frameComputed slot sourceEq)
      (oObserved := oObservedTree)
      (pObserved := ActualReaderPhysicalBranchInverse.topTarget_current input c)
      (incomingEdge := actualSlot_incomingEdge input c frame frameComputed slot oObserved)
      (p := p))).mp ⟨descriptor, pState⟩



theorem actualTreeMark_center_eq_some_of_physicalMarked
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
    {center : input.certified.Atom}
    (centerMember : center ∈ AcyclicCutBranchAutomorphism.CutBranch
      input.certified.moleculeGraph c.1 oAtom)
    (centerMarked : PhysicalMarkedAtom input ⟨c.1, c.2⟩ center) :
    ∃ descriptor : RS,
      actualTreeMark input singleBonded acyclic tree center = some descriptor := by
  have previousEq := actualTree_previousEq_of_source input c frame frameComputed slot sourceEq
  have sameRoot := actualTree_sameRoot_of_source input c frame frameComputed slot sourceEq
  have valid := actualTree_valid_of_source input c frame frameComputed slot sourceEq
  have oObservedTree :=
    actualTree_oObserved_of_source input c frame frameComputed slot sourceEq oObserved
  obtain ⟨p, pAtom⟩ := exists_position_of_mem_cutBranch
    (input := input.certified)
    (carrierFuel := LocalizedUniversalReference.carrierFuel input)
    (read := ActualReaderPhysicalBranchInverse.dependencyReader input c)
    (tree := tree)
    singleBonded acyclic (globalCarrierFuel_adequate input) realizes
    (ActualReaderPhysicalBranchInverse.topTarget input c) previousEq valid sameRoot
    oObservedTree (ActualReaderPhysicalBranchInverse.topTarget_current input c)
    (actualSlot_incomingEdge input c frame frameComputed slot oObserved)
    centerMember
  have treeRoot : tree.source.occurrence.1.root = c.1 := by
    rw [sameRoot, ActualReaderPhysicalBranchInverse.topTarget_root]
  have rootEq : (positionSource p).occurrence.1.root = c.1 := by
    rw [positionSource_root_eq_of_realized realizes p, treeRoot]
  have targetCurrent : (positionSource p).occurrence.1.node.current? = some center := by
    rw [← pAtom]
    exact positionAtom_spec singleBonded acyclic p
  have aMem : center ∈ AcyclicCutBranchAutomorphism.CutBranch
      input.certified.moleculeGraph c.1 oAtom := by
    rw [← pAtom]
    exact positionAtom_mem_cutBranch
      (input := input.certified)
      (carrierFuel := LocalizedUniversalReference.carrierFuel input)
      (read := ActualReaderPhysicalBranchInverse.dependencyReader input c)
      (tree := tree)
      (singleBonded := singleBonded)
      (acyclic := acyclic)
      (enough := globalCarrierFuel_adequate input)
      (realizes := realizes)
      (previous := ActualReaderPhysicalBranchInverse.topTarget input c)
      (previousEq := previousEq)
      (valid := valid)
      (oObserved := oObservedTree)
      (pObserved := ActualReaderPhysicalBranchInverse.topTarget_current input c)
      (incomingEdge := actualSlot_incomingEdge input c frame frameComputed slot oObserved)
      (p := p)
  obtain ⟨descriptor, stateChiral⟩ :=
    (referenceState_chiral_iff_physicalMarked input singleBonded acyclic hcharge noDouble
      cfg c domain
      (actualSlot_incomingEdge input c frame frameComputed slot oObserved)
      (positionSource p).occurrence rootEq targetCurrent aMem).mpr centerMarked
  exact ⟨descriptor,
    (actualTreeMark_eq_some_iff input c singleBonded acyclic realizes previousEq sameRoot
      oObservedTree (actualSlot_incomingEdge input c frame frameComputed slot oObserved)
      center descriptor).mpr ⟨p, pAtom, stateChiral⟩⟩

/-! ## E2. The derived mark is determined by the stored root and the current atom

This is the missing identity connection.  The carrier injectivity theorem
`localizedCIPOccurrence_current_injective_at_fixedRoot` says that two actual carrier occurrences
at the same fuel with the same stored original root and the same physical `current?` atom are the
same occurrence.  Every position of an actual realized tree keeps the tree's own stored root, and
its `current?` atom is its `positionAtom`.  Consequently the reference state at a position — and
hence the derived mark — depends only on the stored root and the current atom, and the two
actual stage trees at one frame cursor have the **same** derived mark at the physical nearest
centre.  No sorted-address stability is needed anywhere in this module. -/

/-- **Carrier occurrence identity at a fixed stored root and current atom.**  Two actual positions
of actual decorated trees at the same carrier fuel whose sources have the same stored original
root and the same physical `current?` atom carry the same actual carrier occurrence.  This is
`localizedCIPOccurrence_current_injective_at_fixedRoot` read at the position coordinates. -/
theorem positionSource_occurrence_eq_of_current
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    {treeL treeR : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input)}
    (p : Position treeL) (q : Position treeR)
    (sameRoot : (positionSource p).occurrence.1.root =
      (positionSource q).occurrence.1.root)
    (sameCurrent : (positionSource p).occurrence.1.node.current? =
      (positionSource q).occurrence.1.node.current?) :
    (positionSource p).occurrence = (positionSource q).occurrence :=
  input.certified.localizedCIPOccurrence_current_injective_at_fixedRoot
    singleBonded acyclic (positionSource p).occurrence (positionSource q).occurrence
    sameRoot sameCurrent

/-- **The derived mark only reads the stored root and the current atom.**  If two actual positions
of two actual realized decorated trees carry the same physical atom and their sources have the
same stored original root and the same current atom, then the derived actual marks of that atom in
the two trees coincide.  Realization is used only to know that every position of a tree keeps the
root of the tree's own source; no reader law, address order or sibling alignment is used. -/
theorem actualTreeMark_eq_of_position
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    {readL readR : input.certified.LocalizedRerootCursor
        (LocalizedUniversalReference.carrierFuel input) → Option LocalizedAuxiliaryLabel}
    {treeL treeR : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input)}
    (realizesL : LocalizedCumulativeTreeRealizes input.certified readL treeL)
    (realizesR : LocalizedCumulativeTreeRealizes input.certified readR treeR)
    (treeRootEq : treeL.source.occurrence.1.root = treeR.source.occurrence.1.root)
    (p : Position treeL) (q : Position treeR)
    (atomEq : positionAtom singleBonded acyclic p =
      positionAtom singleBonded acyclic q) :
    actualTreeMark input singleBonded acyclic treeL (positionAtom singleBonded acyclic p) =
      actualTreeMark input singleBonded acyclic treeR
        (positionAtom singleBonded acyclic q) := by
  classical
  have hexL : ∃ r : Position treeL,
      positionAtom singleBonded acyclic r = positionAtom singleBonded acyclic p :=
    ⟨p, rfl⟩
  have hexR : ∃ r : Position treeR,
      positionAtom singleBonded acyclic r = positionAtom singleBonded acyclic p :=
    ⟨q, atomEq.symm⟩
  rw [show positionAtom singleBonded acyclic q =
      positionAtom singleBonded acyclic p from atomEq.symm]
  unfold actualTreeMark
  rw [dif_pos hexL, dif_pos hexR]
  have occEq : (positionSource (Classical.choose hexL)).occurrence =
      (positionSource (Classical.choose hexR)).occurrence := by
    refine positionSource_occurrence_eq_of_current input singleBonded acyclic
      (Classical.choose hexL) (Classical.choose hexR) ?_ ?_
    · rw [positionSource_root_eq_of_realized realizesL (Classical.choose hexL),
        positionSource_root_eq_of_realized realizesR (Classical.choose hexR), treeRootEq]
    · rw [positionAtom_spec singleBonded acyclic (Classical.choose hexL),
        positionAtom_spec singleBonded acyclic (Classical.choose hexR),
        Classical.choose_spec hexL, Classical.choose_spec hexR]
  rw [occEq]

/-- **The two derived marks agree at a physical atom carried by both actual trees.**  Two actual
realized stage trees at the same frame cursor and the same incoming edge have the same derived
mark at any atom that both carry.  The hypotheses `markL`/`markR` are exactly the two derived
`some` values produced by `tree_observations_of_physicalBranchUniqueNearest`; nothing about the
sibling order or the addresses is assumed. -/
theorem actualTreeMark_eq_of_marks_some
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    {treeL treeR : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input)}
    (sourceEqL : treeL.source = frame.cursorAt slot)
    (sourceEqR : treeR.source = frame.cursorAt slot)
    (realizesL : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) treeL)
    (realizesR : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) treeR)
    {oAtom : input.certified.Atom}
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    (incomingEdge : input.certified.moleculeGraph.Adj c.1 oAtom)
    {center : input.certified.Atom} {descriptorL descriptorR : RS}
    (markL : actualTreeMark input singleBonded acyclic treeL center = some descriptorL)
    (markR : actualTreeMark input singleBonded acyclic treeR center = some descriptorR) :
    actualTreeMark input singleBonded acyclic treeL center =
      actualTreeMark input singleBonded acyclic treeR center := by
  obtain ⟨pL, pLAtom, _pLState⟩ :=
    (actualTreeMark_eq_some_iff input c singleBonded acyclic realizesL
      (actualTree_previousEq_of_source input c frame frameComputed slot sourceEqL)
      (actualTree_sameRoot_of_source input c frame frameComputed slot sourceEqL)
      (actualTree_oObserved_of_source input c frame frameComputed slot sourceEqL oObserved)
      incomingEdge center descriptorL).mp markL
  obtain ⟨pR, pRAtom, _pRState⟩ :=
    (actualTreeMark_eq_some_iff input c singleBonded acyclic realizesR
      (actualTree_previousEq_of_source input c frame frameComputed slot sourceEqR)
      (actualTree_sameRoot_of_source input c frame frameComputed slot sourceEqR)
      (actualTree_oObserved_of_source input c frame frameComputed slot sourceEqR oObserved)
      incomingEdge center descriptorR).mp markR
  have treeRootEq : treeL.source.occurrence.1.root = treeR.source.occurrence.1.root := by
    rw [sourceEqL, sourceEqR]
  have identity := actualTreeMark_eq_of_position input singleBonded acyclic
    realizesL realizesR treeRootEq pL pR (by rw [pLAtom, pRAtom])
  rwa [pLAtom, pRAtom] at identity

/-! ## F. Actual tree-depth observations from the pure physical nearest predicate -/

/-- **The actual tree observations at a physically unique nearest centre.**  For an actual
realized production tree at an actual frame cursor, the pure physical predicate
`PhysicalBranchUniqueNearest` yields:

* no chiral observation at any earlier depth,
* exactly one chiral descriptor at the nearest physical radius,
* the derived actual mark of the centre is that same descriptor.

There is no reader hypothesis and no per-depth label hypothesis.  Deeper detected centres are
unrestricted, and the tree depth is the physical simple-walk distance from the attachment. -/
theorem tree_observations_of_physicalBranchUniqueNearest
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
    (unique : PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom center distance) :
    ∃ descriptor : RS,
      (∀ earlier < distance,
        LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
          (LocalizedCumulativeDecoratedTree.observationsAtDepth
            (fun node => node.label) earlier tree) = []) ∧
      LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
        (LocalizedCumulativeDecoratedTree.observationsAtDepth
          (fun node => node.label) distance tree) = [descriptor] ∧
      actualTreeMark input singleBonded acyclic tree center = some descriptor := by
  have previousEq := actualTree_previousEq_of_source input c frame frameComputed slot sourceEq
  have sameRoot := actualTree_sameRoot_of_source input c frame frameComputed slot sourceEq
  have valid := actualTree_valid_of_source input c frame frameComputed slot sourceEq
  have previousShorter :=
    actualTree_previousShorter_of_source input c frame frameComputed slot sourceEq
  have oObservedTree :=
    actualTree_oObserved_of_source input c frame frameComputed slot sourceEq oObserved
  have incomingEdge := actualSlot_incomingEdge input c frame frameComputed slot oObserved
  obtain ⟨descriptor, markCenter⟩ :=
    actualTreeMark_center_eq_some_of_physicalMarked input c frame frameComputed slot
      singleBonded acyclic hcharge noDouble cfg domain oObserved sourceEq realizes
      unique.1 unique.2.1
  have reader := actualTreeMark_reader input c frame frameComputed slot singleBonded acyclic
    realizes previousEq valid previousShorter sameRoot oObservedTree incomingEdge
  have observations := tree_observations_of_physicalUniqueNearest
    (input := input.certified)
    (carrierFuel := LocalizedUniversalReference.carrierFuel input)
    (singleBonded := singleBonded)
    (acyclic := acyclic)
    (enough := globalCarrierFuel_adequate input)
    (tree := tree)
    (realizes := realizes)
    (previous := ActualReaderPhysicalBranchInverse.topTarget input c)
    (previousEq := previousEq)
    (valid := valid)
    (sameRoot := sameRoot)
    (oObserved := oObservedTree)
    (pObserved := ActualReaderPhysicalBranchInverse.topTarget_current input c)
    (incomingEdge := incomingEdge)
    (marked := actualTreeMark input singleBonded acyclic tree)
    (reader := reader)
    (center := center)
    (descriptor := descriptor)
    (distance := distance)
    (centerMarked := markCenter)
    (centerMember := unique.1)
    (centerSphere := unique.2.2.1)
    (noEarlier := by
      intro y r yMember yMarked walk path shorter
      exact unique.2.2.2.1 y yMember
        (physicalMarkedAtom_of_actualTreeMark_eq_some input c frame frameComputed slot
          singleBonded acyclic hcharge noDouble cfg domain oObserved sourceEq realizes
          yMarked)
        walk path shorter)
    (uniqueAt := by
      intro y r yMember yMarked walk path exactLength
      exact unique.2.2.2.2 y yMember
        (physicalMarkedAtom_of_actualTreeMark_eq_some input c frame frameComputed slot
          singleBonded acyclic hcharge noDouble cfg domain oObserved sourceEq realizes
          yMarked)
        walk path exactLength)
  exact ⟨descriptor, observations.1, observations.2, markCenter⟩

/-! ## G. Unconditional strictness on the actual production-built slot tree -/










theorem actualSlotTree_stageFor_descriptorTable_ne_of_physicalUniqueNearest
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
    (oAtom : input.certified.Atom)
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    (own : Option RS)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom center distance) :
    ((actualSlotTree input c frame frameComputed slot).tables
        (localizedRule5StageFor own .R)).descriptor ≠
      ((actualSlotTree input c frame frameComputed slot).tables
        (localizedRule5StageFor own .S)).descriptor := by
  obtain ⟨descriptor, _earlier, distanceSingleton, _markCenter⟩ :=
    tree_observations_of_physicalBranchUniqueNearest input c frame frameComputed slot
      singleBonded acyclic hcharge noDouble cfg domain oObserved
      (sourceEq := actualSlotTree_source input c frame frameComputed slot)
      (realizes := actualSlotTree_realizes input c frame frameComputed slot)
      unique
  have raw := descriptor_ne_of_unique_chiral_at_depth
    (stageR := localizedRule5StageFor own .R)
    (stageS := localizedRule5StageFor own .S)
    (probeEqR := stageRule5Probe_stageFor_R own)
    (probeEqS := stageRule5Probe_stageFor_S own)
    (treeR := actualSlotTree input c frame frameComputed slot)
    (treeS := actualSlotTree input c frame frameComputed slot)
    (depth := distance) (descriptor := descriptor)
    distanceSingleton distanceSingleton
  simpa only [LocalizedCumulativeDecoratedTree.tables_descriptor] using raw







theorem actualSlotTree_stageFor_descriptorTable_ne_of_actualGeneralRigidPhysicalDomain
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
    (own : Option RS)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom center distance) :
    ((actualSlotTree input c frame frameComputed slot).tables
        (localizedRule5StageFor own .R)).descriptor ≠
      ((actualSlotTree input c frame frameComputed slot).tables
        (localizedRule5StageFor own .S)).descriptor := by
  exact actualSlotTree_stageFor_descriptorTable_ne_of_physicalUniqueNearest input c frame
    frameComputed slot singleBonded acyclic hcharge noDouble
    (cfg := input.certified.canonicalReindexConfiguration cfgPhys)
    (domain := actualGeneralRigidGlobalPhysicalDomain_of_actualGeneralRigidPhysicalDomain
      input.certified cfgPhys c physicalDomain)
    oAtom oObserved own unique

/-! ## H. Key-level transfer for two actual stage builds -/

/-- **Strict descriptor difference of two actual stage keys at a physical unique nearest
centre.**

`treeR`/`treeS` are actual decorated trees of the two production stage builds at the common
frame cursor, with their exact table matches.  The reader correspondence and the depth
observations of each tree are **derived** from the actual realization, the actual reference
state and the pure physical nearest predicate.  The two derived actual marks agree at the
physical nearest centre by the fixed-root carrier injectivity
(`actualTreeMark_eq_of_marks_some`); there is **no** alignment premise left.  In particular no
sorted-address-stability statement is needed or used. -/
theorem key_descriptor_ne_of_physicalUniqueNearest_stageFor
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
    (oAtom : input.certified.Atom)
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    (own : Option RS)
    {treeR treeS : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input)}
    (keyR keyS : input.certified.LocalizedRerootCumulativeRule45Key)
    (sourceEqR : treeR.source = frame.cursorAt slot)
    (sourceEqS : treeS.source = frame.cursorAt slot)
    (realizesR : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) treeR)
    (realizesS : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) treeS)
    (tableMatchR : LocalizedCumulativeTreeTableMatch
      (localizedRule5StageFor own .R) treeR keyR)
    (tableMatchS : LocalizedCumulativeTreeTableMatch
      (localizedRule5StageFor own .S) treeS keyS)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom center distance) :
    keyR.descriptor ≠ keyS.descriptor := by
  obtain ⟨descriptorR, _earlierR, distanceSingletonR, markCenterR⟩ :=
    tree_observations_of_physicalBranchUniqueNearest input c frame frameComputed slot
      singleBonded acyclic hcharge noDouble cfg domain oObserved sourceEqR realizesR unique
  obtain ⟨descriptorS, _earlierS, distanceSingletonS, markCenterS⟩ :=
    tree_observations_of_physicalBranchUniqueNearest input c frame frameComputed slot
      singleBonded acyclic hcharge noDouble cfg domain oObserved sourceEqS realizesS unique
  have markEq : actualTreeMark input singleBonded acyclic treeR center =
      actualTreeMark input singleBonded acyclic treeS center :=
    actualTreeMark_eq_of_marks_some input c frame frameComputed slot singleBonded acyclic
      sourceEqR sourceEqS realizesR realizesS oObserved
      (actualSlot_incomingEdge input c frame frameComputed slot oObserved)
      markCenterR markCenterS
  have descriptorEq : descriptorR = descriptorS := by
    have someEq : some descriptorR = some descriptorS := by
      rw [← markCenterR, ← markCenterS]
      exact markEq
    exact Option.some.inj someEq
  rw [← descriptorEq] at distanceSingletonS
  exact key_descriptor_ne_of_unique_chiral_at_depth
    (stageR := localizedRule5StageFor own .R)
    (stageS := localizedRule5StageFor own .S)
    (probeEqR := stageRule5Probe_stageFor_R own)
    (probeEqS := stageRule5Probe_stageFor_S own)
    (treeR := treeR) (treeS := treeS)
    (keyR := keyR) (keyS := keyS)
    (tableMatchR := tableMatchR) (tableMatchS := tableMatchS)
    (depth := distance) (descriptor := descriptorR)
    distanceSingletonR distanceSingletonS




theorem key_descriptor_ne_of_physicalUniqueNearest_stageFor_of_canonicalReindex
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
    (own : Option RS)
    {treeR treeS : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input)}
    (keyR keyS : input.certified.LocalizedRerootCumulativeRule45Key)
    (sourceEqR : treeR.source = frame.cursorAt slot)
    (sourceEqS : treeS.source = frame.cursorAt slot)
    (realizesR : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) treeR)
    (realizesS : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input c) treeS)
    (tableMatchR : LocalizedCumulativeTreeTableMatch
      (localizedRule5StageFor own .R) treeR keyR)
    (tableMatchS : LocalizedCumulativeTreeTableMatch
      (localizedRule5StageFor own .S) treeS keyS)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom center distance) :
    keyR.descriptor ≠ keyS.descriptor := by
  exact key_descriptor_ne_of_physicalUniqueNearest_stageFor input c frame frameComputed slot
    singleBonded acyclic hcharge noDouble
    (cfg := input.certified.canonicalReindexConfiguration cfgPhys)
    (domain := actualGeneralRigidGlobalPhysicalDomain_of_actualGeneralRigidPhysicalDomain
      input.certified cfgPhys c physicalDomain)
    oAtom oObserved own keyR keyS sourceEqR sourceEqS realizesR realizesS
    tableMatchR tableMatchS unique

/-- **Both stage builds succeed at adequate fuel, with actual trees and provenance.**  The two
keys are the production builder outputs at `2 * (carrierFuel + 1)`; the trees, their sources,
their table matches and their actual realizations are derived from the existing
`exists_decoratedTree_of_buildLocalizedRerootCumulativeRule45Key?` API. -/
theorem exists_stageFor_builds_and_trees_at_adequate_fuel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (own : Option RS)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor) :
    ∃ (keyR keyS : input.LocalizedRerootCumulativeRule45Key)
      (treeR treeS : LocalizedCumulativeDecoratedTree input carrierFuel),
      input.buildLocalizedRerootCumulativeRule45Key?
          (localizedRule5StageFor own .R) target view
          (2 * (carrierFuel + 1)) cursor = some keyR ∧
        input.buildLocalizedRerootCumulativeRule45Key?
            (localizedRule5StageFor own .S) target view
            (2 * (carrierFuel + 1)) cursor = some keyS ∧
          treeR.source = cursor ∧
            treeS.source = cursor ∧
              LocalizedCumulativeTreeTableMatch
                  (localizedRule5StageFor own .R) treeR keyR ∧
                LocalizedCumulativeTreeTableMatch
                    (localizedRule5StageFor own .S) treeS keyS ∧
                  LocalizedCumulativeTreeRealizes input
                      (fun cursor => input.localizedDependencyLabel target view cursor)
                      treeR ∧
                    LocalizedCumulativeTreeRealizes input
                      (fun cursor => input.localizedDependencyLabel target view cursor)
                      treeS := by
  obtain ⟨keyR, computedR⟩ :=
    input.exists_buildLocalizedRerootCumulativeRule45Key?_at_twice
      (localizedRule5StageFor own .R) target view cursor valid
  obtain ⟨keyS, computedS⟩ :=
    input.exists_buildLocalizedRerootCumulativeRule45Key?_at_twice
      (localizedRule5StageFor own .S) target view cursor valid
  obtain ⟨treeR, treeRSource, tableMatchR, _labelTableR, realizesR⟩ :=
    exists_decoratedTree_of_buildLocalizedRerootCumulativeRule45Key? input
      (localizedRule5StageFor own .R) target view (2 * (carrierFuel + 1)) cursor
      keyR computedR
  obtain ⟨treeS, treeSSource, tableMatchS, _labelTableS, realizesS⟩ :=
    exists_decoratedTree_of_buildLocalizedRerootCumulativeRule45Key? input
      (localizedRule5StageFor own .S) target view (2 * (carrierFuel + 1)) cursor
      keyS computedS
  exact ⟨keyR, keyS, treeR, treeS, computedR, computedS, treeRSource, treeSSource,
    tableMatchR, tableMatchS, realizesR, realizesS⟩

/-! ## I. Actual production builds at the final-root frame slot

The generic fuel theorem above is instantiated at the *actual* final original-root target, the
*actual* generated restricted dependency view and the *actual* computed frame cursor.  Every
build equation below is therefore a production build equation; no key, tree, table match,
realization, descriptor or alignment is supplied.  The fuel `2 * (carrierFuel + 1)` is exactly
`localizedOccurrenceRerootEvaluationFuel`, the fuel used by the occurrence evaluator
(`I.actualSlot_compoundBuilt_and_stageFor_keys_ne_at_evaluationFuel`). -/

/-- **Both actual cumulative Rule-5 stage builds succeed at the actual frame cursor.**  The two
keys, their decorated trees, their sources, their exact table matches and their realizations of
the generated dependency reader are all produced by the actual builder at
`frame.cursorAt slot`. -/
theorem exists_actualSlot_stageFor_builds_and_trees
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame)
    (slot : Fin 4)
    (own : Option RS) :
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
          treeR.source = frame.cursorAt slot ∧
            treeS.source = frame.cursorAt slot ∧
              LocalizedCumulativeTreeTableMatch
                  (localizedRule5StageFor own .R) treeR keyR ∧
                LocalizedCumulativeTreeTableMatch
                    (localizedRule5StageFor own .S) treeS keyS ∧
                  LocalizedCumulativeTreeRealizes input.certified
                      (ActualReaderPhysicalBranchInverse.dependencyReader input c) treeR ∧
                    LocalizedCumulativeTreeRealizes input.certified
                      (ActualReaderPhysicalBranchInverse.dependencyReader input c) treeS :=
  exists_stageFor_builds_and_trees_at_adequate_fuel input.certified own
    (ActualReaderPhysicalBranchInverse.topTarget input c)
    (referenceDependencyView input c) (frame.cursorAt slot)
    (input.certified.localizedOccurrenceFourLigandFrame_cursor_valid
      (ActualReaderPhysicalBranchInverse.topTarget input c) frame frameComputed
      (frame.cursorAt slot) (List.get_mem frame.cursors _))

/-- **Strictness of the two actual production stage builds at the actual frame cursor.**  Both
keys are given by explicit production build equations at the actual cursor; the trees, table
matches and realizations are derived from those equations.  The derived marks agree by the
fixed-root carrier injectivity, so no alignment premise is needed. -/
theorem actualSlot_stageFor_keys_descriptor_ne_of_physicalUniqueNearest
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
    (oAtom : input.certified.Atom)
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
    keyR.descriptor ≠ keyS.descriptor := by
  obtain ⟨treeR, sourceEqR, tableMatchR, _labelTableR, realizesR⟩ :=
    exists_decoratedTree_of_buildLocalizedRerootCumulativeRule45Key? input.certified
      (localizedRule5StageFor own .R)
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (2 * (LocalizedUniversalReference.carrierFuel input + 1))
      (frame.cursorAt slot) keyR builtR
  obtain ⟨treeS, sourceEqS, tableMatchS, _labelTableS, realizesS⟩ :=
    exists_decoratedTree_of_buildLocalizedRerootCumulativeRule45Key? input.certified
      (localizedRule5StageFor own .S)
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      (referenceDependencyView input c)
      (2 * (LocalizedUniversalReference.carrierFuel input + 1))
      (frame.cursorAt slot) keyS builtS
  exact key_descriptor_ne_of_physicalUniqueNearest_stageFor input c frame frameComputed slot
    singleBonded acyclic hcharge noDouble cfg domain oAtom oObserved own keyR keyS
    sourceEqR sourceEqS realizesR realizesS tableMatchR tableMatchS unique

/-- **Actual existence of the two production stage builds together with strictness.**  No key is
supplied: the two keys are the actual builder outputs at the actual frame cursor, and their
descriptor tables differ under the pure physical unique-nearest predicate. -/
theorem exists_actualSlot_stageFor_keys_descriptor_ne_of_physicalUniqueNearest
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
    (oAtom : input.certified.Atom)
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    (own : Option RS)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom center distance) :
    ∃ (keyR keyS : input.certified.LocalizedRerootCumulativeRule45Key),
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
          keyR.descriptor ≠ keyS.descriptor := by
  obtain ⟨keyR, keyS, _treeR, _treeS, builtR, builtS, _sourceEqR, _sourceEqS,
    _tableMatchR, _tableMatchS, _realizesR, _realizesS⟩ :=
    exists_actualSlot_stageFor_builds_and_trees input c frame frameComputed slot own
  exact ⟨keyR, keyS, builtR, builtS,
    actualSlot_stageFor_keys_descriptor_ne_of_physicalUniqueNearest input c frame
      frameComputed slot singleBonded acyclic hcharge noDouble cfg domain oAtom oObserved
      own builtR builtS unique⟩

/-- **Actual existence of the two production stage builds, their actual trees and provenance,
together with strictness.**  This is the strongest form of the endpoint: the builder outputs are
not supplied, the trees come from the actual build equations, and the descriptor tables are
strictly different. -/
theorem exists_actualSlot_stageFor_builds_trees_and_descriptor_ne_of_physicalUniqueNearest
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
    (oAtom : input.certified.Atom)
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    (own : Option RS)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom center distance) :
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
          treeR.source = frame.cursorAt slot ∧
            treeS.source = frame.cursorAt slot ∧
              LocalizedCumulativeTreeTableMatch
                  (localizedRule5StageFor own .R) treeR keyR ∧
                LocalizedCumulativeTreeTableMatch
                    (localizedRule5StageFor own .S) treeS keyS ∧
                  LocalizedCumulativeTreeRealizes input.certified
                      (ActualReaderPhysicalBranchInverse.dependencyReader input c) treeR ∧
                    LocalizedCumulativeTreeRealizes input.certified
                        (ActualReaderPhysicalBranchInverse.dependencyReader input c) treeS ∧
                      keyR.descriptor ≠ keyS.descriptor := by
  obtain ⟨keyR, keyS, treeR, treeS, builtR, builtS, sourceEqR, sourceEqS,
    tableMatchR, tableMatchS, realizesR, realizesS⟩ :=
    exists_actualSlot_stageFor_builds_and_trees input c frame frameComputed slot own
  exact ⟨keyR, keyS, treeR, treeS, builtR, builtS, sourceEqR, sourceEqS,
    tableMatchR, tableMatchS, realizesR, realizesS,
    key_descriptor_ne_of_physicalUniqueNearest_stageFor input c frame frameComputed slot
      singleBonded acyclic hcharge noDouble cfg domain oAtom oObserved own keyR keyS
      sourceEqR sourceEqS realizesR realizesS tableMatchR tableMatchS unique⟩

/-- **The actual compound build and the two actual stage builds at the production evaluation
fuel.**  The first component is the actual production compound Rules-4a--5 build of the frame
slot (`actualSlotCompoundBuilt`); the second component is the same two-stage strictness statement
at the fuel `localizedOccurrenceRerootEvaluationFuel`, which is definitionally
`2 * (carrierFuel + 1)`.  Both are actual builder outputs at the same cursor. -/
theorem actualSlot_compoundBuilt_and_stageFor_keys_ne_at_evaluationFuel
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
    (oAtom : input.certified.Atom)
    (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom)
    (own : Option RS)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input ⟨c.1, c.2⟩ oAtom center distance) :
    input.certified.buildLocalizedRerootCompoundRule45Key?
        (ActualReaderPhysicalBranchInverse.topTarget input c)
        (referenceDependencyView input c)
        (localizedOccurrenceRerootEvaluationFuel
          (LocalizedUniversalReference.carrierFuel input))
        (frame.cursorAt slot) =
      some (actualSlotCompoundKey input c frame frameComputed slot) ∧
      ∃ (keyR keyS : input.certified.LocalizedRerootCumulativeRule45Key),
        input.certified.buildLocalizedRerootCumulativeRule45Key?
            (localizedRule5StageFor own .R)
            (ActualReaderPhysicalBranchInverse.topTarget input c)
            (referenceDependencyView input c)
            (localizedOccurrenceRerootEvaluationFuel
              (LocalizedUniversalReference.carrierFuel input))
            (frame.cursorAt slot) = some keyR ∧
          input.certified.buildLocalizedRerootCumulativeRule45Key?
              (localizedRule5StageFor own .S)
              (ActualReaderPhysicalBranchInverse.topTarget input c)
              (referenceDependencyView input c)
              (localizedOccurrenceRerootEvaluationFuel
                (LocalizedUniversalReference.carrierFuel input))
              (frame.cursorAt slot) = some keyS ∧
            keyR.descriptor ≠ keyS.descriptor := by
  refine ⟨actualSlotCompoundBuilt input c frame frameComputed slot, ?_⟩
  simpa only [localizedOccurrenceRerootEvaluationFuel] using
    exists_actualSlot_stageFor_keys_descriptor_ne_of_physicalUniqueNearest input c frame
      frameComputed slot singleBonded acyclic hcharge noDouble cfg domain oAtom oObserved
      own unique

/-! ## J. Conditional through-Rule-5 wrappers

These remain honest conditional intermediates: they do not claim the physical full-table sign,
and they do not assume any reader law at a physical endpoint.  They are the interface consumed
by the signed downstream work once the nearest-address alignment is available. -/

/-- The common-`R` reading comparison of two singleton reading lists is strict whenever the
left reading's own common-`R` descriptor differs from its common-`S` descriptor and the two
readings are mirror-crossed. -/
theorem compareRule5Readings_R_ne_of_singleton_mirror
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule45Key)
    (leftReading rightReading : input.LocalizedRerootRule5Reading)
    (leftEq : left.rule5Readings = [leftReading])
    (rightEq : right.rule5Readings = [rightReading])
    (mirror : LocalizedRule5SwapAndSignal.MirrorReading input leftReading rightReading)
    (strict : OfficialRuleMajorKey.compareSparseLayers
        compareLocalizedCumulativeRule45Priority
        leftReading.commonR.descriptor leftReading.commonS.descriptor ≠ Ordering.eq) :
    input.compareLocalizedRerootCompoundRule5Readings .R
        left.rule5Readings right.rule5Readings ≠ Ordering.eq := by
  rw [leftEq, rightEq,
    Rule4c5SourceDecision.compareLocalizedRerootCompoundRule5Readings_singleton]
  rw [Rule4c5SourceDecision.localizedRerootRule5Descriptor_R_eq_commonR,
    Rule4c5SourceDecision.localizedRerootRule5Descriptor_R_eq_commonR, ← mirror.2]
  exact strict

/-- **Through-Rule-5 direction from singleton mirror readings and a derived prior tie.**

Under a complete prior Rules-4b/4c tie, mirror-crossed common-reference readings and a strict
common-`R` descriptor difference of the left branch, the actual through-Rule-5 comparison reports
`pseudo = true` and a non-`eq` ordering.  This is the `±2` enantiomorphic signal of the physical
mirror pair, stated at the actual comparator.  It is a conditional intermediate: the physical
derivation of the singleton readings and of the prior tie belongs to the signed downstream
work. -/
theorem throughRule5_pseudo_true_and_ordering_ne_of_singleton_mirror
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule45Key)
    (leftReading rightReading : input.LocalizedRerootRule5Reading)
    (leftEq : left.rule5Readings = [leftReading])
    (rightEq : right.rule5Readings = [rightReading])
    (mirror : LocalizedRule5SwapAndSignal.MirrorReading input leftReading rightReading)
    (priorTie : input.compareLocalizedRerootCompoundRule4bcKeys
      left.prior right.prior = Ordering.eq)
    (strict : OfficialRuleMajorKey.compareSparseLayers
        compareLocalizedCumulativeRule45Priority
        leftReading.commonR.descriptor leftReading.commonS.descriptor ≠ Ordering.eq) :
    (input.compareLocalizedRerootCompoundThroughRule5 left right).pseudo = true ∧
      (input.compareLocalizedRerootCompoundThroughRule5 left right).ordering
        ≠ Ordering.eq := by
  have mirrorReadings : LocalizedRule5SwapAndSignal.MirrorReadings input
      left.rule5Readings right.rule5Readings := by
    rw [leftEq, rightEq]
    exact List.Forall₂.cons mirror List.Forall₂.nil
  have readingsNe := compareRule5Readings_R_ne_of_singleton_mirror input left right
    leftReading rightReading leftEq rightEq mirror strict
  constructor
  · rw [LocalizedRule5SwapAndSignal.compareLocalizedRerootCompoundThroughRule5_pseudo_eq_true_iff_of_mirror_of_prior_tie
      input left right mirrorReadings priorTie]
    exact readingsNe
  · rw [input.compareLocalizedRerootCompoundThroughRule5_ordering]
    unfold compareLocalizedRerootCompoundRule45Keys
    simp only [compareLex, Ordering.byKey, priorTie]
    exact readingsNe

end LocalizedUniqueNearestRule5Direction

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.observationsAtDepth_priority
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.descriptorTable_getD_map_snd
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.stageFinalRule5Value
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.rule5BitSum
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.stageFinalRule5Value_def
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.stageFinalRule5Value_eq_of_probe
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.sum_stageFinalRule5Value_eq_of_map_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.rule5BitSum_eq_chiralDescriptors_sum
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.rule5BitSum_eq_bit_of_chiralDescriptors_singleton
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.rule5BitSum_R_ne_S_of_same_chiral
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.stagePriorityPrefix_stageFor_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.stageRule5Probe_stageFor_R
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.stageRule5Probe_stageFor_S
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.comparePriority_stageFor_R_S_chiral
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.comparePriority_stageFor_R_S_chiral_R
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.compareSparseLayers_stageFor_R_S_chiral_R
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.descriptor_ne_of_unique_chiral_at_depth
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.key_descriptor_ne_of_unique_chiral_at_depth
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.actualTreeMark
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.actualTree_previousEq_of_source
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.actualTree_sameRoot_of_source
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.actualTree_valid_of_source
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.actualTree_previousShorter_of_source
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.actualTree_oObserved_of_source
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.actualTreeMark_eq_some_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.actualTreeMark_reader
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.physicalMarkedAtom_of_actualTreeMark_eq_some
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.actualTreeMark_center_eq_some_of_physicalMarked
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.positionSource_occurrence_eq_of_current
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.actualTreeMark_eq_of_position
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.actualTreeMark_eq_of_marks_some
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.tree_observations_of_physicalBranchUniqueNearest
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.actualSlotTree_stageFor_descriptorTable_ne_of_physicalUniqueNearest
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.actualSlotTree_stageFor_descriptorTable_ne_of_actualGeneralRigidPhysicalDomain
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.key_descriptor_ne_of_physicalUniqueNearest_stageFor
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.key_descriptor_ne_of_physicalUniqueNearest_stageFor_of_canonicalReindex
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.exists_stageFor_builds_and_trees_at_adequate_fuel
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.exists_actualSlot_stageFor_builds_and_trees
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.actualSlot_stageFor_keys_descriptor_ne_of_physicalUniqueNearest
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.exists_actualSlot_stageFor_keys_descriptor_ne_of_physicalUniqueNearest
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.exists_actualSlot_stageFor_builds_trees_and_descriptor_ne_of_physicalUniqueNearest
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.actualSlot_compoundBuilt_and_stageFor_keys_ne_at_evaluationFuel
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.compareRule5Readings_R_ne_of_singleton_mirror
assert_kernel_only TetraStereo.OneCenter.LocalizedUniqueNearestRule5Direction.throughRule5_pseudo_true_and_ordering_ne_of_singleton_mirror
