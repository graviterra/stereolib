import TetraStereo.OneCenter.LocalizedChemicalRingActualFullLabelMatch
import TetraStereo.OneCenter.LocalizedChemicalRingActualKindMatch
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Label matching derived from the actual retained comparison

At any actual real detected target of a finite simple-bonded input, equality of the actual
refined comparison keys derives exact molecular-reader label equality at the two ligand roots.
It also constructs actual common-reference reading trees with equal decorated observations and
equal reader labels at corresponding reading addresses. The raw auxiliary state is arbitrary;
no successful build, selected alternative or reader agreement is assumed.

These reading addresses need not be the promoted-marker addresses. The separate kind theorem
uses the latter addresses. Combining full labels and reference markers on one correspondence,
then reconstructing an orientation-preserving molecular symmetry, remains open.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingActualComparisonLabelMatch

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedCumulativeDecoratedTree LocalizedMarkedRetainedCanonicalFrame
open LocalizedMarkedRetainedPromotedKey LocalizedMarkedRetainedMolecularSelection
open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedPromotedRanking
open LocalizedMarkedRetainedStateReader LocalizedChemicalRingPromotedColorReadback
open LocalizedMarkedRetainedCanonicalMarker Rule4aTableBridge
open LocalizedChemicalRingActualFullLabelMatch

noncomputable section
open scoped Classical

variable {input : CertifiedLocalizedCIPInput}
  (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
  (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
  (frame : RetainedExecutionFrame descriptorMap target)

theorem frame_uniform_built (slot : Fin 4) :
    input.buildRuleMajorCompoundRule45KeyWith?
      (fun stage => input.buildRuleMajorCumulativeWithRead? stage
        (input.molecularReader descriptorMap target) (2 * (retainedCarrierFuel input + 1)))
      (frame.stages slot).a.tree.source = some (frame.compounds slot) := by
  rw [(frame.stages slot).a.sourceEq]
  exact (input.buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor target
    (input.molecularView descriptorMap target) (2 * (retainedCarrierFuel input + 1))
    (frame.frame.cursorAt slot)).symm.trans
    ((input.buildActualRuleMajorCompoundRule45KeyExec?_eq target
      (input.molecularView descriptorMap target) (2 * (retainedCarrierFuel input + 1))
      (frame.frame.cursorAt slot)).symm.trans (frame.compoundBuilt slot))

theorem frame_tie_root_labels
    (tetrahedral : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (single : input.moleculeGraph.SimpleBonded) (unit : DetectedOccurrence input.moleculeGraph)
    (targetUnit : input.molecularFrameUnit target.1 = unit.1) (left right : Fin 4)
    (tie : frame.retainedKeys unit left = frame.retainedKeys unit right) :
    input.molecularReader descriptorMap target (frame.stages left).a.tree.source =
      input.molecularReader descriptorMap target (frame.stages right).a.tree.source := by
  have full := frame.fullOrdering tetrahedral single unit targetUnit left right
  rw [tie, (completeLigandRule5Key_compare_eq_iff _ _).mpr rfl] at full
  exact full_tie_root_labels _ _ _ _ _ _ _ _ (frame_uniform_built descriptorMap target frame left)
    (frame_uniform_built descriptorMap target frame right) full

theorem frame_tie_same_label_trees
    (tetrahedral : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (single : input.moleculeGraph.SimpleBonded) (unit : DetectedOccurrence input.moleculeGraph)
    (targetUnit : input.molecularFrameUnit target.1 = unit.1) (left right : Fin 4)
    (tie : frame.retainedKeys unit left = frame.retainedKeys unit right) :
    ∃ (treeL treeR : LocalizedCumulativeDecoratedTree input (retainedCarrierFuel input)),
      treeL.source = (frame.stages left).a.tree.source ∧
      treeR.source = (frame.stages right).a.tree.source ∧
      LocalizedCumulativeTreeRealizes input (input.molecularReader descriptorMap target) treeL ∧
      LocalizedCumulativeTreeRealizes input (input.molecularReader descriptorMap target) treeR ∧
      observation treeL = observation treeR ∧
      (∀ path subL subR, subtreeAt? treeL path = some subL → subtreeAt? treeR path = some subR →
        input.molecularReader descriptorMap target subL.source =
          input.molecularReader descriptorMap target subR.source) := by
  have full := frame.fullOrdering tetrahedral single unit targetUnit left right
  rw [tie, (completeLigandRule5Key_compare_eq_iff _ _).mpr rfl] at full
  obtain ⟨treeL, treeR, sourceL, sourceR, realizesL, realizesR, obs⟩ :=
    full_tie_same_observations _ _ _ _ _ _ _ _ (frame_uniform_built descriptorMap target frame left)
      (frame_uniform_built descriptorMap target frame right) full
  refine ⟨treeL, treeR, sourceL, sourceR, realizesL, realizesR, obs, ?_⟩
  intro path subL subR lookupL lookupR
  have labels := subtreeAt?_label_eq_of_observation_eq path treeL treeR obs subL subR lookupL lookupR
  have l := subtreeAt?_node_label_eq_read realizesL lookupL
  have r := subtreeAt?_node_label_eq_read realizesR lookupR
  exact l.symm.trans (labels.symm.trans r)

/-- Marker refinements within one tied sibling class cannot interchange different root labels.
The actual ordinary builds are obtained from child validity. -/
theorem deepPrior_tie_sibling_labels (fallback : CompleteLigandRule5Key)
    (tree : LocalizedCumulativeDecoratedTree input (retainedCarrierFuel input))
    (realizes : LocalizedCumulativeTreeRealizes input (input.molecularReader descriptorMap target) tree)
    (tetrahedral : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (single : input.moleculeGraph.SimpleBonded)
    (rootChild : tree.source ∈ input.executableLocalizedRerootChildren ⟨target, none⟩)
    (parent left right : (ruleMajorTreeGraph tree).Node)
    (edgeL : (ruleMajorTreeGraph tree).child parent left)
    (edgeR : (ruleMajorTreeGraph tree).child parent right)
    (tie : deepPrior descriptorMap target fallback tree left =
      deepPrior descriptorMap target fallback tree right) :
    input.molecularReader descriptorMap target (nodeSource input tree left) =
      input.molecularReader descriptorMap target (nodeSource input tree right) := by
  have validL := input.localizedRerootChild_valid _ _ _
    (input.executableLocalizedRerootChildren_declarative (nodeSource input tree parent))
    (child_edge tree realizes edgeL)
  have validR := input.localizedRerootChild_valid _ _ _
    (input.executableLocalizedRerootChildren_declarative (nodeSource input tree parent))
    (child_edge tree realizes edgeR)
  obtain ⟨keyL, builtL⟩ := ordinaryKey?_exists input target (input.molecularView descriptorMap target)
    (nodeSource input tree left) validL
  obtain ⟨keyR, builtR⟩ := ordinaryKey?_exists input target (input.molecularView descriptorMap target)
    (nodeSource input tree right) validR
  have full := deepPrior_agreement descriptorMap target fallback tree realizes tetrahedral single
    rootChild parent left right edgeL edgeR keyL keyR builtL builtR
  rw [tie] at full
  have fullTie : (input.compareLocalizedRerootCompoundThroughRule5 keyL keyR).ordering = .eq :=
    full.trans (compare_eq_iff_eq.mpr rfl)
  unfold ordinaryKey? at builtL builtR
  rw [input.buildActualRuleMajorCompoundRule45KeyExec?_eq,
    input.buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor] at builtL builtR
  exact full_tie_root_labels _ _ _ _ _ _ _ _ builtL builtR fullTie

section Actual

variable (input : CertifiedLocalizedCIPInput) (single : input.moleculeGraph.SimpleBonded)
  (state : OccurrenceAuxState) (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
  (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
  (unit : DetectedOccurrence input.moleculeGraph) (targetUnit : input.molecularFrameUnit target.1 = unit.1)
  (reference : input.Atom) (W D : Nat)

/-- No successful build, reference-selection or label-agreement premise is supplied. -/
theorem actual_refined_tie_root_labels (left right : Fin 4)
    (tie : refinedKey input single state target real unit targetUnit reference W D left =
      refinedKey input single state target real unit targetUnit reference W D right) :
    rawStateReader input state target (slotTree input single state target real unit targetUnit left).source =
      rawStateReader input state target (slotTree input single state target real unit targetUnit right).source := by
  simp only [rawStateReader_eq_molecularReader]
  exact frame_tie_root_labels (rawStateDescriptorMap input state) target
    (frames input single state target real unit targetUnit) (rawStateDescriptorMap_tetrahedral input state)
    single unit targetUnit left right (congrArg (fun value : RefinedKey => (ofLex value).1) tie)

/-- Exact reader correspondence throughout actual common-reference reading trees, derived
from the keys of the real comparison at an arbitrary auxiliary state. -/
theorem actual_refined_tie_same_label_trees (left right : Fin 4)
    (tie : refinedKey input single state target real unit targetUnit reference W D left =
      refinedKey input single state target real unit targetUnit reference W D right) :
    ∃ (treeL treeR : LocalizedCumulativeDecoratedTree input (retainedCarrierFuel input)),
      treeL.source = (slotTree input single state target real unit targetUnit left).source ∧
      treeR.source = (slotTree input single state target real unit targetUnit right).source ∧
      LocalizedCumulativeTreeRealizes input (rawStateReader input state target) treeL ∧
      LocalizedCumulativeTreeRealizes input (rawStateReader input state target) treeR ∧
      observation treeL = observation treeR ∧
      (∀ path subL subR, subtreeAt? treeL path = some subL → subtreeAt? treeR path = some subR →
        rawStateReader input state target subL.source = rawStateReader input state target subR.source) := by
  simp only [rawStateReader_eq_molecularReader]
  exact frame_tie_same_label_trees (rawStateDescriptorMap input state) target
    (frames input single state target real unit targetUnit) (rawStateDescriptorMap_tetrahedral input state)
    single unit targetUnit left right (congrArg (fun value : RefinedKey => (ofLex value).1) tie)

end Actual
end
end TetraStereo.OneCenter.LocalizedChemicalRingActualComparisonLabelMatch

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingActualComparisonLabelMatch.frame_uniform_built
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingActualComparisonLabelMatch.frame_tie_root_labels
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingActualComparisonLabelMatch.frame_tie_same_label_trees
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingActualComparisonLabelMatch.deepPrior_tie_sibling_labels
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingActualComparisonLabelMatch.actual_refined_tie_root_labels
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingActualComparisonLabelMatch.actual_refined_tie_same_label_trees
