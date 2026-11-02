import TetraStereo.OneCenter.LocalizedContextTreeReadback
import TetraStereo.OneCenter.LocalizedActualArmReadback
import TetraStereo.OneCenter.LocalizedRuleMajorOwnMolecularEvidence
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace Rule4aTableBridge

open CertifiedLocalizedCIPInput
open DeclarativeCIP
open LocalizedCumulativeDecoratedTree
noncomputable section
open scoped Classical

/-- The molecular readback obligations needed by the Rule-4a canonical bridge for an arbitrary
realized contextual tree. The observer's own labels, tetrahedral availability, and Rule-3 mask are
all recorded against the independent occurrence-reading semantics at `unit`. -/
structure ContextTreeRankReadback {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph) : Prop where
  label : ∀ (node : (toOfficialSourceTree tree).toDeclarativeDigraph.Node)
      (actual : LocalizedCumulativeDecoratedTree input carrierFuel),
      subtreeAt? tree node.1 = some actual →
        actual.label =
          (occurrenceReading input.moleculeGraph descriptorMap unit
            (toOfficialSourceTree tree).toDeclarativeDigraph node).toLocalizedLabel
  tetrahedral : ∀ node : (toOfficialSourceTree tree).toDeclarativeDigraph.Node,
      (occurrenceReading input.moleculeGraph descriptorMap unit
        (toOfficialSourceTree tree).toDeclarativeDigraph node).IsTetrahedral
  available : ∀ node : (toOfficialSourceTree tree).toDeclarativeDigraph.Node,
      occurrenceReading input.moleculeGraph descriptorMap unit
        (toOfficialSourceTree tree).toDeclarativeDigraph node ≠ .unavailable
  rule4aOnly : Rule4aOnly (toOfficialSourceTree tree).toDeclarativeDigraph
      (rankEvidence input.moleculeGraph descriptorMap unit
        (toOfficialSourceTree tree).toDeclarativeDigraph)

/-- Any realized tree rooted at an executable child of the target has the complete context
readback bundle. The only descriptor-map premise is tetrahedrality of values it actually returns. -/
theorem contextTreeRankReadback_of_realizedTree
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (tetrahedralMap : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (target : input.LocalizedRerootCursor carrierFuel)
    (unit : DetectedOccurrence input.moleculeGraph)
    (targetUnit : input.molecularFrameUnit target.occurrence.1 = unit.1)
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (realizes : LocalizedCumulativeTreeRealizes input
      (input.molecularReader descriptorMap target.occurrence) tree)
    (rootChild : tree.source ∈ input.executableLocalizedRerootChildren target) :
    ContextTreeRankReadback tree descriptorMap unit := by
  have observed := input.realizedTree_node_label_eq_occurrenceReading descriptorMap
    singleBonded acyclic target unit targetUnit tree realizes rootChild
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro node actual lookup
    obtain ⟨actual', lookup', labelEq, _available⟩ := observed node
    cases Option.some.inj (lookup.symm.trans lookup')
    exact labelEq
  · intro node
    exact occurrenceReading_tetrahedral_of_map _ _ _ _ tetrahedralMap node
  · intro node
    obtain ⟨_, _, _, available⟩ := observed node
    exact available
  · exact rule4aOnly_rankEvidence_of_simpleBonded singleBonded _ _ _

/-- The revised evaluator's generated own-state reader supplies the generic contextual bundle.
This specialization uses `LocalizedRuleMajorReference.descriptorMap`, the map built from the revised
`referenceState`, and transfers realization through its proved reader equality. -/
theorem ruleMajorGeneratedContextTreeRankReadback
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (target : input.certified.LocalizedRerootCursor
      (input.certified.certified.input.molecule.atomCount + 1))
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.occurrence.1 = unit.1)
    (tree : LocalizedCumulativeDecoratedTree input.certified
      (input.certified.certified.input.molecule.atomCount + 1))
    (realizes : LocalizedCumulativeTreeRealizes input.certified
      (input.certified.localizedDependencyLabel target.occurrence
        (input.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState input) target.occurrence)) tree)
    (rootChild : tree.source ∈ input.certified.executableLocalizedRerootChildren target) :
    ContextTreeRankReadback tree (LocalizedRuleMajorReference.descriptorMap input) unit := by
  have readerEq := LocalizedRuleMajorReference.molecularReader_eq_generatedReader input
    singleBonded acyclic target.occurrence
  have realizes' : LocalizedCumulativeTreeRealizes input.certified
      (input.certified.molecularReader (LocalizedRuleMajorReference.descriptorMap input)
        target.occurrence) tree := by
    rw [readerEq]
    exact realizes
  exact contextTreeRankReadback_of_realizedTree
    (LocalizedRuleMajorReference.descriptorMap input)
    (fun occurrence value observed =>
      LocalizedRuleMajorReference.descriptorMap_tetrahedral input occurrence value observed)
    singleBonded acyclic target unit targetUnit tree realizes' rootChild

/-- Convenient arm specialization for a rule-major tree whose source is an actual executable
child of an arbitrary contextual target. -/
theorem ruleMajorArmGeneratedContextTreeRankReadback
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (target : input.certified.LocalizedRerootCursor
      (input.certified.certified.input.molecule.atomCount + 1))
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.occurrence.1 = unit.1)
    (center : input.certified.TetrahedralCenter) (index : Fin 4)
    (stage : LocalizedCumulativeRule45Stage)
    (arm : input.certified.RuleMajorRootArm center index stage
      (input.certified.localizedDependencyLabel target.occurrence
        (input.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState input) target.occurrence)))
    (rootChild : arm.tree.source ∈ input.certified.executableLocalizedRerootChildren target) :
    ContextTreeRankReadback arm.tree (LocalizedRuleMajorReference.descriptorMap input) unit :=
  ruleMajorGeneratedContextTreeRankReadback input singleBonded acyclic target unit targetUnit
    arm.tree arm.realizes rootChild

end
end Rule4aTableBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ContextTreeRankReadback
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.contextTreeRankReadback_of_realizedTree
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorGeneratedContextTreeRankReadback
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorArmGeneratedContextTreeRankReadback
