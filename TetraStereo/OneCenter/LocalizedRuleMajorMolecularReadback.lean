import TetraStereo.OneCenter.LocalizedRuleMajorCumulativeTrace
import TetraStereo.OneCenter.LocalizedActualArmReadback
import TetraStereo.OneCenter.LocalizedOrderedMolecularEvidence
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Actual molecule-to-reader correspondence for the whole-rule builder. The physical
rigid/twin assumptions are absent: labels may be chiral, pseudoasymmetric or absent, and
all actual nodes are read directly from the supplied molecular descriptor map. -/

namespace TetraStereo.OneCenter
namespace Rule4aTableBridge
open LocalizedCumulativeDecoratedTree CertifiedLocalizedCIPInput
open DeclarativeCIP MolecularEvidenceTree
noncomputable section
open scoped Classical

theorem ruleMajor_molecularReader_arm_observations {input : CertifiedLocalizedCIPInput}
    {center : input.TetrahedralCenter} {index : Fin 4} {stage : LocalizedCumulativeRule45Stage}
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
    (arm : input.RuleMajorRootArm center index stage (input.molecularReader descriptorMap target))
    (htargetRoot : target.1.root = center.1) (htargetAddress : target.1.address = [])
    (singleBonded : input.moleculeGraph.SimpleBonded) (acyclic : input.moleculeGraph.Acyclic) :
    ∀ node : ((toOfficialSourceTree arm.tree).toDeclarativeDigraph).Node,
      ∃ actual, subtreeAt? arm.tree node.1 = some actual ∧
        actual.label =
          (occurrenceReading input.moleculeGraph descriptorMap (input.topUnit center)
            ((toOfficialSourceTree arm.tree).toDeclarativeDigraph) node).toLocalizedLabel ∧
        occurrenceReading input.moleculeGraph descriptorMap (input.topUnit center)
          ((toOfficialSourceTree arm.tree).toDeclarativeDigraph) node ≠ .unavailable := by
  have realizes := arm.realizes
  have generated := arm.generated
  have treeRoot := arm.root
  have hsource := arm.source
  have incoming : LocalizedCumulativeTreeIncoming input arm.tree :=
    input.localizedCumulativeTreeIncoming_of_realizes _ arm.tree realizes
      (by rw [hsource]; exact input.localizedLigandRootCursor_incoming center index)
  intro node
  obtain ⟨erased, herased⟩ :=
    OfficialCIPSourceTree.exists_subtreeAt?_eq_some_of_mem_hierarchyAddresses
      (toOfficialSourceTree arm.tree) node.1 node.2
  rw [toOfficialSourceTree_subtreeAt?_eq, Option.map_eq_some_iff] at herased
  obtain ⟨actual, hactual, rfl⟩ := herased
  refine ⟨actual, hactual, ?_⟩
  have hlookup : (toOfficialSourceTree arm.tree).subtreeAt? node.1 =
      some (toOfficialSourceTree actual) := by
    rw [toOfficialSourceTree_subtreeAt?_eq, hactual]
    rfl
  have hlabel := OfficialCIPSourceTree.declarativeLabel_eq_of_subtreeAt? (toOfficialSourceTree arm.tree)
    _ node hlookup
  -- every carrier occurrence is a real atom on a tree-like input
  have hrealCursor : actual.source.occurrence.1.node.provenance = .realAtom :=
    input.carrierOccurrence_provenance_real singleBonded acyclic actual.source.occurrence
  have hrealSource : (toOfficialSourceTree actual).source.provenance = .realAtom := by
    rw [toOfficialSourceTree_source]; exact hrealCursor
  have hprovenance : ((toOfficialSourceTree arm.tree).toDeclarativeDigraph.label node).provenance =
      (toOfficialSourceTree actual).source.provenance.toDeclarative := by
    change ((toOfficialSourceTree arm.tree).declarativeLabel node).provenance = _
    rw [hlabel]
    rfl
  have hreal : ((toOfficialSourceTree arm.tree).toDeclarativeDigraph.label node).provenance =
      .realAtom := by
    rw [hprovenance, hrealSource]; rfl
  have rootCurrent : (toOfficialSourceTree arm.tree).source.current? =
      some (input.canonicalLigandAtom center index) := by rw [treeRoot]; rfl
  obtain ⟨rest, hpath, hhistory⟩ :=
    generated_history input.executableOfficialCIPChildren
      (executableOfficialCIPChildren_extend input) node.1 (toOfficialSourceTree arm.tree) _
      (input.canonicalLigandAtom center index) generated rootCurrent hlookup
  have hligand : input.canonicalLigandAtom center index ≠ center.1 := by
    intro h
    have hadj := input.canonicalLigandAtom_adj center index
    rw [show input.canonicalLigandAtom center index = center.1 from h] at hadj
    simp [MoleculeGraph.Adj, input.moleculeGraph.bond_self] at hadj
  have rootNodup : (toOfficialSourceTree arm.tree).source.history.Nodup := by
    rw [treeRoot]
    simp [OfficialCIPNode.rootFromEdge, hligand]
  have hnodup := generated_nodup input.executableOfficialCIPChildren
    (executableOfficialCIPChildren_extend input) (executableOfficialCIPChildren_terminal input)
    node.1 (toOfficialSourceTree arm.tree) _ generated rootNodup hlookup hrealSource
  have rootHistory : (toOfficialSourceTree arm.tree).source.history =
      [input.canonicalLigandAtom center index, center.1] := by rw [treeRoot]; rfl
  have hcursorHistory : actual.source.occurrence.1.node.history =
      (center.1 :: input.canonicalLigandAtom center index :: rest).reverse := by
    rw [← toOfficialSourceTree_source, hhistory, rootHistory]
    simp
  have hsteps : ancestorAtoms (toOfficialSourceTree arm.tree).toDeclarativeDigraph node =
      some (input.canonicalLigandAtom center index :: rest) := by
    rw [ancestorAtoms, ancestorPath_toDeclarativeDigraph, hpath]
    exact mapM_id_map_some _
  have hroot : actual.source.occurrence.1.root = center.1 := by
    rw [subtreeAt?_source_occurrence_root_eq realizes hactual, hsource]
    rfl
  have haddress : actual.source.occurrence.1.address ≠ [] :=
    address_ne_nil_of_incoming (incoming_of_subtreeAt? node.1 arm.tree actual incoming hactual)
  have hsimple : (center.1 :: input.canonicalLigandAtom center index :: rest).Nodup := by
    rw [← List.nodup_reverse, ← hcursorHistory, ← toOfficialSourceTree_source]
    exact hnodup
  have hreading : occurrenceReading input.moleculeGraph descriptorMap (input.topUnit center)
      ((toOfficialSourceTree arm.tree).toDeclarativeDigraph) node =
        readContext input.moleculeGraph descriptorMap (input.topUnit center)
          (input.canonicalLigandAtom center index :: rest) :=
    occurrenceReading_eq_readContext input.moleculeGraph descriptorMap (input.topUnit center) _ hreal
      hsteps
  refine ⟨?_, ?_⟩
  · rw [subtreeAt?_node_label_eq_read realizes hactual, hreading]
    exact input.molecularReader_eq_readContext descriptorMap target actual.source (input.topUnit center)
      rfl htargetRoot htargetAddress hroot haddress hrealCursor
      (input.canonicalLigandAtom center index :: rest)
      hcursorHistory hsimple
      (List.cons_ne_nil _ _)
  · rw [hreading]
    unfold readContext
    split
    · simp
    · rename_i source _
      cases descriptorMap source <;> simp

/-- The actual ordered state only emits tetrahedral descriptor values, with both uppercase and
lowercase cases retained. No physical rigidity premise is needed. -/
theorem actualOrderedReferenceDescriptorMap_tetrahedral (input : LocalizedUniversalReference.Input)
    (unit : DetectedOccurrence input.certified.moleculeGraph) (value : Descriptor)
    (observed : actualOrderedReferenceDescriptorMap input unit = some value) :
    value.IsTetrahedral := by
  unfold actualOrderedReferenceDescriptorMap at observed
  obtain ⟨occurrence, _, mapped⟩ := Option.bind_eq_some_iff.1 observed
  obtain ⟨label, _, rfl⟩ := Option.map_eq_some_iff.1 mapped
  cases label with
  | chiral rs => cases rs <;> trivial
  | pseudoasymmetric ps => cases ps <;> trivial

end
end Rule4aTableBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajor_molecularReader_arm_observations
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.actualOrderedReferenceDescriptorMap_tetrahedral
