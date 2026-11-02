import TetraStereo.OneCenter.LocalizedActualRankKeyBridge
import TetraStereo.OneCenter.LocalizedAcyclicBranchCarrier
import TetraStereo.OneCenter.LocalizedActualReferenceMolecularEvidence
import TetraStereo.KernelOnly

set_option autoImplicit false




















namespace TetraStereo.OneCenter
namespace Rule4aTableBridge

open LocalizedCumulativeDecoratedTree
open CertifiedLocalizedCIPInput
open CertifiedLocalizedCIPInput.OriginalRootArm
open DeclarativeCIP
open MolecularEvidenceTree

noncomputable section
open scoped Classical

/-! ## Whole-tree readback for the arm's own tree -/

theorem molecularReader_arm_observations {input : CertifiedLocalizedCIPInput}
    {center : input.TetrahedralCenter} {index : Fin 4} {stage : LocalizedCumulativeRule45Stage}
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
    (arm : input.OriginalRootArm center index stage (input.molecularReader descriptorMap target))
    (htargetRoot : target.1.root = center.1) (htargetAddress : target.1.address = [])
    (singleBonded : input.moleculeGraph.SimpleBonded) (acyclic : input.moleculeGraph.Acyclic) :
    ∀ node : (armGraph arm).Node,
      ∃ actual, subtreeAt? arm.tree node.1 = some actual ∧
        actual.label =
          (occurrenceReading input.moleculeGraph descriptorMap (input.topUnit center)
            (armGraph arm) node).toLocalizedLabel ∧
        occurrenceReading input.moleculeGraph descriptorMap (input.topUnit center)
          (armGraph arm) node ≠ .unavailable := by
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
      (armGraph arm) node =
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

/-! ## The generated descriptor map is tetrahedral -/

theorem actualReferenceDescriptorMap_tetrahedral (input : LocalizedUniversalReference.Input)
    (unit : DetectedOccurrence input.certified.moleculeGraph) (value : Descriptor)
    (h : actualReferenceDescriptorMap input unit = some value) : value.IsTetrahedral := by
  unfold actualReferenceDescriptorMap at h
  rcases Option.bind_eq_some_iff.1 h with ⟨occurrence, _, hmap⟩
  obtain ⟨label, _, rfl⟩ := Option.map_eq_some_iff.1 hmap
  cases label with
  | chiral rs => cases rs <;> trivial
  | pseudoasymmetric ps => cases ps <;> trivial

theorem occurrenceReading_tetrahedral_of_map {Atom : Type} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom)
    (htetra : ∀ u d, descriptorMap u = some d → d.IsTetrahedral) (node : graph.Node) :
    (occurrenceReading molecule descriptorMap unit graph node).IsTetrahedral := by
  unfold occurrenceReading
  split
  · rename_i steps _ _
    unfold readContext
    split
    · trivial
    · rename_i source _
      cases h : descriptorMap source with
      | none => trivial
      | some d => exact htetra source d h
  · trivial

/-! ## Rule 3 is absent without multiple bonds -/

theorem rule4aOnly_rankEvidence_of_simpleBonded {input : CertifiedLocalizedCIPInput}
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph) (graph : RootedDigraph input.Atom) :
    Rule4aOnly graph (rankEvidence input.moleculeGraph descriptorMap unit graph) := by
  intro rule hrule node
  cases rule with
  | rule4aStereogenicUnitKind => exact absurd rfl hrule
  | rule3DoubleBondGeometry =>
      have hsingle : ∀ atom other, input.moleculeGraph.bond atom other ≤ 1 := by
        intro atom other
        rcases Nat.eq_zero_or_pos (input.moleculeGraph.bond atom other) with hzero | hpos
        · rw [hzero]; exact Nat.zero_le 1
        · exact le_of_eq (singleBonded atom other hpos)
      have hrule3 := molecularEvidence_rule3_eq_none input.moleculeGraph hsingle descriptorMap unit
        graph node
      change rule3Observation input.moleculeGraph descriptorMap unit graph node = none at hrule3
      show stereoValue .rule3DoubleBondGeometry (some (rankEvidence _ _ _ _ node)) = ⊥
      simp [stereoValue, rankEvidence, hrule3, liftObservation]
  | rule4bLikeUnlikeDescriptorPairs => rfl
  | rule4cPseudoasymmetricDescriptor => rfl
  | rule5EnantiomorphicDescriptor => rfl

/-! ## Assembly -/

theorem armReadback_of_treeLike (input : LocalizedUniversalReference.Input)
    {center : input.certified.TetrahedralCenter} {index : Fin 4}
    (target : input.certified.LocalizedCIPOccurrence
      (input.certified.certified.input.molecule.atomCount + 1))
    (htargetRoot : target.1.root = center.1) (htargetAddress : target.1.address = [])
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (arm : input.certified.OriginalRootArm center index .rule4a
      (input.certified.molecularReader (actualReferenceDescriptorMap input) target)) :
    ArmReadback arm (actualReferenceDescriptorMap input) (input.certified.topUnit center) := by
  have readback := molecularReader_arm_observations (actualReferenceDescriptorMap input) target arm
    htargetRoot htargetAddress singleBonded acyclic
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro node actual lookup
    obtain ⟨actual', lookup', hlabel, _⟩ := readback node
    rw [decoratedSubtreeAt?_eq_subtreeAt?] at lookup
    cases Option.some.inj (lookup.symm.trans lookup')
    exact hlabel
  · intro node
    exact occurrenceReading_tetrahedral_of_map _ _ _ _
      (fun u d h => actualReferenceDescriptorMap_tetrahedral input u d h) node
  · intro node
    obtain ⟨_, _, _, havail⟩ := readback node
    exact havail
  · exact rule4aOnly_rankEvidence_of_simpleBonded singleBonded _ _ _

/-- **Headline.**  On a finite acyclic single-bond input, the actual stage-`.rule4a` addressing of
every original-root arm of the actual molecular reader is an ordinary canonical addressing for the
pre-Rule-4b molecular evidence.  No restriction on the number of nearest references is used. -/
theorem arm_ordinaryCanonicalAddressing_rankEvidence_of_treeLike
    (input : LocalizedUniversalReference.Input)
    {center : input.certified.TetrahedralCenter} {index : Fin 4}
    (target : input.certified.LocalizedCIPOccurrence
      (input.certified.certified.input.molecule.atomCount + 1))
    (htargetRoot : target.1.root = center.1) (htargetAddress : target.1.address = [])
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (arm : input.certified.OriginalRootArm center index .rule4a
      (input.certified.molecularReader (actualReferenceDescriptorMap input) target)) :
    OrdinaryCanonicalAddressing input.certified.moleculeGraph
      (rankEvidence input.certified.moleculeGraph (actualReferenceDescriptorMap input)
        (input.certified.topUnit center) (armGraph arm))
      (toOfficialSourceTree arm.tree).declarativeAddressing :=
  arm_ordinaryCanonicalAddressing_rankEvidence arm
    (armReadback_of_treeLike input target htargetRoot htargetAddress singleBonded acyclic arm)

end
end Rule4aTableBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.molecularReader_arm_observations
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.actualReferenceDescriptorMap_tetrahedral
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.rule4aOnly_rankEvidence_of_simpleBonded
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.armReadback_of_treeLike
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.arm_ordinaryCanonicalAddressing_rankEvidence_of_treeLike
