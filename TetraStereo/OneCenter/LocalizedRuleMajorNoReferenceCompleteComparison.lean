import TetraStereo.OneCenter.LocalizedRuleMajorNoReferenceRule4cTableBridge
import TetraStereo.OneCenter.LocalizedRuleMajorActualCompleteReadingComparison
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Node-major no-reference Rule-4c descriptors reduce to their scalar Rule-4c column when
Rule 4a ties. The actual molecular reading comparison then follows from faithful-arm evidence. -/

namespace TetraStereo.OneCenter
namespace Rule4cObservationBridge

open CertifiedLocalizedCIPInput LocalizedCumulativeDecoratedTree
open Rule4aTableBridge DeclarativeCIP OfficialSparseCanonicalVectorComparison
noncomputable section

private theorem compareSparseLayer_noReference_pair_of_fst_eq :
    ∀ (left right : List (OfficialSparseEntry (Nat × Nat))),
      left.map (sparseEntryMap Prod.fst) = right.map (sparseEntryMap Prod.fst) →
      OfficialRuleMajorKey.compareSparseLayer compareLocalizedCumulativeRule45Priority
          (left.map (sparseEntryMap fun p => [p.1, p.2]))
          (right.map (sparseEntryMap fun p => [p.1, p.2])) =
        OfficialRuleMajorKey.compareSparseLayer OfficialRuleMajorKey.compareNat
          (left.map (sparseEntryMap Prod.snd)) (right.map (sparseEntryMap Prod.snd))
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | le :: lt, re :: rt, h => by
      simp only [List.map_cons, List.cons.injEq, sparseEntryMap, Prod.mk.injEq] at h
      obtain ⟨⟨addressEq, firstEq⟩, tailEq⟩ := h
      simp only [List.map_cons, OfficialRuleMajorKey.compareSparseLayer, List.compareLex_cons_cons]
      rw [← OfficialRuleMajorKey.compareSparseLayer, ← OfficialRuleMajorKey.compareSparseLayer,
        compareSparseLayer_noReference_pair_of_fst_eq lt rt (by
          simpa only [List.map_cons, sparseEntryMap] using tailEq)]
      congr 1
      unfold OfficialRuleMajorKey.compareSparseEntry sparseEntryMap
      simp only [compareLex, Ordering.byKey, addressEq, firstEq]
      congr 1
      unfold compareLocalizedCumulativeRule45Priority
      simp only [List.compareLex_cons_cons, List.compareLex_nil_nil,
        CompilerProjectionFidelity.compareNat_self]
      cases OfficialRuleMajorKey.compareNat le.2.2 re.2.2 <;> rfl

private theorem compareSparseLayers_noReference_pair_of_fst_eq :
    ∀ (left right : List (List (OfficialSparseEntry (Nat × Nat)))),
      left.map (List.map (sparseEntryMap Prod.fst)) =
          right.map (List.map (sparseEntryMap Prod.fst)) →
      OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
          (left.map (List.map (sparseEntryMap fun p => [p.1, p.2])))
          (right.map (List.map (sparseEntryMap fun p => [p.1, p.2]))) =
        OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
          (left.map (List.map (sparseEntryMap Prod.snd)))
          (right.map (List.map (sparseEntryMap Prod.snd)))
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | ll :: ltail, rr :: rtail, h => by
      simp only [List.map_cons, List.cons.injEq] at h
      simp only [List.map_cons, OfficialRuleMajorKey.compareSparseLayers, List.compareLex_cons_cons]
      rw [← OfficialRuleMajorKey.compareSparseLayers, ← OfficialRuleMajorKey.compareSparseLayers,
        compareSparseLayers_noReference_pair_of_fst_eq ltail rtail h.2,
        compareSparseLayer_noReference_pair_of_fst_eq ll rr h.1]

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
  {treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel}
  {keyL keyR : input.LocalizedRerootCumulativeRule45Key}

theorem descriptor_eq_pair_noReference
    (matchL : LocalizedCumulativeTreeTableMatch .rule4cNoReference treeL keyL)
    (matchR : LocalizedCumulativeTreeTableMatch .rule4cNoReference treeR keyR) :
    keyL.descriptor =
        (table (fun node => (prio4a node, localizedRule4cPriority node.label)) treeL).map
          (List.map (sparseEntryMap fun p => [p.1, p.2])) ∧
    keyR.descriptor =
        (table (fun node => (prio4a node, localizedRule4cPriority node.label)) treeR).map
          (List.map (sparseEntryMap fun p => [p.1, p.2])) := by
  constructor
  · rw [← matchL.2.2.2, tables_descriptor, table_map]
    rfl
  · rw [← matchR.2.2.2, tables_descriptor, table_map]
    rfl

/-- Under an actual Rule-4a column tie, node-major no-reference Rule-4c descriptors compare
exactly as the whole no-reference Rule-4c column. Lowercase labels are retained. -/
theorem compare_descriptor_eq_scalar4b_of_prior_scalar4a_eq
    (matchL : LocalizedCumulativeTreeTableMatch .rule4cNoReference treeL keyL)
    (matchR : LocalizedCumulativeTreeTableMatch .rule4cNoReference treeR keyR)
    (priorTie : scalar4a keyL = scalar4a keyR) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        keyL.descriptor keyR.descriptor =
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (scalar4b keyL) (scalar4b keyR) := by
  rcases descriptor_eq_pair_noReference matchL matchR with ⟨descL, descR⟩
  rw [descL, descR, scalar4b_noReference_eq_rule4cTable matchL,
    scalar4b_noReference_eq_rule4cTable matchR]
  rw [← table_map (fun node => (prio4a node, localizedRule4cPriority node.label)) Prod.snd,
    ← table_map (fun node => (prio4a node, localizedRule4cPriority node.label)) Prod.snd]
  apply compareSparseLayers_noReference_pair_of_fst_eq
  rw [table_map, table_map]
  rw [← scalar4a_eq_table_anyStage matchL, ← scalar4a_eq_table_anyStage matchR]
  exact priorTie

end
end Rule4cObservationBridge

namespace Rule4aTableBridge
open CertifiedLocalizedCIPInput LocalizedCumulativeDecoratedTree DeclarativeCIP
open Rule4cObservationBridge OfficialSparseCanonicalVectorComparison
noncomputable section

variable {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter}
  {leftIndex rightIndex : Fin 4} {leftReference rightReference : RS}
  (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
  (tetrahedral : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
  (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
  (targetRoot : target.1.root = center.1) (targetAddress : target.1.address = [])
  (singleBonded : input.moleculeGraph.SimpleBonded) (acyclic : input.moleculeGraph.Acyclic)

include tetrahedral targetRoot targetAddress singleBonded acyclic

/-- The actual no-reference arm descriptor comparison is the independent molecular
Rule-4c complete-reading comparison, after the earlier Rule-1a and Rule-4a ties. -/
theorem actual_ruleMajor_noReference_completeReading_compare
    (left : input.RuleMajorRootArm center leftIndex .rule4cNoReference
      (input.molecularReader descriptorMap target))
    (right : input.RuleMajorRootArm center rightIndex .rule4cNoReference
      (input.molecularReader descriptorMap target))
    (graphL graphR : RootedDigraph input.Atom)
    (faithfulL : graphL.FaithfulExactExpansion input.moleculeGraph center.1
      (input.canonicalLigandAtom center leftIndex))
    (faithfulR : graphR.FaithfulExactExpansion input.moleculeGraph center.1
      (input.canonicalLigandAtom center rightIndex))
    {W D : Nat} (widthL : (ruleMajorArmGraph left).width ≤ W)
    (depthL : (ruleMajorArmGraph left).height ≤ D)
    (widthR : (ruleMajorArmGraph right).width ≤ W)
    (depthR : (ruleMajorArmGraph right).height ≤ D)
    (tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      left.key.constitutional.rule1a right.key.constitutional.rule1a = .eq)
    (tied4a : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (scalar4a left.key) (scalar4a right.key) = .eq) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        left.key.descriptor right.key.descriptor =
      compare
        (ofLex (completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
          graphL W D none)).2
        (ofLex (completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
          graphR W D none)).2 := by
  have priorScalarTie : scalar4a left.key = scalar4a right.key :=
    (compareSparseLayers_compareNat_eq_iff _ _).mp tied4a
  rw [Rule4cObservationBridge.compare_descriptor_eq_scalar4b_of_prior_scalar4a_eq
    left.tableMatch right.tableMatch priorScalarTie]
  exact actual_ruleMajor_noReference4c_compare descriptorMap tetrahedral target targetRoot
    targetAddress singleBonded acyclic left right graphL graphR faithfulL faithfulR
    widthL depthL widthR depthR tied tied4a

omit tetrahedral targetRoot targetAddress singleBonded acyclic in
/-- At a stage-`.rule4a` table match, an equal scalar Rule-4a column makes the node-major
singleton-vector descriptors identical. -/
theorem compare_rule4a_descriptor_eq_of_scalar4a_tie
    {carrierFuel : Nat} {treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel}
    {keyL keyR : input.LocalizedRerootCumulativeRule45Key}
    (matchL : LocalizedCumulativeTreeTableMatch .rule4a treeL keyL)
    (matchR : LocalizedCumulativeTreeTableMatch .rule4a treeR keyR)
    (scalarTie : scalar4a keyL = scalar4a keyR) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        keyL.descriptor keyR.descriptor = .eq := by
  have descriptorTie : keyL.descriptor = keyR.descriptor := by
    rw [descriptor_eq_map_single matchL, descriptor_eq_map_single matchR,
      ← scalar4a_eq_table matchL, ← scalar4a_eq_table matchR, scalarTie]
  exact (compareSparseLayers_compareLocalizedCumulativeRule45Priority_eq_iff
    keyL.descriptor keyR.descriptor).2 descriptorTie

end
end Rule4aTableBridge

assert_kernel_only TetraStereo.OneCenter.Rule4cObservationBridge.compare_descriptor_eq_scalar4b_of_prior_scalar4a_eq
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.actual_ruleMajor_noReference_completeReading_compare
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.compare_rule4a_descriptor_eq_of_scalar4a_tie
