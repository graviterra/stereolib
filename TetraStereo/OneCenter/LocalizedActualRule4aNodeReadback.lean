import TetraStereo.OneCenter.LocalizedActualRule4aTableBridge
import TetraStereo.OneCenter.DeclarativeCIPRankKeyProjection
import TetraStereo.OneCenter.DeclarativeCIPMolecularReferenceSelection
import TetraStereo.OneCenter.LocalizedActualMolecularEvidenceRefinement
import TetraStereo.KernelOnly

set_option autoImplicit false



















namespace TetraStereo.OneCenter
namespace Rule4aTableBridge

open LocalizedCumulativeDecoratedTree
open CertifiedLocalizedCIPInput
open CertifiedLocalizedCIPInput.OriginalRootArm
open OfficialSparseCanonicalVectorComparison
open DeclarativeCIP

noncomputable section
open scoped Classical

/-! ## The two subtree lookups agree -/

theorem decoratedSubtreeAt?_eq_subtreeAt? {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat} :
    ∀ (tree : LocalizedCumulativeDecoratedTree input carrierFuel) (path : List Nat),
      tree.decoratedSubtreeAt? path = subtreeAt? tree path
  | _, [] => rfl
  | tree, slot :: rest => by
      rw [decoratedSubtreeAt?, subtreeAt?_cons]
      cases tree.children[slot]? with
      | none => rfl
      | some child => exact decoratedSubtreeAt?_eq_subtreeAt? child rest

/-! ## Encoded Rule-4a observations of a table-matched realized key -/

theorem encoded4a_nil {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {dsub : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (tableMatch : LocalizedCumulativeTreeTableMatch .rule4a dsub key)
    (realizes : LocalizedCumulativeTreeRealizes input read dsub) :
    encoded4a key [] = (((code (prio4a dsub) : StereoCode) : StereoLabel) : WithBot StereoLabel) := by
  unfold encoded4a
  have hpresent : SparseSupportAlignment.HasAddress key.constitutional.rule1a [] := by
    have viaTable : SparseSupportAlignment.HasAddress
        (table (fun node => node.atomicNumber) dsub) [] :=
      (hasAddress_atomicNumber_table_iff_subtree realizes []).2 ⟨dsub, rfl⟩
    simpa [← tableMatch.1, tables_rule1a] using viaTable
  rw [if_pos hpresent, scalar4a_eq_table tableMatch, tableValue_table_eq_observeAt prio4a dsub []]
  rfl

theorem encoded4a_cons_of_key {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {dsub : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (tableMatch : LocalizedCumulativeTreeTableMatch .rule4a dsub key)
    (realizes : LocalizedCumulativeTreeRealizes input read dsub)
    {sortedKeys : List input.LocalizedRerootCumulativeRule45Key}
    (paired : List.Forall₂ (fun childKey childTree =>
        LocalizedCumulativeTreeTableMatch .rule4a childTree childKey ∧
          LocalizedCumulativeTreeRealizes input read childTree) sortedKeys dsub.children)
    (digit : Nat) (path : List Nat) :
    encoded4a key (digit :: path) =
      ((sortedKeys[digit]?).map fun childKey => encoded4a childKey path).getD ⊥ := by
  have keysLength : sortedKeys.length = dsub.children.length := List.Forall₂.length_eq paired
  unfold encoded4a
  by_cases hpresent : SparseSupportAlignment.HasAddress key.constitutional.rule1a (digit :: path)
  · rw [if_pos hpresent]
    have guardTable : SparseSupportAlignment.HasAddress
        (table (fun node => node.atomicNumber) dsub) (digit :: path) := by
      simpa [← tableMatch.1, tables_rule1a] using hpresent
    obtain ⟨subtree, subtreeLookup⟩ :=
      (hasAddress_atomicNumber_table_iff_subtree realizes (digit :: path)).1 guardTable
    obtain ⟨child, subtree', childGet, childPath⟩ :=
      (decoratedSubtreeAt?_cons_some dsub digit path).1 ⟨subtree, subtreeLookup⟩
    have digitLtChildren : digit < dsub.children.length := (List.getElem?_eq_some_iff.1 childGet).1
    have digitLtKeys : digit < sortedKeys.length := by simpa [keysLength] using digitLtChildren
    have keysGet : sortedKeys[digit]? = some (sortedKeys[digit]'digitLtKeys) :=
      List.getElem?_eq_getElem digitLtKeys
    have childIs : child = dsub.children[digit]'digitLtChildren :=
      (Option.some.inj ((List.getElem?_eq_getElem digitLtChildren).symm.trans childGet)).symm
    have slotPaired : LocalizedCumulativeTreeTableMatch .rule4a
        (dsub.children[digit]'digitLtChildren) (sortedKeys[digit]'digitLtKeys) ∧
        LocalizedCumulativeTreeRealizes input read (dsub.children[digit]'digitLtChildren) :=
      List.Forall₂.get (i := digit) paired digitLtKeys digitLtChildren
    have childSubtree : (dsub.children[digit]'digitLtChildren).decoratedSubtreeAt? path =
        some subtree' := by
      simpa [childIs] using childPath
    have childGuard : SparseSupportAlignment.HasAddress
        (sortedKeys[digit]'digitLtKeys).constitutional.rule1a path := by
      have viaChildTable : SparseSupportAlignment.HasAddress
          (table (fun node => node.atomicNumber) (dsub.children[digit]'digitLtChildren)) path :=
        (hasAddress_atomicNumber_table_iff_subtree slotPaired.2 path).2 ⟨subtree', childSubtree⟩
      simpa [← slotPaired.1.1, tables_rule1a] using viaChildTable
    rw [keysGet]
    simp only [Option.map_some, Option.getD_some]
    rw [if_pos childGuard]
    have valueEq : SparsePhysicalFirstDifference.tableValue (scalar4a key) (digit :: path) =
        SparsePhysicalFirstDifference.tableValue (scalar4a (sortedKeys[digit]'digitLtKeys)) path := by
      rw [scalar4a_eq_table tableMatch, scalar4a_eq_table slotPaired.1,
        tableValue_table_eq_observeAt, tableValue_table_eq_observeAt]
      unfold observeAt
      rw [decoratedSubtreeAt?, childGet, childIs]
    rw [valueEq]
  · rw [if_neg hpresent]
    cases keysGet : sortedKeys[digit]? with
    | none => rfl
    | some childKey =>
        simp only [Option.map_some, Option.getD_some]
        have digitLtKeys : digit < sortedKeys.length := (List.getElem?_eq_some_iff.1 keysGet).1
        have digitLtChildren : digit < dsub.children.length := by omega
        have slotPaired : LocalizedCumulativeTreeTableMatch .rule4a
            (dsub.children[digit]'digitLtChildren) (sortedKeys[digit]'digitLtKeys) ∧
            LocalizedCumulativeTreeRealizes input read (dsub.children[digit]'digitLtChildren) :=
          List.Forall₂.get (i := digit) paired digitLtKeys digitLtChildren
        have childKeyIs : childKey = sortedKeys[digit]'digitLtKeys :=
          Option.some.inj (keysGet.symm.trans (List.getElem?_eq_getElem digitLtKeys))
        rw [if_neg]
        intro childGuard
        apply hpresent
        have viaChildTable : SparseSupportAlignment.HasAddress
            (table (fun node => node.atomicNumber) (dsub.children[digit]'digitLtChildren)) path := by
          rw [childKeyIs] at childGuard
          simpa [← slotPaired.1.1, tables_rule1a] using childGuard
        obtain ⟨subtree', childPath⟩ :=
          (hasAddress_atomicNumber_table_iff_subtree slotPaired.2 path).1 viaChildTable
        have lookup : ∃ subtree, dsub.decoratedSubtreeAt? (digit :: path) = some subtree :=
          (decoratedSubtreeAt?_cons_some dsub digit path).2
            ⟨_, subtree', List.getElem?_eq_getElem digitLtChildren, childPath⟩
        have viaTable := (hasAddress_atomicNumber_table_iff_subtree realizes (digit :: path)).2 lookup
        simpa [← tableMatch.1, tables_rule1a] using viaTable

/-! ## The independent Rule-4a label of an available reading -/

theorem stereoLabel_rankEvidence_rule4a {input : CertifiedLocalizedCIPInput}
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph) (graph : RootedDigraph input.Atom)
    (node : graph.Node)
    (havail : occurrenceReading input.moleculeGraph descriptorMap unit graph node ≠ .unavailable) :
    stereoLabel graph (rankEvidence input.moleculeGraph descriptorMap unit graph)
        .rule4aStereogenicUnitKind node =
      ((code (occurrenceReading input.moleculeGraph descriptorMap unit graph node).kindPriority :
        StereoCode) : StereoLabel) := by
  unfold stereoLabel stereoValue rankEvidence rule4aObservation
  cases h : occurrenceReading input.moleculeGraph descriptorMap unit graph node with
  | unavailable => exact absurd h havail
  | outsideInventory => rfl
  | unassigned => rfl
  | descriptor value => rfl

theorem prio4a_eq_kindPriority {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (dsub : LocalizedCumulativeDecoratedTree input carrierFuel) (reading : OccurrenceReading)
    (hlabel : dsub.label = reading.toLocalizedLabel) (htetra : reading.IsTetrahedral) :
    prio4a dsub = reading.kindPriority := by
  unfold prio4a
  rw [hlabel]
  exact kindPriority_eq_runtime reading htetra

/-- The independent Rule-4a observation at the empty path equals the encoded actual observation. -/
theorem stereoNodePathObservation_nil_eq_encoded4a {input : CertifiedLocalizedCIPInput}
    {carrierFuel : Nat} {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph) (graph : RootedDigraph input.Atom) (W D : Nat)
    (node : graph.Node) {dsub : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (tableMatch : LocalizedCumulativeTreeTableMatch .rule4a dsub key)
    (realizes : LocalizedCumulativeTreeRealizes input read dsub)
    (hlabel : dsub.label =
      (occurrenceReading input.moleculeGraph descriptorMap unit graph node).toLocalizedLabel)
    (htetra : (occurrenceReading input.moleculeGraph descriptorMap unit graph node).IsTetrahedral)
    (havail : occurrenceReading input.moleculeGraph descriptorMap unit graph node ≠ .unavailable) :
    stereoNodePathObservation input.moleculeGraph graph
        (rankEvidence input.moleculeGraph descriptorMap unit graph) W D
        .rule4aStereogenicUnitKind node [] = encoded4a key [] := by
  rw [stereoNodePathObservation_nil, stereoLabel_rankEvidence_rule4a descriptorMap unit graph node havail,
    encoded4a_nil tableMatch realizes, prio4a_eq_kindPriority dsub _ hlabel htetra]

/-! ## Descending actual keys are descending pair keys -/

theorem pairKey_le_of_compare_ne_lt {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {graph : RootedDigraph input.Atom} (evidence : StereochemicalEvidence graph)
    {treeI treeJ : LocalizedCumulativeDecoratedTree input carrierFuel}
    {keyI keyJ : input.LocalizedRerootCumulativeRule45Key}
    (matchI : LocalizedCumulativeTreeTableMatch .rule4a treeI keyI)
    (matchJ : LocalizedCumulativeTreeTableMatch .rule4a treeJ keyJ)
    (realizesI : LocalizedCumulativeTreeRealizes input read treeI)
    (realizesJ : LocalizedCumulativeTreeRealizes input read treeJ)
    {W D : Nat} {childI childJ : graph.Node}
    (repI : Represents W D (ruleKey input.moleculeGraph graph W D childI) keyI.constitutional)
    (repJ : Represents W D (ruleKey input.moleculeGraph graph W D childJ) keyJ.constitutional)
    (rep4I : Represents4a W D (rule4aComponent input.moleculeGraph graph evidence W D childI) keyI)
    (rep4J : Represents4a W D (rule4aComponent input.moleculeGraph graph evidence W D childJ) keyJ)
    (hne : input.compareLocalizedRerootCumulativeRule45Keys keyI keyJ ≠ Ordering.lt) :
    pairKey input.moleculeGraph graph evidence W D childJ ≤
      pairKey input.moleculeGraph graph evidence W D childI := by
  have wfI := wellFormedRuleMajorKey_of_tableMatch matchI realizesI
  have wfJ := wellFormedRuleMajorKey_of_tableMatch matchJ realizesJ
  have hconst : OfficialRuleMajorKey.compare keyI.constitutional keyJ.constitutional =
      compare (ruleKey input.moleculeGraph graph W D childI)
        (ruleKey input.moleculeGraph graph W D childJ) :=
    compare_eq_compare_vector wfI wfJ
      (ruleKey_vectorWellShaped input.moleculeGraph graph W D childI)
      (ruleKey_vectorWellShaped input.moleculeGraph graph W D childJ) repI repJ
  unfold pairKey
  unfold compareLocalizedRerootCumulativeRule45Keys at hne
  rcases h : OfficialRuleMajorKey.compare keyI.constitutional keyJ.constitutional with _ | _ | _
  · exact absurd (by simp [compareLex, Ordering.byKey, h]) hne
  · have veq : ruleKey input.moleculeGraph graph W D childI =
        ruleKey input.moleculeGraph graph W D childJ :=
      (vectorCompare_eq_iff _ _).1 (hconst.symm.trans h)
    have hdesc : OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        keyI.descriptor keyJ.descriptor ≠ Ordering.lt := by
      simpa [compareLex, Ordering.byKey, h] using hne
    have rule1aTie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        keyI.constitutional.rule1a keyJ.constitutional.rule1a = Ordering.eq := by
      unfold OfficialRuleMajorKey.compare at h
      exact (compareLex_eq_eq.1 h).1
    rw [compare_descriptor_eq_compare_key matchI matchJ realizesI realizesJ rule1aTie
      (ordinaryKey_stereo_wellShaped input.moleculeGraph graph evidence W D _ childI)
      (ordinaryKey_stereo_wellShaped input.moleculeGraph graph evidence W D _ childJ)
      rep4I rep4J] at hdesc
    have hle : rule4aComponent input.moleculeGraph graph evidence W D childJ ≤
        rule4aComponent input.moleculeGraph graph evidence W D childI :=
      not_lt.1 fun hlt => hdesc ((stereoKeyCompare_lt_iff _ _).2 hlt)
    rw [Prod.Lex.le_iff]
    exact Or.inr ⟨veq.symm, hle⟩
  · have hlt : ruleKey input.moleculeGraph graph W D childJ <
        ruleKey input.moleculeGraph graph W D childI :=
      (vectorCompare_gt_iff _ _).1 (hconst.symm.trans h)
    rw [Prod.Lex.le_iff]
    exact Or.inl hlt

/-! ## A component observes `⊥` exactly off the shared layout -/

theorem stereoNodePathObservation_eq_bot_iff {Atom : Type} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (graph : RootedDigraph Atom)
    (evidence : StereochemicalEvidence graph) (rule : StereochemicalRule) (W D : Nat) :
    ∀ (path : List Nat) (node : graph.Node),
      stereoNodePathObservation molecule graph evidence W D rule node path = ⊥ ↔
        nodePathObservation molecule graph W D 0 node path = ⊥
  | [], node => by
      rw [stereoNodePathObservation_nil, nodePathObservation_nil molecule graph (by omega)]
      simp
  | digit :: path, node => by
      obtain ⟨ranked, hperm, hsorted⟩ := exists_ordinaryRanked molecule graph evidence W D node
      rw [stereoNodePathObservation_cons molecule graph evidence W D rule node hperm hsorted,
        nodePathObservation_cons molecule graph (by omega) node hperm
          (ruleKey_sorted_of_ordinary_sorted molecule graph evidence W D hsorted)]
      by_cases hguard : digit < W ∧ path.length < D
      · rw [if_pos hguard, if_pos hguard]
        cases ranked[digit]? with
        | none => simp
        | some child =>
            simp only [Option.map_some, Option.getD_some]
            exact stereoNodePathObservation_eq_bot_iff molecule graph evidence rule W D path child
      · rw [if_neg hguard, if_neg hguard]
        simp

end
end Rule4aTableBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.decoratedSubtreeAt?_eq_subtreeAt?
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.encoded4a_nil
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.encoded4a_cons_of_key
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.stereoNodePathObservation_nil_eq_encoded4a
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.pairKey_le_of_compare_ne_lt
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.stereoNodePathObservation_eq_bot_iff
