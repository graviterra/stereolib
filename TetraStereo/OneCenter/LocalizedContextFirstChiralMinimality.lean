import TetraStereo.OneCenter.LocalizedContextRankedLabelsSpheres
import TetraStereo.OneCenter.LocalizedActualFirstChiralMinimality
import TetraStereo.OneCenter.LocalizedRuleMajorRule4aAgreement
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! First-chiral minimality for arbitrary auxiliary context trees. Tied sibling blocks are
connected by the established cross-cursor Rule-4a projection invariant, after deriving exact
agreement of the whole-rule and width-one production builders. -/

namespace TetraStereo.OneCenter.Rule4aTableBridge
open LocalizedCumulativeDecoratedTree CertifiedLocalizedCIPInput DeclarativeCIP
noncomputable section
open scoped Classical
private theorem findSome?_eq_some_index {α β : Type*} (f : α → Option β) :
    ∀ (l : List α) (b : β), l.findSome? f = some b →
      ∃ i, ∃ hi : i < l.length, f l[i] = some b ∧ ∀ k (hk : k < i), f (l[k]'(by omega)) = none
  | [], b, h => by simp at h
  | a :: l, b, h => by
      rw [List.findSome?_cons] at h
      cases hfa : f a with
      | some c =>
          rw [hfa] at h
          cases h
          exact ⟨0, by simp, hfa, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
      | none =>
          rw [hfa] at h
          obtain ⟨i, hi, hfi, hbefore⟩ := findSome?_eq_some_index f l b h
          refine ⟨i + 1, by simpa using hi, hfi, ?_⟩
          intro k hk
          cases k with
          | zero => exact hfa
          | succ k => exact hbefore k (by omega)

private theorem mem_flatMap_index {α β : Type*} (g : α → List β) (l : List α) (e : β)
    (h : e ∈ l.flatMap g) : ∃ j, ∃ hj : j < l.length, e ∈ g l[j] := by
  rw [List.mem_flatMap] at h
  obtain ⟨a, ha, he⟩ := h
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 ha
  exact ⟨j, hj, he⟩


private theorem getD_map_projection (layers : List (List LabelEntry)) (d : Nat) :
    (layers.map projectRule4aLayer).getD d [] = projectRule4aLayer (layers.getD d []) := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases layers[d]? <;> rfl

/-! ## Lexicographic facts on rank addresses -/

private theorem cons_le_cons_of_le {r : Nat} {a b : List Nat} (h : b ≤ a) : r :: b ≤ r :: a := by
  apply not_lt.1
  intro hlt
  have : List.Lex (· < ·) (r :: a) (r :: b) := hlt
  rw [List.cons_lex_cons_iff] at this
  rcases this with h' | ⟨_, h'⟩
  · exact lt_irrefl _ h'
  · exact not_lt.2 h h'

private theorem cons_le_cons_of_lt {r r' : Nat} (h : r < r') (a b : List Nat) :
    r :: b ≤ r' :: a := by
  apply not_lt.1
  intro hlt
  have : List.Lex (· < ·) (r' :: a) (r :: b) := hlt
  rw [List.cons_lex_cons_iff] at this
  rcases this with h' | ⟨h', _⟩
  · exact lt_asymm h h'
  · exact absurd h' (ne_of_gt h)




variable {input : CertifiedLocalizedCIPInput}

theorem contextTree_node_minimal
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
    (tree : LocalizedCumulativeDecoratedTree input (input.certified.input.molecule.atomCount + 1))
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (observations : ∀ rule node actual, tree.decoratedSubtreeAt? node.1 = some actual →
      observe rule node = priorityValue rule (armObservation rule actual))
    {treeFuel : Nat} {treeKey : input.LocalizedRerootCumulativeRule45Key}
    (treeTrace : LocalizedRuleMajorSortTrace input .rule4a
      (input.molecularReader descriptorMap target) treeFuel tree treeKey)
    {unit : DetectedOccurrence input.moleculeGraph} (hyp : ContextTreeRankReadback tree descriptorMap unit)
    {fuel : Nat}
    (ih : ∀ (node : (ruleMajorTreeGraph tree).Node)
      (dsub : LocalizedCumulativeDecoratedTree input (input.certified.input.molecule.atomCount + 1))
      (key : input.LocalizedRerootCumulativeRule45Key),
      LocalizedRuleMajorSortTrace input .rule4a (input.molecularReader descriptorMap target)
          fuel dsub key →
        tree.decoratedSubtreeAt? node.1 = some dsub →
          ∀ (d : Nat) (first : List Nat), firstChiralRank (key.rankedLabels.getD d []) = some first →
            ∀ e ∈ key.rankedLabels.getD d [], IsChiralEntry e → first ≤ e.1)
    (node : (ruleMajorTreeGraph tree).Node)
    (cursor : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1))
    (children : List (input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1)))
    (childKeys sortedKeys : List input.LocalizedRerootCumulativeRule45Key)
    (sortedTrees : List (LocalizedCumulativeDecoratedTree input
      (input.certified.input.molecule.atomCount + 1)))
    (childKeysComputed : children.mapM (input.buildRuleMajorCumulativeWithRead? .rule4a
      (input.molecularReader descriptorMap target) fuel) = some childKeys)
    (sortedEq : sortedKeys = input.sortRuleMajorCumulativeKeys .rule4a childKeys)
    (childrenTraced : LocalizedRuleMajorSortTraceList input .rule4a
      (input.molecularReader descriptorMap target) fuel sortedKeys sortedTrees)
    (lookup : tree.decoratedSubtreeAt? node.1 =
      some (localizedRootTree input cursor (input.molecularReader descriptorMap target cursor)
        sortedTrees))
    (d : Nat) (first : List Nat)
    (hfirst : firstChiralRank ((localizedCumulativeRule45StepKey input .rule4a cursor
      (input.molecularReader descriptorMap target cursor) sortedKeys).rankedLabels.getD d []) =
        some first)
    (e : LabelEntry)
    (he : e ∈ (localizedCumulativeRule45StepKey input .rule4a cursor
      (input.molecularReader descriptorMap target cursor) sortedKeys).rankedLabels.getD d [])
    (hchiral : IsChiralEntry e) : first ≤ e.1 := by
  cases d with
  | zero => exact root_entry_minimal first hfirst e he
  | succ d =>
  -- shared setup
  have hkeysorted := contextTree_keySorted_rankEvidence tree observe observations hyp treeTrace
  have hdense := observedTree_denseAt_of_lookup tree node _ lookup
  have childrenEq : (localizedRootTree input cursor (input.molecularReader descriptorMap target cursor)
      sortedTrees).children = sortedTrees := rfl
  rw [childrenEq] at hdense
  have paired := LocalizedRuleMajorSortTraceList.to_forall₂ childrenTraced
  have lengthEq : sortedKeys.length = sortedTrees.length := List.Forall₂.length_eq paired
  set slots := slotList (toOfficialSourceTree tree).declarativeAddressing node
    sortedTrees.length with hslots
  have slotLength : slots.length = sortedTrees.length := by simp [hslots, slotList]
  have childAt : ∀ i (hi : i < sortedTrees.length), ∃ child : (ruleMajorTreeGraph tree).Node,
      slots[i]? = some child ∧ child.1 = node.1 ++ [i] ∧
        tree.decoratedSubtreeAt? child.1 = some (sortedTrees[i]'hi) := by
    intro i hi
    obtain ⟨child, slotSome, addr⟩ := slotList_getD_of_lt (addressing :=
      (toOfficialSourceTree tree).declarativeAddressing) (parent := node)
      (count := sortedTrees.length) hdense hi
    have addrFlat : child.1 = node.1 ++ [i] := by
      rw [(toOfficialSourceTree tree).declarativeAddressing_address,
        (toOfficialSourceTree tree).declarativeAddressing_address] at addr
      exact addr
    refine ⟨child, slotSome, addrFlat, ?_⟩
    rw [addrFlat, decoratedSubtreeAt?_append tree node.1 [i], lookup]
    simp [childrenEq, decoratedSubtreeAt?, List.getElem?_eq_getElem hi]
  have traceAt : ∀ i (hi : i < sortedTrees.length),
      LocalizedRuleMajorSortTrace input .rule4a (input.molecularReader descriptorMap target)
        fuel (sortedTrees[i]'hi) (sortedKeys[i]'(by omega)) :=
    fun i hi => List.Forall₂.get (i := i) paired (by omega) hi
  have represented : ∀ i (hi : i < sortedTrees.length) (child : (ruleMajorTreeGraph tree).Node),
      tree.decoratedSubtreeAt? child.1 = some (sortedTrees[i]'hi) →
        ObservedRepresented (read := input.molecularReader descriptorMap target) tree observe descriptorMap unit
          (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height (sortedKeys[i]'(by omega)) child :=
    fun i hi child hl =>
      ⟨sortedTrees[i]'hi, (LocalizedRuleMajorSortTrace.fullMatch_of_trace (traceAt i hi)).tableMatch,
        LocalizedRuleMajorSortTrace.realizes_of_trace (traceAt i hi),
        (observedTree_node_bridge tree observe observations le_rfl le_rfl child (sortedTrees[i]'hi) (sortedKeys[i]'(by omega))
          (traceAt i hi) hl).2,
        (contextTree_node_bridge4a tree observe observations hyp le_rfl le_rfl child (sortedTrees[i]'hi) (sortedKeys[i]'(by omega))
          (traceAt i hi) hl).2⟩
  have slotGet : ∀ i (hi : i < sortedTrees.length), ∃ child, slots[i]'(by rw [slotLength]; exact hi) = child ∧
      tree.decoratedSubtreeAt? child.1 = some (sortedTrees[i]'hi) := by
    intro i hi
    obtain ⟨child, slotSome, _, hl⟩ := childAt i hi
    exact ⟨child, Option.some.inj ((List.getElem?_eq_getElem _).symm.trans slotSome), hl⟩
  have pairedSlots : List.Forall₂ (ObservedRepresented (read := input.molecularReader descriptorMap target) tree observe descriptorMap unit
      (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height) sortedKeys slots := by
    rw [List.forall₂_iff_get]
    refine ⟨by rw [lengthEq, slotLength], ?_⟩
    intro i hi hi'
    simp only [List.get_eq_getElem]
    obtain ⟨child, hget, hl⟩ := slotGet i (by omega)
    rw [hget]
    exact represented i (by omega) child hl
  set oks := slots.map (ordinaryKeyWithObservations (ruleMajorTreeGraph tree) observe
    (rankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree))
    (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height) with hoks
  have oksSorted : oks.Pairwise fun x y => y ≤ x := by
    have oksEq : rankedOrdinaryKeysWithObservations (ruleMajorTreeGraph tree) observe
        (rankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree))
        (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height node = oks := by
      unfold rankedOrdinaryKeysWithObservations
      exact sortDesc_childKeys_eq_slotOrder _ hdense hkeysorted
    rw [← oksEq]
    exact Certificate.CanonicalSphereKey.sortDesc_pairwise _
  have hranks := observedRankedChildren_snd_eq_headRanks (tree := tree) (observe := observe) (descriptorMap := descriptorMap) (unit := unit) hyp.rule4aOnly sortedKeys slots pairedSlots
  rw [headRanks_eq_map_rankIndexIn _ oksSorted] at hranks
  have hfst := rankedChildren_fst (input := input) sortedKeys
  set ranked := input.localizedRerootRankedChildren sortedKeys with hranked
  have rankedLength : ranked.length = sortedKeys.length := by
    have := congrArg List.length hfst
    simpa using this
  have hp1 : ∀ i (hi : i < ranked.length), ranked[i].1 = sortedKeys[i]'(by omega) := by
    intro i hi
    have := congrArg (fun l => l[i]?) hfst
    simp only [List.getElem?_map, List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem (show i < sortedKeys.length by omega), Option.map_some,
      Option.some.injEq] at this
    exact this
  have hp2 : ∀ i (hi : i < ranked.length), ranked[i].2 =
      rankIndexIn oks (ordinaryKeyWithObservations (ruleMajorTreeGraph tree) observe
        (rankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree))
        (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height (slots[i]'(by omega))) := by
    intro i hi
    have := congrArg (fun l => l[i]?) hranks
    simp only [hoks, List.getElem?_map, List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem (show i < slots.length by omega), Option.map_some,
      Option.some.injEq] at this
    exact this
  have memOks : ∀ i (hi : i < slots.length), ordinaryKeyWithObservations (ruleMajorTreeGraph tree) observe
      (rankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree))
      (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height slots[i] ∈ oks := fun i hi =>
    List.mem_map_of_mem (List.getElem_mem hi)
  have keyPerm : sortedKeys.Perm childKeys := by
    rw [sortedEq]
    exact CertifiedLocalizedCIPInput.sortKeysBy_perm _ childKeys
  have keyMem : ∀ i (hi : i < sortedKeys.length), sortedKeys[i] ∈ childKeys := fun i hi =>
    keyPerm.subset (List.getElem_mem hi)
  -- the sphere as a flatMap
  have sphereEq : (localizedCumulativeRule45StepKey input .rule4a cursor
      (input.molecularReader descriptorMap target cursor) sortedKeys).rankedLabels.getD (d + 1) [] =
      ranked.flatMap fun p => OfficialRuleMajorKey.prefixLayer p.2 (p.1.rankedLabels.getD d []) := by
    show ([[([], input.molecularReader descriptorMap target cursor)]] ++
      input.mergeLocalizedRerootRankedLabelChildren sortedKeys).getD (d + 1) [] = _
    rw [List.cons_append, List.nil_append, List.getD_cons_succ,
      getD_mergeLocalizedRerootRankedLabelChildren]
  rw [sphereEq] at hfirst he
  rw [firstChiralRank_flatMap] at hfirst
  obtain ⟨i₀, hi₀, hf₀, hbefore⟩ := findSome?_eq_some_index _ ranked first hfirst
  obtain ⟨j, hj, hej⟩ := mem_flatMap_index _ ranked e he
  rw [firstChiralRank_prefixLayer, Option.map_eq_some_iff] at hf₀
  obtain ⟨b, hb, rfl⟩ := hf₀
  rw [mem_prefixLayer_iff] at hej
  obtain ⟨e', he', rfl⟩ := hej
  have hchiral' : IsChiralEntry e' := hchiral
  -- induction hypothesis at block `i₀`
  obtain ⟨child₀, hget₀, hl₀⟩ := slotGet i₀ (by omega)
  have ihb : ∀ e'' ∈ ranked[i₀].1.rankedLabels.getD d [], IsChiralEntry e'' → b ≤ e''.1 := by
    rw [hp1 i₀ hi₀]
    exact ih child₀ (sortedTrees[i₀]'(by omega)) (sortedKeys[i₀]'(by omega)) (traceAt i₀ (by omega))
      hl₀ d b (by rw [← hp1 i₀ hi₀]; exact hb)
  rcases Nat.lt_trichotomy j i₀ with hlt | rfl | hgt
  · exfalso
    have hnone := hbefore j hlt
    rw [firstChiralRank_prefixLayer, Option.map_eq_none_iff, firstChiralRank_eq_none_iff] at hnone
    exact hnone e' he' hchiral'
  · exact cons_le_cons_of_le (ihb e' he' hchiral')
  · -- ranks are nondecreasing in slot order
    have hjs : j < slots.length := by omega
    have hi₀s : i₀ < slots.length := by omega
    have keyLe : ordinaryKeyWithObservations (ruleMajorTreeGraph tree) observe
        (rankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree))
        (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height slots[j] ≤
        ordinaryKeyWithObservations (ruleMajorTreeGraph tree) observe
          (rankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree))
          (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height slots[i₀] := by
      have := (List.pairwise_iff_getElem.1 oksSorted) i₀ j (by simp [hoks]; omega)
        (by simp [hoks]; omega) hgt
      simpa [hoks] using this
    rw [hp2 i₀ hi₀, hp2 j hj]
    rcases lt_or_eq_of_le keyLe with keyLt | keyEq
    · exact cons_le_cons_of_lt (rankIndexIn_lt_of_lt (memOks i₀ hi₀s) keyLt) _ _
    · rw [keyEq]

      obtain ⟨childj, hgetj, hlj⟩ := slotGet j (by omega)
      have tie : input.compareLocalizedRerootCumulativeRule45Keys (sortedKeys[i₀]'(by omega))
          (sortedKeys[j]'(by omega)) = Ordering.eq := by
        rw [ObservedRepresented.tie_iff tree observe descriptorMap unit hyp.rule4aOnly (represented i₀ (by omega) child₀ hl₀)
          (represented j (by omega) childj hlj)]
        rw [← hget₀, ← hgetj]
        exact keyEq.symm
      have oldComputed : children.mapM (input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
          (input.molecularReader descriptorMap target) fuel) = some childKeys := by
        have buildEq : input.buildRuleMajorCumulativeWithRead? .rule4a
            (input.molecularReader descriptorMap target) fuel =
            input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
              (input.molecularReader descriptorMap target) fuel :=
          funext fun position => input.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized
            (input.molecularReader descriptorMap target) fuel position
        rw [← buildEq]
        exact childKeysComputed
      have proj := projected_rankedLabels_eq_of_tie descriptorMap target oldComputed
        (keyMem i₀ (by omega)) (keyMem j (by omega)) tie
      have projLayer : projectRule4aLayer ((sortedKeys[i₀]'(by omega)).rankedLabels.getD d []) =
          projectRule4aLayer ((sortedKeys[j]'(by omega)).rankedLabels.getD d []) := by
        rw [← getD_map_projection, ← getD_map_projection, proj]
      have hmem : (e'.1, [2]) ∈ projectRule4aLayer ((sortedKeys[i₀]'(by omega)).rankedLabels.getD d []) := by
        rw [projLayer, ← hp1 j hj]
        exact projection_mem_of_chiral _ e' he' hchiral'
      obtain ⟨e'', he'', hadd, hchiral''⟩ := exists_chiral_of_projection_mem _ _ hmem
      have hle := ihb e'' (by rw [hp1 i₀ hi₀]; exact he'') hchiral''
      rw [hadd] at hle
      exact cons_le_cons_of_le hle

/-! ## Minimality -/

/-- **The first chiral entry has the least rank address** among the chiral entries of its sphere,
at every node of an actual arm of the molecular reader. -/
theorem contextTree_firstChiralRank_minimal
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
    (tree : LocalizedCumulativeDecoratedTree input (input.certified.input.molecule.atomCount + 1))
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (observations : ∀ rule node actual, tree.decoratedSubtreeAt? node.1 = some actual →
      observe rule node = priorityValue rule (armObservation rule actual))
    {treeFuel : Nat} {treeKey : input.LocalizedRerootCumulativeRule45Key}
    (treeTrace : LocalizedRuleMajorSortTrace input .rule4a
      (input.molecularReader descriptorMap target) treeFuel tree treeKey)
    {unit : DetectedOccurrence input.moleculeGraph} (hyp : ContextTreeRankReadback tree descriptorMap unit) :
    ∀ {fuel : Nat} (node : (ruleMajorTreeGraph tree).Node)
      (dsub : LocalizedCumulativeDecoratedTree input (input.certified.input.molecule.atomCount + 1))
      (key : input.LocalizedRerootCumulativeRule45Key),
      LocalizedRuleMajorSortTrace input .rule4a (input.molecularReader descriptorMap target)
          fuel dsub key →
        tree.decoratedSubtreeAt? node.1 = some dsub →
          ∀ (d : Nat) (first : List Nat), firstChiralRank (key.rankedLabels.getD d []) = some first →
            ∀ e ∈ key.rankedLabels.getD d [], IsChiralEntry e → first ≤ e.1 := by
  intro fuel
  induction fuel with
  | zero =>
      intro node dsub key trace lookup d first hfirst e he hchiral
      cases trace with
      | terminal _fuel cursor _children _childrenComputed _terminalChildren _fullMatch _realizes =>
          exact terminal_minimal d first hfirst e he
  | succ fuel ih =>
      intro node dsub key trace lookup d first hfirst e he hchiral
      rcases LocalizedRuleMajorSortTrace.structure_of_trace trace with
        ⟨cursor, _children, dsubEq, keyEq, _childrenEq, _childrenComputed, _terminalChildren⟩ |
        ⟨cursor, children, childKeys, sortedKeys, sortedTrees, dsubEq, keyEq, _childrenEq,
          _childrenComputed, _nonempty, childKeysComputed, sortedEq, _constitutionalDescending, _sortedDescending,
          childrenTraced⟩
      · subst dsub; subst key
        exact terminal_minimal d first hfirst e he
      · subst dsub; subst key
        exact contextTree_node_minimal descriptorMap target tree observe observations treeTrace hyp ih node cursor children childKeys sortedKeys
          sortedTrees childKeysComputed sortedEq childrenTraced lookup d first hfirst e he hchiral

end
end TetraStereo.OneCenter.Rule4aTableBridge
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.contextTree_node_minimal
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.contextTree_firstChiralRank_minimal
