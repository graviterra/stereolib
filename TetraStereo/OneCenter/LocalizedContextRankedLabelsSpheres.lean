import TetraStereo.OneCenter.LocalizedContextRule4aCanonicalBridge
import TetraStereo.OneCenter.DeclarativeCIPContextualReferenceIso
import TetraStereo.OneCenter.DeclarativeCIPObservedRankAddress
import TetraStereo.OneCenter.LocalizedRuleMajorRule4aAgreement
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! Rank-addressed spheres for actual Rule-4a keys at a retained-root context. -/

namespace TetraStereo.OneCenter
namespace Rule4aTableBridge

open LocalizedCumulativeDecoratedTree CertifiedLocalizedCIPInput
open OfficialSparseCanonicalVectorComparison DeclarativeCIP
noncomputable section
open scoped Classical

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
  {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}

/-- A stage-4a key represented by a node of an observer-parametric source tree. -/
def ObservedRepresented (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph) (W D : Nat)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (node : (ruleMajorTreeGraph tree).Node) : Prop :=
  ∃ actual : LocalizedCumulativeDecoratedTree input carrierFuel,
    LocalizedCumulativeTreeTableMatch .rule4a actual key ∧
    LocalizedCumulativeTreeRealizes input read actual ∧
    Represents W D (ruleKeyWithObservations (ruleMajorTreeGraph tree) W D observe node)
      key.constitutional ∧
    Represents4a W D (observedRule4aComponent (ruleMajorTreeGraph tree) observe
      (rankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) W D node) key

/-- Equality of actual stage-4a comparison means equality of observer-parametric ordinary keys,
provided the trees have the contextual readback representations. -/
theorem ObservedRepresented.tie_iff
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph)
    (h4a : Rule4aOnly (ruleMajorTreeGraph tree)
      (rankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)))
    {W D : Nat} {keyI keyJ : input.LocalizedRerootCumulativeRule45Key}
    {nodeI nodeJ : (ruleMajorTreeGraph tree).Node}
    (hI : ObservedRepresented (read := read) tree observe descriptorMap unit W D keyI nodeI)
    (hJ : ObservedRepresented (read := read) tree observe descriptorMap unit W D keyJ nodeJ) :
    input.compareLocalizedRerootCumulativeRule45Keys keyI keyJ = Ordering.eq ↔
      ordinaryKeyWithObservations (ruleMajorTreeGraph tree) observe
        (rankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) W D nodeI =
      ordinaryKeyWithObservations (ruleMajorTreeGraph tree) observe
        (rankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) W D nodeJ := by
  obtain ⟨actualI, matchI, realizesI, repI, rep4I⟩ := hI
  obtain ⟨actualJ, matchJ, realizesJ, repJ, rep4J⟩ := hJ
  let graph := ruleMajorTreeGraph tree
  let evidence := rankEvidence input.moleculeGraph descriptorMap unit graph
  have pairTie : input.compareLocalizedRerootCumulativeRule45Keys keyI keyJ = Ordering.eq ↔
      observedPairKey graph observe evidence W D nodeI = observedPairKey graph observe evidence W D nodeJ := by
    constructor
    · intro hold
      have hnew : input.compareRuleMajorCumulativeDescriptor 1 keyI keyJ = Ordering.eq := by
        rw [← compareRule4aOld_eq_ruleMajor_one matchI matchJ]
        exact hold
      letI : Std.OrientedCmp (input.compareRuleMajorCumulativeDescriptor 1) :=
        input.compareRuleMajorCumulativeDescriptor_orientedCmp 1
      have oriented := Std.OrientedCmp.eq_swap
        (cmp := input.compareRuleMajorCumulativeDescriptor 1) (a := keyI) (b := keyJ)
      have hnewReverse : input.compareRuleMajorCumulativeDescriptor 1 keyJ keyI = Ordering.eq := by
        rw [hnew] at oriented
        cases hrev : input.compareRuleMajorCumulativeDescriptor 1 keyJ keyI <;>
          simp [hrev] at oriented ⊢
      have hji := observedPairKey_le_of_ruleMajor_compare_ne_lt observe evidence
        matchJ matchI realizesJ realizesI repJ repI rep4J rep4I (by simp [hnewReverse])
      have hij := observedPairKey_le_of_ruleMajor_compare_ne_lt observe evidence
        matchI matchJ realizesI realizesJ repI repJ rep4I rep4J (by simp [hnew])
      exact le_antisymm hji hij
    · intro pairEq
      have hp := congrArg ofLex pairEq
      have vectorEq : ruleKeyWithObservations graph W D observe nodeI =
          ruleKeyWithObservations graph W D observe nodeJ := congrArg Prod.fst hp
      have stereoEq : observedRule4aComponent graph observe evidence W D nodeI =
          observedRule4aComponent graph observe evidence W D nodeJ := congrArg Prod.snd hp
      have wfI := wellFormedRuleMajorKey_of_tableMatch matchI realizesI
      have wfJ := wellFormedRuleMajorKey_of_tableMatch matchJ realizesJ
      have hconst : OfficialRuleMajorKey.compare keyI.constitutional keyJ.constitutional =
          compare (ruleKeyWithObservations graph W D observe nodeI)
            (ruleKeyWithObservations graph W D observe nodeJ) :=
        compare_eq_compare_vector wfI wfJ
          (ruleKeyWithObservations_vectorWellShaped (graph := graph) (observe := observe) W D nodeI)
          (ruleKeyWithObservations_vectorWellShaped (graph := graph) (observe := observe) W D nodeJ)
          repI repJ
      have hconstEq : OfficialRuleMajorKey.compare keyI.constitutional keyJ.constitutional =
          Ordering.eq := by rw [hconst]; exact (vectorCompare_eq_iff _ _).2 vectorEq
      have rule1aTie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
          keyI.constitutional.rule1a keyJ.constitutional.rule1a = Ordering.eq := by
        unfold OfficialRuleMajorKey.compare at hconstEq
        exact (compareLex_eq_eq.1 hconstEq).1
      have hdesc : OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
          keyI.descriptor keyJ.descriptor = Ordering.eq := by
        rw [compare_descriptor_eq_compare_key matchI matchJ realizesI realizesJ rule1aTie
          (ordinaryKeyWithObservations_stereo_wellShaped graph observe evidence W D
            .rule4aStereogenicUnitKind nodeI)
          (ordinaryKeyWithObservations_stereo_wellShaped graph observe evidence W D
            .rule4aStereogenicUnitKind nodeJ) rep4I rep4J]
        exact (stereoKeyCompare_eq_iff _ _).2 stereoEq
      unfold compareLocalizedRerootCumulativeRule45Keys
      simp [compareLex, Ordering.byKey, hconstEq, hdesc]
  have leObs : ordinaryKeyWithObservations graph observe evidence W D nodeI ≤
      ordinaryKeyWithObservations graph observe evidence W D nodeJ ↔
    observedPairKey graph observe evidence W D nodeI ≤ observedPairKey graph observe evidence W D nodeJ := by
    simpa only [not_lt] using not_congr
      (observedOrdinaryKey_lt_iff_pairKey graph observe evidence h4a W D nodeJ nodeI)
  have leObsRev : ordinaryKeyWithObservations graph observe evidence W D nodeJ ≤
      ordinaryKeyWithObservations graph observe evidence W D nodeI ↔
    observedPairKey graph observe evidence W D nodeJ ≤ observedPairKey graph observe evidence W D nodeI := by
    simpa only [not_lt] using not_congr
      (observedOrdinaryKey_lt_iff_pairKey graph observe evidence h4a W D nodeI nodeJ)
  constructor
  · intro h
    have heqPair := pairTie.mp h
    exact le_antisymm (leObs.mpr (le_of_eq heqPair))
      (leObsRev.mpr (le_of_eq heqPair.symm))
  · intro h
    have stereoEq : observedRule4aComponent graph observe evidence W D nodeI =
        observedRule4aComponent graph observe evidence W D nodeJ := by
      have hproj := congrArg (fun k : OrdinaryKey =>
        (ofLex k).2.getD (stereoIndex .rule4aStereogenicUnitKind) []) h
      simpa only [observedRule4aComponent] using hproj
    have vectorEq : ruleKeyWithObservations graph W D observe nodeI =
        ruleKeyWithObservations graph W D observe nodeJ := by
      have hproj := congrArg (fun k : OrdinaryKey => (ofLex k).1) h
      simpa only [ordinaryKeyWithObservations_fst] using hproj
    have hpair : observedPairKey graph observe evidence W D nodeI =
        observedPairKey graph observe evidence W D nodeJ := by
      exact congrArg toLex (Prod.ext vectorEq stereoEq)
    exact pairTie.mpr hpair

theorem observedRankedChildTail_snd_eq_tailRanks
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph)
    (h4a : Rule4aOnly (ruleMajorTreeGraph tree)
      (rankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)))
    {W D : Nat} :
    ∀ (keys : List input.LocalizedRerootCumulativeRule45Key)
      (nodes : List (ruleMajorTreeGraph tree).Node),
      List.Forall₂ (ObservedRepresented (read := read) tree observe descriptorMap unit W D)
        keys nodes →
      ∀ (prev : input.LocalizedRerootCumulativeRule45Key)
        (prevNode : (ruleMajorTreeGraph tree).Node),
        ObservedRepresented (read := read) tree observe descriptorMap unit W D prev prevNode →
      ∀ rank : Nat,
        (input.localizedRerootRankedChildTail prev rank keys).map (·.2) =
          tailRanks (ordinaryKeyWithObservations (ruleMajorTreeGraph tree) observe
            (rankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) W D
            prevNode) rank
            (nodes.map (ordinaryKeyWithObservations (ruleMajorTreeGraph tree) observe
              (rankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) W D))
  | [], [], _, _, _, _, _ => rfl
  | [], _ :: _, h, _, _, _, _ => nomatch h
  | _ :: _, [], h, _, _, _, _ => nomatch h
  | key :: keys, node :: nodes, h, prev, prevNode, hprev, rank => by
      obtain ⟨hkey, hrest⟩ := List.forall₂_cons.1 h
      have tie := ObservedRepresented.tie_iff tree observe descriptorMap unit h4a hkey hprev
      simp only [List.map_cons, localizedRerootRankedChildTail, tailRanks]
      by_cases hc : input.compareLocalizedRerootCumulativeRule45Keys key prev = Ordering.eq
      · rw [if_pos hc, if_pos (tie.1 hc)]
        rw [observedRankedChildTail_snd_eq_tailRanks tree observe descriptorMap unit h4a
          keys nodes hrest key node hkey rank]
      · rw [if_neg hc, if_neg fun h => hc (tie.2 h)]
        rw [observedRankedChildTail_snd_eq_tailRanks tree observe descriptorMap unit h4a
          keys nodes hrest key node hkey (rank + 1)]

theorem observedRankedChildren_snd_eq_headRanks
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph)
    (h4a : Rule4aOnly (ruleMajorTreeGraph tree)
      (rankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)))
    {W D : Nat}
    (keys : List input.LocalizedRerootCumulativeRule45Key)
    (nodes : List (ruleMajorTreeGraph tree).Node)
    (h : List.Forall₂ (ObservedRepresented (read := read) tree observe descriptorMap unit W D)
      keys nodes) :
    (input.localizedRerootRankedChildren keys).map (·.2) =
      headRanks (nodes.map (ordinaryKeyWithObservations (ruleMajorTreeGraph tree) observe
        (rankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) W D)) := by
  cases h with
  | nil => rfl
  | cons hkey hrest =>
      simp only [localizedRerootRankedChildren, List.map_cons, headRanks]
      rw [observedRankedChildTail_snd_eq_tailRanks tree observe descriptorMap unit h4a
        _ _ hrest _ _ hkey 0]

def contextualSphereEntry
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph)
    (start : (ruleMajorTreeGraph tree).Node)
    (chain : List (ruleMajorTreeGraph tree).Node) :
    OfficialSparseEntry (Option LocalizedAuxiliaryLabel) :=
  (DeclarativeCIP.observedChainRankAddress (ruleMajorTreeGraph tree) observe
      (rankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree))
      (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height chain,
    (occurrenceReading input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)
      (chain.getLastD start)).toLocalizedLabel)

def contextualSphereOf
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph)
    (depth : Nat) (start : (ruleMajorTreeGraph tree).Node) :
    List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)) :=
  (depthChains (ruleMajorTreeGraph tree)
      (toOfficialSourceTree tree).declarativeAddressing depth start).map
    (contextualSphereEntry tree observe descriptorMap unit start)

theorem contextualSphereOf_zero
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph)
    (start : (ruleMajorTreeGraph tree).Node) :
    contextualSphereOf tree observe descriptorMap unit 0 start =
      [( [], (occurrenceReading input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph tree) start).toLocalizedLabel )] := rfl

theorem contextualSphereOf_succ_of_no_children
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph)
    (start : (ruleMajorTreeGraph tree).Node)
    (noChildren : (ruleMajorTreeGraph tree).childList start = []) (depth : Nat) :
    contextualSphereOf tree observe descriptorMap unit (depth + 1) start = [] := by
  simp [contextualSphereOf, DeclarativeCIP.depthChains, noChildren,
    DeclarativeCIP.slotList]

theorem contextualTerminal_sphere
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph)
    (hyp : ContextTreeRankReadback tree descriptorMap unit)
    (node : (ruleMajorTreeGraph tree).Node)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (lookup : tree.decoratedSubtreeAt? node.1 =
      some (localizedRootTree input cursor (read cursor) [])) (depth : Nat) :
    (localizedCumulativeRule45TerminalKey input .rule4a cursor (read cursor)).rankedLabels.getD
      depth [] = contextualSphereOf tree observe descriptorMap unit depth node := by
  have hdense := observedTree_denseAt_of_lookup tree node
    (localizedRootTree input cursor (read cursor) []) lookup
  have hchild : (ruleMajorTreeGraph tree).childList node = [] := by
    have hperm := slotList_perm hdense
    have hnil : slotList (toOfficialSourceTree tree).declarativeAddressing node
        (localizedRootTree input cursor (read cursor) []).children.length = [] := by
      simp [slotList, localizedRootTree]
    rw [hnil] at hperm
    exact hperm.symm.eq_nil
  cases depth with
  | zero =>
      have rootLookup : subtreeAt? tree node.1 =
          some (localizedRootTree input cursor (read cursor) []) := by
        rwa [← decoratedSubtreeAt?_eq_subtreeAt?]
      have rootLabel := hyp.label node _ rootLookup
      simpa [contextualSphereOf, contextualSphereEntry, DeclarativeCIP.depthChains,
        DeclarativeCIP.observedChainRankAddress, localizedRootTree] using rootLabel
  | succ depth =>
      rw [contextualSphereOf_succ_of_no_children tree observe descriptorMap unit node hchild depth]
      rfl

private theorem flatMap_eq_of_forall₂ {α β γ : Type*}
    {f : α → List γ} {g : β → List γ} :
    ∀ {left : List α} {right : List β},
      List.Forall₂ (fun a b => f a = g b) left right → left.flatMap f = right.flatMap g
  | [], [], _ => rfl
  | _ :: _, _ :: _, List.Forall₂.cons h hrest => by
      simp only [List.flatMap_cons]
      rw [h, flatMap_eq_of_forall₂ hrest]

theorem contextualStep_sphere
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (observations : ∀ rule node actual, tree.decoratedSubtreeAt? node.1 = some actual →
      observe rule node = priorityValue rule (armObservation rule actual))
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph)
    (hyp : ContextTreeRankReadback tree descriptorMap unit)
    {fuel : Nat}
    (ih : ∀ (node : (ruleMajorTreeGraph tree).Node)
      (dsub : LocalizedCumulativeDecoratedTree input carrierFuel)
      (key : input.LocalizedRerootCumulativeRule45Key),
      LocalizedRuleMajorSortTrace input .rule4a read fuel dsub key →
      tree.decoratedSubtreeAt? node.1 = some dsub → ∀ depth,
        key.rankedLabels.getD depth [] = contextualSphereOf tree observe descriptorMap unit depth node)
    (node : (ruleMajorTreeGraph tree).Node)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (sortedKeys : List input.LocalizedRerootCumulativeRule45Key)
    (sortedTrees : List (LocalizedCumulativeDecoratedTree input carrierFuel))
    (childrenTraced : LocalizedRuleMajorSortTraceList input .rule4a read fuel sortedKeys sortedTrees)
    (lookup : tree.decoratedSubtreeAt? node.1 =
      some (localizedRootTree input cursor (read cursor) sortedTrees))
    {rootFuel : Nat} {rootKey : input.LocalizedRerootCumulativeRule45Key}
    (outerTrace : LocalizedRuleMajorSortTrace input .rule4a read rootFuel tree rootKey)
    (depth : Nat) :
    ((localizedCumulativeRule45StepKey input .rule4a cursor (read cursor) sortedKeys).rankedLabels.getD depth []) =
      contextualSphereOf tree observe descriptorMap unit depth node := by
  cases depth with
  | zero =>
      have rootLookup : subtreeAt? tree node.1 =
          some (localizedRootTree input cursor (read cursor) sortedTrees) := by
        rwa [← decoratedSubtreeAt?_eq_subtreeAt?]
      have rootLabel := hyp.label node _ rootLookup
      simpa [localizedCumulativeRule45StepKey, contextualSphereOf, contextualSphereEntry,
        DeclarativeCIP.depthChains, DeclarativeCIP.observedChainRankAddress,
        localizedRootTree] using rootLabel
  | succ depth =>
      have hkeysorted := contextTree_keySorted_rankEvidence tree observe observations hyp outerTrace
      have hdense := observedTree_denseAt_of_lookup tree node _ lookup
      have childrenEq : (localizedRootTree input cursor (read cursor) sortedTrees).children = sortedTrees := rfl
      rw [childrenEq] at hdense
      have paired := LocalizedRuleMajorSortTraceList.to_forall₂ childrenTraced
      have lengthEq : sortedKeys.length = sortedTrees.length := List.Forall₂.length_eq paired
      have hcount : ((ruleMajorTreeGraph tree).childList node).length = sortedTrees.length := by
        have hlen := (slotList_perm hdense).length_eq
        simp only [slotList, List.length_map, List.length_range] at hlen
        exact hlen.symm
      set slots := slotList (toOfficialSourceTree tree).declarativeAddressing node sortedTrees.length with hslots
      have slotLength : slots.length = sortedTrees.length := by simp [hslots, slotList]
      have childAt : ∀ i (hi : i < sortedTrees.length), ∃ child : (ruleMajorTreeGraph tree).Node,
          slots[i]? = some child ∧ child.1 = node.1 ++ [i] ∧
            tree.decoratedSubtreeAt? child.1 = some (sortedTrees[i]'hi) := by
        intro i hi
        obtain ⟨child, slotSome, addr⟩ := slotList_getD_of_lt
          (addressing := (toOfficialSourceTree tree).declarativeAddressing)
          (parent := node) (count := sortedTrees.length) hdense hi
        have addrFlat : child.1 = node.1 ++ [i] := by
          rw [(toOfficialSourceTree tree).declarativeAddressing_address,
            (toOfficialSourceTree tree).declarativeAddressing_address] at addr
          exact addr
        refine ⟨child, slotSome, addrFlat, ?_⟩
        rw [addrFlat, decoratedSubtreeAt?_append tree node.1 [i], lookup]
        simp [childrenEq, decoratedSubtreeAt?, List.getElem?_eq_getElem hi]
      have traceAt : ∀ i (hi : i < sortedTrees.length),
          LocalizedRuleMajorSortTrace input .rule4a read fuel (sortedTrees[i]'hi)
            (sortedKeys[i]'(by omega)) :=
        fun i hi => List.Forall₂.get (i := i) paired (by omega) hi
      have represented : ∀ i (hi : i < sortedTrees.length) (child : (ruleMajorTreeGraph tree).Node),
          tree.decoratedSubtreeAt? child.1 = some (sortedTrees[i]'hi) →
            ObservedRepresented (read := read) tree observe descriptorMap unit
              (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height
              (sortedKeys[i]'(by omega)) child := by
        intro i hi child hl
        refine ⟨sortedTrees[i]'hi,
          (LocalizedRuleMajorSortTrace.fullMatch_of_trace (traceAt i hi)).tableMatch,
          LocalizedRuleMajorSortTrace.realizes_of_trace (traceAt i hi), ?_, ?_⟩
        · exact (observedTree_node_bridge tree observe observations le_rfl le_rfl
            child (sortedTrees[i]'hi) (sortedKeys[i]'(by omega)) (traceAt i hi) hl).2
        · exact (contextTree_node_bridge4a tree observe observations hyp le_rfl le_rfl
            child (sortedTrees[i]'hi) (sortedKeys[i]'(by omega)) (traceAt i hi) hl).2
      have slotGet : ∀ i (hi : i < sortedTrees.length), ∃ child,
          slots[i]'(by rw [slotLength]; exact hi) = child ∧
            tree.decoratedSubtreeAt? child.1 = some (sortedTrees[i]'hi) := by
        intro i hi
        obtain ⟨child, slotSome, _, hl⟩ := childAt i hi
        exact ⟨child, Option.some.inj ((List.getElem?_eq_getElem _).symm.trans slotSome), hl⟩
      have pairedSlots : List.Forall₂
          (ObservedRepresented (read := read) tree observe descriptorMap unit
            (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height) sortedKeys slots := by
        rw [List.forall₂_iff_get]
        refine ⟨by rw [lengthEq, slotLength], ?_⟩
        intro i hi hi'
        simp only [List.get_eq_getElem]
        obtain ⟨child, hget, hl⟩ := slotGet i (by omega)
        rw [hget]
        exact represented i (by omega) child hl
      have oksEq : rankedOrdinaryKeysWithObservations (ruleMajorTreeGraph tree) observe
          (rankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree))
          (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height node =
          slots.map (ordinaryKeyWithObservations (ruleMajorTreeGraph tree) observe
            (rankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree))
            (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height) := by
        unfold rankedOrdinaryKeysWithObservations
        exact sortDesc_childKeys_eq_slotOrder _ hdense hkeysorted
      have oksSorted : (slots.map (ordinaryKeyWithObservations (ruleMajorTreeGraph tree) observe
          (rankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree))
          (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height)).Pairwise
            fun x y => y ≤ x := by
        rw [← oksEq]
        exact Certificate.CanonicalSphereKey.sortDesc_pairwise _
      have hranks := observedRankedChildren_snd_eq_headRanks tree observe descriptorMap unit
        hyp.rule4aOnly sortedKeys slots pairedSlots
      rw [headRanks_eq_map_rankIndexIn _ oksSorted] at hranks
      have hfst := rankedChildren_fst (input := input) sortedKeys
      show ([[([], read cursor)]] ++ input.mergeLocalizedRerootRankedLabelChildren sortedKeys).getD
        (depth + 1) [] = _
      rw [List.cons_append, List.nil_append, List.getD_cons_succ,
        getD_mergeLocalizedRerootRankedLabelChildren]
      unfold contextualSphereOf
      simp only [DeclarativeCIP.depthChains, hcount, List.map_flatMap]
      rw [← hslots]
      have rankedLength : (input.localizedRerootRankedChildren sortedKeys).length = sortedKeys.length := by
        have := congrArg List.length hfst
        simpa using this
      apply flatMap_eq_of_forall₂
      rw [List.forall₂_iff_get]
      refine ⟨by rw [rankedLength, lengthEq, slotLength], ?_⟩
      intro i hi hi'
      simp only [List.get_eq_getElem]
      have hiTree : i < sortedTrees.length := by rw [slotLength] at hi'; exact hi'
      obtain ⟨child, hget, hl⟩ := slotGet i hiTree
      rw [hget]
      have hp1 : (input.localizedRerootRankedChildren sortedKeys)[i].1 =
          sortedKeys[i]'(by omega) := by
        have := congrArg (fun l => l[i]?) hfst
        simp only [List.getElem?_map, List.getElem?_eq_getElem hi,
          List.getElem?_eq_getElem (show i < sortedKeys.length by omega), Option.map_some,
          Option.some.injEq] at this
        exact this
      have hp2 : (input.localizedRerootRankedChildren sortedKeys)[i].2 =
          rankIndexIn (rankedOrdinaryKeysWithObservations (ruleMajorTreeGraph tree) observe
            (rankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree))
            (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height node)
            (ordinaryKeyWithObservations (ruleMajorTreeGraph tree) observe
              (rankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree))
              (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height child) := by
        have := congrArg (fun l => l[i]?) hranks
        simp only [List.getElem?_map, List.getElem?_eq_getElem hi,
          List.getElem?_eq_getElem hi', Option.map_some, Option.some.injEq] at this
        rw [this, hget, oksEq]
      rw [hp2, hp1, ih child (sortedTrees[i]'hiTree) (sortedKeys[i]'(by omega))
        (traceAt i hiTree) hl depth]
      unfold contextualSphereOf
      simp only [OfficialRuleMajorKey.prefixLayer, List.map_map]
      apply List.map_congr_left
      intro chain hchain
      obtain ⟨hne, hhead, _⟩ := mem_depthChains_shape
        (ruleMajorTreeGraph tree) (toOfficialSourceTree tree).declarativeAddressing
        depth child chain hchain
      cases chain with
      | nil => exact absurd rfl hne
      | cons first rest =>
          simp only [List.head?_cons, Option.some.injEq] at hhead
          subst hhead
          simp only [Function.comp, contextualSphereEntry,
            DeclarativeCIP.observedChainRankAddress, List.getLastD_cons]

theorem contextTree_rankedLabels_getD
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (observations : ∀ rule node actual, tree.decoratedSubtreeAt? node.1 = some actual →
      observe rule node = priorityValue rule (armObservation rule actual))
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph)
    (hyp : ContextTreeRankReadback tree descriptorMap unit)
    {rootFuel : Nat} {rootKey : input.LocalizedRerootCumulativeRule45Key}
    (rootTrace : LocalizedRuleMajorSortTrace input .rule4a read rootFuel tree rootKey) :
    ∀ {fuel : Nat} (node : (ruleMajorTreeGraph tree).Node)
      (dsub : LocalizedCumulativeDecoratedTree input carrierFuel)
      (key : input.LocalizedRerootCumulativeRule45Key),
      LocalizedRuleMajorSortTrace input .rule4a read fuel dsub key →
      tree.decoratedSubtreeAt? node.1 = some dsub → ∀ depth,
        key.rankedLabels.getD depth [] = contextualSphereOf tree observe descriptorMap unit depth node := by
  intro fuel
  induction fuel with
  | zero =>
      intro node dsub key childTrace lookup depth
      cases childTrace with
      | terminal _ cursor _children _childrenComputed _terminalChildren _fullMatch _realizes =>
          exact contextualTerminal_sphere tree observe descriptorMap unit hyp node cursor lookup depth
  | succ fuel ih =>
      intro node dsub key childTrace lookup depth
      rcases LocalizedRuleMajorSortTrace.structure_of_trace childTrace with
        ⟨cursor, _children, dsubEq, keyEq, _childrenEq, _childrenComputed, _terminalChildren⟩ |
        ⟨cursor, _children, _childKeys, sortedKeys, sortedTrees, dsubEq, keyEq, _childrenEq,
          _childrenComputed, _nonempty, _childKeysComputed, _sortedEq, _constitutionalDescending,
          _sortedDescending, childrenTraced⟩
      · subst dsub
        subst key
        exact contextualTerminal_sphere tree observe descriptorMap unit hyp node cursor lookup depth
      · subst dsub
        subst key
        exact contextualStep_sphere tree observe observations descriptorMap unit hyp ih
          node cursor sortedKeys sortedTrees childrenTraced lookup rootTrace depth

/-- The tree root's Rule-4a ranked-label spheres in any fixed retained-root context. -/
theorem contextTree_root_rankedLabels_getD
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (observations : ∀ rule node actual, tree.decoratedSubtreeAt? node.1 = some actual →
      observe rule node = priorityValue rule (armObservation rule actual))
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph)
    (hyp : ContextTreeRankReadback tree descriptorMap unit)
    {fuel : Nat} {key : input.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedRuleMajorSortTrace input .rule4a read fuel tree key)
    (depth : Nat) :
    key.rankedLabels.getD depth [] =
      contextualSphereOf tree observe descriptorMap unit depth (ruleMajorTreeGraph tree).root := by
  apply contextTree_rankedLabels_getD tree observe observations descriptorMap unit hyp trace
    (ruleMajorTreeGraph tree).root tree key trace ?_ depth
  change tree.decoratedSubtreeAt? [] = some tree
  rw [decoratedSubtreeAt?]

end
end Rule4aTableBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ObservedRepresented
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ObservedRepresented.tie_iff
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.observedRankedChildTail_snd_eq_tailRanks
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.observedRankedChildren_snd_eq_headRanks
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.contextualSphereEntry
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.contextualSphereOf
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.contextualSphereOf_zero
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.contextualSphereOf_succ_of_no_children
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.contextualTerminal_sphere
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.contextualStep_sphere
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.contextTree_rankedLabels_getD
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.contextTree_root_rankedLabels_getD
