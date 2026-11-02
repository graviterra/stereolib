import TetraStereo.OneCenter.LocalizedRetainedRule4aCanonicalBridge
import TetraStereo.OneCenter.DeclarativeCIPRetainedCompleteSignatures
import TetraStereo.OneCenter.DeclarativeCIPObservedRankAddress
import TetraStereo.OneCenter.LocalizedActualFirstChiralMinimality
import TetraStereo.OneCenter.LocalizedActualReferenceSelectionBridge
import TetraStereo.OneCenter.LocalizedActualRankedLabelsSpheres
import TetraStereo.OneCenter.LocalizedRankedPopulationMerge
import TetraStereo.OneCenter.LocalizedRule4bReferenceAgreement
import TetraStereo.OneCenter.LocalizedRule4bPopulationInvariance
import TetraStereo.OneCenter.LocalizedRuleMajorRule4aAgreement
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000





















namespace TetraStereo.OneCenter.RetainedContextReferenceSelection

open LocalizedCumulativeDecoratedTree
open CertifiedLocalizedCIPInput
open OfficialSparseCanonicalVectorComparison
open DeclarativeCIP
open TetraStereo.OneCenter.Rule4aTableBridge
open TetraStereo.OneCenter.RetainedRule4aCanonicalBridge
open TetraStereo.OneCenter.RetainedContextStereoReadback

noncomputable section
open scoped Classical

variable {input : CertifiedLocalizedCIPInput}

/-- Rank address of one node under an observer and `retainedRankEvidence`, at the digraph's own
width and height. -/
def retainedReferenceRankAddress
    {Atom : Type} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom)
    (observe : ConstitutionalRule → graph.Node → ℤ) (node : graph.Node) : List ℕ :=
  observedRankAddress graph observe
    (retainedRankEvidence molecule descriptorMap unit graph) graph.width graph.height node

/-- Equal-depth rank-address order reverses the retained ancestor-key path once the observer is
the retained context observer. -/
theorem retainedReferenceRankAddress_lt_iff
    {Atom : Type} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom)
    (observe : ConstitutionalRule → graph.Node → ℤ)
    (observeEq : ∀ rule node, observe rule node =
      retainedContextNodeObservation molecule graph unit rule node)
    (addressing : graph.Addressing) {n m : graph.Node}
    (sameDepth : graph.depth n = graph.depth m) :
    retainedReferenceRankAddress molecule descriptorMap unit graph observe n <
        retainedReferenceRankAddress molecule descriptorMap unit graph observe m ↔
      retainedRankPath molecule descriptorMap unit graph m <
        retainedRankPath molecule descriptorMap unit graph n := by
  haveI : Fintype graph.Node := graph.nodeFintype
  have pathEq : ∀ node : graph.Node,
      (ancestorChain graph node).map
          (ordinaryKeyWithObservations graph observe
            (retainedRankEvidence molecule descriptorMap unit graph)
            graph.width graph.height) =
        retainedRankPath molecule descriptorMap unit graph node := by
    intro node
    unfold retainedRankPath
    apply List.map_congr_left
    intro ancestor _
    unfold retainedRankKey
    exact ordinaryKeyWithObservations_congr graph observe
      (retainedRankEvidence molecule descriptorMap unit graph)
      (retainedContextNodeObservation molecule graph unit) observeEq
      graph.width graph.height ancestor
  simpa [retainedReferenceRankAddress, observedRankAddress, pathEq] using
    observedRankAddress_lt_iff graph observe
      (retainedRankEvidence molecule descriptorMap unit graph) addressing
      graph.width graph.height le_rfl le_rfl sameDepth

section Spheres
variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
  {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}

/-- A stage-4a key represented by a node of an observer-parametric source tree. -/
def RetainedRepresented (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
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
      (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) W D node) key

/-- Equality of actual stage-4a comparison means equality of observer-parametric ordinary keys,
provided the trees have the contextual readback representations. -/
theorem RetainedRepresented.tie_iff
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph)
    (h4a : Rule4aOnly (ruleMajorTreeGraph tree)
      (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)))
    {W D : Nat} {keyI keyJ : input.LocalizedRerootCumulativeRule45Key}
    {nodeI nodeJ : (ruleMajorTreeGraph tree).Node}
    (hI : RetainedRepresented (read := read) tree observe descriptorMap unit W D keyI nodeI)
    (hJ : RetainedRepresented (read := read) tree observe descriptorMap unit W D keyJ nodeJ) :
    input.compareLocalizedRerootCumulativeRule45Keys keyI keyJ = Ordering.eq ↔
      ordinaryKeyWithObservations (ruleMajorTreeGraph tree) observe
        (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) W D nodeI =
      ordinaryKeyWithObservations (ruleMajorTreeGraph tree) observe
        (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) W D nodeJ := by
  obtain ⟨actualI, matchI, realizesI, repI, rep4I⟩ := hI
  obtain ⟨actualJ, matchJ, realizesJ, repJ, rep4J⟩ := hJ
  let graph := ruleMajorTreeGraph tree
  let evidence := retainedRankEvidence input.moleculeGraph descriptorMap unit graph
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

theorem retainedRankedChildTail_snd_eq_tailRanks
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph)
    (h4a : Rule4aOnly (ruleMajorTreeGraph tree)
      (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)))
    {W D : Nat} :
    ∀ (keys : List input.LocalizedRerootCumulativeRule45Key)
      (nodes : List (ruleMajorTreeGraph tree).Node),
      List.Forall₂ (RetainedRepresented (read := read) tree observe descriptorMap unit W D)
        keys nodes →
      ∀ (prev : input.LocalizedRerootCumulativeRule45Key)
        (prevNode : (ruleMajorTreeGraph tree).Node),
        RetainedRepresented (read := read) tree observe descriptorMap unit W D prev prevNode →
      ∀ rank : Nat,
        (input.localizedRerootRankedChildTail prev rank keys).map (·.2) =
          tailRanks (ordinaryKeyWithObservations (ruleMajorTreeGraph tree) observe
            (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) W D
            prevNode) rank
            (nodes.map (ordinaryKeyWithObservations (ruleMajorTreeGraph tree) observe
              (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) W D))
  | [], [], _, _, _, _, _ => rfl
  | [], _ :: _, h, _, _, _, _ => nomatch h
  | _ :: _, [], h, _, _, _, _ => nomatch h
  | key :: keys, node :: nodes, h, prev, prevNode, hprev, rank => by
      obtain ⟨hkey, hrest⟩ := List.forall₂_cons.1 h
      have tie := RetainedRepresented.tie_iff tree observe descriptorMap unit h4a hkey hprev
      simp only [List.map_cons, localizedRerootRankedChildTail, tailRanks]
      by_cases hc : input.compareLocalizedRerootCumulativeRule45Keys key prev = Ordering.eq
      · rw [if_pos hc, if_pos (tie.1 hc)]
        rw [retainedRankedChildTail_snd_eq_tailRanks tree observe descriptorMap unit h4a
          keys nodes hrest key node hkey rank]
      · rw [if_neg hc, if_neg fun h => hc (tie.2 h)]
        rw [retainedRankedChildTail_snd_eq_tailRanks tree observe descriptorMap unit h4a
          keys nodes hrest key node hkey (rank + 1)]

theorem retainedRankedChildren_snd_eq_headRanks
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph)
    (h4a : Rule4aOnly (ruleMajorTreeGraph tree)
      (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)))
    {W D : Nat}
    (keys : List input.LocalizedRerootCumulativeRule45Key)
    (nodes : List (ruleMajorTreeGraph tree).Node)
    (h : List.Forall₂ (RetainedRepresented (read := read) tree observe descriptorMap unit W D)
      keys nodes) :
    (input.localizedRerootRankedChildren keys).map (·.2) =
      headRanks (nodes.map (ordinaryKeyWithObservations (ruleMajorTreeGraph tree) observe
        (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) W D)) := by
  cases h with
  | nil => rfl
  | cons hkey hrest =>
      simp only [localizedRerootRankedChildren, List.map_cons, headRanks]
      rw [retainedRankedChildTail_snd_eq_tailRanks tree observe descriptorMap unit h4a
        _ _ hrest _ _ hkey 0]

def retainedSphereEntry
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph)
    (start : (ruleMajorTreeGraph tree).Node)
    (chain : List (ruleMajorTreeGraph tree).Node) :
    OfficialSparseEntry (Option LocalizedAuxiliaryLabel) :=
  (DeclarativeCIP.observedChainRankAddress (ruleMajorTreeGraph tree) observe
      (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree))
      (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height chain,
    (occurrenceReading input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)
      (chain.getLastD start)).toLocalizedLabel)

def retainedSphereOf
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph)
    (depth : Nat) (start : (ruleMajorTreeGraph tree).Node) :
    List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)) :=
  (depthChains (ruleMajorTreeGraph tree)
      (toOfficialSourceTree tree).declarativeAddressing depth start).map
    (retainedSphereEntry tree observe descriptorMap unit start)

theorem retainedSphereOf_zero
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph)
    (start : (ruleMajorTreeGraph tree).Node) :
    retainedSphereOf tree observe descriptorMap unit 0 start =
      [( [], (occurrenceReading input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph tree) start).toLocalizedLabel )] := rfl

theorem retainedSphereOf_succ_of_no_children
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph)
    (start : (ruleMajorTreeGraph tree).Node)
    (noChildren : (ruleMajorTreeGraph tree).childList start = []) (depth : Nat) :
    retainedSphereOf tree observe descriptorMap unit (depth + 1) start = [] := by
  simp [retainedSphereOf, DeclarativeCIP.depthChains, noChildren,
    DeclarativeCIP.slotList]

theorem retainedTerminal_sphere
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph)
    (hyp : RetainedContextTreeRankReadback tree descriptorMap unit)
    (node : (ruleMajorTreeGraph tree).Node)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (lookup : tree.decoratedSubtreeAt? node.1 =
      some (localizedRootTree input cursor (read cursor) [])) (depth : Nat) :
    (localizedCumulativeRule45TerminalKey input .rule4a cursor (read cursor)).rankedLabels.getD
      depth [] = retainedSphereOf tree observe descriptorMap unit depth node := by
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
      simpa [retainedSphereOf, retainedSphereEntry, DeclarativeCIP.depthChains,
        DeclarativeCIP.observedChainRankAddress, localizedRootTree] using rootLabel
  | succ depth =>
      rw [retainedSphereOf_succ_of_no_children tree observe descriptorMap unit node hchild depth]
      rfl

private theorem flatMap_eq_of_forall₂ {α β γ : Type*}
    {f : α → List γ} {g : β → List γ} :
    ∀ {left : List α} {right : List β},
      List.Forall₂ (fun a b => f a = g b) left right → left.flatMap f = right.flatMap g
  | [], [], _ => rfl
  | _ :: _, _ :: _, List.Forall₂.cons h hrest => by
      simp only [List.flatMap_cons]
      rw [h, flatMap_eq_of_forall₂ hrest]

theorem retainedStep_sphere
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (observations : ∀ rule node actual, tree.decoratedSubtreeAt? node.1 = some actual →
      observe rule node = priorityValue rule (armObservation rule actual))
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph)
    (hyp : RetainedContextTreeRankReadback tree descriptorMap unit)
    {fuel : Nat}
    (ih : ∀ (node : (ruleMajorTreeGraph tree).Node)
      (dsub : LocalizedCumulativeDecoratedTree input carrierFuel)
      (key : input.LocalizedRerootCumulativeRule45Key),
      LocalizedRuleMajorSortTrace input .rule4a read fuel dsub key →
      tree.decoratedSubtreeAt? node.1 = some dsub → ∀ depth,
        key.rankedLabels.getD depth [] = retainedSphereOf tree observe descriptorMap unit depth node)
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
      retainedSphereOf tree observe descriptorMap unit depth node := by
  cases depth with
  | zero =>
      have rootLookup : subtreeAt? tree node.1 =
          some (localizedRootTree input cursor (read cursor) sortedTrees) := by
        rwa [← decoratedSubtreeAt?_eq_subtreeAt?]
      have rootLabel := hyp.label node _ rootLookup
      simpa [localizedCumulativeRule45StepKey, retainedSphereOf, retainedSphereEntry,
        DeclarativeCIP.depthChains, DeclarativeCIP.observedChainRankAddress,
        localizedRootTree] using rootLabel
  | succ depth =>
      have hkeysorted := retainedContextTree_keySorted_rankEvidence tree observe observations hyp outerTrace
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
            RetainedRepresented (read := read) tree observe descriptorMap unit
              (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height
              (sortedKeys[i]'(by omega)) child := by
        intro i hi child hl
        refine ⟨sortedTrees[i]'hi,
          (LocalizedRuleMajorSortTrace.fullMatch_of_trace (traceAt i hi)).tableMatch,
          LocalizedRuleMajorSortTrace.realizes_of_trace (traceAt i hi), ?_, ?_⟩
        · exact (observedTree_node_bridge tree observe observations le_rfl le_rfl
            child (sortedTrees[i]'hi) (sortedKeys[i]'(by omega)) (traceAt i hi) hl).2
        · exact (retainedContextTree_node_bridge4a tree observe observations hyp le_rfl le_rfl
            child (sortedTrees[i]'hi) (sortedKeys[i]'(by omega)) (traceAt i hi) hl).2
      have slotGet : ∀ i (hi : i < sortedTrees.length), ∃ child,
          slots[i]'(by rw [slotLength]; exact hi) = child ∧
            tree.decoratedSubtreeAt? child.1 = some (sortedTrees[i]'hi) := by
        intro i hi
        obtain ⟨child, slotSome, _, hl⟩ := childAt i hi
        exact ⟨child, Option.some.inj ((List.getElem?_eq_getElem _).symm.trans slotSome), hl⟩
      have pairedSlots : List.Forall₂
          (RetainedRepresented (read := read) tree observe descriptorMap unit
            (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height) sortedKeys slots := by
        rw [List.forall₂_iff_get]
        refine ⟨by rw [lengthEq, slotLength], ?_⟩
        intro i hi hi'
        simp only [List.get_eq_getElem]
        obtain ⟨child, hget, hl⟩ := slotGet i (by omega)
        rw [hget]
        exact represented i (by omega) child hl
      have oksEq : rankedOrdinaryKeysWithObservations (ruleMajorTreeGraph tree) observe
          (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree))
          (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height node =
          slots.map (ordinaryKeyWithObservations (ruleMajorTreeGraph tree) observe
            (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree))
            (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height) := by
        unfold rankedOrdinaryKeysWithObservations
        exact sortDesc_childKeys_eq_slotOrder _ hdense hkeysorted
      have oksSorted : (slots.map (ordinaryKeyWithObservations (ruleMajorTreeGraph tree) observe
          (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree))
          (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height)).Pairwise
            fun x y => y ≤ x := by
        rw [← oksEq]
        exact Certificate.CanonicalSphereKey.sortDesc_pairwise _
      have hranks := retainedRankedChildren_snd_eq_headRanks tree observe descriptorMap unit
        hyp.rule4aOnly sortedKeys slots pairedSlots
      rw [headRanks_eq_map_rankIndexIn _ oksSorted] at hranks
      have hfst := rankedChildren_fst (input := input) sortedKeys
      show ([[([], read cursor)]] ++ input.mergeLocalizedRerootRankedLabelChildren sortedKeys).getD
        (depth + 1) [] = _
      rw [List.cons_append, List.nil_append, List.getD_cons_succ,
        getD_mergeLocalizedRerootRankedLabelChildren]
      unfold retainedSphereOf
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
            (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree))
            (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height node)
            (ordinaryKeyWithObservations (ruleMajorTreeGraph tree) observe
              (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree))
              (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height child) := by
        have := congrArg (fun l => l[i]?) hranks
        simp only [List.getElem?_map, List.getElem?_eq_getElem hi,
          List.getElem?_eq_getElem hi', Option.map_some, Option.some.injEq] at this
        rw [this, hget, oksEq]
      rw [hp2, hp1, ih child (sortedTrees[i]'hiTree) (sortedKeys[i]'(by omega))
        (traceAt i hiTree) hl depth]
      unfold retainedSphereOf
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
          simp only [Function.comp, retainedSphereEntry,
            DeclarativeCIP.observedChainRankAddress, List.getLastD_cons]

theorem retainedTree_rankedLabels_getD
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (observations : ∀ rule node actual, tree.decoratedSubtreeAt? node.1 = some actual →
      observe rule node = priorityValue rule (armObservation rule actual))
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph)
    (hyp : RetainedContextTreeRankReadback tree descriptorMap unit)
    {rootFuel : Nat} {rootKey : input.LocalizedRerootCumulativeRule45Key}
    (rootTrace : LocalizedRuleMajorSortTrace input .rule4a read rootFuel tree rootKey) :
    ∀ {fuel : Nat} (node : (ruleMajorTreeGraph tree).Node)
      (dsub : LocalizedCumulativeDecoratedTree input carrierFuel)
      (key : input.LocalizedRerootCumulativeRule45Key),
      LocalizedRuleMajorSortTrace input .rule4a read fuel dsub key →
      tree.decoratedSubtreeAt? node.1 = some dsub → ∀ depth,
        key.rankedLabels.getD depth [] = retainedSphereOf tree observe descriptorMap unit depth node := by
  intro fuel
  induction fuel with
  | zero =>
      intro node dsub key childTrace lookup depth
      cases childTrace with
      | terminal _ cursor _children _childrenComputed _terminalChildren _fullMatch _realizes =>
          exact retainedTerminal_sphere tree observe descriptorMap unit hyp node cursor lookup depth
  | succ fuel ih =>
      intro node dsub key childTrace lookup depth
      rcases LocalizedRuleMajorSortTrace.structure_of_trace childTrace with
        ⟨cursor, _children, dsubEq, keyEq, _childrenEq, _childrenComputed, _terminalChildren⟩ |
        ⟨cursor, _children, _childKeys, sortedKeys, sortedTrees, dsubEq, keyEq, _childrenEq,
          _childrenComputed, _nonempty, _childKeysComputed, _sortedEq, _constitutionalDescending,
          _sortedDescending, childrenTraced⟩
      · subst dsub
        subst key
        exact retainedTerminal_sphere tree observe descriptorMap unit hyp node cursor lookup depth
      · subst dsub
        subst key
        exact retainedStep_sphere tree observe observations descriptorMap unit hyp ih
          node cursor sortedKeys sortedTrees childrenTraced lookup rootTrace depth

/-- The tree root's Rule-4a ranked-label spheres in any fixed retained-root context. -/
theorem retainedTree_root_rankedLabels_getD
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (observations : ∀ rule node actual, tree.decoratedSubtreeAt? node.1 = some actual →
      observe rule node = priorityValue rule (armObservation rule actual))
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph)
    (hyp : RetainedContextTreeRankReadback tree descriptorMap unit)
    {fuel : Nat} {key : input.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedRuleMajorSortTrace input .rule4a read fuel tree key)
    (depth : Nat) :
    key.rankedLabels.getD depth [] =
      retainedSphereOf tree observe descriptorMap unit depth (ruleMajorTreeGraph tree).root := by
  apply retainedTree_rankedLabels_getD tree observe observations descriptorMap unit hyp trace
    (ruleMajorTreeGraph tree).root tree key trace ?_ depth
  change tree.decoratedSubtreeAt? [] = some tree
  rw [decoratedSubtreeAt?]

end Spheres

section Minimality
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

theorem retainedTree_node_minimal
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
    (tree : LocalizedCumulativeDecoratedTree input (input.certified.input.molecule.atomCount + 1))
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (observations : ∀ rule node actual, tree.decoratedSubtreeAt? node.1 = some actual →
      observe rule node = priorityValue rule (armObservation rule actual))
    {treeFuel : Nat} {treeKey : input.LocalizedRerootCumulativeRule45Key}
    (treeTrace : LocalizedRuleMajorSortTrace input .rule4a
      (input.molecularReader descriptorMap target) treeFuel tree treeKey)
    {unit : DetectedOccurrence input.moleculeGraph} (hyp : RetainedContextTreeRankReadback tree descriptorMap unit)
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
  have hkeysorted := retainedContextTree_keySorted_rankEvidence tree observe observations hyp treeTrace
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
        RetainedRepresented (read := input.molecularReader descriptorMap target) tree observe descriptorMap unit
          (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height (sortedKeys[i]'(by omega)) child :=
    fun i hi child hl =>
      ⟨sortedTrees[i]'hi, (LocalizedRuleMajorSortTrace.fullMatch_of_trace (traceAt i hi)).tableMatch,
        LocalizedRuleMajorSortTrace.realizes_of_trace (traceAt i hi),
        (observedTree_node_bridge tree observe observations le_rfl le_rfl child (sortedTrees[i]'hi) (sortedKeys[i]'(by omega))
          (traceAt i hi) hl).2,
        (retainedContextTree_node_bridge4a tree observe observations hyp le_rfl le_rfl child (sortedTrees[i]'hi) (sortedKeys[i]'(by omega))
          (traceAt i hi) hl).2⟩
  have slotGet : ∀ i (hi : i < sortedTrees.length), ∃ child, slots[i]'(by rw [slotLength]; exact hi) = child ∧
      tree.decoratedSubtreeAt? child.1 = some (sortedTrees[i]'hi) := by
    intro i hi
    obtain ⟨child, slotSome, _, hl⟩ := childAt i hi
    exact ⟨child, Option.some.inj ((List.getElem?_eq_getElem _).symm.trans slotSome), hl⟩
  have pairedSlots : List.Forall₂ (RetainedRepresented (read := input.molecularReader descriptorMap target) tree observe descriptorMap unit
      (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height) sortedKeys slots := by
    rw [List.forall₂_iff_get]
    refine ⟨by rw [lengthEq, slotLength], ?_⟩
    intro i hi hi'
    simp only [List.get_eq_getElem]
    obtain ⟨child, hget, hl⟩ := slotGet i (by omega)
    rw [hget]
    exact represented i (by omega) child hl
  set oks := slots.map (ordinaryKeyWithObservations (ruleMajorTreeGraph tree) observe
    (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree))
    (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height) with hoks
  have oksSorted : oks.Pairwise fun x y => y ≤ x := by
    have oksEq : rankedOrdinaryKeysWithObservations (ruleMajorTreeGraph tree) observe
        (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree))
        (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height node = oks := by
      unfold rankedOrdinaryKeysWithObservations
      exact sortDesc_childKeys_eq_slotOrder _ hdense hkeysorted
    rw [← oksEq]
    exact Certificate.CanonicalSphereKey.sortDesc_pairwise _
  have hranks := retainedRankedChildren_snd_eq_headRanks (tree := tree) (observe := observe) (descriptorMap := descriptorMap) (unit := unit) hyp.rule4aOnly sortedKeys slots pairedSlots
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
        (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree))
        (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height (slots[i]'(by omega))) := by
    intro i hi
    have := congrArg (fun l => l[i]?) hranks
    simp only [hoks, List.getElem?_map, List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem (show i < slots.length by omega), Option.map_some,
      Option.some.injEq] at this
    exact this
  have memOks : ∀ i (hi : i < slots.length), ordinaryKeyWithObservations (ruleMajorTreeGraph tree) observe
      (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree))
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
        (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree))
        (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height slots[j] ≤
        ordinaryKeyWithObservations (ruleMajorTreeGraph tree) observe
          (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree))
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
        rw [RetainedRepresented.tie_iff tree observe descriptorMap unit hyp.rule4aOnly (represented i₀ (by omega) child₀ hl₀)
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
theorem retainedTree_firstChiralRank_minimal
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
    (tree : LocalizedCumulativeDecoratedTree input (input.certified.input.molecule.atomCount + 1))
    (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
    (observations : ∀ rule node actual, tree.decoratedSubtreeAt? node.1 = some actual →
      observe rule node = priorityValue rule (armObservation rule actual))
    {treeFuel : Nat} {treeKey : input.LocalizedRerootCumulativeRule45Key}
    (treeTrace : LocalizedRuleMajorSortTrace input .rule4a
      (input.molecularReader descriptorMap target) treeFuel tree treeKey)
    {unit : DetectedOccurrence input.moleculeGraph} (hyp : RetainedContextTreeRankReadback tree descriptorMap unit) :
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
        exact retainedTree_node_minimal descriptorMap target tree observe observations treeTrace hyp ih node cursor children childKeys sortedKeys
          sortedTrees childKeysComputed sortedEq childrenTraced lookup d first hfirst e he hchiral

end Minimality

section Tree
variable (tree : LocalizedCumulativeDecoratedTree input (input.certified.input.molecule.atomCount + 1))
  (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
  (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
  (unit : DetectedOccurrence input.moleculeGraph)
/-- The reading-based label of a node. -/
abbrev nodeLabel (node : (ruleMajorTreeGraph tree).Node) : Option LocalizedAuxiliaryLabel :=
  (occurrenceReading input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) node).toLocalizedLabel

theorem nodeLabel_chiral_iff (hyp : RetainedContextTreeRankReadback tree descriptorMap unit) (node : (ruleMajorTreeGraph tree).Node)
    (rs : RS) :
    nodeLabel tree descriptorMap unit node = some (.chiral rs) ↔
      eligibleSense input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) node = some (senseOf rs) := by
  show _ ↔ readingSense (occurrenceReading input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) node) =
    some (senseOf rs)
  exact toLocalizedLabel_chiral_iff _ (hyp.tetrahedral node) rs

theorem eligible_iff_nodeLabel_chiral (hyp : RetainedContextTreeRankReadback tree descriptorMap unit)
    (node : (ruleMajorTreeGraph tree).Node) :
    Eligible input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) node ↔
      ∃ rs, nodeLabel tree descriptorMap unit node = some (.chiral rs) := by
  unfold Eligible
  rw [Option.isSome_iff_exists]
  constructor
  · rintro ⟨sense, hsense⟩
    cases sense with
    | senior => exact ⟨.R, (nodeLabel_chiral_iff tree descriptorMap unit hyp node .R).2 hsense⟩
    | junior => exact ⟨.S, (nodeLabel_chiral_iff tree descriptorMap unit hyp node .S).2 hsense⟩
  · rintro ⟨rs, hrs⟩
    exact ⟨senseOf rs, (nodeLabel_chiral_iff tree descriptorMap unit hyp node rs).1 hrs⟩

/-! ## Entries of the root spheres are nodes at that depth -/

theorem hdense_tree : Dense (toOfficialSourceTree tree).declarativeAddressing :=
  (toOfficialSourceTree tree).declarativeAddressing_dense

/-- The entry of a root chain, in terms of its endpoint. -/
theorem sphereEntry_root_eq (_hyp : RetainedContextTreeRankReadback tree descriptorMap unit) (d : Nat)
    (chain : List (ruleMajorTreeGraph tree).Node) (hchain : chain ∈ depthChains (ruleMajorTreeGraph tree) (toOfficialSourceTree tree).declarativeAddressing d (ruleMajorTreeGraph tree).root) :
    retainedSphereEntry tree observe descriptorMap unit (ruleMajorTreeGraph tree).root chain =
      (retainedReferenceRankAddress input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) observe (chain.getLastD (ruleMajorTreeGraph tree).root),
        nodeLabel tree descriptorMap unit (chain.getLastD (ruleMajorTreeGraph tree).root)) := by
  unfold retainedSphereEntry retainedReferenceRankAddress
  rw [observedRankAddress_eq_observedChainRankAddress_of_mem (ruleMajorTreeGraph tree) observe (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) (toOfficialSourceTree tree).declarativeAddressing (hdense_tree tree) (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height d chain hchain]

theorem mem_sphereOf_root_iff (hyp : RetainedContextTreeRankReadback tree descriptorMap unit) (d : Nat) (e : LabelEntry) :
    e ∈ retainedSphereOf tree observe descriptorMap unit d (ruleMajorTreeGraph tree).root ↔
      ∃ node : (ruleMajorTreeGraph tree).Node, (ruleMajorTreeGraph tree).depth node = d ∧
        e = (retainedReferenceRankAddress input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) observe node,
          nodeLabel tree descriptorMap unit node) := by
  unfold retainedSphereOf
  rw [List.mem_map]
  constructor
  · rintro ⟨chain, hchain, rfl⟩
    refine ⟨chain.getLastD (ruleMajorTreeGraph tree).root, ?_, sphereEntry_root_eq tree observe descriptorMap unit hyp d chain hchain⟩
    rw [← mem_depthNodes_root_iff (ruleMajorTreeGraph tree) (hdense_tree tree) d,
      ← depthChains_getLastD (ruleMajorTreeGraph tree) (toOfficialSourceTree tree).declarativeAddressing d (ruleMajorTreeGraph tree).root]
    exact List.mem_map_of_mem hchain
  · rintro ⟨node, hdepth, rfl⟩
    have hmem : node ∈ depthNodes (ruleMajorTreeGraph tree) (toOfficialSourceTree tree).declarativeAddressing d (ruleMajorTreeGraph tree).root :=
      (mem_depthNodes_root_iff (ruleMajorTreeGraph tree) (hdense_tree tree) d node).2 hdepth
    rw [← depthChains_getLastD (ruleMajorTreeGraph tree) (toOfficialSourceTree tree).declarativeAddressing d (ruleMajorTreeGraph tree).root, List.mem_map] at hmem
    obtain ⟨chain, hchain, hlast⟩ := hmem
    refine ⟨chain, hchain, ?_⟩
    rw [sphereEntry_root_eq tree observe descriptorMap unit hyp d chain hchain, hlast]

/-- The root sphere `d`, as a map over the depth-`d` nodes. -/
theorem sphereOf_root_eq_map (hyp : RetainedContextTreeRankReadback tree descriptorMap unit) (d : Nat) :
    retainedSphereOf tree observe descriptorMap unit d (ruleMajorTreeGraph tree).root =
      (depthNodes (ruleMajorTreeGraph tree) (toOfficialSourceTree tree).declarativeAddressing d (ruleMajorTreeGraph tree).root).map fun node =>
        (retainedReferenceRankAddress input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) observe node,
          nodeLabel tree descriptorMap unit node) := by
  unfold retainedSphereOf
  rw [← depthChains_getLastD (ruleMajorTreeGraph tree) (toOfficialSourceTree tree).declarativeAddressing d (ruleMajorTreeGraph tree).root, List.map_map]
  apply List.map_congr_left
  intro chain hchain
  exact sphereEntry_root_eq tree observe descriptorMap unit hyp d chain hchain


/-- A ring duplicate remains in its depth sphere. Its localized label is `none`, so it is not a
chiral reference, and its retained rank address still uses the present nonstereogenic code. -/
theorem retainedSphere_ringDuplicate_label_none
    (hyp : RetainedContextTreeRankReadback tree descriptorMap unit) (d : Nat)
    (node : (ruleMajorTreeGraph tree).Node)
    (hdepth : (ruleMajorTreeGraph tree).depth node = d) (distance : Nat)
    (duplicate : ((ruleMajorTreeGraph tree).label node).provenance = .ringDuplicate distance) :
    (retainedReferenceRankAddress input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph tree) observe node, none) ∈
      retainedSphereOf tree observe descriptorMap unit d (ruleMajorTreeGraph tree).root := by
  have noneLabel : nodeLabel tree descriptorMap unit node = none := by
    unfold nodeLabel
    rw [occurrenceReading_of_ringDuplicate input.moleculeGraph descriptorMap unit
      (ruleMajorTreeGraph tree) node distance duplicate]
    rfl
  have entryEq :
      (retainedReferenceRankAddress input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph tree) observe node, nodeLabel tree descriptorMap unit node) =
        (retainedReferenceRankAddress input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph tree) observe node, none) := by
    rw [noneLabel]
  rw [← entryEq]
  exact (mem_sphereOf_root_iff tree observe descriptorMap unit hyp d _).2 ⟨node, hdepth, rfl⟩

/-- Ring duplicates are ineligible for the retained reference class. -/
theorem not_Eligible_ringDuplicate_tree (node : (ruleMajorTreeGraph tree).Node) (distance : Nat)
    (duplicate : ((ruleMajorTreeGraph tree).label node).provenance = .ringDuplicate distance) :
    ¬ Eligible input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) node :=
  not_Eligible_ringDuplicate input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)
    node distance duplicate


end Tree
private theorem length_filter_filterMap {α β : Type*} (f : α → Option β) (p : β → Bool) :
    ∀ l : List α, ((l.filterMap f).filter p).length =
      (l.filter fun a => ((f a).map p).getD false).length
  | [] => rfl
  | a :: l => by
      rw [List.filterMap_cons]
      cases hfa : f a with
      | none =>
          simp only [List.filter_cons, hfa, Option.map_none, Option.getD_none, Bool.false_eq_true,
            if_false]
          exact length_filter_filterMap f p l
      | some b =>
          simp only [List.filter_cons, hfa, Option.map_some, Option.getD_some]
          by_cases hb : p b = true
          · simp only [hb, if_true, List.length_cons]
            rw [length_filter_filterMap f p l]
          · simp only [hb, Bool.false_eq_true, if_false]
            exact length_filter_filterMap f p l


section Assembly
variable (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
  (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
  (tree : LocalizedCumulativeDecoratedTree input (input.certified.input.molecule.atomCount + 1))
  (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
  (observations : ∀ rule node actual, tree.decoratedSubtreeAt? node.1 = some actual →
    observe rule node = priorityValue rule (armObservation rule actual))
  {fuel : Nat} {key : input.LocalizedRerootCumulativeRule45Key}
  (trace : LocalizedRuleMajorSortTrace input .rule4a
    (input.molecularReader descriptorMap target) fuel tree key)
  (unit : DetectedOccurrence input.moleculeGraph)
  (observeEq : ∀ rule node, observe rule node =
    retainedContextNodeObservation input.moleculeGraph (ruleMajorTreeGraph tree) unit rule node)
  (hyp : RetainedContextTreeRankReadback tree descriptorMap unit)
include hyp
local instance retainedAssemblyNodeFintype :
    Fintype (ruleMajorTreeGraph tree).Node := (ruleMajorTreeGraph tree).nodeFintype

include observations trace in
/-- Node form of the first-chiral minimality at the root spheres. -/
theorem rankAddress_min_of_firstChiralRank (d : Nat) (first : List Nat)
    (hfirst : firstChiralRank (retainedSphereOf tree observe descriptorMap unit d (ruleMajorTreeGraph tree).root) = some first)
    (node : (ruleMajorTreeGraph tree).Node) (hdepth : (ruleMajorTreeGraph tree).depth node = d)
    (helig : Eligible input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) node) :
    first ≤ retainedReferenceRankAddress input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) observe node := by
  obtain ⟨rs, hrs⟩ := (eligible_iff_nodeLabel_chiral tree descriptorMap unit hyp node).1 helig
  have hmem : (retainedReferenceRankAddress input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) observe node,
      nodeLabel tree descriptorMap unit node) ∈ retainedSphereOf tree observe descriptorMap unit d (ruleMajorTreeGraph tree).root :=
    (mem_sphereOf_root_iff tree observe descriptorMap unit hyp d _).2 ⟨node, hdepth, rfl⟩
  have := retainedTree_firstChiralRank_minimal descriptorMap target tree observe observations trace hyp (ruleMajorTreeGraph tree).root tree key
    trace rfl d first (by rw [retainedTree_root_rankedLabels_getD tree observe observations descriptorMap unit hyp trace]; exact hfirst) _
    (by rw [retainedTree_root_rankedLabels_getD tree observe observations descriptorMap unit hyp trace]; exact hmem) ⟨rs, hrs⟩
  exact this

theorem exists_node_of_firstChiralRank (d : Nat) (first : List Nat)
    (hfirst : firstChiralRank (retainedSphereOf tree observe descriptorMap unit d (ruleMajorTreeGraph tree).root) = some first) :
    ∃ node : (ruleMajorTreeGraph tree).Node, (ruleMajorTreeGraph tree).depth node = d ∧
      Eligible input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) node ∧
        retainedReferenceRankAddress input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) observe node = first := by
  obtain ⟨e, he, haddr, rs, hrs⟩ := firstChiralRank_mem _ first hfirst
  obtain ⟨node, hdepth, rfl⟩ := (mem_sphereOf_root_iff tree observe descriptorMap unit hyp d e).1 he
  exact ⟨node, hdepth, (eligible_iff_nodeLabel_chiral tree descriptorMap unit hyp node).2 ⟨rs, hrs⟩,
    haddr⟩

theorem firstChiralRank_eq_none_iff_root (d : Nat) :
    firstChiralRank (retainedSphereOf tree observe descriptorMap unit d (ruleMajorTreeGraph tree).root) = none ↔
      ¬ ∃ node : (ruleMajorTreeGraph tree).Node, (ruleMajorTreeGraph tree).depth node = d ∧
        Eligible input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) node := by
  rw [firstChiralRank_eq_none_iff]
  constructor
  · rintro h ⟨node, hdepth, helig⟩
    obtain ⟨rs, hrs⟩ := (eligible_iff_nodeLabel_chiral tree descriptorMap unit hyp node).1 helig
    exact h _ ((mem_sphereOf_root_iff tree observe descriptorMap unit hyp d _).2 ⟨node, hdepth, rfl⟩) ⟨rs, hrs⟩
  · intro h e he ⟨rs, hrs⟩
    obtain ⟨node, hdepth, rfl⟩ := (mem_sphereOf_root_iff tree observe descriptorMap unit hyp d e).1 he
    exact h ⟨node, hdepth, (eligible_iff_nodeLabel_chiral tree descriptorMap unit hyp node).2 ⟨rs, hrs⟩⟩

include observe observations trace observeEq in
/-- **The actual reference population is the independent retained selection.** -/
theorem retainedTree_references_eq_retainedReferenceSelection :
    localizedRule4bReferencesFromRankedLabels key.rankedLabels =
      toReferenceList (retainedReferenceSelection input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph tree)) := by
  set layers := key.rankedLabels with hlayersDef
  set n := layers.length with hn
  have hS : ∀ d, layers.getD d [] = retainedSphereOf tree observe descriptorMap unit d (ruleMajorTreeGraph tree).root :=
    fun d => retainedTree_root_rankedLabels_getD tree observe observations descriptorMap unit hyp trace d
  have hlayers : layers = (List.range n).map fun d => retainedSphereOf tree observe descriptorMap unit d (ruleMajorTreeGraph tree).root := by
    conv_lhs => rw [list_eq_map_range_getD layers]
    exact List.map_congr_left fun d _ => hS d
  have hbeyond : ∀ d, n ≤ d → retainedSphereOf tree observe descriptorMap unit d (ruleMajorTreeGraph tree).root = [] := by
    intro d hd
    rw [← hS d, List.getD_eq_getElem?_getD, List.getElem?_eq_none hd]
    rfl
  unfold localizedRule4bReferencesFromRankedLabels
  rw [localizedFirstChiralRankPopulation_eq_findSome?, hlayers, List.findSome?_map,
    show (localizedFirstChiralRankPopulationInLayer ∘ fun d =>
        retainedSphereOf tree observe descriptorMap unit d (ruleMajorTreeGraph tree).root) =
      fun d => (firstChiralRank (retainedSphereOf tree observe descriptorMap unit d (ruleMajorTreeGraph tree).root)).map
        fun rank => localizedChiralDescriptorsAtRank rank
          (retainedSphereOf tree observe descriptorMap unit d (ruleMajorTreeGraph tree).root) from
      funext fun d => localizedFirstChiralRankPopulationInLayer_eq_map_firstChiralRank _]
  by_cases hex : ∃ node : (ruleMajorTreeGraph tree).Node,
      Eligible input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) node
  · -- the nearest eligible depth
    have hexd : ∃ d, ∃ node : (ruleMajorTreeGraph tree).Node, (ruleMajorTreeGraph tree).depth node = d ∧
        Eligible input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) node := by
      obtain ⟨node, h⟩ := hex
      exact ⟨_, node, rfl, h⟩
    set d₀ := Nat.find hexd with hd₀def
    have hd₀ : ∃ node : (ruleMajorTreeGraph tree).Node, (ruleMajorTreeGraph tree).depth node = d₀ ∧
        Eligible input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) node := Nat.find_spec hexd
    have hmin : ∀ d, d < d₀ → ¬ ∃ node : (ruleMajorTreeGraph tree).Node, (ruleMajorTreeGraph tree).depth node = d ∧
        Eligible input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) node :=
      fun d hd => Nat.find_min hexd hd
    obtain ⟨a₀, ha₀⟩ : ∃ a₀, firstChiralRank (retainedSphereOf tree observe descriptorMap unit d₀ (ruleMajorTreeGraph tree).root) =
        some a₀ := by
      rcases h : firstChiralRank (retainedSphereOf tree observe descriptorMap unit d₀ (ruleMajorTreeGraph tree).root) with _ | a
      · exact absurd hd₀ ((firstChiralRank_eq_none_iff_root descriptorMap tree observe unit hyp d₀).1 h)
      · exact ⟨a, rfl⟩
    have hd₀n : d₀ < n := by
      by_contra hge
      push_neg at hge
      rw [hbeyond d₀ hge] at ha₀
      simp [firstChiralRank] at ha₀
    have hbefore : ∀ d < d₀, (firstChiralRank (retainedSphereOf tree observe descriptorMap unit d (ruleMajorTreeGraph tree).root)).map
        (fun rank => localizedChiralDescriptorsAtRank rank
          (retainedSphereOf tree observe descriptorMap unit d (ruleMajorTreeGraph tree).root)) = none := by
      intro d hd
      rw [(firstChiralRank_eq_none_iff_root descriptorMap tree observe unit hyp d).2 (hmin d hd)]
      rfl
    rw [findSome?_range_of_first _ n d₀ _ hd₀n (by rw [ha₀]; rfl) hbefore]
    simp only [Option.getD_some]
    set pop := localizedChiralDescriptorsAtRank a₀
      (retainedSphereOf tree observe descriptorMap unit d₀ (ruleMajorTreeGraph tree).root) with hpop
    -- the class
    have nearest_iff : ∀ m : (ruleMajorTreeGraph tree).Node,
        NearestEligible input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) m ↔
          Eligible input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) m ∧
            (ruleMajorTreeGraph tree).depth m = d₀ := by
      intro m
      constructor
      · rintro ⟨helig, hle⟩
        refine ⟨helig, le_antisymm ?_ ?_⟩
        · obtain ⟨node, hdepth, helig'⟩ := hd₀
          rw [← hdepth]
          exact hle node helig'
        · by_contra hlt
          push_neg at hlt
          exact hmin _ hlt ⟨m, rfl, helig⟩
      · rintro ⟨helig, hdepth⟩
        refine ⟨helig, fun other hother => ?_⟩
        rw [hdepth]
        by_contra hlt
        push_neg at hlt
        exact hmin _ hlt ⟨other, rfl, hother⟩
    have class_iff : ∀ m : (ruleMajorTreeGraph tree).Node,
        RetainedInReferenceClass input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) m ↔
          Eligible input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) m ∧
            (ruleMajorTreeGraph tree).depth m = d₀ ∧
              retainedReferenceRankAddress input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) observe m = a₀ := by
      intro m
      unfold RetainedInReferenceClass
      rw [nearest_iff]
      constructor
      · rintro ⟨⟨helig, hdepth⟩, hmax⟩
        refine ⟨helig, hdepth, le_antisymm ?_ ?_⟩
        · obtain ⟨n₀, hdepth₀, helig₀, haddr₀⟩ :=
            exists_node_of_firstChiralRank descriptorMap tree observe unit hyp d₀ a₀ ha₀
          have hle := hmax n₀ ((nearest_iff n₀).2 ⟨helig₀, hdepth₀⟩)
          rw [← haddr₀]
          apply not_lt.1
          intro hlt
          rw [retainedReferenceRankAddress_lt_iff input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) observe observeEq
            (toOfficialSourceTree tree).declarativeAddressing (by rw [hdepth₀, hdepth])] at hlt
          exact absurd hle (not_le.2 hlt)
        · exact rankAddress_min_of_firstChiralRank descriptorMap target tree observe observations trace unit hyp d₀ a₀ ha₀ m hdepth helig
      · rintro ⟨helig, hdepth, haddr⟩
        refine ⟨⟨helig, hdepth⟩, fun o ho => ?_⟩
        obtain ⟨helig', hdepth'⟩ := (nearest_iff o).1 ho
        apply not_lt.1
        intro hlt
        rw [← retainedReferenceRankAddress_lt_iff input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) observe observeEq
          (toOfficialSourceTree tree).declarativeAddressing (by rw [hdepth', hdepth])] at hlt
        have := rankAddress_min_of_firstChiralRank descriptorMap target tree observe observations trace unit hyp d₀ a₀ ha₀ o hdepth' helig'
        rw [haddr] at hlt
        exact absurd this (not_le.2 hlt)
    -- counts
    have count : ∀ rs : RS, (pop.filter fun d => d == rs).length =
        ((retainedReferenceClass input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)).filter fun node =>
          eligibleSense input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) node =
            some (senseOf rs)).card := by
      intro rs
      rw [hpop, localizedChiralDescriptorsAtRank_eq_filterMap,
        sphereOf_root_eq_map tree observe descriptorMap unit hyp, List.filterMap_map, length_filter_filterMap]
      simp only [Function.comp_def]
      have hnod := depthNodes_nodup (ruleMajorTreeGraph tree) (toOfficialSourceTree tree).declarativeAddressing
        (hdense_tree tree) d₀ (ruleMajorTreeGraph tree).root
      have key : ∀ P : (ruleMajorTreeGraph tree).Node → Bool,
          ((depthNodes (ruleMajorTreeGraph tree) (toOfficialSourceTree tree).declarativeAddressing d₀
            (ruleMajorTreeGraph tree).root).filter P).length =
          ((depthNodes (ruleMajorTreeGraph tree) (toOfficialSourceTree tree).declarativeAddressing d₀
            (ruleMajorTreeGraph tree).root).filter P).toFinset.card :=
        fun P => (List.toFinset_card_of_nodup (hnod.filter P)).symm
      rw [key, List.toFinset_filter]
      congr 1
      ext m
      simp only [Finset.mem_filter, List.mem_toFinset,
        mem_depthNodes_root_iff (ruleMajorTreeGraph tree) (hdense_tree tree), retainedReferenceClass,
        Finset.mem_univ, true_and]
      rw [class_iff]
      constructor
      · rintro ⟨hdepth, hb⟩
        cases hc : chiralDescriptorAtRank a₀
            (retainedReferenceRankAddress input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) observe m,
              nodeLabel tree descriptorMap unit m) with
        | none => rw [hc] at hb; simp at hb
        | some d =>
            rw [hc] at hb
            simp only [Option.map_some, Option.getD_some, beq_iff_eq] at hb
            subst hb
            obtain ⟨haddr, hlabel⟩ := (chiralDescriptorAtRank_eq_some_iff _ _ _).1 hc
            have hsense := (nodeLabel_chiral_iff tree descriptorMap unit hyp m d).1 hlabel
            refine ⟨⟨?_, hdepth, haddr⟩, hsense⟩
            unfold Eligible
            rw [hsense]
            rfl
      · rintro ⟨⟨_, hdepth, haddr⟩, hsense⟩
        refine ⟨hdepth, ?_⟩
        have hlabel := (nodeLabel_chiral_iff tree descriptorMap unit hyp m rs).2 hsense
        rw [(chiralDescriptorAtRank_eq_some_iff a₀ _ rs).2 ⟨haddr, hlabel⟩]
        simp
    have hR := count .R
    have hS' := count .S
    simp only [senseOf] at hR hS'
    -- the population is nonempty
    have hne : pop.isEmpty = false := by
      obtain ⟨e, he, haddr, rs, hrs⟩ := firstChiralRank_mem _ a₀ ha₀
      rw [List.isEmpty_eq_false_iff_exists_mem]
      refine ⟨rs, ?_⟩
      rw [hpop, localizedChiralDescriptorsAtRank_eq_filterMap, List.mem_filterMap]
      exact ⟨e, he, (chiralDescriptorAtRank_eq_some_iff _ _ _).2 ⟨haddr, hrs⟩⟩
    unfold localizedRule4bReferencesFromPopulation retainedReferenceSelection
    rw [if_neg (by rw [hne]; decide), if_neg (not_not.2 hex)]
    unfold retainedSeniorCount retainedJuniorCount
    rw [← hR, ← hS']
    dsimp only
    split_ifs <;> rfl
  · -- no eligible node: no chiral entry in any sphere
    have hnone : ∀ d, (firstChiralRank (retainedSphereOf tree observe descriptorMap unit d (ruleMajorTreeGraph tree).root)).map
        (fun rank => localizedChiralDescriptorsAtRank rank
          (retainedSphereOf tree observe descriptorMap unit d (ruleMajorTreeGraph tree).root)) = none := by
      intro d
      rw [(firstChiralRank_eq_none_iff_root descriptorMap tree observe unit hyp d).2
        (fun ⟨node, _, helig⟩ => hex ⟨node, helig⟩)]
      rfl
    rw [findSome?_range_eq_none _ n hnone]
    unfold localizedRule4bReferencesFromPopulation retainedReferenceSelection
    rw [if_pos hex]
    rfl

end Assembly

/-- The generated dependency reader selects the retained reference population. The target may be
any detected carrier context. `SimpleBonded` supplies the reader equality and the retained rank
bundle; acyclicity is not used. -/
theorem retainedGeneratedContextTree_references_eq_selection
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (target : input.certified.LocalizedRerootCursor
      (LocalizedRuleMajorReference.carrierFuel input))
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.occurrence.1 = unit.1)
    (tree : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedRuleMajorReference.carrierFuel input))
    {fuel : Nat} {key : input.certified.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedRuleMajorSortTrace input.certified .rule4a
      (input.certified.localizedDependencyLabel target.occurrence
        (input.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState input) target.occurrence)) fuel tree key)
    (rootChild : tree.source ∈ input.certified.executableLocalizedRerootChildren target) :
    localizedRule4bReferencesFromRankedLabels key.rankedLabels =
      toReferenceList (retainedReferenceSelection input.certified.moleculeGraph
        (LocalizedRuleMajorReference.descriptorMap input) unit (ruleMajorTreeGraph tree)) := by
  have realizes := LocalizedRuleMajorSortTrace.realizes_of_trace trace
  have hyp := retainedGeneratedContextTreeRankReadback input singleBonded target unit targetUnit
    tree realizes rootChild
  let observe := retainedContextNodeObservation input.certified.moleculeGraph
    (ruleMajorTreeGraph tree) unit
  have observations : ∀ rule node actual, tree.decoratedSubtreeAt? node.1 = some actual →
      observe rule node = priorityValue rule (armObservation rule actual) := by
    intro rule node actual lookup
    exact retainedDecoratedObservation_eq_arm singleBonded target unit targetUnit tree realizes
      rootChild rule node actual lookup
  have observeEq : ∀ rule node, observe rule node =
      retainedContextNodeObservation input.certified.moleculeGraph (ruleMajorTreeGraph tree) unit
        rule node := by
    intro rule node
    rfl
  have readerEq := LocalizedRuleMajorReference.molecularReader_eq_generatedReader_of_simpleBonded
    input singleBonded target.occurrence
  have trace' : LocalizedRuleMajorSortTrace input.certified .rule4a
      (input.certified.molecularReader (LocalizedRuleMajorReference.descriptorMap input)
        target.occurrence) fuel tree key := by
    rw [readerEq]
    exact trace
  exact retainedTree_references_eq_retainedReferenceSelection
    (LocalizedRuleMajorReference.descriptorMap input) target.occurrence tree observe observations
    trace' unit observeEq hyp

/-- Adequate-budget existence of a realized Rule-4a key whose reference list is the retained
selection. Cursor validity is derived from executable child membership. -/
theorem exists_retainedGeneratedContextTree_references_eq_selection
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (target : input.certified.LocalizedRerootCursor
      (LocalizedRuleMajorReference.carrierFuel input))
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.occurrence.1 = unit.1)
    (cursor : input.certified.LocalizedRerootCursor
      (LocalizedRuleMajorReference.carrierFuel input))
    (rootChild : cursor ∈ input.certified.executableLocalizedRerootChildren target) :
    ∃ (tree : LocalizedCumulativeDecoratedTree input.certified
        (LocalizedRuleMajorReference.carrierFuel input))
      (key : input.certified.LocalizedRerootCumulativeRule45Key),
      tree.source = cursor ∧
      input.certified.buildRuleMajorCumulativeWithReadExec? .rule4a
        (input.certified.localizedDependencyLabel target.occurrence
          (input.certified.localizedDependencyView
            (LocalizedRuleMajorReference.referenceState input) target.occurrence))
        (2 * (LocalizedRuleMajorReference.carrierFuel input + 1)) cursor = some key ∧
      localizedRule4bReferencesFromRankedLabels key.rankedLabels =
        toReferenceList (retainedReferenceSelection input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit (ruleMajorTreeGraph tree)) := by
  have valid := input.certified.localizedRerootChild_valid target cursor _
    (input.certified.executableLocalizedRerootChildren_declarative target) rootChild
  obtain ⟨tree, key, source, built, trace⟩ := exists_ruleMajorTrace_at_twice input.certified
    .rule4a
    (input.certified.localizedDependencyLabel target.occurrence
      (input.certified.localizedDependencyView
        (LocalizedRuleMajorReference.referenceState input) target.occurrence)) cursor valid
  refine ⟨tree, key, source, ?_, ?_⟩
  · rw [input.certified.buildRuleMajorCumulativeWithReadExec_eq]
    exact built
  · exact retainedGeneratedContextTree_references_eq_selection input singleBonded target unit
      targetUnit tree trace (by simpa only [source] using rootChild)

end

end RetainedContextReferenceSelection
end TetraStereo.OneCenter
assert_kernel_only TetraStereo.OneCenter.RetainedContextReferenceSelection.retainedReferenceRankAddress
assert_kernel_only TetraStereo.OneCenter.RetainedContextReferenceSelection.retainedReferenceRankAddress_lt_iff
assert_kernel_only TetraStereo.OneCenter.RetainedContextReferenceSelection.RetainedRepresented
assert_kernel_only TetraStereo.OneCenter.RetainedContextReferenceSelection.RetainedRepresented.tie_iff
assert_kernel_only TetraStereo.OneCenter.RetainedContextReferenceSelection.retainedRankedChildTail_snd_eq_tailRanks
assert_kernel_only TetraStereo.OneCenter.RetainedContextReferenceSelection.retainedRankedChildren_snd_eq_headRanks
assert_kernel_only TetraStereo.OneCenter.RetainedContextReferenceSelection.retainedSphereEntry
assert_kernel_only TetraStereo.OneCenter.RetainedContextReferenceSelection.retainedSphereOf
assert_kernel_only TetraStereo.OneCenter.RetainedContextReferenceSelection.retainedSphereOf_zero
assert_kernel_only TetraStereo.OneCenter.RetainedContextReferenceSelection.retainedSphereOf_succ_of_no_children
assert_kernel_only TetraStereo.OneCenter.RetainedContextReferenceSelection.retainedTerminal_sphere
assert_kernel_only TetraStereo.OneCenter.RetainedContextReferenceSelection.retainedStep_sphere
assert_kernel_only TetraStereo.OneCenter.RetainedContextReferenceSelection.retainedTree_rankedLabels_getD
assert_kernel_only TetraStereo.OneCenter.RetainedContextReferenceSelection.retainedTree_root_rankedLabels_getD
assert_kernel_only TetraStereo.OneCenter.RetainedContextReferenceSelection.retainedTree_node_minimal
assert_kernel_only TetraStereo.OneCenter.RetainedContextReferenceSelection.retainedTree_firstChiralRank_minimal
assert_kernel_only TetraStereo.OneCenter.RetainedContextReferenceSelection.nodeLabel
assert_kernel_only TetraStereo.OneCenter.RetainedContextReferenceSelection.nodeLabel_chiral_iff
assert_kernel_only TetraStereo.OneCenter.RetainedContextReferenceSelection.eligible_iff_nodeLabel_chiral
assert_kernel_only TetraStereo.OneCenter.RetainedContextReferenceSelection.hdense_tree
assert_kernel_only TetraStereo.OneCenter.RetainedContextReferenceSelection.sphereEntry_root_eq
assert_kernel_only TetraStereo.OneCenter.RetainedContextReferenceSelection.mem_sphereOf_root_iff
assert_kernel_only TetraStereo.OneCenter.RetainedContextReferenceSelection.sphereOf_root_eq_map
assert_kernel_only TetraStereo.OneCenter.RetainedContextReferenceSelection.retainedSphere_ringDuplicate_label_none
assert_kernel_only TetraStereo.OneCenter.RetainedContextReferenceSelection.not_Eligible_ringDuplicate_tree
assert_kernel_only TetraStereo.OneCenter.RetainedContextReferenceSelection.rankAddress_min_of_firstChiralRank
assert_kernel_only TetraStereo.OneCenter.RetainedContextReferenceSelection.exists_node_of_firstChiralRank
assert_kernel_only TetraStereo.OneCenter.RetainedContextReferenceSelection.firstChiralRank_eq_none_iff_root
assert_kernel_only TetraStereo.OneCenter.RetainedContextReferenceSelection.retainedTree_references_eq_retainedReferenceSelection
assert_kernel_only TetraStereo.OneCenter.RetainedContextReferenceSelection.retainedGeneratedContextTree_references_eq_selection
assert_kernel_only TetraStereo.OneCenter.RetainedContextReferenceSelection.exists_retainedGeneratedContextTree_references_eq_selection
