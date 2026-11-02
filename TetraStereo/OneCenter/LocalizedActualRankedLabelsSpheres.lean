import TetraStereo.OneCenter.LocalizedActualRankKeyBridge
import TetraStereo.OneCenter.DeclarativeCIPDepthChains
import TetraStereo.OneCenter.LocalizedRankedPopulationMerge
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# The rank-addressed label spheres of the actual Rule-4a key

For an original-root arm at stage `.rule4a` satisfying `ArmReadback`, sphere `d` of the actual
key's `rankedLabels` is exactly the slot-ordered list of the arm's nodes `d` levels below, each
addressed by its independent rank list and carrying the molecular reading
(`arm_rankedLabels_getD`).  Two ingredients: a tie of two actual sibling keys is equality of the
independent pair keys (`compare_eq_iff_pairKey_eq`), so the runtime's adjacent-tie ranks are
`headRanks` of the slot keys (`rankedChildren_snd_eq_headRanks`), hence `rankIndexIn`
(`DeclarativeCIPDepthChains.headRanks_eq_map_rankIndexIn`).
-/

namespace TetraStereo.OneCenter
namespace Rule4aTableBridge

open LocalizedCumulativeDecoratedTree
open CertifiedLocalizedCIPInput
open CertifiedLocalizedCIPInput.OriginalRootArm
open OfficialSparseCanonicalVectorComparison
open DeclarativeCIP

noncomputable section
open scoped Classical

/-! ## Ties are pair-key equalities -/

theorem compare_eq_iff_pairKey_eq {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
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
    (rep4J : Represents4a W D (rule4aComponent input.moleculeGraph graph evidence W D childJ) keyJ) :
    input.compareLocalizedRerootCumulativeRule45Keys keyI keyJ = Ordering.eq ↔
      pairKey input.moleculeGraph graph evidence W D childI =
        pairKey input.moleculeGraph graph evidence W D childJ := by
  have wfI := wellFormedRuleMajorKey_of_tableMatch matchI realizesI
  have wfJ := wellFormedRuleMajorKey_of_tableMatch matchJ realizesJ
  have hconst : OfficialRuleMajorKey.compare keyI.constitutional keyJ.constitutional =
      compare (ruleKey input.moleculeGraph graph W D childI)
        (ruleKey input.moleculeGraph graph W D childJ) :=
    compare_eq_compare_vector wfI wfJ
      (ruleKey_vectorWellShaped input.moleculeGraph graph W D childI)
      (ruleKey_vectorWellShaped input.moleculeGraph graph W D childJ) repI repJ
  unfold pairKey
  unfold compareLocalizedRerootCumulativeRule45Keys
  simp only [compareLex, Ordering.byKey]
  constructor
  · intro h
    rcases hc : OfficialRuleMajorKey.compare keyI.constitutional keyJ.constitutional with _ | _ | _ <;>
      rw [hc] at h
    · cases h
    · have veq : ruleKey input.moleculeGraph graph W D childI =
          ruleKey input.moleculeGraph graph W D childJ :=
        (vectorCompare_eq_iff _ _).1 (hconst.symm.trans hc)
      have rule1aTie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
          keyI.constitutional.rule1a keyJ.constitutional.rule1a = Ordering.eq := by
        unfold OfficialRuleMajorKey.compare at hc
        exact (compareLex_eq_eq.1 hc).1
      simp only [Ordering.then] at h
      rw [compare_descriptor_eq_compare_key matchI matchJ realizesI realizesJ rule1aTie
        (ordinaryKey_stereo_wellShaped input.moleculeGraph graph evidence W D _ childI)
        (ordinaryKey_stereo_wellShaped input.moleculeGraph graph evidence W D _ childJ)
        rep4I rep4J] at h
      have seq := (stereoKeyCompare_eq_iff _ _).1 h
      exact congrArg toLex (Prod.ext veq seq)
    · cases h
  · intro h
    have hpair := congrArg ofLex h
    have veq : ruleKey input.moleculeGraph graph W D childI =
        ruleKey input.moleculeGraph graph W D childJ := congrArg Prod.fst hpair
    have seq : rule4aComponent input.moleculeGraph graph evidence W D childI =
        rule4aComponent input.moleculeGraph graph evidence W D childJ := congrArg Prod.snd hpair
    have hc : OfficialRuleMajorKey.compare keyI.constitutional keyJ.constitutional = Ordering.eq := by
      rw [hconst]; exact (vectorCompare_eq_iff _ _).2 veq
    have rule1aTie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        keyI.constitutional.rule1a keyJ.constitutional.rule1a = Ordering.eq := by
      unfold OfficialRuleMajorKey.compare at hc
      exact (compareLex_eq_eq.1 hc).1
    rw [hc]
    simp only [Ordering.then]
    rw [compare_descriptor_eq_compare_key matchI matchJ realizesI realizesJ rule1aTie
      (ordinaryKey_stereo_wellShaped input.moleculeGraph graph evidence W D _ childI)
      (ordinaryKey_stereo_wellShaped input.moleculeGraph graph evidence W D _ childJ)
      rep4I rep4J]
    exact (stereoKeyCompare_eq_iff _ _).2 seq

/-! ## The runtime's ranks -/

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
  {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
  {graph : RootedDigraph input.Atom}

/-- An actual key paired with the arm node it represents at stage `.rule4a`. -/
def Represented (evidence : StereochemicalEvidence graph) (W D : Nat)
    (key : input.LocalizedRerootCumulativeRule45Key) (node : graph.Node) : Prop :=
  ∃ tree : LocalizedCumulativeDecoratedTree input carrierFuel,
    LocalizedCumulativeTreeTableMatch .rule4a tree key ∧
      LocalizedCumulativeTreeRealizes input read tree ∧
      Represents W D (ruleKey input.moleculeGraph graph W D node) key.constitutional ∧
      Represents4a W D (rule4aComponent input.moleculeGraph graph evidence W D node) key

theorem Represented.tie_iff {evidence : StereochemicalEvidence graph} (h4a : Rule4aOnly graph evidence)
    {W D : Nat} {keyI keyJ : input.LocalizedRerootCumulativeRule45Key} {childI childJ : graph.Node}
    (hI : Represented (read := read) evidence W D keyI childI)
    (hJ : Represented (read := read) evidence W D keyJ childJ) :
    input.compareLocalizedRerootCumulativeRule45Keys keyI keyJ = Ordering.eq ↔
      ordinaryKey input.moleculeGraph graph evidence W D childI =
        ordinaryKey input.moleculeGraph graph evidence W D childJ := by
  obtain ⟨treeI, matchI, realizesI, repI, rep4I⟩ := hI
  obtain ⟨treeJ, matchJ, realizesJ, repJ, rep4J⟩ := hJ
  rw [compare_eq_iff_pairKey_eq evidence matchI matchJ realizesI realizesJ repI repJ rep4I rep4J,
    ordinaryKey_eq_iff_pairKey input.moleculeGraph graph evidence h4a W D]

theorem rankedChildTail_snd_eq_tailRanks {evidence : StereochemicalEvidence graph}
    (h4a : Rule4aOnly graph evidence) {W D : Nat} :
    ∀ (keys : List input.LocalizedRerootCumulativeRule45Key) (nodes : List graph.Node),
      List.Forall₂ (Represented (read := read) evidence W D) keys nodes →
      ∀ (prev : input.LocalizedRerootCumulativeRule45Key) (prevNode : graph.Node),
        Represented (read := read) evidence W D prev prevNode → ∀ rank : Nat,
          (input.localizedRerootRankedChildTail prev rank keys).map (·.2) =
            tailRanks (ordinaryKey input.moleculeGraph graph evidence W D prevNode) rank
              (nodes.map (ordinaryKey input.moleculeGraph graph evidence W D))
  | [], [], _, _, _, _, _ => rfl
  | [], _ :: _, h, _, _, _, _ => nomatch h
  | _ :: _, [], h, _, _, _, _ => nomatch h
  | key :: keys, node :: nodes, h, prev, prevNode, hprev, rank => by
      obtain ⟨hkey, hrest⟩ := List.forall₂_cons.1 h
      have tie := Represented.tie_iff h4a hkey hprev
      simp only [List.map_cons, localizedRerootRankedChildTail, tailRanks]
      by_cases hc : input.compareLocalizedRerootCumulativeRule45Keys key prev = Ordering.eq
      · rw [if_pos hc, if_pos (tie.1 hc)]
        rw [rankedChildTail_snd_eq_tailRanks h4a keys nodes hrest key node hkey rank]
      · rw [if_neg hc, if_neg fun h => hc (tie.2 h)]
        rw [rankedChildTail_snd_eq_tailRanks h4a keys nodes hrest key node hkey (rank + 1)]

theorem rankedChildren_snd_eq_headRanks {evidence : StereochemicalEvidence graph}
    (h4a : Rule4aOnly graph evidence) {W D : Nat}
    (keys : List input.LocalizedRerootCumulativeRule45Key) (nodes : List graph.Node)
    (h : List.Forall₂ (Represented (read := read) evidence W D) keys nodes) :
    (input.localizedRerootRankedChildren keys).map (·.2) =
      headRanks (nodes.map (ordinaryKey input.moleculeGraph graph evidence W D)) := by
  cases h with
  | nil => rfl
  | cons hkey hrest =>
      simp only [localizedRerootRankedChildren, List.map_cons, headRanks]
      rw [rankedChildTail_snd_eq_tailRanks h4a _ _ hrest _ _ hkey 0]

theorem rankedChildTail_fst (prev : input.LocalizedRerootCumulativeRule45Key) (rank : Nat) :
    ∀ keys : List input.LocalizedRerootCumulativeRule45Key,
      (input.localizedRerootRankedChildTail prev rank keys).map (·.1) = keys
  | [] => rfl
  | key :: keys => by
      simp only [localizedRerootRankedChildTail, List.map_cons]
      rw [rankedChildTail_fst _ _ keys]

theorem rankedChildren_fst (keys : List input.LocalizedRerootCumulativeRule45Key) :
    (input.localizedRerootRankedChildren keys).map (·.1) = keys := by
  cases keys with
  | nil => rfl
  | cons key keys =>
      simp only [localizedRerootRankedChildren, List.map_cons]
      rw [rankedChildTail_fst]

/-! ## Spheres -/

private theorem flatMap_eq_of_forall₂ {α β γ : Type*} {f : α → List γ} {g : β → List γ} :
    ∀ {l : List α} {m : List β}, List.Forall₂ (fun a b => f a = g b) l m → l.flatMap f = m.flatMap g
  | [], [], _ => rfl
  | _ :: _, _ :: _, List.Forall₂.cons h hrest => by
      simp only [List.flatMap_cons]
      rw [h, flatMap_eq_of_forall₂ hrest]

variable {center : input.TetrahedralCenter} {index : Fin 4}

section Spheres

variable {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
    Option LocalizedAuxiliaryLabel}
  (arm : input.OriginalRootArm center index .rule4a read)
  (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
  (unit : DetectedOccurrence input.moleculeGraph)

/-- The sphere entry contributed by a chain below `start`: its rank list and the reading at its
endpoint. -/
def sphereEntry (start : (armGraph arm).Node) (chain : List (armGraph arm).Node) :
    OfficialSparseEntry (Option LocalizedAuxiliaryLabel) :=
  (chainRankAddress input.moleculeGraph (armGraph arm)
      (rankEvidence input.moleculeGraph descriptorMap unit (armGraph arm))
      (armGraph arm).width (armGraph arm).height chain,
    (occurrenceReading input.moleculeGraph descriptorMap unit (armGraph arm)
      (chain.getLastD start)).toLocalizedLabel)

/-- The independent sphere `d` below `start`: slot-ordered chains, each as a sphere entry. -/
def sphereOf (d : Nat) (start : (armGraph arm).Node) :
    List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)) :=
  (depthChains (armGraph arm) (toOfficialSourceTree arm.tree).declarativeAddressing d start).map
    (sphereEntry arm descriptorMap unit start)

theorem sphereOf_zero (hyp : ArmReadback arm descriptorMap unit) (start : (armGraph arm).Node)
    (actual : LocalizedCumulativeDecoratedTree input (input.certified.input.molecule.atomCount + 1))
    (lookup : arm.tree.decoratedSubtreeAt? start.1 = some actual) :
    sphereOf arm descriptorMap unit 0 start = [([], actual.label)] := by
  rw [hyp.label start actual lookup]
  rfl

theorem sphereOf_succ_of_no_children (start : (armGraph arm).Node)
    (hnone : (armGraph arm).childList start = []) (d : Nat) :
    sphereOf arm descriptorMap unit (d + 1) start = [] := by
  simp [sphereOf, depthChains, hnone, slotList]

theorem terminal_sphere (hyp : ArmReadback arm descriptorMap unit) (node : (armGraph arm).Node)
    (cursor : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1))
    (lookup : arm.tree.decoratedSubtreeAt? node.1 =
      some (localizedRootTree input cursor (read cursor) [])) (d : Nat) :
    (localizedCumulativeRule45TerminalKey input .rule4a cursor (read cursor)).rankedLabels.getD d [] =
      sphereOf arm descriptorMap unit d node := by
  have hdense := denseAt_of_lookup arm node _ lookup
  have hchild : (armGraph arm).childList node = [] := by
    have hperm := slotList_perm hdense
    have hnil : slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
        (localizedRootTree input cursor (read cursor) []).children.length = [] := by
      simp [slotList, localizedRootTree]
    rw [hnil] at hperm
    exact hperm.symm.eq_nil
  cases d with
  | zero =>
      rw [sphereOf_zero arm descriptorMap unit hyp node _ lookup]
      rfl
  | succ d =>
      rw [sphereOf_succ_of_no_children arm descriptorMap unit node hchild]
      rfl

theorem node_sphere (hyp : ArmReadback arm descriptorMap unit) {fuel : Nat}
    (ih : ∀ (node : (armGraph arm).Node)
      (dsub : LocalizedCumulativeDecoratedTree input (input.certified.input.molecule.atomCount + 1))
      (key : input.LocalizedRerootCumulativeRule45Key),
      LocalizedActualRecursiveSortTrace input .rule4a read fuel dsub key →
        arm.tree.decoratedSubtreeAt? node.1 = some dsub → ∀ d,
          key.rankedLabels.getD d [] = sphereOf arm descriptorMap unit d node)
    (node : (armGraph arm).Node)
    (cursor : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1))
    (sortedKeys : List input.LocalizedRerootCumulativeRule45Key)
    (sortedTrees : List (LocalizedCumulativeDecoratedTree input
      (input.certified.input.molecule.atomCount + 1)))
    (childrenTraced : LocalizedActualRecursiveSortTraceList input .rule4a read fuel sortedKeys
      sortedTrees)
    (lookup : arm.tree.decoratedSubtreeAt? node.1 =
      some (localizedRootTree input cursor (read cursor) sortedTrees)) (d : Nat) :
    (localizedCumulativeRule45StepKey input .rule4a cursor (read cursor)
        sortedKeys).rankedLabels.getD d [] =
      sphereOf arm descriptorMap unit d node := by
  cases d with
  | zero =>
      rw [sphereOf_zero arm descriptorMap unit hyp node _ lookup]
      rfl
  | succ d =>
  -- abbreviations
  have hcanon := arm_ordinaryCanonicalAddressing_rankEvidence arm hyp
  have hdenseAll : Dense (toOfficialSourceTree arm.tree).declarativeAddressing := hcanon.1
  have hkeysorted := hcanon.2
  have hdense := denseAt_of_lookup arm node _ lookup
  have childrenEq : (localizedRootTree input cursor (read cursor) sortedTrees).children =
      sortedTrees := rfl
  rw [childrenEq] at hdense
  have paired := LocalizedActualRecursiveSortTraceList.to_forall₂ childrenTraced
  have lengthEq : sortedKeys.length = sortedTrees.length := List.Forall₂.length_eq paired
  have hcount : ((armGraph arm).childList node).length = sortedTrees.length := by
    have := (slotList_perm hdense).length_eq
    simp only [slotList, List.length_map, List.length_range] at this
    exact this.symm
  set slots := slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
    sortedTrees.length with hslots
  have slotLength : slots.length = sortedTrees.length := by simp [hslots, slotList]
  have childAt : ∀ i (hi : i < sortedTrees.length), ∃ child : (armGraph arm).Node,
      slots[i]? = some child ∧ child.1 = node.1 ++ [i] ∧
        arm.tree.decoratedSubtreeAt? child.1 = some (sortedTrees[i]'hi) := by
    intro i hi
    obtain ⟨child, slotSome, addr⟩ := slotList_getD_of_lt (addressing :=
      (toOfficialSourceTree arm.tree).declarativeAddressing) (parent := node)
      (count := sortedTrees.length) hdense hi
    have addrFlat : child.1 = node.1 ++ [i] := by
      rw [(toOfficialSourceTree arm.tree).declarativeAddressing_address,
        (toOfficialSourceTree arm.tree).declarativeAddressing_address] at addr
      exact addr
    refine ⟨child, slotSome, addrFlat, ?_⟩
    rw [addrFlat, decoratedSubtreeAt?_append arm.tree node.1 [i], lookup]
    simp [childrenEq, decoratedSubtreeAt?, List.getElem?_eq_getElem hi]
  have traceAt : ∀ i (hi : i < sortedTrees.length),
      LocalizedActualRecursiveSortTrace input .rule4a read fuel (sortedTrees[i]'hi)
        (sortedKeys[i]'(by omega)) :=
    fun i hi => List.Forall₂.get (i := i) paired (by omega) hi
  have represented : ∀ i (hi : i < sortedTrees.length) (child : (armGraph arm).Node),
      arm.tree.decoratedSubtreeAt? child.1 = some (sortedTrees[i]'hi) →
        Represented (read := read)
          (rankEvidence input.moleculeGraph descriptorMap unit (armGraph arm))
          (armGraph arm).width (armGraph arm).height (sortedKeys[i]'(by omega)) child :=
    fun i hi child hl =>
      ⟨sortedTrees[i]'hi, (LocalizedActualRecursiveSortTrace.fullMatch_of_trace (traceAt i hi)).tableMatch,
        LocalizedActualRecursiveSortTrace.realizes_of_trace (traceAt i hi),
        (arm_node_bridge arm le_rfl le_rfl child (sortedTrees[i]'hi) (sortedKeys[i]'(by omega))
          (traceAt i hi) hl).2,
        (arm_node_bridge4a arm hyp le_rfl le_rfl child (sortedTrees[i]'hi) (sortedKeys[i]'(by omega))
          (traceAt i hi) hl).2⟩
  have slotGet : ∀ i (hi : i < sortedTrees.length), ∃ child, slots[i]'(by rw [slotLength]; exact hi) = child ∧
      arm.tree.decoratedSubtreeAt? child.1 = some (sortedTrees[i]'hi) := by
    intro i hi
    obtain ⟨child, slotSome, _, hl⟩ := childAt i hi
    exact ⟨child, Option.some.inj ((List.getElem?_eq_getElem _).symm.trans slotSome), hl⟩
  have pairedSlots : List.Forall₂ (Represented (read := read)
      (rankEvidence input.moleculeGraph descriptorMap unit (armGraph arm))
      (armGraph arm).width (armGraph arm).height) sortedKeys slots := by
    rw [List.forall₂_iff_get]
    refine ⟨by rw [lengthEq, slotLength], ?_⟩
    intro i hi hi'
    simp only [List.get_eq_getElem]
    obtain ⟨child, hget, hl⟩ := slotGet i (by omega)
    rw [hget]
    exact represented i (by omega) child hl
  -- the slot keys are the ranked ordinary keys
  have oksEq : rankedOrdinaryKeys input.moleculeGraph (armGraph arm)
      (rankEvidence input.moleculeGraph descriptorMap unit (armGraph arm))
      (armGraph arm).width (armGraph arm).height node =
      slots.map (ordinaryKey input.moleculeGraph (armGraph arm)
        (rankEvidence input.moleculeGraph descriptorMap unit (armGraph arm))
        (armGraph arm).width (armGraph arm).height) := by
    unfold rankedOrdinaryKeys
    exact sortDesc_childKeys_eq_slotOrder _ hdense hkeysorted
  have oksSorted : (slots.map (ordinaryKey input.moleculeGraph (armGraph arm)
      (rankEvidence input.moleculeGraph descriptorMap unit (armGraph arm))
      (armGraph arm).width (armGraph arm).height)).Pairwise fun x y => y ≤ x := by
    rw [← oksEq]
    exact Certificate.CanonicalSphereKey.sortDesc_pairwise _
  have hranks := rankedChildren_snd_eq_headRanks hyp.rule4aOnly sortedKeys slots pairedSlots
  rw [headRanks_eq_map_rankIndexIn _ oksSorted] at hranks
  have hfst := rankedChildren_fst (input := input) sortedKeys
  -- unfold both sides
  show ([[([], read cursor)]] ++ input.mergeLocalizedRerootRankedLabelChildren sortedKeys).getD
      (d + 1) [] = _
  rw [List.cons_append, List.nil_append, List.getD_cons_succ,
    getD_mergeLocalizedRerootRankedLabelChildren]
  unfold sphereOf
  simp only [depthChains, hcount, List.map_flatMap]
  rw [← hslots]
  apply flatMap_eq_of_forall₂
  rw [List.forall₂_iff_get]
  have rankedLength : (input.localizedRerootRankedChildren sortedKeys).length = sortedKeys.length := by
    have := congrArg List.length hfst
    simpa using this
  refine ⟨by rw [rankedLength, lengthEq, slotLength], ?_⟩
  intro i hi hi'
  simp only [List.get_eq_getElem]
  have hi1 : i < sortedTrees.length := by rw [slotLength] at hi'; exact hi'
  obtain ⟨child, hget, hl⟩ := slotGet i hi1
  rw [hget]
  -- the pair at slot `i`
  have hp1 : (input.localizedRerootRankedChildren sortedKeys)[i].1 = sortedKeys[i]'(by omega) := by
    have := congrArg (fun l => l[i]?) hfst
    simp only [List.getElem?_map, List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem (show i < sortedKeys.length by omega), Option.map_some,
      Option.some.injEq] at this
    exact this
  have hp2 : (input.localizedRerootRankedChildren sortedKeys)[i].2 =
      rankIndexIn (rankedOrdinaryKeys input.moleculeGraph (armGraph arm)
        (rankEvidence input.moleculeGraph descriptorMap unit (armGraph arm))
        (armGraph arm).width (armGraph arm).height node)
        (ordinaryKey input.moleculeGraph (armGraph arm)
          (rankEvidence input.moleculeGraph descriptorMap unit (armGraph arm))
          (armGraph arm).width (armGraph arm).height child) := by
    have := congrArg (fun l => l[i]?) hranks
    simp only [List.getElem?_map, List.getElem?_eq_getElem hi,
      List.getElem?_eq_getElem hi', Option.map_some, Option.some.injEq] at this
    rw [this, hget, oksEq]
  rw [hp2, hp1, ih child (sortedTrees[i]'hi1) (sortedKeys[i]'(by omega)) (traceAt i hi1) hl d]
  unfold sphereOf
  simp only [OfficialRuleMajorKey.prefixLayer, List.map_map]
  apply List.map_congr_left
  intro chain hchain
  obtain ⟨hne, hhead, _⟩ := mem_depthChains_shape (armGraph arm) _ d child chain hchain
  cases chain with
  | nil => exact absurd rfl hne
  | cons a rest =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst hhead
      simp only [Function.comp, sphereEntry, chainRankAddress, List.getLastD_cons]

end Spheres

/-- **Sphere `d` of the actual Rule-4a key** lists the arm's nodes `d` levels below the node, in
slot order, addressed by their independent rank lists and carrying the molecular readings. -/
theorem arm_rankedLabels_getD
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm : input.OriginalRootArm center index .rule4a read)
    {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
    {unit : DetectedOccurrence input.moleculeGraph}
    (hyp : ArmReadback arm descriptorMap unit) :
    ∀ {fuel : Nat} (node : (armGraph arm).Node)
      (dsub : LocalizedCumulativeDecoratedTree input (input.certified.input.molecule.atomCount + 1))
      (key : input.LocalizedRerootCumulativeRule45Key),
      LocalizedActualRecursiveSortTrace input .rule4a read fuel dsub key →
        arm.tree.decoratedSubtreeAt? node.1 = some dsub → ∀ d : Nat,
          key.rankedLabels.getD d [] = sphereOf arm descriptorMap unit d node := by
  intro fuel
  induction fuel with
  | zero =>
      intro node dsub key trace lookup d
      cases trace with
      | terminal _fuel cursor _children _childrenComputed _terminalChildren _fullMatch _realizes =>
          exact terminal_sphere arm descriptorMap unit hyp node cursor lookup d
  | succ fuel ih =>
      intro node dsub key trace lookup d
      rcases LocalizedActualRecursiveSortTrace.structure_of_trace trace with
        ⟨cursor, _children, dsubEq, keyEq, _childrenEq, _childrenComputed, _terminalChildren⟩ |
        ⟨cursor, _children, _childKeys, sortedKeys, sortedTrees, dsubEq, keyEq, _childrenEq,
          _childrenComputed, _nonempty, _childKeysComputed, _sortedEq, _constitutionalDescending,
          childrenTraced⟩
      · subst dsub; subst key
        exact terminal_sphere arm descriptorMap unit hyp node cursor lookup d
      · subst dsub; subst key
        exact node_sphere arm descriptorMap unit hyp ih node cursor sortedKeys sortedTrees
          childrenTraced lookup d

/-- The arm root's spheres. -/
theorem arm_root_rankedLabels_getD
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (arm : input.OriginalRootArm center index .rule4a read)
    {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
    {unit : DetectedOccurrence input.moleculeGraph}
    (hyp : ArmReadback arm descriptorMap unit) (d : Nat) :
    arm.key.rankedLabels.getD d [] = sphereOf arm descriptorMap unit d (armGraph arm).root :=
  arm_rankedLabels_getD arm hyp (armGraph arm).root arm.tree arm.key arm.trace rfl d

end
end Rule4aTableBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.compare_eq_iff_pairKey_eq
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.rankedChildren_snd_eq_headRanks
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.arm_rankedLabels_getD
