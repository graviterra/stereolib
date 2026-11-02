import TetraStereo.OneCenter.LocalizedContextFirstChiralMinimality
import TetraStereo.OneCenter.DeclarativeCIPContextualReferenceSelection
import TetraStereo.OneCenter.LocalizedActualReferenceSelectionBridge
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! Exact nearest-eligible/maximal-rank/majority reference selection for the actual reader
at an arbitrary retained-root auxiliary context. -/
namespace TetraStereo.OneCenter
namespace ContextReferenceBridge
open CertifiedLocalizedCIPInput LocalizedCumulativeDecoratedTree DeclarativeCIP Rule4aTableBridge
noncomputable section
open scoped Classical
variable {input : CertifiedLocalizedCIPInput}

section Tree
variable (tree : LocalizedCumulativeDecoratedTree input (input.certified.input.molecule.atomCount + 1))
  (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
  (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
  (unit : DetectedOccurrence input.moleculeGraph)
/-- The reading-based label of a node. -/
abbrev nodeLabel (node : (ruleMajorTreeGraph tree).Node) : Option LocalizedAuxiliaryLabel :=
  (occurrenceReading input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) node).toLocalizedLabel

theorem nodeLabel_chiral_iff (hyp : ContextTreeRankReadback tree descriptorMap unit) (node : (ruleMajorTreeGraph tree).Node)
    (rs : RS) :
    nodeLabel tree descriptorMap unit node = some (.chiral rs) ↔
      eligibleSense input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) node = some (senseOf rs) := by
  show _ ↔ readingSense (occurrenceReading input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) node) =
    some (senseOf rs)
  exact toLocalizedLabel_chiral_iff _ (hyp.tetrahedral node) rs

theorem eligible_iff_nodeLabel_chiral (hyp : ContextTreeRankReadback tree descriptorMap unit)
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
theorem sphereEntry_root_eq (_hyp : ContextTreeRankReadback tree descriptorMap unit) (d : Nat)
    (chain : List (ruleMajorTreeGraph tree).Node) (hchain : chain ∈ depthChains (ruleMajorTreeGraph tree) (toOfficialSourceTree tree).declarativeAddressing d (ruleMajorTreeGraph tree).root) :
    contextualSphereEntry tree observe descriptorMap unit (ruleMajorTreeGraph tree).root chain =
      (observedReferenceRankAddress input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) observe (chain.getLastD (ruleMajorTreeGraph tree).root),
        nodeLabel tree descriptorMap unit (chain.getLastD (ruleMajorTreeGraph tree).root)) := by
  unfold contextualSphereEntry observedReferenceRankAddress
  rw [observedRankAddress_eq_observedChainRankAddress_of_mem (ruleMajorTreeGraph tree) observe (rankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)) (toOfficialSourceTree tree).declarativeAddressing (hdense_tree tree) (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height d chain hchain]

theorem mem_sphereOf_root_iff (hyp : ContextTreeRankReadback tree descriptorMap unit) (d : Nat) (e : LabelEntry) :
    e ∈ contextualSphereOf tree observe descriptorMap unit d (ruleMajorTreeGraph tree).root ↔
      ∃ node : (ruleMajorTreeGraph tree).Node, (ruleMajorTreeGraph tree).depth node = d ∧
        e = (observedReferenceRankAddress input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) observe node,
          nodeLabel tree descriptorMap unit node) := by
  unfold contextualSphereOf
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
theorem sphereOf_root_eq_map (hyp : ContextTreeRankReadback tree descriptorMap unit) (d : Nat) :
    contextualSphereOf tree observe descriptorMap unit d (ruleMajorTreeGraph tree).root =
      (depthNodes (ruleMajorTreeGraph tree) (toOfficialSourceTree tree).declarativeAddressing d (ruleMajorTreeGraph tree).root).map fun node =>
        (observedReferenceRankAddress input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) observe node,
          nodeLabel tree descriptorMap unit node) := by
  unfold contextualSphereOf
  rw [← depthChains_getLastD (ruleMajorTreeGraph tree) (toOfficialSourceTree tree).declarativeAddressing d (ruleMajorTreeGraph tree).root, List.map_map]
  apply List.map_congr_left
  intro chain hchain
  exact sphereEntry_root_eq tree observe descriptorMap unit hyp d chain hchain


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
  (hyp : ContextTreeRankReadback tree descriptorMap unit)
include hyp

include observations trace in
/-- Node form of the first-chiral minimality at the root spheres. -/
theorem rankAddress_min_of_firstChiralRank (d : Nat) (first : List Nat)
    (hfirst : firstChiralRank (contextualSphereOf tree observe descriptorMap unit d (ruleMajorTreeGraph tree).root) = some first)
    (node : (ruleMajorTreeGraph tree).Node) (hdepth : (ruleMajorTreeGraph tree).depth node = d)
    (helig : Eligible input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) node) :
    first ≤ observedReferenceRankAddress input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) observe node := by
  obtain ⟨rs, hrs⟩ := (eligible_iff_nodeLabel_chiral tree descriptorMap unit hyp node).1 helig
  have hmem : (observedReferenceRankAddress input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) observe node,
      nodeLabel tree descriptorMap unit node) ∈ contextualSphereOf tree observe descriptorMap unit d (ruleMajorTreeGraph tree).root :=
    (mem_sphereOf_root_iff tree observe descriptorMap unit hyp d _).2 ⟨node, hdepth, rfl⟩
  have := contextTree_firstChiralRank_minimal descriptorMap target tree observe observations trace hyp (ruleMajorTreeGraph tree).root tree key
    trace rfl d first (by rw [contextTree_root_rankedLabels_getD tree observe observations descriptorMap unit hyp trace]; exact hfirst) _
    (by rw [contextTree_root_rankedLabels_getD tree observe observations descriptorMap unit hyp trace]; exact hmem) ⟨rs, hrs⟩
  exact this

theorem exists_node_of_firstChiralRank (d : Nat) (first : List Nat)
    (hfirst : firstChiralRank (contextualSphereOf tree observe descriptorMap unit d (ruleMajorTreeGraph tree).root) = some first) :
    ∃ node : (ruleMajorTreeGraph tree).Node, (ruleMajorTreeGraph tree).depth node = d ∧
      Eligible input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) node ∧
        observedReferenceRankAddress input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) observe node = first := by
  obtain ⟨e, he, haddr, rs, hrs⟩ := firstChiralRank_mem _ first hfirst
  obtain ⟨node, hdepth, rfl⟩ := (mem_sphereOf_root_iff tree observe descriptorMap unit hyp d e).1 he
  exact ⟨node, hdepth, (eligible_iff_nodeLabel_chiral tree descriptorMap unit hyp node).2 ⟨rs, hrs⟩,
    haddr⟩

theorem firstChiralRank_eq_none_iff_root (d : Nat) :
    firstChiralRank (contextualSphereOf tree observe descriptorMap unit d (ruleMajorTreeGraph tree).root) = none ↔
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

include observations trace in
/-- **The actual reference population is the independent selection.** -/
theorem tree_references_eq_observedReferenceSelection :
    localizedRule4bReferencesFromRankedLabels key.rankedLabels =
      toReferenceList (observedReferenceSelection input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) observe) := by
  set layers := key.rankedLabels with hlayersDef
  set n := layers.length with hn
  have hS : ∀ d, layers.getD d [] = contextualSphereOf tree observe descriptorMap unit d (ruleMajorTreeGraph tree).root :=
    fun d => contextTree_root_rankedLabels_getD tree observe observations descriptorMap unit hyp trace d
  have hlayers : layers = (List.range n).map fun d => contextualSphereOf tree observe descriptorMap unit d (ruleMajorTreeGraph tree).root := by
    conv_lhs => rw [list_eq_map_range_getD layers]
    exact List.map_congr_left fun d _ => hS d
  have hbeyond : ∀ d, n ≤ d → contextualSphereOf tree observe descriptorMap unit d (ruleMajorTreeGraph tree).root = [] := by
    intro d hd
    rw [← hS d, List.getD_eq_getElem?_getD, List.getElem?_eq_none hd]
    rfl
  unfold localizedRule4bReferencesFromRankedLabels
  rw [localizedFirstChiralRankPopulation_eq_findSome?, hlayers, List.findSome?_map,
    show (localizedFirstChiralRankPopulationInLayer ∘ fun d =>
        contextualSphereOf tree observe descriptorMap unit d (ruleMajorTreeGraph tree).root) =
      fun d => (firstChiralRank (contextualSphereOf tree observe descriptorMap unit d (ruleMajorTreeGraph tree).root)).map
        fun rank => localizedChiralDescriptorsAtRank rank
          (contextualSphereOf tree observe descriptorMap unit d (ruleMajorTreeGraph tree).root) from
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
    obtain ⟨a₀, ha₀⟩ : ∃ a₀, firstChiralRank (contextualSphereOf tree observe descriptorMap unit d₀ (ruleMajorTreeGraph tree).root) =
        some a₀ := by
      rcases h : firstChiralRank (contextualSphereOf tree observe descriptorMap unit d₀ (ruleMajorTreeGraph tree).root) with _ | a
      · exact absurd hd₀ ((firstChiralRank_eq_none_iff_root descriptorMap tree observe unit hyp d₀).1 h)
      · exact ⟨a, rfl⟩
    have hd₀n : d₀ < n := by
      by_contra hge
      push_neg at hge
      rw [hbeyond d₀ hge] at ha₀
      simp [firstChiralRank] at ha₀
    have hbefore : ∀ d < d₀, (firstChiralRank (contextualSphereOf tree observe descriptorMap unit d (ruleMajorTreeGraph tree).root)).map
        (fun rank => localizedChiralDescriptorsAtRank rank
          (contextualSphereOf tree observe descriptorMap unit d (ruleMajorTreeGraph tree).root)) = none := by
      intro d hd
      rw [(firstChiralRank_eq_none_iff_root descriptorMap tree observe unit hyp d).2 (hmin d hd)]
      rfl
    rw [findSome?_range_of_first _ n d₀ _ hd₀n (by rw [ha₀]; rfl) hbefore]
    simp only [Option.getD_some]
    set pop := localizedChiralDescriptorsAtRank a₀
      (contextualSphereOf tree observe descriptorMap unit d₀ (ruleMajorTreeGraph tree).root) with hpop
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
        ObservedInReferenceClass input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) observe m ↔
          Eligible input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) m ∧
            (ruleMajorTreeGraph tree).depth m = d₀ ∧
              observedReferenceRankAddress input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) observe m = a₀ := by
      intro m
      unfold ObservedInReferenceClass
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
          rw [observedReferenceRankAddress_lt_iff input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) observe
            (toOfficialSourceTree tree).declarativeAddressing (by rw [hdepth₀, hdepth])] at hlt
          exact absurd hle (not_le.2 hlt)
        · exact rankAddress_min_of_firstChiralRank descriptorMap target tree observe observations trace unit hyp d₀ a₀ ha₀ m hdepth helig
      · rintro ⟨helig, hdepth, haddr⟩
        refine ⟨⟨helig, hdepth⟩, fun o ho => ?_⟩
        obtain ⟨helig', hdepth'⟩ := (nearest_iff o).1 ho
        apply not_lt.1
        intro hlt
        rw [← observedReferenceRankAddress_lt_iff input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) observe
          (toOfficialSourceTree tree).declarativeAddressing (by rw [hdepth', hdepth])] at hlt
        have := rankAddress_min_of_firstChiralRank descriptorMap target tree observe observations trace unit hyp d₀ a₀ ha₀ o hdepth' helig'
        rw [haddr] at hlt
        exact absurd this (not_le.2 hlt)
    -- counts
    have count : ∀ rs : RS, (pop.filter fun d => d == rs).length =
        ((observedReferenceClass input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) observe).filter fun node =>
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
        mem_depthNodes_root_iff (ruleMajorTreeGraph tree) (hdense_tree tree), observedReferenceClass,
        Finset.mem_univ, true_and]
      rw [class_iff]
      constructor
      · rintro ⟨hdepth, hb⟩
        cases hc : chiralDescriptorAtRank a₀
            (observedReferenceRankAddress input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) observe m,
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
    unfold localizedRule4bReferencesFromPopulation observedReferenceSelection
    rw [if_neg (by rw [hne]; decide), if_neg (not_not.2 hex)]
    unfold observedSeniorCount observedJuniorCount
    rw [← hR, ← hS']
    dsimp only
    split_ifs <;> rfl
  · -- no eligible node: no chiral entry in any sphere
    have hnone : ∀ d, (firstChiralRank (contextualSphereOf tree observe descriptorMap unit d (ruleMajorTreeGraph tree).root)).map
        (fun rank => localizedChiralDescriptorsAtRank rank
          (contextualSphereOf tree observe descriptorMap unit d (ruleMajorTreeGraph tree).root)) = none := by
      intro d
      rw [(firstChiralRank_eq_none_iff_root descriptorMap tree observe unit hyp d).2
        (fun ⟨node, _, helig⟩ => hex ⟨node, helig⟩)]
      rfl
    rw [findSome?_range_eq_none _ n hnone]
    unfold localizedRule4bReferencesFromPopulation observedReferenceSelection
    rw [if_pos hex]
    rfl


end Assembly

/-- The actual generated reader selects exactly the independent contextual references at any
auxiliary target. The target path is unrestricted; empty and tied-multiple reference populations
are included. -/
theorem generatedContextTree_references_eq_selection
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (target : input.certified.LocalizedRerootCursor
      (input.certified.certified.input.molecule.atomCount + 1))
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.occurrence.1 = unit.1)
    (tree : LocalizedCumulativeDecoratedTree input.certified
      (input.certified.certified.input.molecule.atomCount + 1))
    {fuel : Nat} {key : input.certified.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedRuleMajorSortTrace input.certified .rule4a
      (input.certified.localizedDependencyLabel target.occurrence
        (input.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState input) target.occurrence)) fuel tree key)
    (rootChild : tree.source ∈ input.certified.executableLocalizedRerootChildren target) :
    localizedRule4bReferencesFromRankedLabels key.rankedLabels =
      toReferenceList (contextualReferenceSelection input.certified.moleculeGraph
        (LocalizedRuleMajorReference.descriptorMap input) unit (ruleMajorTreeGraph tree)) := by
  have realizes := LocalizedRuleMajorSortTrace.realizes_of_trace trace
  have hyp := ruleMajorGeneratedContextTreeRankReadback input singleBonded acyclic
    target unit targetUnit tree realizes rootChild
  have rootEq := contextTree_outerRoot_eq_unitRoot singleBonded acyclic
    target unit targetUnit tree rootChild
  have observations : ∀ rule node actual, tree.decoratedSubtreeAt? node.1 = some actual →
      contextualNodeObservation input.certified.moleculeGraph (ruleMajorTreeGraph tree)
        unit.1.root rule node = priorityValue rule (armObservation rule actual) := by
    intro rule node actual lookup
    rw [← rootEq]
    exact contextualTree_nodeObservation singleBonded acyclic tree realizes rule node actual lookup
  have trace' : LocalizedRuleMajorSortTrace input.certified .rule4a
      (input.certified.molecularReader (LocalizedRuleMajorReference.descriptorMap input)
        target.occurrence) fuel tree key := by
    rw [LocalizedRuleMajorReference.molecularReader_eq_generatedReader input singleBonded acyclic]
    exact trace
  exact tree_references_eq_observedReferenceSelection
    (LocalizedRuleMajorReference.descriptorMap input) target.occurrence tree _ observations
    trace' unit hyp

/-- Success and reference correspondence derived at the actual execution bound. Cursor validity
is derived from executable child membership, rather than required of the caller. -/
theorem exists_generatedContextTree_references_eq_selection
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (target : input.certified.LocalizedRerootCursor
      (input.certified.certified.input.molecule.atomCount + 1))
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.occurrence.1 = unit.1)
    (cursor : input.certified.LocalizedRerootCursor
      (input.certified.certified.input.molecule.atomCount + 1))
    (rootChild : cursor ∈ input.certified.executableLocalizedRerootChildren target) :
    ∃ (tree : LocalizedCumulativeDecoratedTree input.certified
        (input.certified.certified.input.molecule.atomCount + 1))
      (key : input.certified.LocalizedRerootCumulativeRule45Key),
      tree.source = cursor ∧
      input.certified.buildRuleMajorCumulativeWithReadExec? .rule4a
        (input.certified.localizedDependencyLabel target.occurrence
          (input.certified.localizedDependencyView
            (LocalizedRuleMajorReference.referenceState input) target.occurrence))
        (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1)) cursor = some key ∧
      localizedRule4bReferencesFromRankedLabels key.rankedLabels =
        toReferenceList (contextualReferenceSelection input.certified.moleculeGraph
          (LocalizedRuleMajorReference.descriptorMap input) unit (ruleMajorTreeGraph tree)) := by
  have valid := input.certified.localizedRerootChild_valid target cursor _
    (input.certified.executableLocalizedRerootChildren_declarative target) rootChild
  obtain ⟨tree, key, source, built, trace⟩ := exists_ruleMajorTrace_at_twice input.certified .rule4a
    (input.certified.localizedDependencyLabel target.occurrence
      (input.certified.localizedDependencyView
        (LocalizedRuleMajorReference.referenceState input) target.occurrence)) cursor valid
  refine ⟨tree, key, source, ?_, ?_⟩
  · rw [input.certified.buildRuleMajorCumulativeWithReadExec_eq]
    exact built
  · exact generatedContextTree_references_eq_selection input singleBonded acyclic
      target unit targetUnit tree trace (by simpa only [source] using rootChild)

end
end ContextReferenceBridge
end TetraStereo.OneCenter
assert_kernel_only TetraStereo.OneCenter.ContextReferenceBridge.tree_references_eq_observedReferenceSelection
assert_kernel_only TetraStereo.OneCenter.ContextReferenceBridge.generatedContextTree_references_eq_selection
assert_kernel_only TetraStereo.OneCenter.ContextReferenceBridge.exists_generatedContextTree_references_eq_selection
