import TetraStereo.OneCenter.LocalizedRetainedContextReferenceSelection
import TetraStereo.OneCenter.DeclarativeCIPOrdinaryCanonicalOrderLaws
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace TetraStereo.OneCenter.LocalizedMarkedRetainedSubtreeSelection

open CertifiedLocalizedCIPInput DeclarativeCIP LocalizedCumulativeDecoratedTree
open Rule4aTableBridge RetainedContextStereoReadback RetainedContextReferenceSelection
open OfficialSparseCanonicalVectorComparison
open scoped Classical
noncomputable section

section Independent
variable {Atom : Type} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom)
  (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom)

local instance : Fintype graph.Node := graph.nodeFintype

/-- Eligibility below a chosen node of the original graph; the source unit is unchanged. -/
def EligibleBelow (start node : graph.Node) : Prop :=
  Relation.ReflTransGen graph.child start node ∧
    Eligible molecule descriptorMap unit graph node

def NearestEligibleBelow (start node : graph.Node) : Prop :=
  EligibleBelow molecule descriptorMap unit graph start node ∧
    ∀ other, EligibleBelow molecule descriptorMap unit graph start other →
      graph.depth node ≤ graph.depth other

/-- The maximal full retained ancestor-key path within the nearest eligible descendants. -/
def InReferenceClassBelow (start node : graph.Node) : Prop :=
  NearestEligibleBelow molecule descriptorMap unit graph start node ∧
    ∀ other, NearestEligibleBelow molecule descriptorMap unit graph start other →
      retainedRankPath molecule descriptorMap unit graph other ≤
        retainedRankPath molecule descriptorMap unit graph node

def referenceClassBelow (start : graph.Node) : Finset graph.Node :=
  Finset.univ.filter (InReferenceClassBelow molecule descriptorMap unit graph start)

def seniorCountBelow (start : graph.Node) : Nat :=
  ((referenceClassBelow molecule descriptorMap unit graph start).filter fun node =>
    eligibleSense molecule descriptorMap unit graph node = some .senior).card

def juniorCountBelow (start : graph.Node) : Nat :=
  ((referenceClassBelow molecule descriptorMap unit graph start).filter fun node =>
    eligibleSense molecule descriptorMap unit graph node = some .junior).card

def RetainedReferenceSelectionBelow (start : graph.Node) : ReferenceSelection :=
  if ¬ ∃ node, EligibleBelow molecule descriptorMap unit graph start node then .empty
  else if juniorCountBelow molecule descriptorMap unit graph start <
      seniorCountBelow molecule descriptorMap unit graph start then .one .senior
  else if seniorCountBelow molecule descriptorMap unit graph start <
      juniorCountBelow molecule descriptorMap unit graph start then .one .junior
  else .both

@[simp] theorem eligibleBelow_root (node : graph.Node) :
    EligibleBelow molecule descriptorMap unit graph graph.root node ↔
      Eligible molecule descriptorMap unit graph node :=
  ⟨And.right, fun h => ⟨graph.reachable node, h⟩⟩

@[simp] theorem nearestEligibleBelow_root (node : graph.Node) :
    NearestEligibleBelow molecule descriptorMap unit graph graph.root node ↔
      NearestEligible molecule descriptorMap unit graph node := by
  simp only [NearestEligibleBelow, eligibleBelow_root, NearestEligible]

@[simp] theorem inReferenceClassBelow_root (node : graph.Node) :
    InReferenceClassBelow molecule descriptorMap unit graph graph.root node ↔
      RetainedInReferenceClass molecule descriptorMap unit graph node := by
  simp only [InReferenceClassBelow, nearestEligibleBelow_root, RetainedInReferenceClass]

theorem selection_root :
    RetainedReferenceSelectionBelow molecule descriptorMap unit graph graph.root =
      retainedReferenceSelection molecule descriptorMap unit graph := by
  have predicateEq : InReferenceClassBelow molecule descriptorMap unit graph graph.root =
      RetainedInReferenceClass molecule descriptorMap unit graph := by
    funext node
    exact propext (inReferenceClassBelow_root molecule descriptorMap unit graph node)
  simp only [RetainedReferenceSelectionBelow, retainedReferenceSelection,
    eligibleBelow_root, juniorCountBelow, seniorCountBelow, referenceClassBelow,
    predicateEq, retainedJuniorCount, retainedSeniorCount,
    retainedReferenceClass]

end Independent

section Chains
variable {Atom : Type} (graph : RootedDigraph Atom)
  (observe : ConstitutionalRule → graph.Node → ℤ)
  (evidence : StereochemicalEvidence graph) (W D : Nat)

/-- Rank digits concatenate when chains are spliced at their common endpoint. -/
theorem chainRank_splice (before : List graph.Node) (last : graph.Node)
    (lastEq : before.getLast? = some last) (after : List graph.Node) :
    observedChainRankAddress graph observe evidence W D (before ++ after) =
      observedChainRankAddress graph observe evidence W D before ++
        observedChainRankAddress graph observe evidence W D (last :: after) := by
  induction before with
  | nil => simp at lastEq
  | cons first rest ih =>
      cases rest with
      | nil =>
          simp only [List.getLast?_singleton, Option.some.injEq] at lastEq
          subst last
          rfl
      | cons second rest =>
          rw [List.getLast?_cons_cons] at lastEq
          simp only [List.cons_append, observedChainRankAddress]
          congr 1
          simpa only [List.cons_append] using ih lastEq

/-- The whole-arm rank address is the common ancestor prefix followed by the local rank digits.
No reference population or actual comparator result is assumed. -/
theorem rankAddress_eq_prefix_append
    (addressing : graph.Addressing) (dense : Dense addressing)
    (depth : Nat) (start : graph.Node) (chain : List graph.Node)
    (member : chain ∈ depthChains graph addressing depth start) :
    observedRankAddress graph observe evidence W D (chain.getLastD start) =
      observedRankAddress graph observe evidence W D start ++
        observedChainRankAddress graph observe evidence W D chain := by
  have pre := ancestorChain_spec_of_addressing graph addressing start
  have joined := ancestorChain_of_mem_depthChains graph dense depth start chain member pre
  have unique := ancestorChain_unique_of_addressing graph addressing
    (ancestorChain_spec_of_addressing graph addressing (chain.getLastD start)) joined
  have lastEq : (ancestorChain graph start).getLast? = some start := by
    rw [List.getLast?_eq_some_getLast (AncestorChain.ne_nil graph pre),
      AncestorChain.getLast graph pre]
  unfold observedRankAddress
  rw [unique, chainRank_splice graph observe evidence W D _ start lastEq]
  obtain ⟨nonempty, head, _⟩ := mem_depthChains_shape graph addressing depth start chain member
  cases chain with
  | nil => exact (nonempty rfl).elim
  | cons first rest =>
      simp only [List.head?_cons, Option.some.injEq] at head
      subst first
      rfl

end Chains

section Spheres
variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
  (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
  (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
  (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
  (unit : DetectedOccurrence input.moleculeGraph)

/-- The suffix of the whole-arm rank address below the selected node. -/
def relativeRankAddress (start node : (ruleMajorTreeGraph tree).Node) : List Nat :=
  (retainedReferenceRankAddress input.moleculeGraph descriptorMap unit
    (ruleMajorTreeGraph tree) observe node).drop ((ruleMajorTreeGraph tree).depth start)

theorem retainedRankAddress_length (node : (ruleMajorTreeGraph tree).Node) :
    (retainedReferenceRankAddress input.moleculeGraph descriptorMap unit
      (ruleMajorTreeGraph tree) observe node).length = (ruleMajorTreeGraph tree).depth node := by
  unfold retainedReferenceRankAddress observedRankAddress
  rw [observedChainRankAddress_length,
    AncestorChain.length _ (ancestorChain_spec_of_addressing _
      (toOfficialSourceTree tree).declarativeAddressing node)]
  change ((ruleMajorTreeGraph tree).depth node + 1) - 1 = _
  omega

theorem sphereEntry_eq_relative (depth : Nat) (start : (ruleMajorTreeGraph tree).Node)
    (chain : List (ruleMajorTreeGraph tree).Node)
    (member : chain ∈ depthChains (ruleMajorTreeGraph tree)
      (toOfficialSourceTree tree).declarativeAddressing depth start) :
    retainedSphereEntry tree observe descriptorMap unit start chain =
      (relativeRankAddress tree observe descriptorMap unit start (chain.getLastD start),
        (occurrenceReading input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)
          (chain.getLastD start)).toLocalizedLabel) := by
  have joined := rankAddress_eq_prefix_append (ruleMajorTreeGraph tree) observe
    (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree))
    (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height
    (toOfficialSourceTree tree).declarativeAddressing
    (toOfficialSourceTree tree).declarativeAddressing_dense depth start chain member
  unfold retainedSphereEntry relativeRankAddress
  apply Prod.ext
  · change _ = (observedRankAddress (ruleMajorTreeGraph tree) observe
      (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree))
      (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height
      (chain.getLastD start)).drop _
    rw [joined]
    have lengthEq := retainedRankAddress_length tree observe descriptorMap unit start
    unfold retainedReferenceRankAddress at lengthEq
    rw [← lengthEq, List.drop_left]
  · rfl

theorem sphereOf_eq_map (depth : Nat) (start : (ruleMajorTreeGraph tree).Node) :
    retainedSphereOf tree observe descriptorMap unit depth start =
      (depthNodes (ruleMajorTreeGraph tree) (toOfficialSourceTree tree).declarativeAddressing
        depth start).map fun node =>
          (relativeRankAddress tree observe descriptorMap unit start node,
            (occurrenceReading input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)
              node).toLocalizedLabel) := by
  unfold retainedSphereOf
  rw [← depthChains_getLastD (ruleMajorTreeGraph tree)
    (toOfficialSourceTree tree).declarativeAddressing depth start, List.map_map]
  apply List.map_congr_left
  intro chain member
  exact sphereEntry_eq_relative tree observe descriptorMap unit depth start chain member

theorem rankAddress_eq_prefix_relative
    (start node : (ruleMajorTreeGraph tree).Node)
    (below : Relation.ReflTransGen (ruleMajorTreeGraph tree).child start node) :
    retainedReferenceRankAddress input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph tree) observe node =
      retainedReferenceRankAddress input.moleculeGraph descriptorMap unit
          (ruleMajorTreeGraph tree) observe start ++
        relativeRankAddress tree observe descriptorMap unit start node := by
  have depthLe := depth_le_of_reflTransGen (ruleMajorTreeGraph tree) below
  have member : node ∈ depthNodes (ruleMajorTreeGraph tree)
      (toOfficialSourceTree tree).declarativeAddressing
      ((ruleMajorTreeGraph tree).depth node - (ruleMajorTreeGraph tree).depth start) start :=
    (mem_depthNodes_iff _ (toOfficialSourceTree tree).declarativeAddressing_dense _ _ _).2
      ⟨below, by
        change (ruleMajorTreeGraph tree).depth node =
          (ruleMajorTreeGraph tree).depth start +
            ((ruleMajorTreeGraph tree).depth node - (ruleMajorTreeGraph tree).depth start)
        omega⟩
  rw [← depthChains_getLastD, List.mem_map] at member
  obtain ⟨chain, member, lastEq⟩ := member
  have joined := rankAddress_eq_prefix_append (ruleMajorTreeGraph tree) observe
    (retainedRankEvidence input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree))
    (ruleMajorTreeGraph tree).width (ruleMajorTreeGraph tree).height
    (toOfficialSourceTree tree).declarativeAddressing
    (toOfficialSourceTree tree).declarativeAddressing_dense _ start chain member
  have suffixEq := congrArg Prod.fst
    (sphereEntry_eq_relative tree observe descriptorMap unit _ start chain member)
  change observedChainRankAddress _ _ _ _ _ chain = _ at suffixEq
  rw [suffixEq, lastEq] at joined
  exact joined

theorem relativeRankAddress_lt_iff
    (observeEq : ∀ rule node, observe rule node =
      retainedContextNodeObservation input.moleculeGraph (ruleMajorTreeGraph tree) unit rule node)
    (start left right : (ruleMajorTreeGraph tree).Node)
    (leftBelow : Relation.ReflTransGen (ruleMajorTreeGraph tree).child start left)
    (rightBelow : Relation.ReflTransGen (ruleMajorTreeGraph tree).child start right)
    (sameDepth : (ruleMajorTreeGraph tree).depth left = (ruleMajorTreeGraph tree).depth right) :
    relativeRankAddress tree observe descriptorMap unit start left <
        relativeRankAddress tree observe descriptorMap unit start right ↔
      retainedRankPath input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) right <
        retainedRankPath input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) left := by
  have ordered := retainedReferenceRankAddress_lt_iff input.moleculeGraph descriptorMap unit
    (ruleMajorTreeGraph tree) observe observeEq
    (toOfficialSourceTree tree).declarativeAddressing sameDepth
  rw [rankAddress_eq_prefix_relative tree observe descriptorMap unit start left leftBelow,
    rankAddress_eq_prefix_relative tree observe descriptorMap unit start right rightBelow,
    List.append_lt_append_left_iff] at ordered
  exact ordered

end Spheres


section Assembly
variable {input : CertifiedLocalizedCIPInput}
  (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
  (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
  (tree : LocalizedCumulativeDecoratedTree input (input.certified.input.molecule.atomCount + 1))
  (observe : ConstitutionalRule → (ruleMajorTreeGraph tree).Node → ℤ)
  (observations : ∀ rule node actual, tree.decoratedSubtreeAt? node.1 = some actual →
    observe rule node = priorityValue rule (armObservation rule actual))
  {treeFuel : Nat} {treeKey : input.LocalizedRerootCumulativeRule45Key}
  (treeTrace : LocalizedRuleMajorSortTrace input .rule4a
    (input.molecularReader descriptorMap target) treeFuel tree treeKey)
  (unit : DetectedOccurrence input.moleculeGraph)
  (observeEq : ∀ rule node, observe rule node =
    retainedContextNodeObservation input.moleculeGraph (ruleMajorTreeGraph tree) unit rule node)
  (hyp : RetainedContextTreeRankReadback tree descriptorMap unit)
  (start : (ruleMajorTreeGraph tree).Node)
  (actual : LocalizedCumulativeDecoratedTree input (input.certified.input.molecule.atomCount + 1))
  {fuel : Nat} {key : input.LocalizedRerootCumulativeRule45Key}
  (trace : LocalizedRuleMajorSortTrace input .rule4a
    (input.molecularReader descriptorMap target) fuel actual key)
  (lookup : tree.decoratedSubtreeAt? start.1 = some actual)

local instance : Fintype (ruleMajorTreeGraph tree).Node := (ruleMajorTreeGraph tree).nodeFintype

 theorem mem_sphere_below_iff (d : Nat) (entry : LabelEntry) :
    entry ∈ retainedSphereOf tree observe descriptorMap unit d start ↔
      ∃ node : (ruleMajorTreeGraph tree).Node,
        Relation.ReflTransGen (ruleMajorTreeGraph tree).child start node ∧
        (ruleMajorTreeGraph tree).depth node = (ruleMajorTreeGraph tree).depth start + d ∧
        entry = (relativeRankAddress tree observe descriptorMap unit start node,
          nodeLabel tree descriptorMap unit node) := by
  rw [sphereOf_eq_map, List.mem_map]
  constructor
  · rintro ⟨node, member, rfl⟩
    obtain ⟨below, depth⟩ := (mem_depthNodes_iff _
      (toOfficialSourceTree tree).declarativeAddressing_dense d start node).1 member
    exact ⟨node, below, depth, rfl⟩
  · rintro ⟨node, below, depth, rfl⟩
    exact ⟨node, (mem_depthNodes_iff _
      (toOfficialSourceTree tree).declarativeAddressing_dense d start node).2 ⟨below, depth⟩, rfl⟩

include hyp in
 theorem first_none_iff (d : Nat) :
    firstChiralRank (retainedSphereOf tree observe descriptorMap unit d start) = none ↔
      ¬ ∃ node : (ruleMajorTreeGraph tree).Node,
        (ruleMajorTreeGraph tree).depth node = (ruleMajorTreeGraph tree).depth start + d ∧
        EligibleBelow input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) start node := by
  rw [firstChiralRank_eq_none_iff]
  constructor
  · rintro absent ⟨node, depth, below, eligible⟩
    obtain ⟨rs, label⟩ := (eligible_iff_nodeLabel_chiral tree descriptorMap unit hyp node).1 eligible
    exact absent _ ((mem_sphere_below_iff descriptorMap tree observe unit start d _).2
      ⟨node, below, depth, rfl⟩) ⟨rs, label⟩
  · intro absent entry member ⟨rs, label⟩
    obtain ⟨node, below, depth, rfl⟩ :=
      (mem_sphere_below_iff descriptorMap tree observe unit start d entry).1 member
    exact absent ⟨node, depth, below,
      (eligible_iff_nodeLabel_chiral tree descriptorMap unit hyp node).2 ⟨rs, label⟩⟩

include hyp in
 theorem first_exists_node (d : Nat) (first : List Nat)
    (found : firstChiralRank (retainedSphereOf tree observe descriptorMap unit d start) = some first) :
    ∃ node : (ruleMajorTreeGraph tree).Node,
      (ruleMajorTreeGraph tree).depth node = (ruleMajorTreeGraph tree).depth start + d ∧
      EligibleBelow input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) start node ∧
      relativeRankAddress tree observe descriptorMap unit start node = first := by
  obtain ⟨entry, member, rank, rs, label⟩ := firstChiralRank_mem _ first found
  obtain ⟨node, below, depth, rfl⟩ :=
    (mem_sphere_below_iff descriptorMap tree observe unit start d entry).1 member
  exact ⟨node, depth, ⟨below,
    (eligible_iff_nodeLabel_chiral tree descriptorMap unit hyp node).2 ⟨rs, label⟩⟩, rank⟩

include observations treeTrace hyp trace lookup in
 theorem first_minimal_below (d : Nat) (first : List Nat)
    (found : firstChiralRank (retainedSphereOf tree observe descriptorMap unit d start) = some first)
    (node : (ruleMajorTreeGraph tree).Node)
    (depth : (ruleMajorTreeGraph tree).depth node = (ruleMajorTreeGraph tree).depth start + d)
    (eligible : EligibleBelow input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) start node) :
    first ≤ relativeRankAddress tree observe descriptorMap unit start node := by
  obtain ⟨rs, label⟩ := (eligible_iff_nodeLabel_chiral tree descriptorMap unit hyp node).1 eligible.2
  have member := (mem_sphere_below_iff descriptorMap tree observe unit start d _).2
    ⟨node, eligible.1, depth, rfl⟩
  have sphere := retainedTree_rankedLabels_getD tree observe observations descriptorMap unit hyp
    treeTrace start actual key trace lookup d
  exact retainedTree_firstChiralRank_minimal descriptorMap target tree observe observations
    treeTrace hyp start actual key trace lookup d first (by rw [sphere]; exact found)
    _ (by rw [sphere]; exact member) ⟨rs, label⟩

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

include observations treeTrace observeEq hyp trace lookup in
/-- Actual selection at any traced subtree equals the independent descendant population in the
original graph. The original descriptor unit, reader and full ancestor rank paths are retained. -/
theorem references_eq_selectionBelow :
    localizedRule4bReferencesFromRankedLabels key.rankedLabels =
      toReferenceList (RetainedReferenceSelectionBelow input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph tree) start) := by
  let graph := ruleMajorTreeGraph tree
  set layers := key.rankedLabels with hlayersDef
  set n := layers.length with hn
  have sphere : ∀ d, layers.getD d [] = retainedSphereOf tree observe descriptorMap unit d start :=
    fun d => retainedTree_rankedLabels_getD tree observe observations descriptorMap unit hyp
      treeTrace start actual key trace lookup d
  have layersEq : layers = (List.range n).map fun d => retainedSphereOf tree observe descriptorMap unit d start := by
    conv_lhs => rw [list_eq_map_range_getD layers]
    exact List.map_congr_left fun d _ => sphere d
  have beyond : ∀ d, n ≤ d → retainedSphereOf tree observe descriptorMap unit d start = [] := by
    intro d hd
    rw [← sphere d, List.getD_eq_getElem?_getD, List.getElem?_eq_none hd]
    rfl
  unfold localizedRule4bReferencesFromRankedLabels
  rw [localizedFirstChiralRankPopulation_eq_findSome?, layersEq, List.findSome?_map,
    show (localizedFirstChiralRankPopulationInLayer ∘ fun d =>
        retainedSphereOf tree observe descriptorMap unit d start) =
      fun d => (firstChiralRank (retainedSphereOf tree observe descriptorMap unit d start)).map
        fun rank => localizedChiralDescriptorsAtRank rank
          (retainedSphereOf tree observe descriptorMap unit d start) from
      funext fun d => localizedFirstChiralRankPopulationInLayer_eq_map_firstChiralRank _]
  by_cases hex : ∃ node : graph.Node,
      EligibleBelow input.moleculeGraph descriptorMap unit graph start node
  · have hexd : ∃ d, ∃ node : graph.Node, graph.depth node = graph.depth start + d ∧
        EligibleBelow input.moleculeGraph descriptorMap unit graph start node := by
      obtain ⟨node, eligible⟩ := hex
      have lower := depth_le_of_reflTransGen graph eligible.1
      exact ⟨graph.depth node - graph.depth start, node, by omega, eligible⟩
    set d₀ := Nat.find hexd
    have hd₀ : ∃ node : graph.Node, graph.depth node = graph.depth start + d₀ ∧
        EligibleBelow input.moleculeGraph descriptorMap unit graph start node := Nat.find_spec hexd
    have hmin : ∀ d, d < d₀ → ¬ ∃ node : graph.Node, graph.depth node = graph.depth start + d ∧
        EligibleBelow input.moleculeGraph descriptorMap unit graph start node :=
      fun d hd => Nat.find_min hexd hd
    obtain ⟨a₀, ha₀⟩ : ∃ a₀, firstChiralRank (retainedSphereOf tree observe descriptorMap unit d₀ start) =
        some a₀ := by
      cases h : firstChiralRank (retainedSphereOf tree observe descriptorMap unit d₀ start) with
      | none => exact absurd hd₀ ((first_none_iff descriptorMap tree observe unit hyp start d₀).1 h)
      | some a => exact ⟨a, rfl⟩
    have hd₀n : d₀ < n := by
      by_contra hge
      push_neg at hge
      rw [beyond d₀ hge] at ha₀
      simp [firstChiralRank] at ha₀
    have before : ∀ d < d₀, (firstChiralRank (retainedSphereOf tree observe descriptorMap unit d start)).map
        (fun rank => localizedChiralDescriptorsAtRank rank
          (retainedSphereOf tree observe descriptorMap unit d start)) = none := by
      intro d hd
      rw [(first_none_iff descriptorMap tree observe unit hyp start d).2 (hmin d hd)]
      rfl
    rw [findSome?_range_of_first _ n d₀ _ hd₀n (by rw [ha₀]; rfl) before]
    simp only [Option.getD_some]
    set pop := localizedChiralDescriptorsAtRank a₀
      (retainedSphereOf tree observe descriptorMap unit d₀ start) with hpop
    have nearest_iff : ∀ m : graph.Node,
        NearestEligibleBelow input.moleculeGraph descriptorMap unit graph start m ↔
          EligibleBelow input.moleculeGraph descriptorMap unit graph start m ∧
            graph.depth m = graph.depth start + d₀ := by
      intro m
      constructor
      · rintro ⟨eligible, minimal⟩
        obtain ⟨chosen, chosenDepth, chosenEligible⟩ := hd₀
        have upper := minimal chosen chosenEligible
        have lower := depth_le_of_reflTransGen graph eligible.1
        refine ⟨eligible, ?_⟩
        by_contra different
        have small : graph.depth m - graph.depth start < d₀ := by omega
        exact hmin _ small ⟨m, by omega, eligible⟩
      · rintro ⟨eligible, depth⟩
        refine ⟨eligible, fun other otherEligible => ?_⟩
        have lower := depth_le_of_reflTransGen graph otherEligible.1
        by_contra tooSmall
        have small : graph.depth other - graph.depth start < d₀ := by omega
        exact hmin _ small ⟨other, by omega, otherEligible⟩
    have class_iff : ∀ m : graph.Node,
        InReferenceClassBelow input.moleculeGraph descriptorMap unit graph start m ↔
          EligibleBelow input.moleculeGraph descriptorMap unit graph start m ∧
            graph.depth m = graph.depth start + d₀ ∧
              relativeRankAddress tree observe descriptorMap unit start m = a₀ := by
      intro m
      unfold InReferenceClassBelow
      rw [nearest_iff]
      constructor
      · rintro ⟨⟨eligible, depth⟩, maximal⟩
        refine ⟨eligible, depth, le_antisymm ?_ ?_⟩
        · obtain ⟨chosen, chosenDepth, chosenEligible, chosenRank⟩ :=
            first_exists_node descriptorMap tree observe unit hyp start d₀ a₀ ha₀
          have priority := maximal chosen ((nearest_iff chosen).2 ⟨chosenEligible, chosenDepth⟩)
          rw [← chosenRank]
          apply not_lt.1
          intro reversed
          have ordered := (relativeRankAddress_lt_iff tree observe descriptorMap unit observeEq
            start chosen m chosenEligible.1 eligible.1 (by exact chosenDepth.trans depth.symm)).1 reversed
          exact (not_le.2 ordered) priority
        · exact first_minimal_below descriptorMap target tree observe observations treeTrace unit hyp
            start actual trace lookup d₀ a₀ ha₀ m depth eligible
      · rintro ⟨eligible, depth, rank⟩
        refine ⟨⟨eligible, depth⟩, fun other otherNearest => ?_⟩
        obtain ⟨otherEligible, otherDepth⟩ := (nearest_iff other).1 otherNearest
        apply not_lt.1
        intro reversed
        have ordered := (relativeRankAddress_lt_iff tree observe descriptorMap unit observeEq
          start other m otherEligible.1 eligible.1 (by exact otherDepth.trans depth.symm)).2 reversed
        have minimum := first_minimal_below descriptorMap target tree observe observations treeTrace
          unit hyp start actual trace lookup d₀ a₀ ha₀ other otherDepth otherEligible
        rw [rank] at ordered
        exact (not_le.2 ordered) minimum
    have count : ∀ rs : RS, (pop.filter fun d => d == rs).length =
        ((referenceClassBelow input.moleculeGraph descriptorMap unit graph start).filter fun node =>
          eligibleSense input.moleculeGraph descriptorMap unit graph node = some (senseOf rs)).card := by
      intro rs
      rw [hpop, localizedChiralDescriptorsAtRank_eq_filterMap, sphereOf_eq_map,
        List.filterMap_map, length_filter_filterMap]
      simp only [Function.comp_def]
      have nodup := depthNodes_nodup graph (toOfficialSourceTree tree).declarativeAddressing
        (toOfficialSourceTree tree).declarativeAddressing_dense d₀ start
      have card : ∀ P : graph.Node → Bool,
          ((depthNodes graph (toOfficialSourceTree tree).declarativeAddressing d₀ start).filter P).length =
          ((depthNodes graph (toOfficialSourceTree tree).declarativeAddressing d₀ start).filter P).toFinset.card :=
        fun P => (List.toFinset_card_of_nodup (nodup.filter P)).symm
      rw [card, List.toFinset_filter]
      congr 1
      ext m
      simp only [Finset.mem_filter, List.mem_toFinset,
        mem_depthNodes_iff graph (toOfficialSourceTree tree).declarativeAddressing_dense,
        referenceClassBelow, Finset.mem_univ, true_and]
      rw [class_iff]
      constructor
      · rintro ⟨⟨below, depth⟩, accepted⟩
        cases extracted : chiralDescriptorAtRank a₀
            (relativeRankAddress tree observe descriptorMap unit start m,
              nodeLabel tree descriptorMap unit m) with
        | none => rw [extracted] at accepted; simp at accepted
        | some d =>
            rw [extracted] at accepted
            simp only [Option.map_some, Option.getD_some, beq_iff_eq] at accepted
            subst accepted
            obtain ⟨rank, label⟩ := (chiralDescriptorAtRank_eq_some_iff _ _ _).1 extracted
            have sense := (nodeLabel_chiral_iff tree descriptorMap unit hyp m d).1 label
            refine ⟨⟨⟨below, ?_⟩, depth, rank⟩, sense⟩
            unfold Eligible
            rw [sense]
            rfl
      · rintro ⟨⟨eligible, depth, rank⟩, sense⟩
        refine ⟨⟨eligible.1, depth⟩, ?_⟩
        have label := (nodeLabel_chiral_iff tree descriptorMap unit hyp m rs).2 sense
        rw [(chiralDescriptorAtRank_eq_some_iff a₀ _ rs).2 ⟨rank, label⟩]
        simp
    have hR := count .R
    have hS := count .S
    simp only [senseOf] at hR hS
    have nonempty : pop.isEmpty = false := by
      obtain ⟨entry, member, rank, rs, label⟩ := firstChiralRank_mem _ a₀ ha₀
      rw [List.isEmpty_eq_false_iff_exists_mem]
      refine ⟨rs, ?_⟩
      rw [hpop, localizedChiralDescriptorsAtRank_eq_filterMap, List.mem_filterMap]
      exact ⟨entry, member, (chiralDescriptorAtRank_eq_some_iff _ _ _).2 ⟨rank, label⟩⟩
    unfold localizedRule4bReferencesFromPopulation RetainedReferenceSelectionBelow
    rw [if_neg (by rw [nonempty]; decide), if_neg (not_not.2 hex)]
    unfold seniorCountBelow juniorCountBelow
    rw [← hR, ← hS]
    dsimp only
    split_ifs <;> rfl
  · have noneBefore : ∀ d, (firstChiralRank (retainedSphereOf tree observe descriptorMap unit d start)).map
        (fun rank => localizedChiralDescriptorsAtRank rank
          (retainedSphereOf tree observe descriptorMap unit d start)) = none := by
      intro d
      rw [(first_none_iff descriptorMap tree observe unit hyp start d).2
        (fun ⟨node, _, eligible⟩ => hex ⟨node, eligible⟩)]
      rfl
    rw [findSome?_range_eq_none _ n noneBefore]
    unfold localizedRule4bReferencesFromPopulation RetainedReferenceSelectionBelow
    rw [if_pos hex]
    rfl


end Assembly

/-- The actual molecular original-arm endpoint. The original target's reader is used at every
subtree; observation and rank-readback facts are derived from the realized arm. Rings are allowed.
No population, reference-selection equality or generated-label meaning is assumed. -/
theorem molecular_references_eq_selectionBelow
    {input : CertifiedLocalizedCIPInput}
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (tetrahedralMap : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (target : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1))
    (unit : DetectedOccurrence input.moleculeGraph)
    (targetUnit : input.molecularFrameUnit target.occurrence.1 = unit.1)
    (tree : LocalizedCumulativeDecoratedTree input (input.certified.input.molecule.atomCount + 1))
    {treeFuel : Nat} {treeKey : input.LocalizedRerootCumulativeRule45Key}
    (treeTrace : LocalizedRuleMajorSortTrace input .rule4a
      (input.molecularReader descriptorMap target.occurrence) treeFuel tree treeKey)
    (rootChild : tree.source ∈ input.executableLocalizedRerootChildren target)
    (start : (ruleMajorTreeGraph tree).Node)
    (actual : LocalizedCumulativeDecoratedTree input (input.certified.input.molecule.atomCount + 1))
    {fuel : Nat} {key : input.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedRuleMajorSortTrace input .rule4a
      (input.molecularReader descriptorMap target.occurrence) fuel actual key)
    (lookup : tree.decoratedSubtreeAt? start.1 = some actual) :
    localizedRule4bReferencesFromRankedLabels key.rankedLabels =
      toReferenceList (RetainedReferenceSelectionBelow input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph tree) start) := by
  have realizes := LocalizedRuleMajorSortTrace.realizes_of_trace treeTrace
  have readback := retainedContextTreeRankReadback_of_molecularReader descriptorMap tetrahedralMap
    singleBonded target unit targetUnit tree realizes rootChild
  exact references_eq_selectionBelow descriptorMap target.occurrence tree
    (retainedContextNodeObservation input.moleculeGraph (ruleMajorTreeGraph tree) unit)
    (fun rule node subtree found =>
      RetainedRule4aCanonicalBridge.retainedDecoratedObservation_eq_arm singleBonded target unit
        targetUnit tree realizes rootChild rule node subtree found)
    treeTrace unit (fun _ _ => rfl) readback start actual trace lookup

end
end TetraStereo.OneCenter.LocalizedMarkedRetainedSubtreeSelection

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedSubtreeSelection.selection_root
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedSubtreeSelection.chainRank_splice
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedSubtreeSelection.rankAddress_eq_prefix_append
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedSubtreeSelection.retainedRankAddress_length
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedSubtreeSelection.sphereEntry_eq_relative
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedSubtreeSelection.sphereOf_eq_map

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedSubtreeSelection.rankAddress_eq_prefix_relative
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedSubtreeSelection.relativeRankAddress_lt_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedSubtreeSelection.references_eq_selectionBelow

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedSubtreeSelection.molecular_references_eq_selectionBelow
