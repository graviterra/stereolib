import TetraStereo.OneCenter.DeclarativeCIPRankAddress
import TetraStereo.OneCenter.DeclarativeCIPObservedCanonicalOrder
import TetraStereo.OneCenter.DeclarativeCIPObservedStereoPath
import TetraStereo.OneCenter.DeclarativeCIPObservedOrdinaryKey
import TetraStereo.OneCenter.DeclarativeCIPDepthChains
import TetraStereo.OneCenter.DeclarativeCIPContextualReferenceSelection
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace TetraStereo.OneCenter.DeclarativeCIP

noncomputable section
open scoped Classical

open Certificate.CanonicalSphereKey
  (sortDesc_eq_of_perm sortDesc_of_pairwise key_eq_iff_pathObservation
    vector_eq_iff_pathObservation)

section ObservedRankAddress

variable {Atom : Type}
  (graph : RootedDigraph Atom)
  (observe : ConstitutionalRule → graph.Node → ℤ)
  (evidence : StereochemicalEvidence graph)

local instance observedRankAddressNodeFintype : Fintype graph.Node := graph.nodeFintype

local instance observedOrdinaryDescTotal (W D : ℕ) :
    Std.Total (KeyDesc (ordinaryKeyWithObservations graph observe evidence W D)) :=
  ⟨fun a b => le_total
    (ordinaryKeyWithObservations graph observe evidence W D b)
    (ordinaryKeyWithObservations graph observe evidence W D a)⟩

local instance observedOrdinaryDescTrans (W D : ℕ) :
    IsTrans graph.Node (KeyDesc (ordinaryKeyWithObservations graph observe evidence W D)) :=
  ⟨fun _ _ _ h₁ h₂ => le_trans h₂ h₁⟩

private theorem exists_observedOrdinaryRanked (W D : ℕ) (node : graph.Node) :
    ∃ ranked : List graph.Node, ranked.Perm (graph.childList node) ∧
      (ranked.map (ordinaryKeyWithObservations graph observe evidence W D)).Pairwise
        fun x y => y ≤ x :=
  ⟨(graph.childList node).insertionSort
      (KeyDesc (ordinaryKeyWithObservations graph observe evidence W D)),
    List.perm_insertionSort _ _, by
      rw [List.pairwise_map]
      exact List.pairwise_insertionSort
        (KeyDesc (ordinaryKeyWithObservations graph observe evidence W D)) _⟩

private theorem rankedOrdinaryKeysWithObservations_eq_map (W D : ℕ) (node : graph.Node)
    {ranked : List graph.Node} (permutation : ranked.Perm (graph.childList node))
    (sorted : (ranked.map (ordinaryKeyWithObservations graph observe evidence W D)).Pairwise
      fun x y => y ≤ x) :
    rankedOrdinaryKeysWithObservations graph observe evidence W D node =
      ranked.map (ordinaryKeyWithObservations graph observe evidence W D) := by
  unfold rankedOrdinaryKeysWithObservations
  rw [sortDesc_eq_of_perm (permutation.symm.map
    (ordinaryKeyWithObservations graph observe evidence W D))]
  exact sortDesc_of_pairwise sorted

private theorem ordinaryKeyWithObservations_stereo_eq (W D : ℕ) (node : graph.Node) :
    (ofLex (ordinaryKeyWithObservations graph observe evidence W D node)).2 =
      [(ofLex (ordinaryKeyWithObservations graph observe evidence W D node)).2.getD 0 [],
       (ofLex (ordinaryKeyWithObservations graph observe evidence W D node)).2.getD 1 [],
       (ofLex (ordinaryKeyWithObservations graph observe evidence W D node)).2.getD 2 [],
       (ofLex (ordinaryKeyWithObservations graph observe evidence W D node)).2.getD 3 [],
       (ofLex (ordinaryKeyWithObservations graph observe evidence W D node)).2.getD 4 []] := by
  rw [ordinaryKeyWithObservations_eq]
  rfl

/-- The stereochemical path key and Rule-1a path key have the same occupied layout even when
their node labels differ. This is the shape fact needed to read all five stereo columns at a
child from the parent's ordinary key. -/
theorem observedStereoNodePathObservation_eq_bot_iff (W D : ℕ)
    (rule : StereochemicalRule) :
    ∀ (path : List ℕ) (node : graph.Node),
      observedStereoNodePathObservation graph observe evidence W D rule node path = ⊥ ↔
        nodePathObservationWithObservations graph observe W D 0 node path = ⊥ := by
  intro path
  induction path with
  | nil =>
      intro node
      rw [observedStereoNodePathObservation_nil,
        nodePathObservationWithObservations_nil graph observe (r := 0) (by omega) node]
      simp
  | cons digit path ih =>
      intro node
      obtain ⟨ranked, permutation, sorted⟩ :=
        exists_observedOrdinaryRanked graph observe evidence W D node
      have ruleSorted :
          (ranked.map (ruleKeyWithObservations graph W D observe)).Pairwise
            fun x y => y ≤ x := by
        rw [List.pairwise_map] at sorted ⊢
        exact sorted.imp fun h => by
          simpa only [ordinaryKeyWithObservations_fst] using fst_le_of_le h
      rw [observedStereoNodePathObservation_cons graph observe evidence W D rule node
          permutation sorted digit path,
        nodePathObservationWithObservations_cons graph observe (by omega) node
          permutation ruleSorted digit path]
      by_cases guard : digit < W ∧ path.length < D
      · rw [if_pos guard, if_pos guard]
        cases ranked[digit]? with
        | none => simp
        | some child =>
            simp only [Option.map_some, Option.getD_some]
            exact ih child
      · rw [if_neg guard, if_neg guard]
        simp

private theorem nodePathObservationWithObservations_eq_bot_of_childDepth
    {W D r : ℕ} (ruleIndexLt : r < 3) {parent child : graph.Node}
    (edge : graph.child parent child) (heightBound : graph.height ≤ D)
    {path : List ℕ} (pathDepth : D ≤ path.length) :
    nodePathObservationWithObservations graph observe W D r child path = ⊥ := by
  by_contra observed
  have depthBound := depth_add_length_le_of_nodePathObservationWithObservations
    graph observe ruleIndexLt path child observed
  have childDepth := graph.child_depth edge
  omega

/-- Equality of observed ordinary keys determines the sorted child-key lists, with the same
width and depth bounds used to interpret the complete key. -/
theorem rankedOrdinaryKeysWithObservations_eq_of_ordinaryKeyWithObservations_eq
    (W D : ℕ) (widthBound : graph.width ≤ W) (heightBound : graph.height ≤ D)
    {p q : graph.Node}
    (keyEq : ordinaryKeyWithObservations graph observe evidence W D p =
      ordinaryKeyWithObservations graph observe evidence W D q) :
    rankedOrdinaryKeysWithObservations graph observe evidence W D p =
      rankedOrdinaryKeysWithObservations graph observe evidence W D q := by
  obtain ⟨rankedP, permutationP, sortedP⟩ :=
    exists_observedOrdinaryRanked graph observe evidence W D p
  obtain ⟨rankedQ, permutationQ, sortedQ⟩ :=
    exists_observedOrdinaryRanked graph observe evidence W D q
  rw [rankedOrdinaryKeysWithObservations_eq_map graph observe evidence W D p
      permutationP sortedP,
    rankedOrdinaryKeysWithObservations_eq_map graph observe evidence W D q
      permutationQ sortedQ]
  have ruleKeyEq : ruleKeyWithObservations graph W D observe p =
      ruleKeyWithObservations graph W D observe q := by
    have firstEq := congrArg (fun key : OrdinaryKey => (ofLex key).1) keyEq
    simpa only [ordinaryKeyWithObservations_fst] using firstEq
  have ruleObservations : ∀ r path,
      nodePathObservationWithObservations graph observe W D r p path =
        nodePathObservationWithObservations graph observe W D r q path := by
    intro r path
    unfold nodePathObservationWithObservations
    rw [ruleKeyEq]
  have stereoObservations : ∀ rule path,
      observedStereoNodePathObservation graph observe evidence W D rule p path =
        observedStereoNodePathObservation graph observe evidence W D rule q path := by
    intro rule path
    unfold observedStereoNodePathObservation
    rw [keyEq]
  have sortedRuleP :
      (rankedP.map (ruleKeyWithObservations graph W D observe)).Pairwise fun x y => y ≤ x := by
    rw [List.pairwise_map] at sortedP ⊢
    exact sortedP.imp fun h => by
      simpa only [ordinaryKeyWithObservations_fst] using fst_le_of_le h
  have sortedRuleQ :
      (rankedQ.map (ruleKeyWithObservations graph W D observe)).Pairwise fun x y => y ≤ x := by
    rw [List.pairwise_map] at sortedQ ⊢
    exact sortedQ.imp fun h => by
      simpa only [ordinaryKeyWithObservations_fst] using fst_le_of_le h
  have childCountP : (graph.childList p).length ≤ graph.width := by
    simpa only [RootedDigraph.width] using (graph.childList_nodup p).length_le_card
  have childCountQ : (graph.childList q).length ≤ graph.width := by
    simpa only [RootedDigraph.width] using (graph.childList_nodup q).length_le_card
  have lengthP : rankedP.length ≤ W :=
    (permutationP.length_eq.trans_le childCountP).trans widthBound
  have lengthQ : rankedQ.length ≤ W :=
    (permutationQ.length_eq.trans_le childCountQ).trans widthBound
  have childDepthPos : ∀ (parent : graph.Node) (ranked : List graph.Node),
      ranked.Perm (graph.childList parent) → ∀ i, i < ranked.length → 0 < D := by
    intro parent ranked permutation i hi
    have edge := (graph.mem_childList).1 (permutation.subset (List.getElem_mem hi))
    have childDepth := graph.child_depth edge
    have childBound := graph.depth_le_height ranked[i]
    omega
  have observationCons : ∀ (parent : graph.Node) (ranked : List graph.Node),
      ranked.Perm (graph.childList parent) →
      (ranked.map (ruleKeyWithObservations graph W D observe)).Pairwise
        (fun x y => y ≤ x) →
      ∀ (i : ℕ) (path : List ℕ), i < W → path.length < D →
        nodePathObservationWithObservations graph observe W D 0 parent (i :: path) =
          ((ranked[i]?).map fun child =>
            nodePathObservationWithObservations graph observe W D 0 child path).getD ⊥ := by
    intro parent ranked permutation sorted i path hi hpath
    rw [nodePathObservationWithObservations_cons graph observe (by omega) parent
      permutation sorted i path, if_pos ⟨hi, hpath⟩]
  have lengthLe : ∀ (a b : graph.Node) (ra rb : List graph.Node),
      ra.Perm (graph.childList a) → rb.Perm (graph.childList b) →
      (ra.map (ordinaryKeyWithObservations graph observe evidence W D)).Pairwise
        (fun x y => y ≤ x) →
      (rb.map (ordinaryKeyWithObservations graph observe evidence W D)).Pairwise
        (fun x y => y ≤ x) →
      ra.length ≤ W →
      (∀ path, nodePathObservationWithObservations graph observe W D 0 a path =
        nodePathObservationWithObservations graph observe W D 0 b path) →
      ra.length ≤ rb.length := by
    intro a b ra rb permA permB sortedA sortedB boundA observations
    by_contra notLe
    have indexBound : rb.length < ra.length := by omega
    have indexLtW : rb.length < W := Nat.lt_of_lt_of_le indexBound boundA
    have positiveD := childDepthPos a ra permA rb.length indexBound
    have sortedRuleA :
        (ra.map (ruleKeyWithObservations graph W D observe)).Pairwise
          (fun x y => y ≤ x) := by
      rw [List.pairwise_map] at sortedA ⊢
      exact sortedA.imp fun h => by
        simpa only [ordinaryKeyWithObservations_fst] using fst_le_of_le h
    have sortedRuleB :
        (rb.map (ruleKeyWithObservations graph W D observe)).Pairwise
          (fun x y => y ≤ x) := by
      rw [List.pairwise_map] at sortedB ⊢
      exact sortedB.imp fun h => by
        simpa only [ordinaryKeyWithObservations_fst] using fst_le_of_le h
    have atDifferentChild := observations [rb.length]
    rw [observationCons a ra permA sortedRuleA rb.length [] indexLtW positiveD,
      observationCons b rb permB sortedRuleB rb.length [] indexLtW positiveD] at atDifferentChild
    rw [List.getElem?_eq_getElem indexBound,
      List.getElem?_eq_none_iff.2 le_rfl] at atDifferentChild
    simp only [Option.map_some, Option.getD_some, Option.map_none, Option.getD_none] at atDifferentChild
    rw [nodePathObservationWithObservations_nil graph observe (r := 0) (by omega)] at atDifferentChild
    exact WithBot.coe_ne_bot atDifferentChild
  have lengthsEq : rankedP.length = rankedQ.length :=
    le_antisymm
      (lengthLe p q rankedP rankedQ permutationP permutationQ sortedP sortedQ lengthP
        (ruleObservations 0))
      (lengthLe q p rankedQ rankedP permutationQ permutationP sortedQ sortedP lengthQ
        fun path => (ruleObservations 0 path).symm)
  apply List.ext_getElem (by simp [lengthsEq])
  intro i hi hi'
  simp only [List.getElem_map]
  rw [List.length_map] at hi hi'
  have edgeP := (graph.mem_childList).1 (permutationP.subset (List.getElem_mem hi))
  have edgeQ := (graph.mem_childList).1 (permutationQ.subset (List.getElem_mem hi'))
  have indexLt : i < W := by omega
  have ruleObservationsAtChildren : ∀ r, r < 3 → ∀ path,
      nodePathObservationWithObservations graph observe W D r rankedP[i] path =
        nodePathObservationWithObservations graph observe W D r rankedQ[i] path := by
    intro r rLt path
    by_cases pathLt : path.length < D
    · have observedP := nodePathObservationWithObservations_cons graph observe rLt p
        permutationP sortedRuleP i path
      have observedQ := nodePathObservationWithObservations_cons graph observe rLt q
        permutationQ sortedRuleQ i path
      rw [if_pos ⟨indexLt, pathLt⟩, List.getElem?_eq_getElem hi] at observedP
      rw [if_pos ⟨indexLt, pathLt⟩, List.getElem?_eq_getElem hi'] at observedQ
      simp only [Option.map_some, Option.getD_some] at observedP observedQ
      rw [← observedP, ← observedQ, ruleObservations]
    · have outOfRange := le_of_not_gt pathLt
      rw [nodePathObservationWithObservations_eq_bot_of_childDepth graph observe rLt
          edgeP heightBound outOfRange,
        nodePathObservationWithObservations_eq_bot_of_childDepth graph observe rLt
          edgeQ heightBound outOfRange]
  have stereoObservationsAtChildren : ∀ rule path,
      observedStereoNodePathObservation graph observe evidence W D rule rankedP[i] path =
        observedStereoNodePathObservation graph observe evidence W D rule rankedQ[i] path := by
    intro rule path
    by_cases pathLt : path.length < D
    · have observedP := observedStereoNodePathObservation_cons graph observe evidence W D
        rule p permutationP sortedP i path
      have observedQ := observedStereoNodePathObservation_cons graph observe evidence W D
        rule q permutationQ sortedQ i path
      rw [if_pos ⟨indexLt, pathLt⟩, List.getElem?_eq_getElem hi] at observedP
      rw [if_pos ⟨indexLt, pathLt⟩, List.getElem?_eq_getElem hi'] at observedQ
      simp only [Option.map_some, Option.getD_some] at observedP observedQ
      rw [← observedP, ← observedQ, stereoObservations]
    · have outOfRange := le_of_not_gt pathLt
      rw [(observedStereoNodePathObservation_eq_bot_iff graph observe evidence W D rule path
            rankedP[i]).2
            (nodePathObservationWithObservations_eq_bot_of_childDepth graph observe (by omega)
              edgeP heightBound outOfRange),
        (observedStereoNodePathObservation_eq_bot_iff graph observe evidence W D rule path
            rankedQ[i]).2
            (nodePathObservationWithObservations_eq_bot_of_childDepth graph observe (by omega)
              edgeQ heightBound outOfRange)]
  have ruleKeyEqAtChildren : ruleKeyWithObservations graph W D observe rankedP[i] =
      ruleKeyWithObservations graph W D observe rankedQ[i] := by
    exact (vector_eq_iff_pathObservation
      (ruleKeyWithObservations_vectorWellShaped graph observe W D rankedP[i])
      (ruleKeyWithObservations_vectorWellShaped graph observe W D rankedQ[i])).2
      (fun r rLt path => ruleObservationsAtChildren r rLt path)
  have stereoKeyEqAtChildren : ∀ rule,
      (ofLex (ordinaryKeyWithObservations graph observe evidence W D rankedP[i])).2.getD
          (stereoIndex rule) [] =
        (ofLex (ordinaryKeyWithObservations graph observe evidence W D rankedQ[i])).2.getD
          (stereoIndex rule) [] := by
    intro rule
    exact (key_eq_iff_pathObservation
      (ordinaryKeyWithObservations_stereo_wellShaped graph observe evidence W D rule rankedP[i])
      (ordinaryKeyWithObservations_stereo_wellShaped graph observe evidence W D rule rankedQ[i])).2
      (stereoObservationsAtChildren rule)
  have stereoVectorEqAtChildren :
      (ofLex (ordinaryKeyWithObservations graph observe evidence W D rankedP[i])).2 =
        (ofLex (ordinaryKeyWithObservations graph observe evidence W D rankedQ[i])).2 := by
    rw [ordinaryKeyWithObservations_stereo_eq graph observe evidence W D rankedP[i],
      ordinaryKeyWithObservations_stereo_eq graph observe evidence W D rankedQ[i]]
    simp only [List.cons.injEq, and_true]
    exact ⟨stereoKeyEqAtChildren .rule3DoubleBondGeometry,
      stereoKeyEqAtChildren .rule4aStereogenicUnitKind,
      stereoKeyEqAtChildren .rule4bLikeUnlikeDescriptorPairs,
      stereoKeyEqAtChildren .rule4cPseudoasymmetricDescriptor,
      stereoKeyEqAtChildren .rule5EnantiomorphicDescriptor⟩
  rw [← toLex_ofLex (ordinaryKeyWithObservations graph observe evidence W D rankedP[i]),
    ← toLex_ofLex (ordinaryKeyWithObservations graph observe evidence W D rankedQ[i])]
  congr 1
  refine Prod.ext ?_ ?_
  · simpa only [ordinaryKeyWithObservations_fst] using ruleKeyEqAtChildren
  · exact stereoVectorEqAtChildren

/-- The next rank digit agrees whenever parent keys and selected child keys agree. This combines
the child-list reconstruction above with the generic `rankIndexIn` definition. -/
theorem rankIndexInWithObservations_eq_of_parent_and_child_key_eq
    (W D : ℕ) (widthBound : graph.width ≤ W) (heightBound : graph.height ≤ D)
    {parentL parentR childL childR : graph.Node}
    (parentKeyEq : ordinaryKeyWithObservations graph observe evidence W D parentL =
      ordinaryKeyWithObservations graph observe evidence W D parentR)
    (childKeyEq : ordinaryKeyWithObservations graph observe evidence W D childL =
      ordinaryKeyWithObservations graph observe evidence W D childR) :
    rankIndexIn (rankedOrdinaryKeysWithObservations graph observe evidence W D parentL)
        (ordinaryKeyWithObservations graph observe evidence W D childL) =
      rankIndexIn (rankedOrdinaryKeysWithObservations graph observe evidence W D parentR)
        (ordinaryKeyWithObservations graph observe evidence W D childR) := by
  rw [rankedOrdinaryKeysWithObservations_eq_of_ordinaryKeyWithObservations_eq
      graph observe evidence W D widthBound heightBound parentKeyEq,
    childKeyEq]

/-- Rank-address sequence of a node chain under the observed ordinary key. -/
def observedChainRankAddress (W D : ℕ) : List graph.Node → List ℕ
  | [] => []
  | [_] => []
  | parent :: child :: rest =>
      rankIndexIn (rankedOrdinaryKeysWithObservations graph observe evidence W D parent)
        (ordinaryKeyWithObservations graph observe evidence W D child) ::
        observedChainRankAddress W D (child :: rest)

/-- Appending a final node appends its sibling rank digit. -/
theorem observedChainRankAddress_append (W D : ℕ) :
    ∀ (chain : List graph.Node) (nonempty : chain ≠ []) (node : graph.Node),
      observedChainRankAddress graph observe evidence W D (chain ++ [node]) =
        observedChainRankAddress graph observe evidence W D chain ++
          [rankIndexIn
            (rankedOrdinaryKeysWithObservations graph observe evidence W D
              (chain.getLast nonempty))
            (ordinaryKeyWithObservations graph observe evidence W D node)]
  | [], nonempty, _ => absurd rfl nonempty
  | [_], _, _ => rfl
  | parent :: child :: rest, _, node => by
      simp only [List.cons_append, observedChainRankAddress, List.getLast_cons_cons]
      rw [show child :: (rest ++ [node]) = (child :: rest) ++ [node] from rfl,
        observedChainRankAddress_append W D (child :: rest) (List.cons_ne_nil child rest) node]

theorem AncestorChain.observedChainRankAddress_step (W D : ℕ)
    {parent child : graph.Node} {chain : List graph.Node}
    (_edge : graph.child parent child) (ancestorChain : AncestorChain graph parent chain) :
    observedChainRankAddress graph observe evidence W D (chain ++ [child]) =
      observedChainRankAddress graph observe evidence W D chain ++
        [rankIndexIn (rankedOrdinaryKeysWithObservations graph observe evidence W D parent)
          (ordinaryKeyWithObservations graph observe evidence W D child)] := by
  rw [observedChainRankAddress_append graph observe evidence W D chain
    (AncestorChain.ne_nil graph ancestorChain) child, AncestorChain.getLast graph ancestorChain]

theorem observedOrdinaryKey_mem_rankedOrdinaryKeys (W D : ℕ)
    {parent child : graph.Node} (edge : graph.child parent child) :
    ordinaryKeyWithObservations graph observe evidence W D child ∈
      rankedOrdinaryKeysWithObservations graph observe evidence W D parent := by
  unfold rankedOrdinaryKeysWithObservations
  rw [(Certificate.CanonicalSphereKey.sortDesc_perm _).mem_iff]
  exact List.mem_map_of_mem ((graph.mem_childList).2 edge)

theorem observedChainRankAddress_length (W D : ℕ) :
    ∀ chain : List graph.Node,
      (observedChainRankAddress graph observe evidence W D chain).length = chain.length - 1
  | [] => rfl
  | [_] => rfl
  | _ :: child :: rest => by
      simp [observedChainRankAddress, observedChainRankAddress_length W D (child :: rest)]

/-- Equal-length ancestor chains compare by the reverse lexicographic order of their observed
ordinary-key paths. Equality of rank-address chains is exactly equality of those key paths. -/
theorem observedChainRankAddress_order (W D : ℕ)
    (widthBound : graph.width ≤ W) (heightBound : graph.height ≤ D) :
    ∀ {n : graph.Node} {chainN : List graph.Node}, AncestorChain graph n chainN →
      ∀ {m : graph.Node} {chainM : List graph.Node}, AncestorChain graph m chainM →
        chainN.length = chainM.length →
        (List.Lex (· < ·)
          (observedChainRankAddress graph observe evidence W D chainN)
          (observedChainRankAddress graph observe evidence W D chainM) ↔
          List.Lex (· < ·)
            (chainM.map (ordinaryKeyWithObservations graph observe evidence W D))
            (chainN.map (ordinaryKeyWithObservations graph observe evidence W D))) ∧
        (observedChainRankAddress graph observe evidence W D chainN =
            observedChainRankAddress graph observe evidence W D chainM ↔
          chainN.map (ordinaryKeyWithObservations graph observe evidence W D) =
            chainM.map (ordinaryKeyWithObservations graph observe evidence W D)) := by
  intro n chainN ancestorN
  induction ancestorN with
  | root =>
      intro m chainM ancestorM equalLength
      cases ancestorM with
      | root =>
          refine ⟨⟨(fun h => nomatch h), fun h => ?_⟩, ⟨fun _ => rfl, fun _ => rfl⟩⟩
          cases h with
          | rel h => exact absurd h (lt_irrefl _)
          | cons h => cases h
      | step _ parentChain =>
          exfalso
          have chainLength := AncestorChain.length graph parentChain
          simp only [List.length_cons, List.length_append, List.length_nil] at equalLength
          omega
  | step edge parentChain ih =>
      intro m chainM ancestorM equalLength
      rename_i parent node chain
      cases ancestorM with
      | root =>
          exfalso
          have chainLength := AncestorChain.length graph parentChain
          simp only [List.length_cons, List.length_append, List.length_nil] at equalLength
          omega
      | step edge' parentChain' =>
          rename_i parent' chain'
          have prefixLength : chain.length = chain'.length := by simpa using equalLength
          obtain ⟨prefixLt, prefixEq⟩ := ih parentChain' prefixLength
          rw [AncestorChain.observedChainRankAddress_step graph observe evidence W D edge parentChain,
            AncestorChain.observedChainRankAddress_step graph observe evidence W D edge' parentChain',
            List.map_append, List.map_append, List.map_singleton, List.map_singleton]
          have rankAddressLength :
              (observedChainRankAddress graph observe evidence W D chain).length =
                (observedChainRankAddress graph observe evidence W D chain').length := by
            rw [observedChainRankAddress_length, observedChainRankAddress_length, prefixLength]
          have observedPathLength :
              (chain.map (ordinaryKeyWithObservations graph observe evidence W D)).length =
                (chain'.map (ordinaryKeyWithObservations graph observe evidence W D)).length := by
            simpa using prefixLength
          rw [lex_append_singleton_iff _ _ rankAddressLength,
            lex_append_singleton_iff _ _ observedPathLength.symm,
            append_singleton_eq_iff _ _ rankAddressLength,
            append_singleton_eq_iff _ _ observedPathLength]
          have parentKeyListsEq :
              chain.map (ordinaryKeyWithObservations graph observe evidence W D) =
                chain'.map (ordinaryKeyWithObservations graph observe evidence W D) →
              rankedOrdinaryKeysWithObservations graph observe evidence W D parent =
                rankedOrdinaryKeysWithObservations graph observe evidence W D parent' := by
            intro pathEq
            have lastEq := congrArg List.getLast? pathEq
            rw [List.getLast?_map, List.getLast?_map,
              List.getLast?_eq_some_getLast (AncestorChain.ne_nil graph parentChain),
              List.getLast?_eq_some_getLast (AncestorChain.ne_nil graph parentChain'),
              AncestorChain.getLast graph parentChain,
              AncestorChain.getLast graph parentChain'] at lastEq
            simp only [Option.map_some, Option.some.injEq] at lastEq
            exact rankedOrdinaryKeysWithObservations_eq_of_ordinaryKeyWithObservations_eq
              graph observe evidence W D widthBound heightBound lastEq
          have memberNode := observedOrdinaryKey_mem_rankedOrdinaryKeys
            graph observe evidence W D edge
          have memberNode' := observedOrdinaryKey_mem_rankedOrdinaryKeys
            graph observe evidence W D edge'
          constructor
          · constructor
            · rintro (less | ⟨prefixEq', rankLess⟩)
              · exact Or.inl (prefixLt.1 less)
              · have keyListsEq := parentKeyListsEq (prefixEq.1 prefixEq')
                rw [keyListsEq] at rankLess
                exact Or.inr ⟨(prefixEq.1 prefixEq').symm,
                  (rankIndexIn_lt_iff (keyListsEq ▸ memberNode) memberNode').1 rankLess⟩
            · rintro (less | ⟨prefixEq', keyLess⟩)
              · exact Or.inl (prefixLt.2 less)
              · have keyListsEq := parentKeyListsEq prefixEq'.symm
                refine Or.inr ⟨prefixEq.2 prefixEq'.symm, ?_⟩
                rw [keyListsEq]
                exact (rankIndexIn_lt_iff (keyListsEq ▸ memberNode) memberNode').2 keyLess
          · constructor
            · rintro ⟨prefixEq', rankEq⟩
              have keyListsEq := parentKeyListsEq (prefixEq.1 prefixEq')
              rw [keyListsEq] at rankEq
              exact ⟨prefixEq.1 prefixEq',
                (rankIndexIn_eq_iff (keyListsEq ▸ memberNode) memberNode').1 rankEq⟩
            · rintro ⟨prefixEq', childKeyEq⟩
              have keyListsEq := parentKeyListsEq prefixEq'
              refine ⟨prefixEq.2 prefixEq', ?_⟩
              rw [keyListsEq, childKeyEq]

/-- Independent ordinary rank address of a graph node under the supplied observation context. -/
def observedRankAddress (W D : ℕ) (node : graph.Node) : List ℕ :=
  observedChainRankAddress graph observe evidence W D (ancestorChain graph node)

/-- For equal-depth nodes, rank-address order reverses observed ordinary-key path order. -/
theorem observedRankAddress_lt_iff (addressing : graph.Addressing) (W D : ℕ)
    (widthBound : graph.width ≤ W) (heightBound : graph.height ≤ D)
    {n m : graph.Node} (sameDepth : graph.depth n = graph.depth m) :
    observedRankAddress graph observe evidence W D n <
        observedRankAddress graph observe evidence W D m ↔
      (ancestorChain graph m).map (ordinaryKeyWithObservations graph observe evidence W D) <
        (ancestorChain graph n).map (ordinaryKeyWithObservations graph observe evidence W D) := by
  have ancestorN := ancestorChain_spec_of_addressing graph addressing n
  have ancestorM := ancestorChain_spec_of_addressing graph addressing m
  have sameLength : (ancestorChain graph n).length = (ancestorChain graph m).length := by
    rw [AncestorChain.length graph ancestorN, AncestorChain.length graph ancestorM, sameDepth]
  exact (observedChainRankAddress_order graph observe evidence W D widthBound heightBound
    ancestorN ancestorM sameLength).1

/-- For equal-depth nodes, rank-address equality is equality of observed ordinary-key paths. -/
theorem observedRankAddress_eq_iff (addressing : graph.Addressing) (W D : ℕ)
    (widthBound : graph.width ≤ W) (heightBound : graph.height ≤ D)
    {n m : graph.Node} (sameDepth : graph.depth n = graph.depth m) :
    observedRankAddress graph observe evidence W D n =
        observedRankAddress graph observe evidence W D m ↔
      (ancestorChain graph n).map (ordinaryKeyWithObservations graph observe evidence W D) =
        (ancestorChain graph m).map (ordinaryKeyWithObservations graph observe evidence W D) := by
  have ancestorN := ancestorChain_spec_of_addressing graph addressing n
  have ancestorM := ancestorChain_spec_of_addressing graph addressing m
  have sameLength : (ancestorChain graph n).length = (ancestorChain graph m).length := by
    rw [AncestorChain.length graph ancestorN, AncestorChain.length graph ancestorM, sameDepth]
  exact (observedChainRankAddress_order graph observe evidence W D widthBound heightBound
    ancestorN ancestorM sameLength).2

/-- On the dense slot enumeration, an endpoint's observed rank address is the observed rank list
of its enumerating root-first chain. -/
theorem observedRankAddress_eq_observedChainRankAddress_of_mem
    (addressing : graph.Addressing) (dense : Dense addressing)
    (W D depth : ℕ) (chain : List graph.Node)
    (member : chain ∈ depthChains graph addressing depth graph.root) :
    observedRankAddress graph observe evidence W D (chain.getLastD graph.root) =
      observedChainRankAddress graph observe evidence W D chain := by
  have chainAncestor := ancestorChain_of_mem_depthChains graph dense depth graph.root chain member
    AncestorChain.root
  have unique := ancestorChain_unique_of_addressing graph addressing
    (ancestorChain_spec_of_addressing graph addressing (chain.getLastD graph.root)) chainAncestor
  unfold observedRankAddress
  rw [unique]
  obtain ⟨nonempty, head, _⟩ := mem_depthChains_shape graph addressing depth graph.root chain member
  cases chain with
  | nil => exact absurd rfl nonempty
  | cons first rest =>
      simp only [List.head?_cons, Option.some.injEq] at head
      subst head
      rfl

end ObservedRankAddress

section ObservedReferenceRankAddress

variable {Atom : Type} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom)
  (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom)
  (observe : ConstitutionalRule → graph.Node → ℤ)

local instance observedReferenceRankAddressNodeFintype : Fintype graph.Node := graph.nodeFintype

/-- The observed reference-selection address at the graph's own width and height bounds. -/
def observedReferenceRankAddress (node : graph.Node) : List ℕ :=
  observedRankAddress graph observe (rankEvidence molecule descriptorMap unit graph)
    graph.width graph.height node

/-- The equal-depth reversal law for reference selection's observed ancestor rank path. -/
theorem observedReferenceRankAddress_lt_iff (addressing : graph.Addressing)
    {n m : graph.Node} (sameDepth : graph.depth n = graph.depth m) :
    observedReferenceRankAddress molecule descriptorMap unit graph observe n <
        observedReferenceRankAddress molecule descriptorMap unit graph observe m ↔
      observedRankPath molecule descriptorMap unit graph observe m <
        observedRankPath molecule descriptorMap unit graph observe n := by
  simpa [observedReferenceRankAddress, observedRankAddress, observedRankPath, observedRankKey] using
    observedRankAddress_lt_iff graph observe (rankEvidence molecule descriptorMap unit graph)
      addressing graph.width graph.height le_rfl le_rfl sameDepth

/-- Rank-address equality at equal depth is equality of reference-selection observed rank paths. -/
theorem observedReferenceRankAddress_eq_iff (addressing : graph.Addressing)
    {n m : graph.Node} (sameDepth : graph.depth n = graph.depth m) :
    observedReferenceRankAddress molecule descriptorMap unit graph observe n =
        observedReferenceRankAddress molecule descriptorMap unit graph observe m ↔
      observedRankPath molecule descriptorMap unit graph observe n =
        observedRankPath molecule descriptorMap unit graph observe m := by
  simpa [observedReferenceRankAddress, observedRankAddress, observedRankPath, observedRankKey] using
    observedRankAddress_eq_iff graph observe (rankEvidence molecule descriptorMap unit graph)
      addressing graph.width graph.height le_rfl le_rfl sameDepth

end ObservedReferenceRankAddress

end
end TetraStereo.OneCenter.DeclarativeCIP

assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.observedStereoNodePathObservation_eq_bot_iff
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.rankedOrdinaryKeysWithObservations_eq_of_ordinaryKeyWithObservations_eq
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.rankIndexInWithObservations_eq_of_parent_and_child_key_eq
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedChainRankAddress
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedChainRankAddress_append
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.AncestorChain.observedChainRankAddress_step
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedOrdinaryKey_mem_rankedOrdinaryKeys
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedChainRankAddress_length
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedChainRankAddress_order
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedRankAddress
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedRankAddress_lt_iff
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedRankAddress_eq_iff
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.observedRankAddress_eq_observedChainRankAddress_of_mem
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedReferenceRankAddress
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedReferenceRankAddress_lt_iff
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.observedReferenceRankAddress_eq_iff
