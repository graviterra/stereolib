import TetraStereo.OneCenter.LocalizedChemicalRingPromotedColorReadback
import TetraStereo.OneCenter.LocalizedRuleMajorObservedCanonicalBridge
import TetraStereo.OneCenter.LocalizedRuleMajorCompoundReadback
import TetraStereo.OneCenter.LocalizedRetainedConstitutionalReaderIndependence
import TetraStereo.KernelOnly

/-!
# Joint constitutional and promoted-marker address readback

Actual refined-key ties produce one pair of dense addressings on which both the
constitutional observations and promoted reference bits agree. Constitutional
sortedness is derived from the ordinary comparison prefix at each sibling; it is
not supplied as a canonicality premise. Non-bottom observations also recover
occupied-address agreement, including atoms with zero-valued observations.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace TetraStereo.OneCenter.LocalizedChemicalRingPromotedConstitutionReadback

open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
open LocalizedCumulativeDecoratedTree LocalizedMarkedRetainedCanonicalFrame
open LocalizedMarkedRetainedCanonicalMarker LocalizedMarkedRetainedSubtreeContext
open LocalizedMarkedRetainedPromotedKey LocalizedMarkedRetainedMolecularSelection
open RetainedConstitutionalReaderIndependence

noncomputable section
open scoped Classical

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}

/-- The three actual constitutional decorations at a hierarchy node. -/
def observe (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (rule : ConstitutionalRule) (node : (ruleMajorTreeGraph tree).Node) : ℤ :=
  priorityValue rule (armObservation rule ((tree.decoratedSubtreeAt? node.1).getD tree))

theorem observe_of_lookup (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (rule : ConstitutionalRule) (node : (ruleMajorTreeGraph tree).Node)
    (actual : LocalizedCumulativeDecoratedTree input carrierFuel)
    (lookup : tree.decoratedSubtreeAt? node.1 = some actual) :
    observe tree rule node = priorityValue rule (armObservation rule actual) := by
  simp only [observe, lookup, Option.getD_some]

/-- Actual decorations recover the official source-node label and stored Rule-1b distance. -/
theorem observe_eq_source (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (rule : ConstitutionalRule) (node : (ruleMajorTreeGraph tree).Node) :
    observe tree rule node = priorityValue rule
      (armSourceObservation input rule (nodeSource input tree node)) := by
  obtain ⟨sub, lookup, _⟩ := observedTree_decoratedSubtree_of_node tree node
  have rawLookup : subtreeAt? tree node.1 = some sub := by
    rwa [← decoratedSubtreeAt?_eq_subtreeAt?]
  rw [observe_of_lookup tree rule node sub lookup, nodeSource_of_lookup input tree rawLookup]
  have realized := realizes_of_decoratedSubtreeAt? tree realizes node.1 sub lookup
  rw [realized]
  cases rule <;> rfl

/-- A strict constitutional prefix cannot be reversed by any later compound column. -/
theorem constitutional_ne_lt_of_full_ne_lt
    (left right : input.LocalizedRerootCompoundRule45Key)
    (ordered : (input.compareLocalizedRerootCompoundThroughRule5 left right).ordering ≠ .lt) :
    OfficialRuleMajorKey.compare left.prior.rule4aKey.constitutional
      right.prior.rule4aKey.constitutional ≠ .lt := by
  intro less
  apply ordered
  simp [CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundThroughRule5,
    CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundRule4bcKeys,
    CertifiedLocalizedCIPInput.compareLocalizedRerootCumulativeRule45Keys,
    compareLex, Ordering.byKey, less]

/-- Recover the actual Rule-4a build from the compound compiled by the marker builder. -/
theorem ordinary_rule4a_built (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (compound : input.LocalizedRerootCompoundRule45Key)
    (built : ordinaryKey? input target view cursor = some compound) :
    input.buildRuleMajorCumulativeWithRead? .rule4a (input.localizedDependencyLabel target view)
      (2 * (carrierFuel + 1)) cursor = some compound.prior.rule4aKey := by
  unfold ordinaryKey? at built
  rw [input.buildActualRuleMajorCompoundRule45KeyExec?_eq,
    input.buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor] at built
  exact (input.buildRuleMajorCompoundRule45KeyWith?_readback _ cursor built).1

/-- Every local subtree key has the same constitutional columns as the independently compiled
ordinary compound at its source, even when readers, stages and successful fuels differ. -/
theorem subtree_constitution_eq_ordinary
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {fuel : Nat} {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedRuleMajorSortTrace input stage read fuel tree key)
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    (compound : input.LocalizedRerootCompoundRule45Key)
    (built : ordinaryKey? input target view tree.source = some compound) :
    constitutionalObservable key.constitutional =
      constitutionalObservable compound.prior.rule4aKey.constitutional := by
  obtain ⟨other, source, otherTrace⟩ := exists_ruleMajorTrace_of_buildWithRead input .rule4a
    (input.localizedDependencyLabel target view) (2 * (carrierFuel + 1)) tree.source
    compound.prior.rule4aKey (ordinary_rule4a_built target view tree.source compound built)
  exact ruleMajorSortTrace_constitutionalObservable_eq trace otherTrace source.symm

variable (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
  (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
  (fallback : CompleteLigandRule5Key)
  {stage : LocalizedCumulativeRule45Stage}
  {read : input.LocalizedRerootCursor (retainedCarrierFuel input) → Option LocalizedAuxiliaryLabel}
  {fuel : Nat} {tree : LocalizedCumulativeDecoratedTree input (retainedCarrierFuel input)}
  {treeKey : input.LocalizedRerootCumulativeRule45Key}
  (trace : LocalizedRuleMajorSortTrace input stage read fuel tree treeKey)
  (tetrahedral : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
  (single : input.moleculeGraph.SimpleBonded)
  (rootChild : tree.source ∈ input.executableLocalizedRerootChildren ⟨target, none⟩)
  (W D : Nat) (width : (ruleMajorTreeGraph tree).width ≤ W)
  (height : (ruleMajorTreeGraph tree).height ≤ D)

include trace tetrahedral single rootChild width height

/-- The independent deep prior refines the constitutional key of the SAME actual arm tree.
This derives the order relation through actual successful compounds and their immutable prefix. -/
theorem deepPrior_refines_constitution (parent left right : (ruleMajorTreeGraph tree).Node)
    (edgeL : (ruleMajorTreeGraph tree).child parent left)
    (edgeR : (ruleMajorTreeGraph tree).child parent right)
    (ordered : deepPrior descriptorMap target fallback tree right ≤
      deepPrior descriptorMap target fallback tree left) :
    ruleKeyWithObservations (ruleMajorTreeGraph tree) W D (observe tree) right ≤
      ruleKeyWithObservations (ruleMajorTreeGraph tree) W D (observe tree) left := by
  have realizes := LocalizedRuleMajorSortTrace.realizes_of_trace trace
  have childL := child_edge tree realizes edgeL
  have childR := child_edge tree realizes edgeR
  have validL := input.localizedRerootChild_valid _ _ _
    (input.executableLocalizedRerootChildren_declarative (nodeSource input tree parent)) childL
  have validR := input.localizedRerootChild_valid _ _ _
    (input.executableLocalizedRerootChildren_declarative (nodeSource input tree parent)) childR
  obtain ⟨compoundL, builtL⟩ := ordinaryKey?_exists input target (input.molecularView descriptorMap target)
    (nodeSource input tree left) validL
  obtain ⟨compoundR, builtR⟩ := ordinaryKey?_exists input target (input.molecularView descriptorMap target)
    (nodeSource input tree right) validR
  have comparePrior := deepPrior_agreement descriptorMap target fallback tree realizes tetrahedral
    single rootChild parent left right edgeL edgeR compoundL compoundR builtL builtR
  have fullOrdered : (input.compareLocalizedRerootCompoundThroughRule5 compoundL compoundR).ordering ≠ .lt := by
    rw [comparePrior]
    exact fun h => not_lt_of_ge ordered (compare_lt_iff_lt.mp h)
  have constitutional := constitutional_ne_lt_of_full_ne_lt compoundL compoundR fullOrdered
  obtain ⟨subL, lookupL⟩ := exists_local_subtree tree left
  obtain ⟨subR, lookupR⟩ := exists_local_subtree tree right
  have decL : tree.decoratedSubtreeAt? left.1 = some subL := by
    rwa [decoratedSubtreeAt?_eq_subtreeAt?]
  have decR : tree.decoratedSubtreeAt? right.1 = some subR := by
    rwa [decoratedSubtreeAt?_eq_subtreeAt?]
  obtain ⟨fuelL, keyL, traceL⟩ := ruleMajorTrace_of_subtree input stage read trace left.1 subL decL
  obtain ⟨fuelR, keyR, traceR⟩ := ruleMajorTrace_of_subtree input stage read trace right.1 subR decR
  rw [nodeSource_of_lookup input tree lookupL] at builtL
  rw [nodeSource_of_lookup input tree lookupR] at builtR
  have sameL := subtree_constitution_eq_ordinary traceL target (input.molecularView descriptorMap target) compoundL builtL
  have sameR := subtree_constitution_eq_ordinary traceR target (input.molecularView descriptorMap target) compoundR builtR
  have compared := ruleMajor_compare_congr keyL.constitutional keyR.constitutional
    compoundL.prior.rule4aKey.constitutional compoundR.prior.rule4aKey.constitutional sameL sameR
  rw [← compared] at constitutional
  exact (OfficialSparseCanonicalVectorComparison.compare_ne_lt_iff_rightVector_le
    (wellFormedRuleMajorKey_of_tableMatch (LocalizedRuleMajorSortTrace.fullMatch_of_trace traceL).tableMatch
      (LocalizedRuleMajorSortTrace.realizes_of_trace traceL))
    (wellFormedRuleMajorKey_of_tableMatch (LocalizedRuleMajorSortTrace.fullMatch_of_trace traceR).tableMatch
      (LocalizedRuleMajorSortTrace.realizes_of_trace traceR))
    (ruleKeyWithObservations_vectorWellShaped (ruleMajorTreeGraph tree) (observe tree) W D left)
    (ruleKeyWithObservations_vectorWellShaped (ruleMajorTreeGraph tree) (observe tree) W D right)
    (observedTree_node_bridge tree (observe tree) (observe_of_lookup tree) width height left subL keyL traceL decL).2
    (observedTree_node_bridge tree (observe tree) (observe_of_lookup tree) width height right subR keyR traceR decR).2).mp constitutional

/-- Every promoted-canonical addressing of an actual arm is also constitutionally sorted. -/
theorem promoted_constitution_sorted (reference : input.Atom) (markerW markerD : Nat)
    {addressing : (ruleMajorTreeGraph tree).Addressing}
    (canonical : PromotedCanonical.CanonicalAddressing (ruleMajorTreeGraph tree)
      (deepPrior descriptorMap target fallback tree) (referenceMark input reference tree)
      markerW markerD addressing) :
    KeySorted (ruleKeyWithObservations (ruleMajorTreeGraph tree) W D (observe tree)) addressing := by
  have priorSorted := PromotedCanonical.canonicalAddressing_prior_sorted _ _ _ _ _ canonical
  intro parent left right slotL slotR addressL addressR slots
  exact deepPrior_refines_constitution descriptorMap target fallback trace tetrahedral single rootChild
    W D width height parent left right
    ((addressing.child_iff parent left).mpr ⟨slotL, addressL⟩)
    ((addressing.child_iff parent right).mpr ⟨slotR, addressR⟩)
    (priorSorted parent left right slotL slotR addressL addressR slots)

omit trace tetrahedral single rootChild width height

section AddressReadback

open RootedDigraph Certificate.CanonicalSphereKey

variable {Atom : Type}
  (graph : RootedDigraph Atom) (obs : ConstitutionalRule → graph.Node → ℤ)

/-- Observer-parametric address reading, retaining an explicit bottom value for absence. -/
def observationAt (addressing : graph.Addressing) (rule : ConstitutionalRule)
    (position : List Nat) : WithBot ℤ :=
  if h : ∃ node, addressing.address node = position then
    (obs rule (Classical.choose h) : WithBot ℤ) else ⊥

theorem observationAt_of_address (addressing : graph.Addressing) (rule : ConstitutionalRule)
    (node : graph.Node) :
    observationAt graph obs addressing rule (addressing.address node) = (obs rule node : WithBot ℤ) := by
  have present : ∃ found, addressing.address found = addressing.address node := ⟨node, rfl⟩
  unfold observationAt
  rw [dif_pos present]
  congr 2
  exact addressing.address_injective (Classical.choose_spec present)

theorem observationAt_of_unoccupied (addressing : graph.Addressing) (rule : ConstitutionalRule)
    {position : List Nat} (absent : ∀ node, addressing.address node ≠ position) :
    observationAt graph obs addressing rule position = ⊥ := by
  unfold observationAt
  rw [dif_neg (by simpa using absent)]

/-- The canonical key reads the same observation at each dense, constitutionally sorted address. -/
theorem observationAt_eq_keyObservation (W D : Nat) {addressing : graph.Addressing}
    (dense : Dense addressing)
    (sorted : KeySorted (ruleKeyWithObservations graph W D obs) addressing)
    (rule : ConstitutionalRule) :
    ∀ (path : List Nat) (node : graph.Node),
      (∀ slot ∈ path, slot < W) → path.length ≤ D →
      keyObservation ((ruleKeyWithObservations graph W D obs node).getD (ruleIndex rule) [])
        path.length (slotOf W path) =
      observationAt graph obs addressing rule (addressing.address node ++ path)
  | [], node, _, _ => by
      rw [List.append_nil, observationAt_of_address, ruleKeyWithObservations_getD]
      simp [keyObservation, ruleComponentWithObservations, assemble, slotOf]
  | slot :: path, node, digits, length => by
      have slotBound : slot < W := digits slot (by simp)
      have pathBounds : ∀ i ∈ path, i < W := fun i hi => digits i (by simp [hi])
      have pathDepth : path.length < D := by simp at length; omega
      have offsetBound := slotOf_lt pathBounds
      obtain ⟨count, countDense⟩ := dense node
      have ranked := sortDesc_childKeys_eq_slotOrder (ruleKeyWithObservations graph W D obs) countDense sorted
      have shaped : ∀ key ∈
          ((slotList addressing node count).map (ruleKeyWithObservations graph W D obs)).map
            (fun key => key.getD (ruleIndex rule) []), WellShaped W D key := by
        intro key member
        obtain ⟨vector, vectorMember, rfl⟩ := List.mem_map.mp member
        obtain ⟨child, _, rfl⟩ := List.mem_map.mp vectorMember
        exact ruleKeyWithObservations_wellShaped graph W D obs rule child
      rw [ruleKeyWithObservations_getD, ranked]
      simp only [keyObservation, ruleComponentWithObservations, assemble, List.length_cons,
        slotOf, List.getD_cons_succ]
      rw [List.getD_eq_getElem?_getD (l := List.map _ _), List.getElem?_map,
        List.getElem?_range pathDepth, Option.map_some, Option.getD_some,
        getD_flatMap_range _ _ W (fun i _ => slotLevel_length shaped pathDepth i) slotBound offsetBound]
      by_cases occupied : slot < count
      · obtain ⟨child, childAt, childAddress⟩ := slotList_getD_of_lt countDense occupied
        have ih := observationAt_eq_keyObservation W D dense sorted rule path child pathBounds (by omega)
        have position : addressing.address node ++ slot :: path = addressing.address child ++ path := by
          rw [childAddress]; simp
        rw [position, ← ih]
        have rowBound : path.length <
            ((ruleKeyWithObservations graph W D obs child).getD (ruleIndex rule) []).length := by
          rw [(ruleKeyWithObservations_wellShaped graph W D obs rule child).1]
          omega
        have rowBound' : path.length <
            ((ruleKeyWithObservations graph W D obs child)[ruleIndex rule]?.getD []).length := by
          simpa [List.getD_eq_getElem?_getD] using rowBound
        simp [keyObservation, List.getD_eq_getElem?_getD, List.getElem?_map, childAt,
          List.getElem?_eq_getElem rowBound']
      · have noChild : ((slotList addressing node count).map
            (ruleKeyWithObservations graph W D obs))[slot]? = none := by
          simp [slotList]
          omega
        have absent : ∀ found,
            addressing.address found ≠ addressing.address node ++ slot :: path := by
          intro found foundAt
          obtain ⟨ancestor, ancestorAt⟩ := addressing.prefix_occupied found
            (addressing.address node ++ [slot]) path (by rw [foundAt]; simp)
          exact occupied ((countDense slot).mp ⟨ancestor, ancestorAt⟩)
        rw [observationAt_of_unoccupied graph obs addressing rule absent]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_map, noChild, Option.map_none,
          Option.getD_none, List.getElem?_nil, pad, List.getElem?_replicate]
        split <;> rfl

theorem observationAt_ne_bot_iff (addressing : graph.Addressing) (rule : ConstitutionalRule)
    (position : List Nat) :
    observationAt graph obs addressing rule position ≠ ⊥ ↔
      ∃ node, addressing.address node = position := by
  unfold observationAt
  split <;> simp_all

private theorem observationAt_outside (addressing : graph.Addressing) (dense : Dense addressing)
    {W D : Nat} (width : graph.width ≤ W) (height : graph.height ≤ D)
    (position : List Nat) (outside : ¬ ((∀ slot ∈ position, slot < W) ∧ position.length ≤ D))
    (rule : ConstitutionalRule) : observationAt graph obs addressing rule position = ⊥ := by
  apply observationAt_of_unoccupied
  intro node equal
  apply outside
  constructor
  · intro slot member
    rw [← equal] at member
    exact (address_slots_lt_width dense node slot member).trans_le width
  · rw [← equal]
    exact (address_length_le_height addressing node).trans height

/-- Equal constitutional keys read equal observations at the SAME address, including absence. -/
theorem observations_eq_of_root_keys_eq
    (right : RootedDigraph Atom) (obsR : ConstitutionalRule → right.Node → ℤ)
    (W D : Nat) (widthL : graph.width ≤ W) (heightL : graph.height ≤ D)
    (widthR : right.width ≤ W) (heightR : right.height ≤ D)
    (addressL : graph.Addressing) (addressR : right.Addressing)
    (denseL : Dense addressL) (denseR : Dense addressR)
    (sortedL : KeySorted (ruleKeyWithObservations graph W D obs) addressL)
    (sortedR : KeySorted (ruleKeyWithObservations right W D obsR) addressR)
    (keys : ruleKeyWithObservations graph W D obs graph.root =
      ruleKeyWithObservations right W D obsR right.root)
    (rule : ConstitutionalRule) (position : List Nat) :
    observationAt graph obs addressL rule position = observationAt right obsR addressR rule position := by
  by_cases inside : (∀ slot ∈ position, slot < W) ∧ position.length ≤ D
  · have readL := observationAt_eq_keyObservation graph obs W D denseL sortedL rule position
      graph.root inside.1 inside.2
    have readR := observationAt_eq_keyObservation right obsR W D denseR sortedR rule position
      right.root inside.1 inside.2
    rw [addressL.root_address, List.nil_append] at readL
    rw [addressR.root_address, List.nil_append] at readR
    rw [keys] at readL
    exact readL.symm.trans readR
  · rw [observationAt_outside graph obs addressL denseL widthL heightL position inside rule,
      observationAt_outside right obsR addressR denseR widthR heightR position inside rule]

/-- Equality of one constitutional observation column already detects matching occupied slots. -/
theorem occupied_iff_of_observations_eq
    (right : RootedDigraph Atom) (obsR : ConstitutionalRule → right.Node → ℤ)
    (addressL : graph.Addressing) (addressR : right.Addressing)
    (same : ∀ rule position, observationAt graph obs addressL rule position =
      observationAt right obsR addressR rule position) (position : List Nat) :
    (∃ node, addressL.address node = position) ↔ (∃ node, addressR.address node = position) := by
  rw [← observationAt_ne_bot_iff graph obs addressL .rule1aAtomicNumber,
    ← observationAt_ne_bot_iff right obsR addressR .rule1aAtomicNumber, same]

end AddressReadback

section Frame

open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedPromotedRanking
open LocalizedMarkedRetainedStateReader LocalizedChemicalRingPromotedColorReadback

/-- An actual full tie has a constitutional tie, independently of later columns. -/
theorem constitutional_eq_of_full_eq (left right : input.LocalizedRerootCompoundRule45Key)
    (tie : (input.compareLocalizedRerootCompoundThroughRule5 left right).ordering = .eq) :
    OfficialRuleMajorKey.compare left.prior.rule4aKey.constitutional
      right.prior.rule4aKey.constitutional = .eq := by
  cases h : OfficialRuleMajorKey.compare left.prior.rule4aKey.constitutional
      right.prior.rule4aKey.constitutional with
  | eq => rfl
  | lt =>
      simp [CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundThroughRule5,
        CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundRule4bcKeys,
        CertifiedLocalizedCIPInput.compareLocalizedRerootCumulativeRule45Keys,
        compareLex, Ordering.byKey, h] at tie
  | gt =>
      simp [CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundThroughRule5,
        CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundRule4bcKeys,
        CertifiedLocalizedCIPInput.compareLocalizedRerootCumulativeRule45Keys,
        compareLex, Ordering.byKey, h] at tie

/-- Independent retained-key equality gives equal constitutional vectors of the actual
Rule-4a trees, at any common covering layout. -/
theorem frame_constitution_keys_eq
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (frame : RetainedExecutionFrame descriptorMap target)
    (tetrahedral : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (single : input.moleculeGraph.SimpleBonded) (unit : DetectedOccurrence input.moleculeGraph)
    (targetUnit : input.molecularFrameUnit target.1 = unit.1) (left right : Fin 4)
    (W D : Nat)
    (widthL : (ruleMajorTreeGraph (frame.stages left).a.tree).width ≤ W)
    (heightL : (ruleMajorTreeGraph (frame.stages left).a.tree).height ≤ D)
    (widthR : (ruleMajorTreeGraph (frame.stages right).a.tree).width ≤ W)
    (heightR : (ruleMajorTreeGraph (frame.stages right).a.tree).height ≤ D)
    (tie : frame.retainedKeys unit left = frame.retainedKeys unit right) :
    ruleKeyWithObservations (ruleMajorTreeGraph (frame.stages left).a.tree) W D
      (observe (frame.stages left).a.tree) (ruleMajorTreeGraph (frame.stages left).a.tree).root =
    ruleKeyWithObservations (ruleMajorTreeGraph (frame.stages right).a.tree) W D
      (observe (frame.stages right).a.tree) (ruleMajorTreeGraph (frame.stages right).a.tree).root := by
  have full := frame.fullOrdering tetrahedral single unit targetUnit left right
  rw [tie, (completeLigandRule5Key_compare_eq_iff _ _).mpr rfl] at full
  have constTie := constitutional_eq_of_full_eq (frame.compounds left) (frame.compounds right) full
  have ordinaryBuilt (slot : Fin 4) : ordinaryKey? input target (input.molecularView descriptorMap target)
      (frame.stages slot).a.tree.source = some (frame.compounds slot) := by
    rw [(frame.stages slot).a.sourceEq]
    exact frame.compoundBuilt slot
  have sameL := subtree_constitution_eq_ordinary (frame.stages left).a.trace target
    (input.molecularView descriptorMap target) (frame.compounds left) (ordinaryBuilt left)
  have sameR := subtree_constitution_eq_ordinary (frame.stages right).a.trace target
    (input.molecularView descriptorMap target) (frame.compounds right) (ordinaryBuilt right)
  have compared := ruleMajor_compare_congr (frame.stages left).a.key.constitutional
    (frame.stages right).a.key.constitutional (frame.compounds left).prior.rule4aKey.constitutional
    (frame.compounds right).prior.rule4aKey.constitutional sameL sameR
  rw [← compared] at constTie
  exact (OfficialSparseCanonicalVectorComparison.compare_eq_iff_vector_eq
    (wellFormedRuleMajorKey_of_tableMatch
      (LocalizedRuleMajorSortTrace.fullMatch_of_trace (frame.stages left).a.trace).tableMatch
      (LocalizedRuleMajorSortTrace.realizes_of_trace (frame.stages left).a.trace))
    (wellFormedRuleMajorKey_of_tableMatch
      (LocalizedRuleMajorSortTrace.fullMatch_of_trace (frame.stages right).a.trace).tableMatch
      (LocalizedRuleMajorSortTrace.realizes_of_trace (frame.stages right).a.trace))
    (ruleKeyWithObservations_vectorWellShaped _ _ W D _)
    (ruleKeyWithObservations_vectorWellShaped _ _ W D _)
    (observedTree_node_bridge _ _ (observe_of_lookup _) widthL heightL _ _ _
      (frame.stages left).a.trace (by
        change (frame.stages left).a.tree.decoratedSubtreeAt? [] = some (frame.stages left).a.tree
        rw [decoratedSubtreeAt?])).2
    (observedTree_node_bridge _ _ (observe_of_lookup _) widthR heightR _ _ _
      (frame.stages right).a.trace (by
        change (frame.stages right).a.tree.decoratedSubtreeAt? [] = some (frame.stages right).a.tree
        rw [decoratedSubtreeAt?])).2).mp constTie

end Frame

section ActualJoint

open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedPromotedRanking
open LocalizedMarkedRetainedStateReader LocalizedChemicalRingPromotedColorReadback

variable (input : CertifiedLocalizedCIPInput) (single : input.moleculeGraph.SimpleBonded)
  (state : OccurrenceAuxState) (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
  (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
  (unit : DetectedOccurrence input.moleculeGraph) (targetUnit : input.molecularFrameUnit target.1 = unit.1)
  (reference : input.Atom) (W D : Nat) (fallback : CompleteLigandRule5Key)

/-- An actual refined-key tie constructs ONE pair of promoted addressings preserving
constitutional observations, occupied positions, and the promoted reference column jointly. -/
theorem actual_tie_joint_readback (left right : Fin 4)
    (widthL : ∀ node, ((ruleMajorTreeGraph (slotTree input single state target real unit targetUnit left)).childList node).length ≤ W)
    (heightL : (ruleMajorTreeGraph (slotTree input single state target real unit targetUnit left)).height ≤ D)
    (widthR : ∀ node, ((ruleMajorTreeGraph (slotTree input single state target real unit targetUnit right)).childList node).length ≤ W)
    (heightR : (ruleMajorTreeGraph (slotTree input single state target real unit targetUnit right)).height ≤ D)
    (tie : refinedKey input single state target real unit targetUnit reference W D left =
      refinedKey input single state target real unit targetUnit reference W D right) :
    let treeL := slotTree input single state target real unit targetUnit left
    let treeR := slotTree input single state target real unit targetUnit right
    ∃ matched : MatchedMarkerAddressings (ruleMajorTreeGraph treeL) (ruleMajorTreeGraph treeR)
        (deepPrior (rawStateDescriptorMap input state) target fallback treeL)
        (deepPrior (rawStateDescriptorMap input state) target fallback treeR)
        (referenceMark input reference treeL) (referenceMark input reference treeR) W D,
      (∀ rule position, observationAt (ruleMajorTreeGraph treeL) (observe treeL)
          matched.leftAddressing rule position =
        observationAt (ruleMajorTreeGraph treeR) (observe treeR) matched.rightAddressing rule position) ∧
      (∀ position, (∃ node, matched.leftAddressing.address node = position) ↔
        (∃ node, matched.rightAddressing.address node = position)) := by
  dsimp only
  obtain ⟨matched⟩ := actual_tie_matched_marker_addressings input single state target real unit
    targetUnit reference W D fallback left right widthL heightL widthR heightR tie
  let frame := frames input single state target real unit targetUnit
  have rootChild (slot : Fin 4) : (frame.stages slot).a.tree.source ∈
      input.executableLocalizedRerootChildren ⟨target, none⟩ := by
    rw [(frame.stages slot).a.sourceEq]
    exact frame.childAt slot
  let cW := max (ruleMajorTreeGraph (frame.stages left).a.tree).width
    (ruleMajorTreeGraph (frame.stages right).a.tree).width
  let cD := max (ruleMajorTreeGraph (frame.stages left).a.tree).height
    (ruleMajorTreeGraph (frame.stages right).a.tree).height
  have wL : (ruleMajorTreeGraph (frame.stages left).a.tree).width ≤ cW := le_max_left _ _
  have wR : (ruleMajorTreeGraph (frame.stages right).a.tree).width ≤ cW := le_max_right _ _
  have dL : (ruleMajorTreeGraph (frame.stages left).a.tree).height ≤ cD := le_max_left _ _
  have dR : (ruleMajorTreeGraph (frame.stages right).a.tree).height ≤ cD := le_max_right _ _
  have sortedL := promoted_constitution_sorted (rawStateDescriptorMap input state) target fallback
    (frame.stages left).a.trace (rawStateDescriptorMap_tetrahedral input state) single (rootChild left)
    cW cD wL dL reference W D matched.leftCanonical
  have sortedR := promoted_constitution_sorted (rawStateDescriptorMap input state) target fallback
    (frame.stages right).a.trace (rawStateDescriptorMap_tetrahedral input state) single (rootChild right)
    cW cD wR dR reference W D matched.rightCanonical
  have ordinary : frame.retainedKeys unit left = frame.retainedKeys unit right := by
    exact congrArg (fun value : RefinedKey => (ofLex value).1) tie
  have keys := frame_constitution_keys_eq (rawStateDescriptorMap input state) target frame
    (rawStateDescriptorMap_tetrahedral input state) single unit targetUnit left right cW cD
    wL dL wR dR ordinary
  have same := observations_eq_of_root_keys_eq
    (ruleMajorTreeGraph (frame.stages left).a.tree) (observe (frame.stages left).a.tree)
    (ruleMajorTreeGraph (frame.stages right).a.tree) (observe (frame.stages right).a.tree)
    cW cD wL dL wR dR matched.leftAddressing matched.rightAddressing
    matched.leftCanonical.1 matched.rightCanonical.1 sortedL sortedR keys
  exact ⟨matched, same, occupied_iff_of_observations_eq _ _ _ _
    matched.leftAddressing matched.rightAddressing same⟩

end ActualJoint

end
end TetraStereo.OneCenter.LocalizedChemicalRingPromotedConstitutionReadback

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedConstitutionReadback.observe
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedConstitutionReadback.observe_of_lookup
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedConstitutionReadback.constitutional_ne_lt_of_full_ne_lt
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedConstitutionReadback.ordinary_rule4a_built
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedConstitutionReadback.subtree_constitution_eq_ordinary
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedConstitutionReadback.deepPrior_refines_constitution
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedConstitutionReadback.promoted_constitution_sorted
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedConstitutionReadback.observe_eq_source
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedConstitutionReadback.observationAt
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedConstitutionReadback.observationAt_of_address
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedConstitutionReadback.observationAt_of_unoccupied
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedConstitutionReadback.observationAt_eq_keyObservation
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedConstitutionReadback.observationAt_ne_bot_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedConstitutionReadback.observations_eq_of_root_keys_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedConstitutionReadback.occupied_iff_of_observations_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedConstitutionReadback.constitutional_eq_of_full_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedConstitutionReadback.frame_constitution_keys_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedConstitutionReadback.actual_tie_joint_readback
