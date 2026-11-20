import TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey
import TetraStereo.OneCenter.LocalizedChemicalRingPromotedConstitutionReadback
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000
































namespace TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerReconstruction

open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
open LocalizedCumulativeDecoratedTree
open LocalizedMarkedRetainedCanonicalFrame
open LocalizedChemicalRingJointMarkerKey
open LocalizedChemicalRingPromotedConstitutionReadback
open LocalizedMarkedRetainedMolecularSelection LocalizedMarkedRetainedPromotedKey
open LocalizedMarkedRetainedCanonicalMarker

noncomputable section
open scoped Classical

universe u

/-! ## Address-aligned hierarchy equivalence -/

/-- A rooted hierarchy equivalence aligned with two supplied addressings.  There is no label
field: label equality is not derivable from occupancy and is not asserted. -/
structure AlignedHierarchyEquiv {Atom : Type u} {left right : RootedDigraph Atom}
    (addressL : left.Addressing) (addressR : right.Addressing) where
  toEquiv : left.Node ≃ right.Node
  map_root : toEquiv left.root = right.root
  map_child : ∀ a b, left.child a b ↔ right.child (toEquiv a) (toEquiv b)
  aligns : ∀ a, addressR.address (toEquiv a) = addressL.address a

/-- Occupied-address agreement alone constructs a root- and child-preserving hierarchy
equivalence aligned with the two addressings.  The proof uses address injectivity and the
parent-preserving child law; it does not need dense sibling slots. -/
theorem exists_aligned_hierarchy_equiv {Atom : Type u} {left right : RootedDigraph Atom}
    (addressL : left.Addressing) (addressR : right.Addressing)
    (occupied : ∀ position,
      (∃ x, addressL.address x = position) ↔
        (∃ y, addressR.address y = position)) :
    Nonempty (AlignedHierarchyEquiv addressL addressR) := by
  classical
  let f : left.Node → right.Node := fun x =>
    Classical.choose ((occupied (addressL.address x)).1 ⟨x, rfl⟩)
  have f_spec : ∀ x, addressR.address (f x) = addressL.address x := fun x =>
    Classical.choose_spec ((occupied (addressL.address x)).1 ⟨x, rfl⟩)
  have f_injective : Function.Injective f := by
    intro x y same
    apply addressL.address_injective
    rw [← f_spec x, ← f_spec y, same]
  have f_surjective : Function.Surjective f := by
    intro y
    obtain ⟨x, hx⟩ := (occupied (addressR.address y)).2 ⟨y, rfl⟩
    exact ⟨x, addressR.address_injective ((f_spec x).trans hx)⟩
  let equiv : left.Node ≃ right.Node := Equiv.ofBijective f ⟨f_injective, f_surjective⟩
  have equiv_apply : ∀ x, equiv x = f x := fun x => rfl
  refine ⟨{ toEquiv := equiv
            map_root := ?_
            map_child := ?_
            aligns := ?_ }⟩
  · apply addressR.address_injective
    rw [equiv_apply, f_spec, addressL.root_address, addressR.root_address]
  · intro a b
    constructor
    · intro h
      obtain ⟨slot, hslot⟩ := (addressL.child_iff a b).1 h
      exact (addressR.child_iff (equiv a) (equiv b)).2
        ⟨slot, by rw [equiv_apply, equiv_apply, f_spec, f_spec, hslot]⟩
    · intro h
      obtain ⟨slot, hslot⟩ := (addressR.child_iff (equiv a) (equiv b)).1 h
      exact (addressL.child_iff a b).2
        ⟨slot, by
          rw [← f_spec b, ← f_spec a, ← equiv_apply, ← equiv_apply]
          exact hslot⟩
  · intro a
    exact f_spec a

/-- The aligned hierarchy equivalence also preserves depth. -/
theorem AlignedHierarchyEquiv.map_depth
    {Atom : Type u} {left right : RootedDigraph Atom}
    {addressL : left.Addressing} {addressR : right.Addressing}
    (equiv : AlignedHierarchyEquiv addressL addressR) (node : left.Node) :
    right.depth (equiv.toEquiv node) = left.depth node := by
  rw [← DeclarativeCIP.RootedDigraph.Addressing.address_length_eq_depth addressR
      (equiv.toEquiv node),
    ← DeclarativeCIP.RootedDigraph.Addressing.address_length_eq_depth addressL node,
    equiv.aligns node]

/-- Once the aligned map is constructed, address equality supplies simultaneous preservation of
every one of the `n` mark coordinates. -/
theorem aligned_hierarchy_marks_preserved
    {Atom : Type u} {left right : RootedDigraph Atom}
    {P : Type*} [LinearOrder P]
    {priorL : left.Node → P} {priorR : right.Node → P}
    {marksL : left.Node → List Nat} {marksR : right.Node → List Nat}
    {n W D : Nat}
    {matched : MatchedJointMarkerAddressings left right priorL priorR marksL marksR n W D}
    {equiv : AlignedHierarchyEquiv matched.leftAddressing matched.rightAddressing}
    (index : Nat) (bound : index < n) (x : left.Node) :
    (marksL x).getD index 0 = (marksR (equiv.toEquiv x)).getD index 0 :=
  matched.marks_preserved_of_address_alignment equiv.toEquiv
    (fun x => (equiv.aligns x).symm) index bound x

/-! ## Constitutional sortedness of a joint-canonical arm -/

/-- The independent deep prior, sorted at the siblings of any addressing, already implies that
the addressing is sorted for the actual constitutional observations.  The window bounds are those
of the actual tree; the marker budget of the joint key is irrelevant here. -/
theorem constitution_sorted_of_prior_sorted
    {input : CertifiedLocalizedCIPInput}
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (fallback : CompleteLigandRule5Key)
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (retainedCarrierFuel input) →
      Option LocalizedAuxiliaryLabel}
    {fuel : Nat} {tree : LocalizedCumulativeDecoratedTree input (retainedCarrierFuel input)}
    {treeKey : input.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedRuleMajorSortTrace input stage read fuel tree treeKey)
    (tetrahedral : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (single : input.moleculeGraph.SimpleBonded)
    (rootChild : tree.source ∈ input.executableLocalizedRerootChildren ⟨target, none⟩)
    (W D : Nat) (width : (ruleMajorTreeGraph tree).width ≤ W)
    (height : (ruleMajorTreeGraph tree).height ≤ D)
    {addressing : (ruleMajorTreeGraph tree).Addressing}
    (priorSorted : KeySorted (deepPrior descriptorMap target fallback tree) addressing) :
    KeySorted (ruleKeyWithObservations (ruleMajorTreeGraph tree) W D (observe tree))
      addressing := by
  intro parent left right slotL slotR addressL addressR slots
  exact deepPrior_refines_constitution descriptorMap target fallback trace tetrahedral single
    rootChild W D width height parent left right
    ((addressing.child_iff parent left).mpr ⟨slotL, addressL⟩)
    ((addressing.child_iff parent right).mpr ⟨slotR, addressR⟩)
    (priorSorted parent left right slotL slotR addressL addressR slots)

/-- A joint-canonical addressing of one actual arm is sorted for the actual constitutional
observations at the very window it was constructed for. -/
theorem joint_constitution_sorted
    {input : CertifiedLocalizedCIPInput}
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (fallback : CompleteLigandRule5Key)
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (retainedCarrierFuel input) →
      Option LocalizedAuxiliaryLabel}
    {fuel : Nat} {tree : LocalizedCumulativeDecoratedTree input (retainedCarrierFuel input)}
    {treeKey : input.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedRuleMajorSortTrace input stage read fuel tree treeKey)
    (tetrahedral : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (single : input.moleculeGraph.SimpleBonded)
    (rootChild : tree.source ∈ input.executableLocalizedRerootChildren ⟨target, none⟩)
    (W D : Nat) (width : (ruleMajorTreeGraph tree).width ≤ W)
    (height : (ruleMajorTreeGraph tree).height ≤ D)
    {n : Nat} {marks : (ruleMajorTreeGraph tree).Node → List Nat}
    {addressing : (ruleMajorTreeGraph tree).Addressing}
    (canonical : JointCanonicalAddressing (ruleMajorTreeGraph tree)
      (deepPrior descriptorMap target fallback tree) marks W D n addressing) :
    KeySorted (ruleKeyWithObservations (ruleMajorTreeGraph tree) W D (observe tree))
      addressing :=
  constitution_sorted_of_prior_sorted descriptorMap target fallback trace tetrahedral single
    rootChild W D width height
    (jointCanonicalAddressing_prior_sorted (ruleMajorTreeGraph tree)
      (deepPrior descriptorMap target fallback tree) marks W D n canonical)

/-! ## Root constitutional key equality from the ordinary built tie -/

/-- An ordinary tie at the two built joint keys gives equality of the two actual root
constitutional keys, through each actual trace's ordinary readback and the shared
constitutional-observable comparison. -/
theorem built_constitution_keys_eq
    (input : CertifiedLocalizedCIPInput)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    {stageL stageR : LocalizedCumulativeRule45Stage}
    {readL readR : input.LocalizedRerootCursor (retainedCarrierFuel input) →
      Option LocalizedAuxiliaryLabel}
    {fuelL fuelR : Nat} {treeL treeR : LocalizedCumulativeDecoratedTree input
      (retainedCarrierFuel input)}
    {treeKeyL treeKeyR : input.LocalizedRerootCumulativeRule45Key}
    (traceL : LocalizedRuleMajorSortTrace input stageL readL fuelL treeL treeKeyL)
    (traceR : LocalizedRuleMajorSortTrace input stageR readR fuelR treeR treeKeyR)
    (references : List input.Atom) (markerW markerD W D : Nat)
    {resultL resultR : JointPromotedKey input}
    (builtL : buildJoint? input target (input.molecularView descriptorMap target)
      references markerW markerD fuelL treeL.source = some resultL)
    (builtR : buildJoint? input target (input.molecularView descriptorMap target)
      references markerW markerD fuelR treeR.source = some resultR)
    (tie : (input.compareLocalizedRerootCompoundThroughRule5 resultL.prior
      resultR.prior).ordering = .eq)
    (widthL : (ruleMajorTreeGraph treeL).width ≤ W)
    (heightL : (ruleMajorTreeGraph treeL).height ≤ D)
    (widthR : (ruleMajorTreeGraph treeR).width ≤ W)
    (heightR : (ruleMajorTreeGraph treeR).height ≤ D) :
    ruleKeyWithObservations (ruleMajorTreeGraph treeL) W D (observe treeL)
        (ruleMajorTreeGraph treeL).root =
      ruleKeyWithObservations (ruleMajorTreeGraph treeR) W D (observe treeR)
        (ruleMajorTreeGraph treeR).root := by
  have ordinaryBuiltL : ordinaryKey? input target (input.molecularView descriptorMap target)
      treeL.source = some resultL.prior :=
    buildJoint?_prior input target (input.molecularView descriptorMap target) references markerW markerD
      fuelL treeL.source resultL builtL
  have ordinaryBuiltR : ordinaryKey? input target (input.molecularView descriptorMap target)
      treeR.source = some resultR.prior :=
    buildJoint?_prior input target (input.molecularView descriptorMap target) references markerW markerD
      fuelR treeR.source resultR builtR
  have sameL := subtree_constitution_eq_ordinary traceL target
    (input.molecularView descriptorMap target) resultL.prior ordinaryBuiltL
  have sameR := subtree_constitution_eq_ordinary traceR target
    (input.molecularView descriptorMap target) resultR.prior ordinaryBuiltR
  have constTie := constitutional_eq_of_full_eq resultL.prior resultR.prior tie
  have compared := ruleMajor_compare_congr treeKeyL.constitutional treeKeyR.constitutional
    resultL.prior.prior.rule4aKey.constitutional
    resultR.prior.prior.rule4aKey.constitutional sameL sameR
  rw [← compared] at constTie
  exact (OfficialSparseCanonicalVectorComparison.compare_eq_iff_vector_eq
    (wellFormedRuleMajorKey_of_tableMatch
      (LocalizedRuleMajorSortTrace.fullMatch_of_trace traceL).tableMatch
      (LocalizedRuleMajorSortTrace.realizes_of_trace traceL))
    (wellFormedRuleMajorKey_of_tableMatch
      (LocalizedRuleMajorSortTrace.fullMatch_of_trace traceR).tableMatch
      (LocalizedRuleMajorSortTrace.realizes_of_trace traceR))
    (ruleKeyWithObservations_vectorWellShaped (ruleMajorTreeGraph treeL) (observe treeL) W D
      (ruleMajorTreeGraph treeL).root)
    (ruleKeyWithObservations_vectorWellShaped (ruleMajorTreeGraph treeR) (observe treeR) W D
      (ruleMajorTreeGraph treeR).root)
    (observedTree_node_bridge treeL (observe treeL) (observe_of_lookup treeL) widthL heightL
      (ruleMajorTreeGraph treeL).root treeL treeKeyL traceL (by
        change treeL.decoratedSubtreeAt? [] = some treeL
        rw [decoratedSubtreeAt?])).2
    (observedTree_node_bridge treeR (observe treeR) (observe_of_lookup treeR) widthR heightR
      (ruleMajorTreeGraph treeR).root treeR treeKeyR traceR (by
        change treeR.decoratedSubtreeAt? [] = some treeR
        rw [decoratedSubtreeAt?])).2).mp constTie

/-! ## The reconstruction from an actual built joint tie

The hypotheses are exactly the actual runtime objects: two realized arm trees with their
rule-major traces, the two successful joint builds at the fixed target/view/references, and a
joint-key tie at the built keys.  The conclusion constructs, in one step:

* the pair of joint-canonical addressings on which every reference mark agrees;
* equality of every constitutional observation, hence equality of occupied positions;
* one address-aligned hierarchy equivalence of the two arm hierarchies;
* preservation of every retained mark coordinate under that equivalence;
* the listed-reference atom predicate at every jointly occupied address.

No common isomorphism, occupancy equality or label equality is assumed. -/
theorem joint_built_tie_reconstruction
    (input : CertifiedLocalizedCIPInput)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (fallback : CompleteLigandRule5Key)
    (references : List input.Atom) (W D : Nat)
    {stageL stageR : LocalizedCumulativeRule45Stage}
    {readL readR : input.LocalizedRerootCursor (retainedCarrierFuel input) →
      Option LocalizedAuxiliaryLabel}
    {fuelL fuelR : Nat}
    {treeL treeR : LocalizedCumulativeDecoratedTree input (retainedCarrierFuel input)}
    {treeKeyL treeKeyR : input.LocalizedRerootCumulativeRule45Key}
    (traceL : LocalizedRuleMajorSortTrace input stageL readL fuelL treeL treeKeyL)
    (traceR : LocalizedRuleMajorSortTrace input stageR readR fuelR treeR treeKeyR)
    (realL : LocalizedCumulativeTreeRealizes input readL treeL)
    (realR : LocalizedCumulativeTreeRealizes input readR treeR)
    (tetrahedral : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (single : input.moleculeGraph.SimpleBonded)
    (rootChildL : treeL.source ∈ input.executableLocalizedRerootChildren ⟨target, none⟩)
    (rootChildR : treeR.source ∈ input.executableLocalizedRerootChildren ⟨target, none⟩)
    (resultL resultR : JointPromotedKey input)
    (builtL : buildJoint? input target (input.molecularView descriptorMap target) references W D
      fuelL treeL.source = some resultL)
    (builtR : buildJoint? input target (input.molecularView descriptorMap target) references W D
      fuelR treeR.source = some resultR)
    (tie : compareJointKeys input resultL resultR = .eq)
    (branchL : ∀ node, ((ruleMajorTreeGraph treeL).childList node).length ≤ W)
    (heightL : (ruleMajorTreeGraph treeL).height ≤ D)
    (branchR : ∀ node, ((ruleMajorTreeGraph treeR).childList node).length ≤ W)
    (heightR : (ruleMajorTreeGraph treeR).height ≤ D)
    (baseL : (ruleMajorTreeGraph treeL).Addressing)
    (baseR : (ruleMajorTreeGraph treeR).Addressing) :
    ∃ (matched : MatchedJointMarkerAddressings (ruleMajorTreeGraph treeL)
        (ruleMajorTreeGraph treeR)
        (deepPrior descriptorMap target fallback treeL)
        (deepPrior descriptorMap target fallback treeR)
        (referenceMarks input references treeL) (referenceMarks input references treeR)
        references.length W D)
      (equiv : AlignedHierarchyEquiv matched.leftAddressing matched.rightAddressing),
      (∀ rule position,
        LocalizedChemicalRingPromotedConstitutionReadback.observationAt
            (ruleMajorTreeGraph treeL) (observe treeL) matched.leftAddressing rule position =
          LocalizedChemicalRingPromotedConstitutionReadback.observationAt
            (ruleMajorTreeGraph treeR) (observe treeR) matched.rightAddressing rule position) ∧
      (∀ position, (∃ node, matched.leftAddressing.address node = position) ↔
        (∃ node, matched.rightAddressing.address node = position)) ∧
      (∀ (index : Nat), index < references.length → ∀ x,
        (referenceMarks input references treeL x).getD index 0 =
          (referenceMarks input references treeR (equiv.toEquiv x)).getD index 0) ∧
      (∀ (x : (ruleMajorTreeGraph treeL).Node) (y : (ruleMajorTreeGraph treeR).Node),
        matched.leftAddressing.address x = matched.rightAddressing.address y →
          ∀ (index : Nat) (bound : index < references.length),
            (nodeSource input treeL x).occurrence.1.node.current? = some references[index] ↔
              (nodeSource input treeR y).occurrence.1.node.current? = some references[index]) := by
  have ordinary := (compareJointKeys_eq_iff input resultL resultR).1 tie
  have agreeL := deepPrior_agreement descriptorMap target fallback treeL realL tetrahedral single
    rootChildL
  have agreeR := deepPrior_agreement descriptorMap target fallback treeR realR tetrahedral single
    rootChildR
  obtain ⟨matched⟩ := matched_joint_marker_addressings_of_built_tie input target
    (input.molecularView descriptorMap target) references W D treeL treeR realL realR
    (deepPrior descriptorMap target fallback treeL)
    (deepPrior descriptorMap target fallback treeR) agreeL agreeR fuelL fuelR resultL resultR
    builtL builtR tie branchL heightL branchR heightR baseL baseR
  let cW := max (ruleMajorTreeGraph treeL).width (ruleMajorTreeGraph treeR).width
  let cD := max (ruleMajorTreeGraph treeL).height (ruleMajorTreeGraph treeR).height
  have widthL : (ruleMajorTreeGraph treeL).width ≤ cW := le_max_left _ _
  have widthR : (ruleMajorTreeGraph treeR).width ≤ cW := le_max_right _ _
  have depthL : (ruleMajorTreeGraph treeL).height ≤ cD := le_max_left _ _
  have depthR : (ruleMajorTreeGraph treeR).height ≤ cD := le_max_right _ _
  have priorSortedL := matched.prior_sorted.1
  have priorSortedR := matched.prior_sorted.2
  have sortedL := constitution_sorted_of_prior_sorted descriptorMap target fallback traceL
    tetrahedral single rootChildL cW cD widthL depthL priorSortedL
  have sortedR := constitution_sorted_of_prior_sorted descriptorMap target fallback traceR
    tetrahedral single rootChildR cW cD widthR depthR priorSortedR
  have keys := built_constitution_keys_eq input descriptorMap target traceL traceR references
    W D cW cD builtL builtR ordinary.1 widthL depthL widthR depthR
  have same := observations_eq_of_root_keys_eq (ruleMajorTreeGraph treeL) (observe treeL)
    (ruleMajorTreeGraph treeR) (observe treeR) cW cD widthL depthL widthR depthR
    matched.leftAddressing matched.rightAddressing matched.leftCanonical.1 matched.rightCanonical.1
    sortedL sortedR keys
  have occupied := occupied_iff_of_observations_eq (ruleMajorTreeGraph treeL) (observe treeL)
    (ruleMajorTreeGraph treeR) (observe treeR) matched.leftAddressing matched.rightAddressing same
  obtain ⟨equiv⟩ := exists_aligned_hierarchy_equiv matched.leftAddressing
    matched.rightAddressing occupied
  exact ⟨matched, equiv, same, occupied,
    fun index bound x => aligned_hierarchy_marks_preserved (matched := matched) (equiv := equiv)
      index bound x,
    fun x y address index bound =>
      reference_atoms_iff_of_matched_joint_addresses treeL treeR references W D matched x y
        address index bound⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerReconstruction

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerReconstruction.AlignedHierarchyEquiv
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerReconstruction.exists_aligned_hierarchy_equiv
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerReconstruction.AlignedHierarchyEquiv.map_depth
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerReconstruction.aligned_hierarchy_marks_preserved
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerReconstruction.constitution_sorted_of_prior_sorted
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerReconstruction.joint_constitution_sorted
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerReconstruction.built_constitution_keys_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerReconstruction.joint_built_tie_reconstruction
