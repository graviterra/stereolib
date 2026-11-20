import TetraStereo.OneCenter.LocalizedChemicalRingPromotedConstitutionReadback
import TetraStereo.OneCenter.LocalizedChemicalRingReaddressedSource
import TetraStereo.OneCenter.LocalizedChemicalRingReferencePathReconstruction
import TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Actual promoted-key ties reconstruct a reference-fixing molecular automorphism

The constitutional and marker observations are read at the same constructed promoted
addresses. Readdressing preserves the complete source payload and generatedness, allowing
the existing boundary reconstruction to produce one automorphism, with no assumed path
map or automorphism. This is a molecular-graph statement; tetrahedral parity preservation
is a separate obligation.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingActualReferenceFixing

open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
open LocalizedCumulativeDecoratedTree LocalizedMarkedRetainedCanonicalMarker
open LocalizedMarkedRetainedPromotedKey LocalizedMarkedRetainedCanonicalFrame
open LocalizedMarkedRetainedSubtreeContext
open LocalizedChemicalRingPromotedColorReadback LocalizedChemicalRingReaddressedSource
open LocalizedChemicalRingPromotedConstitutionReadback
open LocalizedChemicalRingReferencePathReconstruction LocalizedActualBoundaryPathRealization

noncomputable section
open scoped Classical

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}

/-- The complete official payload is the node of the actual hierarchy cursor. -/
theorem payload_eq_source (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (node : (ruleMajorTreeGraph tree).Node) :
    payload (toOfficialSourceTree tree) node = (nodeSource input tree node).occurrence.1.node := by
  obtain ⟨sub, lookup⟩ := exists_local_subtree tree node
  rw [payload_of_lookup (toOfficialSourceTree tree) node (toOfficialSourceTree sub)
    (by rw [toOfficialSourceTree_subtreeAt?, decoratedSubtreeAt?_eq_subtreeAt?, lookup]; rfl),
    nodeSource_of_lookup input tree lookup, toOfficialSourceTree_source]

theorem readdressed_lookup_none (tree : OfficialCIPSourceTree input.Atom)
    (addressing : tree.toDeclarativeDigraph.Addressing) (dense : Dense addressing)
    (position : List Nat) (absent : ∀ node, addressing.address node ≠ position) :
    (readdressed tree addressing dense).sourceAtAddress? position = none := by
  cases found : (readdressed tree addressing dense).sourceAtAddress? position with
  | none => rfl
  | some source =>
      obtain ⟨node, address, _⟩ := (readdressed_lookup_iff tree addressing dense position source).mp found
      exact False.elim (absent node address)

/-- Readdressing the complete source payload reads the exact promoted reference marker. -/
theorem readdressed_referenceAt_eq (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (addressing : (ruleMajorTreeGraph tree).Addressing) (dense : Dense addressing)
    (reference : input.Atom) (position : List Nat) :
    referenceAt (readdressed (toOfficialSourceTree tree) addressing dense) reference position =
      PromotedCanonical.addressMarker (referenceMark input reference tree) addressing position := by
  by_cases present : ∃ node, addressing.address node = position
  · obtain ⟨node, address⟩ := present
    have lookup := (readdressed_lookup_iff (toOfficialSourceTree tree) addressing dense position
      (payload (toOfficialSourceTree tree) node)).mpr ⟨node, address, rfl⟩
    rw [referenceAt, lookup, Option.map_some, Option.getD_some, ← address,
      PromotedCanonical.addressMarker_of_address, payload_eq_source]
    rfl
  · rw [referenceAt, readdressed_lookup_none _ addressing dense position (by simpa using present)]
    rw [PromotedCanonical.addressMarker_of_unoccupied
      (referenceMark input reference tree) addressing (by simpa using present)]
    rfl

/-- All three constitutional columns at one common occupied address recover the official
atomic label and the stored ring-closure distance. -/
theorem matched_node_constitution
    (left right : LocalizedCumulativeDecoratedTree input carrierFuel)
    {readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (realizesL : LocalizedCumulativeTreeRealizes input readL left)
    (realizesR : LocalizedCumulativeTreeRealizes input readR right)
    (addressL : (ruleMajorTreeGraph left).Addressing)
    (addressR : (ruleMajorTreeGraph right).Addressing)
    (same : ∀ rule position,
      LocalizedChemicalRingPromotedConstitutionReadback.observationAt
        (ruleMajorTreeGraph left) (observe left) addressL rule position =
      LocalizedChemicalRingPromotedConstitutionReadback.observationAt
        (ruleMajorTreeGraph right) (observe right) addressR rule position)
    (x : (ruleMajorTreeGraph left).Node) (y : (ruleMajorTreeGraph right).Node)
    (address : addressL.address x = addressR.address y) :
    (input.moleculeGraph.officialNodeAtomLabel (payload (toOfficialSourceTree left) x),
      (payload (toOfficialSourceTree left) x).rule1bRootDistance) =
    (input.moleculeGraph.officialNodeAtomLabel (payload (toOfficialSourceTree right) y),
      (payload (toOfficialSourceTree right) y).rule1bRootDistance) := by
  have observations (rule : ConstitutionalRule) :
      armSourceObservation input rule (nodeSource input left x) =
        armSourceObservation input rule (nodeSource input right y) := by
    have h := same rule (addressL.address x)
    rw [observationAt_of_address, address, observationAt_of_address] at h
    have values : observe left rule x = observe right rule y := WithBot.coe_injective h
    rw [observe_eq_source left realizesL, observe_eq_source right realizesR] at values
    exact priorityValue_injective rule values
  rw [payload_eq_source, payload_eq_source]
  exact Prod.ext (ofLex_inj.mp (Prod.ext
    (observations .rule1aAtomicNumber) (observations .rule2AtomicMass)))
    (observations .rule1bDuplicateNodeProximity)

/-- Constitutional observations, including absence, survive the common promoted readdressing. -/
theorem readdressed_constitution_eq
    (left right : LocalizedCumulativeDecoratedTree input carrierFuel)
    {readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (realizesL : LocalizedCumulativeTreeRealizes input readL left)
    (realizesR : LocalizedCumulativeTreeRealizes input readR right)
    (addressL : (ruleMajorTreeGraph left).Addressing)
    (addressR : (ruleMajorTreeGraph right).Addressing)
    (denseL : Dense addressL) (denseR : Dense addressR)
    (same : ∀ rule position,
      LocalizedChemicalRingPromotedConstitutionReadback.observationAt
        (ruleMajorTreeGraph left) (observe left) addressL rule position =
      LocalizedChemicalRingPromotedConstitutionReadback.observationAt
        (ruleMajorTreeGraph right) (observe right) addressR rule position)
    (occupied : ∀ position, (∃ node, addressL.address node = position) ↔
      (∃ node, addressR.address node = position)) (position : List Nat) :
    constitutionalObservationAt input.moleculeGraph
      (readdressed (toOfficialSourceTree left) addressL denseL) position =
    constitutionalObservationAt input.moleculeGraph
      (readdressed (toOfficialSourceTree right) addressR denseR) position := by
  unfold constitutionalObservationAt
  by_cases present : ∃ node, addressL.address node = position
  · obtain ⟨x, hx⟩ := present
    obtain ⟨y, hy⟩ := (occupied position).mp ⟨x, hx⟩
    rw [(readdressed_lookup_iff _ addressL denseL position _).mpr ⟨x, hx, rfl⟩,
      (readdressed_lookup_iff _ addressR denseR position _).mpr ⟨y, hy, rfl⟩,
      Option.map_some, Option.map_some]
    exact congrArg some (matched_node_constitution left right realizesL realizesR
      addressL addressR same x y (hx.trans hy.symm))
  · have absentR : ¬ ∃ node, addressR.address node = position :=
      fun h => present ((occupied position).mpr h)
    rw [readdressed_lookup_none _ addressL denseL position (by simpa using present),
      readdressed_lookup_none _ addressR denseR position (by simpa using absentR)]

/-- Boundary-rootedness is independent of the sibling addressing. -/
theorem readdressed_boundaryRooted {B : List input.Atom} {a : input.Atom}
    (tree : OfficialCIPSourceTree input.Atom) (addressing : tree.toDeclarativeDigraph.Addressing)
    (dense : Dense addressing) (rooted : BoundaryRootedTree input B a tree) :
    BoundaryRootedTree input B a (readdressed tree addressing dense) :=
  ⟨readdressed_generated tree addressing dense _ rooted.generated,
    (readdressed_source tree addressing dense).trans rooted.root, rooted.nodup⟩

open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedMolecularSelection

/-- At an actual original-root frame, every slot tree is generated below the singleton
center boundary. The incoming-parent and source-generation facts are derived from the frame. -/
theorem root_slot_boundary (single : input.moleculeGraph.SimpleBonded)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (frame : RetainedExecutionFrame descriptorMap target)
    (rootAddress : target.1.address = []) (slot : Fin 4) (atom : input.Atom)
    (current : (frame.frame.cursorAt slot).occurrence.1.node.current? = some atom) :
    BoundaryRootedTree input [target.1.root] atom
      (toOfficialSourceTree (frame.stages slot).a.tree) ∧
      input.moleculeGraph.Adj atom target.1.root := by
  have computed : input.localizedOccurrenceFourLigandFrame? target = some frame.frame := by
    rw [← input.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame? target]
    exact frame.frameComputed
  have present : frame.frame.cursorAt slot ∈ frame.frame.cursors :=
    List.get_mem frame.frame.cursors (Fin.cast frame.frame.length_eq.symm slot)
  have outward := input.localizedOccurrenceFourLigandFrame_cursor_mem_neighborFrames
    target frame.frame computed _ present
  rw [input.localizedRerootNeighborFrames_eq_outwardChildFrames_of_address_nil target rootAddress]
    at outward
  have targetNode : target.1.node = OfficialCIPNode.root target.1.root := by
    have equality := input.declarativeLocalizedOccurrence_eq_root_of_address_nil
      ((input.mem_localizedOccurrences_iff _ _).mp target.2) rootAddress
    have nodes := congrArg (fun occurrence => occurrence.node) equality
    simpa using nodes
  have targetCurrent : target.1.node.current? = some target.1.root := by
    rw [targetNode]
    rfl
  have targetReal : target.1.node.provenance = .realAtom := by rw [targetNode]; rfl
  obtain ⟨neighbor, childSlot, nodeEq, neighborCurrent, rootEq, addressEq, _, _, adjacent⟩ :=
    input.simpleBond_outwardFrame_extend_zero single target targetCurrent targetReal _ outward
  have neighborEq : neighbor = atom := Option.some.inj (neighborCurrent.symm.trans current)
  subst neighbor
  have fresh : atom ∉ target.1.node.history := by
    rw [targetNode]
    change atom ∉ [target.1.root]
    intro member
    have equality := List.mem_singleton.mp member
    subst atom
    simp [MoleculeGraph.Adj, input.moleculeGraph.bond_self] at adjacent
  have childReal : (frame.frame.cursorAt slot).occurrence.1.node.provenance = .realAtom := by
    rw [nodeEq, OfficialCIPNode.extend_provenance,
      OfficialCIPNode.childProvenance_real _ _ fresh]
  have previous := input.localizedOccurrenceFourLigandFrame_cursor_previous
    target frame.frame computed _ present
  have incoming : LocalizedRerootCursorIncomingParent input (frame.frame.cursorAt slot) := by
    refine ⟨target, previous, rootEq.symm, ?_, ?_⟩
    · simp [addressEq]
    · simp [addressEq]
  have realizes := LocalizedRuleMajorSortTrace.realizes_of_trace (frame.stages slot).a.trace
  have treeIncoming := input.localizedCumulativeTreeIncoming_of_realizes _ _ realizes
    (by rw [(frame.stages slot).a.sourceEq]; exact incoming)
  have positive := input.localizedCumulativeTreePositive_of_atomCount_le
    (fuel := retainedCarrierFuel input) (by unfold retainedCarrierFuel; omega)
    (frame.stages slot).a.tree
  have generated := input.toOfficialSourceTree_generatedBy _ _ realizes positive treeIncoming
  obtain ⟨rooted, _, _⟩ := LocalizedActualBoundaryObservationReadback.outwardChild_boundaryRooted
    input single ⟨target, none⟩ (frame.frame.cursorAt slot) rootEq childSlot addressEq targetReal
    childReal current (frame.stages slot).a.tree (frame.stages slot).a.sourceEq generated
  have rooted' : BoundaryRootedTree input [target.1.root] atom
      (toOfficialSourceTree (frame.stages slot).a.tree) := by
    simpa only [targetNode, OfficialCIPNode.root, List.reverse_singleton] using rooted
  exact ⟨rooted', input.moleculeGraph.adj_symm.mp adjacent⟩

section Actual

open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedPromotedRanking
open LocalizedMarkedRetainedStateReader LocalizedMarkedRetainedMolecularSelection

variable (input : CertifiedLocalizedCIPInput) (single : input.moleculeGraph.SimpleBonded)
  (state : OccurrenceAuxState) (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
  (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
  (unit : DetectedOccurrence input.moleculeGraph) (targetUnit : input.molecularFrameUnit target.1 = unit.1)
  (reference : input.Atom) (W D : Nat) (fallback : CompleteLigandRule5Key)

include fallback

/-- An equality of actual refined keys reconstructs one boundary- and reference-fixing
automorphism. Boundary-rootedness concerns the actual arm source, not a supplied isomorphism. -/
theorem actual_tie_reference_fixed_aut (left right : Fin 4)
    (widthL : ∀ node, ((ruleMajorTreeGraph (slotTree input single state target real unit targetUnit left)).childList node).length ≤ W)
    (heightL : (ruleMajorTreeGraph (slotTree input single state target real unit targetUnit left)).height ≤ D)
    (widthR : ∀ node, ((ruleMajorTreeGraph (slotTree input single state target real unit targetUnit right)).childList node).length ≤ W)
    (heightR : (ruleMajorTreeGraph (slotTree input single state target real unit targetUnit right)).height ≤ D)
    (tie : refinedKey input single state target real unit targetUnit reference W D left =
      refinedKey input single state target real unit targetUnit reference W D right)
    (B : List input.Atom) (a b : input.Atom)
    (rootedL : BoundaryRootedTree input B a
      (toOfficialSourceTree (slotTree input single state target real unit targetUnit left)))
    (rootedR : BoundaryRootedTree input B b
      (toOfficialSourceTree (slotTree input single state target real unit targetUnit right)))
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (parentL : ∀ z, B.getLast? = some z → input.moleculeGraph.Adj a z)
    (parentR : ∀ z, B.getLast? = some z → input.moleculeGraph.Adj b z) :
    ∃ π : Equiv.Perm input.Atom, input.moleculeGraph.IsAutomorphism π ∧
      (∀ z ∈ B, π z = z) ∧ π a = b ∧ π reference = reference := by
  obtain ⟨matched, same, occupied⟩ := actual_tie_joint_readback input single state target real unit
    targetUnit reference W D fallback left right widthL heightL widthR heightR tie
  let treeL := slotTree input single state target real unit targetUnit left
  let treeR := slotTree input single state target real unit targetUnit right
  have constitution := readdressed_constitution_eq treeL treeR
    (LocalizedRuleMajorSortTrace.realizes_of_trace
      ((frames input single state target real unit targetUnit).stages left).a.trace)
    (LocalizedRuleMajorSortTrace.realizes_of_trace
      ((frames input single state target real unit targetUnit).stages right).a.trace)
    matched.leftAddressing matched.rightAddressing matched.leftCanonical.1
    matched.rightCanonical.1 same occupied
  have pair := observedTreePair_of_constitutional single
    (readdressed_boundaryRooted _ matched.leftAddressing matched.leftCanonical.1 rootedL)
    (readdressed_boundaryRooted _ matched.rightAddressing matched.rightCanonical.1 rootedR)
    rfl constitution
  apply exists_reference_fixed_aut pair charge parentL parentR reference
  intro position
  rw [readdressed_referenceAt_eq, readdressed_referenceAt_eq]
  exact matched.same position

/-- At an actual root occurrence, a promoted tie constructs a single molecular automorphism
fixing both the center and selected reference and sending the left slot atom to the right.
No generated-tree, common-address, path-equivalence or automorphism premise is supplied. -/
theorem actual_root_tie_reference_fixed_aut (rootAddress : target.1.address = [])
    (left right : Fin 4)
    (widthL : ∀ node, ((ruleMajorTreeGraph (slotTree input single state target real unit targetUnit left)).childList node).length ≤ W)
    (heightL : (ruleMajorTreeGraph (slotTree input single state target real unit targetUnit left)).height ≤ D)
    (widthR : ∀ node, ((ruleMajorTreeGraph (slotTree input single state target real unit targetUnit right)).childList node).length ≤ W)
    (heightR : (ruleMajorTreeGraph (slotTree input single state target real unit targetUnit right)).height ≤ D)
    (tie : refinedKey input single state target real unit targetUnit reference W D left =
      refinedKey input single state target real unit targetUnit reference W D right)
    (a b : input.Atom)
    (currentL : ((frames input single state target real unit targetUnit).frame.cursorAt left).occurrence.1.node.current? = some a)
    (currentR : ((frames input single state target real unit targetUnit).frame.cursorAt right).occurrence.1.node.current? = some b)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph) :
    ∃ π : Equiv.Perm input.Atom, input.moleculeGraph.IsAutomorphism π ∧
      π target.1.root = target.1.root ∧ π a = b ∧ π reference = reference := by
  obtain ⟨rootedL, adjacentL⟩ := root_slot_boundary single (rawStateDescriptorMap input state)
    target (frames input single state target real unit targetUnit) rootAddress left a currentL
  obtain ⟨rootedR, adjacentR⟩ := root_slot_boundary single (rawStateDescriptorMap input state)
    target (frames input single state target real unit targetUnit) rootAddress right b currentR
  obtain ⟨π, aut, fixed, image, ref⟩ := actual_tie_reference_fixed_aut input single state target real
    unit targetUnit reference W D fallback left right widthL heightL widthR heightR tie
    [target.1.root] a b rootedL rootedR charge
    (by
      intro z hz
      have equality : target.1.root = z := by simpa using hz
      rw [← equality]
      exact adjacentL)
    (by
      intro z hz
      have equality : target.1.root = z := by simpa using hz
      rw [← equality]
      exact adjacentR)
  exact ⟨π, aut, fixed _ (by simp), image, ref⟩

end Actual

end
end TetraStereo.OneCenter.LocalizedChemicalRingActualReferenceFixing

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingActualReferenceFixing.payload_eq_source
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingActualReferenceFixing.readdressed_referenceAt_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingActualReferenceFixing.matched_node_constitution
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingActualReferenceFixing.readdressed_constitution_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingActualReferenceFixing.readdressed_boundaryRooted
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingActualReferenceFixing.root_slot_boundary
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingActualReferenceFixing.actual_tie_reference_fixed_aut
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingActualReferenceFixing.actual_root_tie_reference_fixed_aut
