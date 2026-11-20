import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherArmSymmetry
import TetraStereo.OneCenter.LocalizedChemicalRingMovedSlotEligibility
import TetraStereo.OneCenter.LocalizedRuleMajorRule4aAgreement
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitStabilizer
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

/-!
A second actual covering path begins in root arm 30 and ends at center 26, visiting
every detected center. Its first edge is selected by the actual empty-state ordinary
comparison through an explicit graph automorphism. Subsequent canonical descent,
structural budget, tied carrier-branch membership and history rigidity are derived.
No descriptor success, coordinate calibration or physical orientation is asserted here.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherCoveringPath

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedChemicalRingReferenceOrbitInput LocalizedChemicalRingReferenceOrbitOtherArmSymmetry
open LocalizedChemicalRingInheritedRefusalCases LocalizedChemicalRingMovedSlotEligibility
open LocalizedChemicalRingSelectedRefusalWitness LocalizedChemicalRingSelectedOutwardTie
open LocalizedChemicalRingPromotedConstitutionReadback LocalizedCyclicGeneralRigidPriority
open LocalizedChemicalRingFrameReadback LocalizedMarkedCarrierLookup
open LocalizedMarkedRetainedCanonicalFrame LocalizedMarkedRetainedMolecularSelection
open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedPromotedRanking
open LocalizedMarkedRetainedStateReader LocalizedMarkedRetainedPromotedKey
open LocalizedActualBoundaryPathRealization LocalizedActualOutwardRule1bEquivalence
open LocalizedActualBoundaryObservationReadback
open LocalizedMarkedReachableConfigurations
open LocalizedMarkedTerminalReferenceScope (Descends)
open LocalizedMarkedOperationEvaluator (tiedChildren)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedGenericMarkedRecalculation (structuralDepth)
open LocalizedChemicalRingReferenceOrbitStabilizer
open LocalizedChemicalRingPhysicalSense (relabelOf relabelOf_val)

def otherPath : List (Fin 46) :=
  [0, 30, 34, 38, 42, 40, 3, 14, 8, 5, 2, 6, 9, 16, 4, 41, 43, 36, 32, 27, 26]

def otherNode : RawMolecule.CanonicalBranchNode := nodeOf (otherPath.map Fin.val)

theorem other_simple : otherPath.Nodup := by decide +kernel

theorem other_detected (a : Fin 46) (detected : a ∈ graph.tetrahedralCenterSet) :
    a ∈ otherPath := by
  rw [detected_inventory] at detected
  fin_cases a <;> simp_all [otherPath]

noncomputable section
open scoped Classical

private def rootCenter : physical.Center :=
  ⟨(0 : Fin 46), by
    change (0 : Fin 46) ∈ graph.tetrahedralCenterSet
    rw [detected_inventory]
    decide⟩

private def rootData : OccurrenceData certified mol rootCenter (canonicalCenterRoot 0) :=
  Classical.choice (occurrenceData_exists certified mol structure_agreement admissible supported
    single_bonded rootCenter (canonicalCenterRoot 0) (reached_root mol 0 (by decide)) rfl rfl)

private theorem option_val {value : Option (Fin 46)} {a : Fin 46}
    (same : value.map Fin.val = some a.val) : value = some a := by
  cases value with
  | none => cases same
  | some b => exact congrArg some (Fin.ext (Option.some.inj same))

private theorem root_history : rootData.target.1.node.history = [(0 : Fin 46)] := by
  apply List.map_injective_iff.mpr Fin.val_injective
  exact (lookup?_sound certified _ _ rootData.found).history

private theorem root_current : rootData.target.1.node.current? = some (0 : Fin 46) := by
  exact option_val (lookup?_sound certified _ _ rootData.found).current

private theorem root_address : rootData.target.1.address = [] := by
  have address := (certified.legitimateOccurrence_transport single_bonded 1
    (certified.carrierOccurrence_legitimate single_bonded rootData.target)).sourceAddress
  rw [address]
  simp [CertifiedLocalizedCIPInput.canonicalAddress, root_history]

private theorem root_root : rootData.target.1.root = (0 : Fin 46) := by
  have head := (certified.legitimateOccurrence_transport single_bonded 1
    (certified.carrierOccurrence_legitimate single_bonded rootData.target)).sourceHead
  simpa [root_history] using head.symm

private abbrev rootUnit : DetectedOccurrence certified.moleculeGraph :=
  ⟨certified.molecularFrameUnit rootData.target.1, rootData.detected⟩

private abbrev rootExecution :=
  frames certified single_bonded [] rootData.target rootData.real rootUnit rfl

private theorem root_frame_eq : rootExecution.frame = rootData.frame :=
  Option.some.inj (rootExecution.frameComputed.symm.trans rootData.frameExec)

private theorem root_frame_computed :
    certified.localizedOccurrenceFourLigandFrame? rootData.target = some rootExecution.frame := by
  rw [← certified.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?]
  exact rootExecution.frameComputed

/-- Each root slot is an actual real outward occurrence with its exact two-atom history. -/
private theorem root_slot (i : Fin 4) :
    let cursor := rootExecution.frame.cursorAt i
    let a := referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData i
    cursor.occurrence.1.root = (0 : Fin 46) ∧
    cursor.occurrence.1.node.current? = some a ∧
    cursor.occurrence.1.node.history = [a, (0 : Fin 46)] ∧
    cursor.occurrence.1.node.provenance = .realAtom := by
  dsimp only
  let cursor := rootExecution.frame.cursorAt i
  let a := referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData i
  have atAtom : cursor.occurrence.1.node.current? = some a := by
    apply option_val
    change atomAt certified rootExecution.frame i = some a.val
    rw [root_frame_eq]
    exact rootData.atomAt_eq i
  have outward := certified.localizedOccurrenceFourLigandFrame_root_all_outward
    rootData.target rootExecution.frame root_frame_computed root_address i
  obtain ⟨slot, address⟩ := outward.2
  have rootEq := outward.1.2.1.1
  have child := outwardChild_node_mem certified
    (⟨rootData.target, none⟩ : certified.LocalizedRerootCursor (retainedCarrierFuel certified))
    cursor rootEq slot address
  obtain ⟨next, nodeEq, adjacent, _⟩ :=
    (mem_executableOfficialCIPChildren_iff certified single_bonded _ root_current
      rootData.real _).mp child
  have nextEq : next = a := by
    rw [nodeEq] at atAtom
    exact Option.some.inj atAtom
  subst next
  have fresh : a ∉ rootData.target.1.node.history := by
    rw [root_history, List.mem_singleton]
    intro same
    rw [same] at adjacent
    exact (Nat.lt_irrefl 0) (by simpa only [MoleculeGraph.Adj, graph.bond_self] using adjacent)
  refine ⟨rootEq.trans root_root, atAtom, ?_, ?_⟩
  · rw [nodeEq]
    change a :: rootData.target.1.node.history = [a, (0 : Fin 46)]
    rw [root_history]
  · rw [nodeEq]
    exact (extend_rule1b_of_not_mem fresh).1

/-- The covering occurrence's carrier target retains the exact source path, independently of its
occurrence-frame presentation. -/
theorem other_history (c : physical.Center)
    (data : OccurrenceData certified mol c otherNode) :
    data.target.1.node.history = otherPath.reverse := by
  apply List.map_injective_iff.mpr Fin.val_injective
  have history := (lookup?_sound certified _ _ data.found).history
  simpa only [otherNode, nodeOf, List.map_reverse] using history

private theorem root_rule1a_tie {left right : Fin 4}
    (equal : ordinaryKeys certified mol single_bonded rootCenter (canonicalCenterRoot 0)
      rootData left = ordinaryKeys certified mol single_bonded rootCenter
      (canonicalCenterRoot 0) rootData right) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (rootExecution.stages left).a.key.constitutional.rule1a
      (rootExecution.stages right).a.key.constitutional.rule1a = .eq := by
  change rootExecution.retainedKeys rootUnit left = rootExecution.retainedKeys rootUnit right at equal
  have full := rootExecution.fullOrdering (rawStateDescriptorMap_tetrahedral certified [])
    single_bonded rootUnit rfl left right
  rw [equal, (completeLigandRule5Key_compare_eq_iff _ _).mpr rfl] at full
  have constitutional := constitutional_eq_of_full_eq
    (rootExecution.compounds left) (rootExecution.compounds right) full
  have ordinaryBuilt (slot : Fin 4) : ordinaryKey? certified rootData.target
      (certified.molecularView (rawStateDescriptorMap certified []) rootData.target)
      (rootExecution.stages slot).a.tree.source = some (rootExecution.compounds slot) := by
    rw [(rootExecution.stages slot).a.sourceEq]
    exact rootExecution.compoundBuilt slot
  have sameL := subtree_constitution_eq_ordinary (rootExecution.stages left).a.trace rootData.target
    (certified.molecularView (rawStateDescriptorMap certified []) rootData.target)
    (rootExecution.compounds left) (ordinaryBuilt left)
  have sameR := subtree_constitution_eq_ordinary (rootExecution.stages right).a.trace rootData.target
    (certified.molecularView (rawStateDescriptorMap certified []) rootData.target)
    (rootExecution.compounds right) (ordinaryBuilt right)
  have tied := (ruleMajor_compare_congr _ _ _ _ sameL sameR).trans constitutional
  unfold OfficialRuleMajorKey.compare at tied
  cases first : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (rootExecution.stages left).a.key.constitutional.rule1a
      (rootExecution.stages right).a.key.constitutional.rule1a <;>
    simp_all only [compareLex, Ordering.byKey, Ordering.then]

/-- Both arms, their successful actual builds, their Rule-1a tie, and the covering occurrence's
membership in the first arm are constructed from this certified input. -/
theorem other_tied_branch (c : physical.Center)
    (data : OccurrenceData certified mol c otherNode) :
    Nonempty (TiedRootBranch certified data.target) := by
  obtain ⟨p, action, keys⟩ := actual_slot_key_action certified mol structure_agreement admissible
    supported single_bonded otherPhysicalAut rootCenter (canonicalCenterRoot 0) rootData
    (reached_root mol 0 (by decide)) other_root_history_fixed
  obtain ⟨ligand, at30⟩ := physical.ligandAtomAt_surjective rootCenter (30 : Fin 46)
    (by decide +kernel)
  let left := rootData.ligandOf.symm ligand
  let right := p left
  have referenceL : referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData left =
      (30 : Fin 46) := by
    simp only [referenceAt, left, Equiv.apply_symm_apply, at30]
  have referenceR : referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData right =
      (31 : Fin 46) := by
    rw [action, referenceL]
    rfl
  have slotL := root_slot left
  have slotR := root_slot right
  dsimp only at slotL slotR
  rw [referenceL] at slotL
  rw [referenceR] at slotR
  have history := other_history c data
  have packed := certified.legitimateOccurrence_transport single_bonded 1
    (certified.carrierOccurrence_legitimate single_bonded data.target)
  have targetRoot : data.target.1.root = (0 : Fin 46) := by
    have h := packed.sourceHead
    apply Option.some.inj
    simpa only [history, List.reverse_reverse, otherPath, List.head?_cons] using h.symm
  have targetNonroot : data.target.1.address ≠ [] := by
    intro empty
    have length := congrArg List.length packed.sourceAddress
    rw [empty] at length
    simp only [CertifiedLocalizedCIPInput.canonicalAddress, history, List.reverse_reverse,
      otherPath, List.tail_cons, CertifiedLocalizedCIPInput.foldSlots_length,
      List.length_cons, List.length_nil] at length
    omega
  refine ⟨{
    rootCursor := ⟨rootData.target, none⟩
    rootAddress := root_address
    arm := rootExecution.frame.cursorAt left
    arm' := rootExecution.frame.cursorAt right
    member := rootExecution.childAt left
    member' := rootExecution.childAt right
    different := ?_
    real := slotL.2.2.2
    real' := slotR.2.2.2
    read := _
    read' := _
    fuel := 2 * (retainedCarrierFuel certified + 1)
    fuel' := 2 * (retainedCarrierFuel certified + 1)
    key := (rootExecution.stages left).a.key
    key' := (rootExecution.stages right).a.key
    built := (certified.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized _ _ _).symm.trans
      (rootExecution.stages left).a.built
    built' := (certified.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized _ _ _).symm.trans
      (rootExecution.stages right).a.built
    tie := root_rule1a_tie (keys left).symm
    inside := ?_
    nonroot := targetNonroot }⟩
  · intro same
    have h := congrArg (fun occurrence => occurrence.1.node.current?) same
    dsimp only at h
    rw [slotL.2.1, slotR.2.1] at h
    exact (by decide : (30 : Fin 46) ≠ 31) (Option.some.inj h)
  · have armAddress := (certified.legitimateOccurrence_transport single_bonded 1
      (certified.carrierOccurrence_legitimate single_bonded
        (rootExecution.frame.cursorAt left).occurrence)).sourceAddress
    refine ⟨slotL.1.trans targetRoot.symm, ?_⟩
    rw [armAddress, packed.sourceAddress, slotL.1, targetRoot]
    simp only [CertifiedLocalizedCIPInput.canonicalAddress, slotL.2.2.1, history,
      otherPath, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.cons_append, List.tail_cons]
    simp

/-- The same actual arm-exchange symmetry forces selection of the covering path's first
raw child in the empty-state ordinary comparison. -/
theorem other_selected_first_child :
    nodeOf [0, 30] ∈ tiedChildren mol (sparseOperations certified mol) []
      (canonicalCenterRoot 0) := by
  exact moved_child_selected certified mol structure_agreement admissible supported single_bonded
    otherPhysicalAut rootCenter (canonicalCenterRoot 0) rootData (reached_root mol 0 (by decide))
    other_root_history_fixed (30 : Fin 46) (by decide +kernel)
    (by change (31 : Fin 46) ≠ (30 : Fin 46); decide)
    (nodeOf [0, 30]) (by decide +kernel) rfl

private def remainingRoute (n : Nat) :=
  nodeOf ((otherPath.map Fin.val).take (n + 2))

private theorem remaining_edges (i : Fin 19) :
    remainingRoute (i.val + 1) ∈ mol.canonicalChildren (remainingRoute i.val) := by
  fin_cases i <;> decide +kernel

/-- All subsequent steps are actual canonical children; only the first edge needs
ordinary-key selection for the snapshot's recursive forest. -/
theorem other_raw_descent : Descends mol (nodeOf [0, 30]) otherNode := by
  have all : ∀ n : Nat, n ≤ 19 → Descends mol (remainingRoute 0) (remainingRoute n) := by
    intro n
    induction n with
    | zero => intro _; exact .refl
    | succ n ih =>
        intro bound
        exact (ih (by omega)).tail (remaining_edges ⟨n, by omega⟩)
  exact all 19 le_rfl

theorem other_structural_budget :
    otherNode.history.length ≤ structuralDepth mol (canonicalCenterRoot 0) +
      (canonicalCenterRoot 0).history.length := by decide +kernel

theorem other_reached : Reached mol otherNode := by
  have first : Reached mol (nodeOf [0, 30]) :=
    reached_child mol (canonicalCenterRoot 0) (nodeOf [0, 30])
      (reached_root mol 0 (by decide)) (by decide +kernel)
  exact LocalizedMarkedTerminalReferenceScope.descendant_reached first other_raw_descent

/-- The covering history itself fixes the molecular graph, independently of any mark. -/
theorem other_path_stabilizer (e : graph.Aut)
    (historyFixed : ∀ a ∈ otherPath, e.val a = a) : e.val = 1 := by
  have fixed28 : e.val (28 : Fin 46) = 28 := by
    apply fixed_of_signature graph e [0, 32] 28
    · intro a member
      have subset : ([0, 32] : List (Fin 46)) ⊆ otherPath := by decide +kernel
      exact historyFixed a (subset member)
    · unfold SignatureUnique
      decide +kernel
  apply shortcut_stabilizer e _ (historyFixed reference (by decide +kernel))
  intro a present
  have covered : a ∈ otherPath ∨ a = (28 : Fin 46) := by
    have finite : ∀ a : Fin 46, a ∈ shortcutPath → a ∈ otherPath ∨ a = 28 := by
      decide +kernel
    exact finite a present
  rcases covered with covered | same
  · exact historyFixed a covered
  · simpa only [same] using fixed28

theorem other_history_rigid (e : physical.Aut)
    (historyFixed : ∀ value ∈ otherNode.history, relabelOf certified e.val value = value) :
    e = 1 := by
  apply Subtype.ext
  apply other_path_stabilizer ⟨e.val, e.2.1⟩
  intro a present
  have inHistory : a.val ∈ otherNode.history :=
    List.mem_reverse.mpr (List.mem_map.mpr ⟨a, present, rfl⟩)
  have fixed := historyFixed a.val inHistory
  rw [relabelOf_val] at fixed
  exact Fin.ext fixed

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherCoveringPath

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherCoveringPath.other_history
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherCoveringPath.other_tied_branch
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherCoveringPath.other_selected_first_child
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherCoveringPath.other_raw_descent
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherCoveringPath.other_structural_budget

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherCoveringPath.other_simple
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherCoveringPath.other_detected
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherCoveringPath.other_reached
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherCoveringPath.other_path_stabilizer
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherCoveringPath.other_history_rigid
