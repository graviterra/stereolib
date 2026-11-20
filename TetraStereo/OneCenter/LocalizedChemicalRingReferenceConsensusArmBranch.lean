import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitKeySeparation
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherArmSymmetry
import TetraStereo.OneCenter.LocalizedChemicalRingMovedSlotEligibility
import TetraStereo.OneCenter.LocalizedRuleMajorRule4aAgreement
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-!
Every actual occurrence below any of the four root arms lies in an actually tied root branch.
The two successful arm builds and their Rule-1a tie are derived from the explicit arm-exchange
automorphisms; the branch prefix is read from the occurrence's actual lookup history. The
accepted branch certificates cover two specific occurrences; here the target is arbitrary.
No auxiliary descriptor or physical correctness is asserted.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusArmBranch

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedChemicalRingReferenceOrbitInput LocalizedChemicalRingReferenceOrbitKeySeparation
open LocalizedChemicalRingReferenceOrbitArmSymmetry LocalizedChemicalRingReferenceOrbitOtherArmSymmetry
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
open LocalizedPhysicalMarkedParityCompleteness

noncomputable section
open scoped Classical

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

/-- The raw history of a descendant of an arm child ends with that arm and the root. -/
theorem descends_history (arm : Nat) (node : RawMolecule.CanonicalBranchNode)
    (path : Descends mol (nodeOf [0, arm]) node) : ∃ rest, node.history = rest ++ [arm, 0] := by
  induction path with
  | refl => exact ⟨[], rfl⟩
  | @tail parent child _ edge ih =>
      obtain ⟨rest, same⟩ := ih
      have facts := LocalizedGenericMarkedRecalculation.mem_canonicalChildren mol parent child edge
      exact ⟨child.atom :: rest, by rw [facts.1, same]; rfl⟩

private theorem branch_of_aut (e : physical.Aut)
    (historyFixed : ∀ value ∈ (canonicalCenterRoot 0).history,
      LocalizedChemicalRingPhysicalSense.relabelOf certified e.val value = value)
    (a b : Fin 46) (adjacent : physical.mol.Adj rootCenter.1 a) (image : e.val a = b)
    (different : a ≠ b)
    (c : physical.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData certified mol c node)
    (path : Descends mol (nodeOf [0, a.val]) node) :
    Nonempty (TiedRootBranch certified data.target) := by
  obtain ⟨p, action, keys⟩ := actual_slot_key_action certified mol structure_agreement admissible
    supported single_bonded e rootCenter (canonicalCenterRoot 0) rootData
    (reached_root mol 0 (by decide)) historyFixed
  obtain ⟨ligand, atA⟩ := physical.ligandAtomAt_surjective rootCenter a adjacent
  let left := rootData.ligandOf.symm ligand
  let right := p left
  have referenceL : referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData left = a := by
    simp only [referenceAt, left, Equiv.apply_symm_apply, atA]
  have referenceR : referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData right = b := by
    rw [action, referenceL]
    exact image
  have slotL := root_slot left
  have slotR := root_slot right
  dsimp only at slotL slotR
  rw [referenceL] at slotL
  rw [referenceR] at slotR
  obtain ⟨rest, rawHistory⟩ := descends_history a.val node path
  have mapped := (lookup?_sound certified _ _ data.found).history
  rw [rawHistory] at mapped
  obtain ⟨front, back, whole, frontMap, backMap⟩ := List.map_eq_append_iff.mp mapped
  have backEq : back = [a, (0 : Fin 46)] := by
    apply List.map_injective_iff.mpr Fin.val_injective
    exact backMap
  subst backEq
  have packed := certified.legitimateOccurrence_transport single_bonded 1
    (certified.carrierOccurrence_legitimate single_bonded data.target)
  have reverseEq : data.target.1.node.history.reverse = (0 : Fin 46) :: a :: front.reverse := by
    rw [whole]
    simp
  have targetRoot : data.target.1.root = (0 : Fin 46) := by
    apply Option.some.inj
    simpa only [reverseEq, List.head?_cons] using packed.sourceHead.symm
  have targetNonroot : data.target.1.address ≠ [] := by
    intro empty
    have length := congrArg List.length packed.sourceAddress
    rw [empty] at length
    simp only [CertifiedLocalizedCIPInput.canonicalAddress, reverseEq, List.tail_cons,
      CertifiedLocalizedCIPInput.foldSlots_length, List.length_cons, List.length_nil] at length
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
    exact different (Option.some.inj h)
  · have armAddress := (certified.legitimateOccurrence_transport single_bonded 1
      (certified.carrierOccurrence_legitimate single_bonded
        (rootExecution.frame.cursorAt left).occurrence)).sourceAddress
    refine ⟨slotL.1.trans targetRoot.symm, ?_⟩
    rw [armAddress, packed.sourceAddress, slotL.1, targetRoot]
    simp only [CertifiedLocalizedCIPInput.canonicalAddress, slotL.2.2.1, reverseEq,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append, List.tail_cons]
    simp
    exact ⟨_, rfl⟩

/-- Every actual occurrence descending from one of the four root arm children lies in a tied
root branch, without any premise on the occurrence beyond its actual descent. -/
theorem arm_tied_branch (a : Fin 46) (allowed : a = 28 ∨ a = 29 ∨ a = 30 ∨ a = 31)
    (c : physical.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData certified mol c node)
    (path : Descends mol (nodeOf [0, a.val]) node) :
    Nonempty (TiedRootBranch certified data.target) := by
  rcases allowed with rfl | rfl | rfl | rfl
  · exact branch_of_aut physicalAut raw_root_history_fixed 28 29 (by decide +kernel) rfl (by decide)
      c node data path
  · exact branch_of_aut physicalAut raw_root_history_fixed 29 28 (by decide +kernel) rfl (by decide)
      c node data path
  · exact branch_of_aut otherPhysicalAut other_root_history_fixed 30 31 (by decide +kernel) rfl
      (by decide) c node data path
  · exact branch_of_aut otherPhysicalAut other_root_history_fixed 31 30 (by decide +kernel) rfl
      (by decide) c node data path

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusArmBranch

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusArmBranch.descends_history
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusArmBranch.arm_tied_branch
