import TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusSymmetry
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCoveringPath
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherArmSymmetry
import TetraStereo.OneCenter.LocalizedChemicalRingCoveredPathKeySeparation
import TetraStereo.OneCenter.LocalizedChemicalRingPrescribedPathFactMatch
import TetraStereo.OneCenter.LocalizedChemicalRingSelectedOutwardTie
import TetraStereo.OneCenter.LocalizedChemicalRingMovedSlotEligibility
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3200000

/-!
The depth-four occurrence `o+ = [0,28,32,27,26]` of center 26 inside root arm 28 is tied in
the empty state: an explicit O18-exchange fixes its history and moves 34 to 35. This module
proves that its ACTUAL marked keys for the inherited reference 28 nevertheless separate the
two O18 attachments, on the actual generated snapshot below `o+`.

A tie would reconstruct one molecular automorphism fixing the history of `o+` and 28 and
sending 34 to 35, together with a matched generated label at the end of the accepted
covering path `[0,28,32,27,26,34,38,42,40,3,14,8,15,4,16,9,6,2]`. The covered decoder makes
that automorphism proper at center 2, but every such map is odd at center 2.

This is the separation needed for reference independence at `o+`; the companion statement
that the empty marker of the absent reference 28 cannot decide this tie is a separate input.
No evaluator output, label value or physical sign is assumed.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusArmSeparation

open CertifiedLocalizedCIPInput DeclarativeCIP RetainedCoherentSymmetry
open LocalizedChemicalRingReferenceOrbitInput LocalizedChemicalRingReferenceOrbitCalibration
open LocalizedChemicalRingReferenceOrbitAllCalibration (otherCurrent)
open LocalizedChemicalRingReferenceOrbitCoveringPath LocalizedChemicalRingReferenceOrbitStabilizer
open LocalizedChemicalRingReferenceOrbitBranch LocalizedChemicalRingReferenceOrbitOtherArmSymmetry
open LocalizedChemicalRingReferenceConsensusSymmetry
open LocalizedChemicalRingInheritedRefusalCases LocalizedChemicalRingSelectedRefusalWitness
open LocalizedChemicalRingCoveredPathOrientation LocalizedChemicalRingBoundaryWitnessExecution
open LocalizedChemicalRingBoundaryWitnessFactMatch LocalizedChemicalRingWitnessFactMatch
open LocalizedChemicalRingPrescribedPathFactMatch LocalizedChemicalRingSelectedOutwardTie
open LocalizedMarkedRetainedCanonicalFrame LocalizedMarkedRetainedMolecularSelection
open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedPromotedRanking
open LocalizedChemicalRingPhysicalSense (inputGeometry relabelOf relabelOf_val)
open LocalizedMarkedReachableConfigurations (Reached reached_root reached_child)
open LocalizedMarkedTerminalReferenceScope (Descends)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedRetainedStateReader (factLabel)
open LocalizedMarkedCertifiedTerminalRefusal (raw_single)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign)
open LocalizedMarkedOperationEvaluator (tiedChildren)
open LocalizedChemicalRingFrameReadback (atomAt)
open LocalizedChemicalRingMovedSlotEligibility (moved_child_selected)
open RetainedRingSymmetryReconstruction (BondedChain)

def armPath : List (Fin 46) := [0, 28, 32, 27, 26]
def armNode : RawMolecule.CanonicalBranchNode := nodeOf (armPath.map Fin.val)
def armChild : RawMolecule.CanonicalBranchNode := nodeOf [0, 28, 32, 27, 26, 34]
def tailPath : List (Fin 46) := [34, 38, 42, 40, 3, 14, 8, 15, 4, 16, 9, 6, 2]

private def armRoute (n : Nat) := nodeOf ((armPath.map Fin.val).take (n + 1))

private theorem arm_edges (i : Fin 4) :
    armRoute (i.val + 1) ∈ mol.canonicalChildren (armRoute i.val) := by
  fin_cases i <;> decide +kernel

theorem arm_reached : Reached mol armNode := by
  have all : ∀ k, k ≤ 4 → Reached mol (armRoute k) := by
    intro k
    induction k with
    | zero => intro _; exact reached_root mol 0 (by decide)
    | succ k ih =>
        intro bound
        exact reached_child mol (armRoute k) (armRoute (k + 1)) (ih (by omega))
          (arm_edges ⟨k, by omega⟩)
  exact all 4 le_rfl

theorem arm_child_edge : armChild ∈ mol.canonicalChildren armNode := by decide +kernel

private def tailRoute (n : Nat) := nodeOf ((coveringPath.map Fin.val).take (n + 6))

private theorem tail_edges (i : Fin 12) :
    tailRoute (i.val + 1) ∈ mol.canonicalChildren (tailRoute i.val) := by
  fin_cases i <;> decide +kernel

theorem arm_child_descent : Descends mol armChild coveringNode := by
  have all : ∀ n : Nat, n ≤ 12 → Descends mol (tailRoute 0) (tailRoute n) := by
    intro n
    induction n with
    | zero => intro _; exact .refl
    | succ n ih =>
        intro bound
        exact (ih (by omega)).tail (tail_edges ⟨n, by omega⟩)
  exact all 12 le_rfl

noncomputable section
open scoped Classical

def armData : OccurrenceData certified mol otherCurrent armNode :=
  Classical.choice (occurrenceData_exists certified mol structure_agreement admissible supported
    single_bonded otherCurrent armNode arm_reached rfl rfl)

abbrev armUnit : DetectedOccurrence graph :=
  ⟨certified.molecularFrameUnit armData.target.1, armData.detected⟩

theorem arm_history : armData.target.1.node.history = armPath.reverse := by
  apply List.map_injective_iff.mpr Fin.val_injective
  have history := (LocalizedMarkedCarrierLookup.lookup?_sound certified _ _ armData.found).history
  simpa only [armNode, nodeOf, List.map_reverse] using history

theorem arm_root : armData.target.1.root = (0 : Fin 46) := by
  have packed := certified.legitimateOccurrence_transport single_bonded 1
    (certified.carrierOccurrence_legitimate single_bonded armData.target)
  apply Option.some.inj
  simpa only [arm_history, List.reverse_reverse, armPath, List.head?_cons] using
    packed.sourceHead.symm

theorem arm_tied_branch : Nonempty (TiedRootBranch certified armData.target) := by
  let old := Classical.choice (shortcut_tied_branch current shortcutData)
  have oldHistory := shortcut_history current shortcutData
  have oldPacked := certified.legitimateOccurrence_transport single_bonded 1
    (certified.carrierOccurrence_legitimate single_bonded shortcutData.target)
  have packed := certified.legitimateOccurrence_transport single_bonded 1
    (certified.carrierOccurrence_legitimate single_bonded armData.target)
  have oldRoot : shortcutData.target.1.root = (0 : Fin 46) := by
    apply Option.some.inj
    simpa only [oldHistory, List.reverse_reverse, shortcutPath, List.head?_cons] using
      oldPacked.sourceHead.symm
  have edge := (LocalizedMarkedRetainedVirtualTarget.edge_facts old.rootCursor old.arm old.member).2.2
  have armLength : old.arm.occurrence.1.address.length = 1 := by
    rcases edge.2 with shorter | longer
    · rw [old.rootAddress] at shorter
      simp only [List.length_nil] at shorter
      omega
    · rw [old.rootAddress] at longer
      simpa only [List.length_nil, Nat.zero_add] using longer.1.symm
  have sameHead : shortcutData.target.1.address.take 1 = armData.target.1.address.take 1 := by
    rw [oldPacked.sourceAddress, packed.sourceAddress, oldRoot, arm_root]
    simp only [CertifiedLocalizedCIPInput.canonicalAddress, oldHistory, arm_history, List.reverse_reverse,
      shortcutPath, armPath, List.tail_cons]
    rfl
  have inside : certified.RootBranchContains old.arm.occurrence armData.target := by
    refine ⟨old.inside.1.trans (oldRoot.trans arm_root.symm), ?_⟩
    have initial := old.inside.2.take 1
    have takeArm : old.arm.occurrence.1.address.take 1 = old.arm.occurrence.1.address := by
      rw [← armLength, List.take_length]
    rw [takeArm, sameHead] at initial
    exact initial.trans (List.take_prefix _ _)
  have nonroot : armData.target.1.address ≠ [] := by
    intro empty
    have lengths := congrArg List.length packed.sourceAddress
    rw [empty] at lengths
    simp only [CertifiedLocalizedCIPInput.canonicalAddress, arm_history, List.reverse_reverse, armPath,
      List.tail_cons, CertifiedLocalizedCIPInput.foldSlots_length, List.length_cons, List.length_nil] at lengths
    omega
  exact ⟨{ old with inside := inside, nonroot := nonroot }⟩

/-! ## The two O18 attachments of `o+` -/

private def ligandAt (a : Fin 46) (adjacent : physical.mol.Adj otherCurrent.1 a) : Fin 4 :=
  Classical.choose (physical.ligandAtomAt_surjective otherCurrent a adjacent)

def slot34 : Fin 4 := armData.ligandOf.symm (ligandAt 34 (by decide +kernel))
def slot35 : Fin 4 := armData.ligandOf.symm (ligandAt 35 (by decide +kernel))

theorem slot_atoms :
    referenceAt certified mol otherCurrent armNode armData slot34 = (34 : Fin 46) ∧
    referenceAt certified mol otherCurrent armNode armData slot35 = (35 : Fin 46) := by
  constructor
  · simpa only [referenceAt, slot34, ligandAt, Equiv.apply_symm_apply] using
      Classical.choose_spec (physical.ligandAtomAt_surjective otherCurrent (34 : Fin 46) (by decide +kernel))
  · simpa only [referenceAt, slot35, ligandAt, Equiv.apply_symm_apply] using
      Classical.choose_spec (physical.ligandAtomAt_surjective otherCurrent (35 : Fin 46) (by decide +kernel))

theorem slots_distinct : slot34 ≠ slot35 := by
  intro same
  have atoms := slot_atoms
  rw [same] at atoms
  exact (by decide : (34 : Fin 46) ≠ 35) (atoms.1.symm.trans atoms.2)

theorem slot_current (state : OccurrenceAuxState) (slot : Fin 4) (a : Fin 46)
    (atAtom : referenceAt certified mol otherCurrent armNode armData slot = a) :
    ((frames certified single_bonded state armData.target armData.real armUnit rfl).frame.cursorAt
      slot).occurrence.1.node.current? = some a := by
  have frameEq : (frames certified single_bonded state armData.target armData.real armUnit rfl).frame =
      armData.frame :=
    Option.some.inj ((frames certified single_bonded state armData.target armData.real armUnit
      rfl).frameComputed.symm.trans armData.frameExec)
  have mapped : (((frames certified single_bonded state armData.target armData.real armUnit
      rfl).frame.cursorAt slot).occurrence.1.node.current?).map Fin.val = some a.val := by
    change atomAt certified _ slot = some a.val
    rw [frameEq, armData.atomAt_eq]
    exact congrArg (fun x : Fin 46 => some x.val) atAtom
  cases found : ((frames certified single_bonded state armData.target armData.real armUnit
      rfl).frame.cursorAt slot).occurrence.1.node.current? with
  | none => simp [found] at mapped
  | some b =>
      simp only [found, Option.map_some, Option.some.injEq] at mapped
      exact congrArg some (Fin.ext mapped)

/-! ## Actual selection and the covered observation below `o+` -/

private theorem arm_history_fixed :
    ∀ value ∈ armNode.history, relabelOf certified otherPhysicalAut.val value = value := by
  intro value member
  have history : armNode.history = [26, 27, 32, 28, 0] := rfl
  rw [history] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;> rfl

theorem arm_selected_child :
    armChild ∈ tiedChildren mol (sparseOperations certified mol) [] armNode :=
  moved_child_selected certified mol structure_agreement admissible supported single_bonded
    otherPhysicalAut otherCurrent armNode armData arm_reached arm_history_fixed (34 : Fin 46)
    (by decide +kernel) (by change (35 : Fin 46) ≠ (34 : Fin 46); decide)
    armChild arm_child_edge rfl

private theorem covering_rigid (e : physical.Aut)
    (historyFixed : ∀ atom ∈ coveringNode.history, relabelOf certified e.val atom = atom) :
    e = 1 := by
  apply raw_covering_stabilizer e historyFixed
  have fixed34 : e.val (34 : Fin 46) = (34 : Fin 46) := by
    have member : ((34 : Fin 46) : Nat) ∈ coveringNode.history := by decide +kernel
    have same := historyFixed _ member
    rw [relabelOf_val] at same
    exact Fin.ext same
  exact fixed_of_signature graph ⟨e.val, e.2.1⟩ ([34] : List (Fin 46)) (30 : Fin 46)
    (by
      intro a member
      have same : a = 34 := List.mem_singleton.mp member
      rw [same]
      exact fixed34)
    (by unfold SignatureUnique; decide +kernel)

/-- The covering terminal's generated label is present in the actual snapshot below `o+`
for inherited reference 28, at every adequate depth. -/
theorem arm_covering_label_present (depth : Nat) (adequate : 13 ≤ depth) :
    ((snapshotWith LocalizedChemicalRingInheritedFallback.rawStep? certified mol depth
      (inputGeometry certified) armNode 28).factAt? coveringNode).map factLabel ≠ none := by
  intro absent
  have budget : coveringNode.history.length ≤ depth + armNode.history.length := by
    have lengths : coveringNode.history.length = 18 ∧ armNode.history.length = 5 := by
      decide +kernel
    omega
  have refused := LocalizedChemicalRingSelectedFactCompleteness.candidate_absence_refusal
    certified mol depth (inputGeometry certified) armNode armChild coveringNode 28
    arm_selected_child arm_child_descent budget absent
  obtain ⟨value, computed⟩ := LocalizedChemicalRingReferenceStabilizerSuccess.descriptor_exists
    certified mol structure_agreement admissible supported single_bonded cfg current calibrated
    coveringNode coveringData (Classical.choice covering_tied_branch)
    (depth + armNode.history.length - coveringNode.history.length) (28 : Fin 46)
    ⟨0, constant_charge⟩ (fun e historyFixed _ => covering_rigid e historyFixed)
  have computed' : LocalizedChemicalRingInheritedFallback.descriptor? mol
      (sparseOperations certified mol) (depth + armNode.history.length - coveringNode.history.length)
      (inputGeometry certified) [] (some 28) coveringNode = some value := computed
  rw [computed'] at refused
  cases refused

private theorem tail_valid :
    ResidualObsPath graph armData.target.1.node.history.reverse (34 : Fin 46) tailPath := by
  rw [arm_history, List.reverse_reverse]
  refine ⟨by decide, rfl, by decide, ?_, ?_⟩
  · decide +kernel
  · simp only [tailPath, BondedChain]
    decide +kernel

private theorem tail_query :
    rawPathNode armData.target.1.root (boundaryPath armData.target tailPath) = coveringNode := by
  unfold boundaryPath
  rw [arm_history, arm_root]
  rfl

private theorem o18_image (e : graph.Aut) (entry : e.val (34 : Fin 46) = (35 : Fin 46)) :
    e.val (30 : Fin 46) = (31 : Fin 46) := by
  have finite : ∀ x : Fin 46, graph.Adj 35 x → graph.atomZ x = graph.atomZ 30 →
      graph.atomMass x = graph.atomMass 30 → x = 31 := by
    intro x
    fin_cases x <;> decide +kernel
  apply finite
  · rw [← entry]
    exact (MoleculeGraph.Aut.adj_iff (m := graph) e 34 30).mpr (by decide +kernel)
  · exact MoleculeGraph.Aut.atomZ_eq (m := graph) e 30
  · exact MoleculeGraph.Aut.atomMass_eq (m := graph) e 30

/-- **Separation at `o+`.** For inherited reference 28, the actual marked keys of the actual
snapshot below `o+` distinguish its two O18 attachments. No tie, label value or sign premise. -/
theorem arm_refined_separate (depth : Nat) (adequate : 13 ≤ depth) :
    refinedKey certified single_bonded
        (snapshotWith LocalizedChemicalRingInheritedFallback.rawStep? certified mol depth
          (inputGeometry certified) armNode 28)
        armData.target armData.real armUnit rfl (28 : Fin 46)
        (retainedCarrierFuel certified) (2 * (retainedCarrierFuel certified + 1)) slot34 ≠
      refinedKey certified single_bonded
        (snapshotWith LocalizedChemicalRingInheritedFallback.rawStep? certified mol depth
          (inputGeometry certified) armNode 28)
        armData.target armData.real armUnit rfl (28 : Fin 46)
        (retainedCarrierFuel certified) (2 * (retainedCarrierFuel certified + 1)) slot35 := by
  intro tie
  let state := snapshotWith LocalizedChemicalRingInheritedFallback.rawStep? certified mol depth
    (inputGeometry certified) armNode 28
  let branch := Classical.choice arm_tied_branch
  obtain ⟨center, centerCurrent⟩ := certified.localizedRerootCursor_current_exists
    (⟨armData.target, none⟩ : certified.LocalizedRerootCursor (retainedCarrierFuel certified))
  obtain ⟨_, pair, _, _, _, _, _, targetEq, leftEq, rightEq, _, _, _, realL, realR⟩ :=
    selected_refined_tie_real_outward certified single_bonded
      branch.rootCursor branch.rootAddress branch.arm branch.arm' branch.member branch.member'
      branch.different branch.real branch.real' branch.read branch.read' branch.key branch.key'
      branch.built branch.built' branch.tie state armData.target armData.real branch.inside
      branch.nonroot center centerCurrent armUnit rfl (28 : Fin 46) (retainedCarrierFuel certified)
      (2 * (retainedCarrierFuel certified + 1)) slot34 slot35 slots_distinct tie
  have rootL := pair.leftRoot
  have rootR := pair.rightRoot
  have addressL := pair.leftAddress
  have addressR := pair.rightAddress
  rw [targetEq, leftEq] at rootL addressL
  rw [targetEq, rightEq] at rootR addressR
  rw [leftEq] at realL
  rw [rightEq] at realR
  have currentL := slot_current state slot34 34 slot_atoms.1
  have currentR := slot_current state slot35 35 slot_atoms.2
  obtain ⟨_, matched⟩ := actual_outward_default_tie_prescribed_fact_match certified single_bonded
    state armData.target armData.real armUnit rfl (28 : Fin 46) slot34 slot35 (34 : Fin 46) (35 : Fin 46)
    currentL currentR realL realR rootL rootR pair.leftSlot pair.rightSlot addressL addressR tie
    ⟨0, constant_charge⟩
  have detected : IsDetectedCenter graph (pathTerminal tailPath tail_valid.nonempty) :=
    (graph.isTetrahedralCenter_iff_neighborFinset_card _).mp
      ((graph.mem_tetrahedralCenterSet _).mp current.2)
  obtain ⟨π, automorphism, historyFixed, entry, referenceFixed, _, _, _, _, facts⟩ :=
    matched ⟨tailPath, tail_valid⟩ detected
  let e : physical.Aut := graph.detectedMultiCenterAutOfGraphAut ⟨π, automorphism⟩
  have rootFixed : π (0 : Fin 46) = (0 : Fin 46) :=
    historyFixed (0 : Fin 46) (by rw [arm_history]; decide)
  obtain ⟨centerFixed, negative⟩ := other_exchange_lower_negative cfg e rootFixed referenceFixed
    (o18_image ⟨π, automorphism⟩ entry)
  have imageCalibrated : LocalizedRecursiveAuxiliaryPhysicalDomain.ActualPhysicalCalibratedCoordinates
      certified physical cfg (physical.centerPerm e current) := by
    rw [centerFixed]
    exact calibrated
  have boundaryFixed : ∀ atom ∈ armData.target.1.node.history.reverse,
      e.val atom = atom := by
    intro atom member
    exact historyFixed atom (List.mem_reverse.mp member)
  have covered : ∀ c : physical.Center, c.1.val ∈
      (rawPathNode armData.target.1.root (boundaryPath armData.target tailPath)).history := by
    intro c
    rw [tail_query]
    exact List.mem_reverse.mpr (List.mem_map.mpr ⟨c.1, covering_detected c.1 c.2, rfl⟩)
  cases observed : (state.factAt? (rawPathNode armData.target.1.root
      (boundaryPath armData.target tailPath))).map factLabel with
  | none =>
      rw [tail_query] at observed
      exact arm_covering_label_present depth adequate observed
  | some label =>
      have sym := LocalizedChemicalRingSemanticSymmetry.structuralSymmetry_of_aut
        certified mol structure_agreement admissible supported e
      have cov := LocalizedChemicalRingSemanticSymmetry.actual_covariant
        certified mol structure_agreement admissible supported single_bonded e
      have stepMap := LocalizedChemicalRingInheritedFallback.stepMap sym admissible.1.1 admissible.1.2
        (raw_single mol certified structure_agreement admissible.1.1 admissible.1.2 supported
          single_bonded) cov
      have proper := relativeSign_of_covered_snapshot certified mol structure_agreement admissible
        supported single_bonded cfg e LocalizedChemicalRingInheritedFallback.rawStep? stepMap
        (LocalizedChemicalRingInheritedFallback.stepCongr mol (sparseOperations certified mol))
        (LocalizedChemicalRingInheritedFallback.stepFlip mol (sparseOperations certified mol))
        armData.target (28 : Fin 46) (34 : Fin 46) boundaryFixed referenceFixed tailPath tail_valid
        current rfl calibrated imageCalibrated covered depth armNode arm_reached facts label observed
      rw [negative] at proper
      norm_num at proper

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusArmSeparation

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusArmSeparation.arm_reached
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusArmSeparation.arm_child_descent
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusArmSeparation.arm_history
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusArmSeparation.arm_tied_branch
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusArmSeparation.slot_atoms
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusArmSeparation.slot_current
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusArmSeparation.arm_selected_child
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusArmSeparation.arm_covering_label_present
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusArmSeparation.arm_refined_separate
