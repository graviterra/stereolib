import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitBranch
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCalibration
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitStabilizer
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceStabilizerSuccess
import TetraStereo.OneCenter.LocalizedChemicalRingSelectedFactCompleteness
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

/-!
A simple actual occurrence path in the accepted 46-atom input visits every detected
center before ending at center 2. Its first edge is selected by the existing ordinary
comparison. Its history/reference stabilizer is trivial, so the isolated inherited
fallback produces a descriptor at every depth and emits it in the stated root snapshot.
No comparison-key equality, descriptor letter, or physical correctness is asserted.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCoveringPath

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingReferenceOrbitInput LocalizedChemicalRingReferenceOrbitBranch
open LocalizedChemicalRingReferenceOrbitCalibration LocalizedChemicalRingReferenceOrbitStabilizer
open LocalizedChemicalRingInheritedRefusalCases LocalizedChemicalRingSelectedRefusalWitness
open LocalizedChemicalRingPhysicalSense (inputGeometry relabelOf relabelOf_val)
open LocalizedMarkedReachableConfigurations (Reached reached_root reached_child)
open LocalizedMarkedTerminalReferenceScope (Descends)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedChemicalRingBoundaryWitnessExecution (snapshotWith)
open LocalizedGenericMarkedRecalculation (structuralDepth factOf)
open LocalizedMarkedRetainedStateReader (factLabel)

def coveringPath : List (Fin 46) :=
  [0, 28, 32, 27, 26, 34, 38, 42, 40, 3, 14, 8, 15, 4, 16, 9, 6, 2]

def coveringNode : RawMolecule.CanonicalBranchNode := nodeOf (coveringPath.map Fin.val)

theorem covering_simple : coveringPath.Nodup := by decide +kernel

theorem covering_detected (a : Fin 46) (detected : a ∈ graph.tetrahedralCenterSet) :
    a ∈ coveringPath := by
  rw [detected_inventory] at detected
  fin_cases a <;> simp_all [coveringPath]

private def remainingRoute (n : Nat) := nodeOf ((coveringPath.map Fin.val).take (n + 2))

private theorem remaining_edges (i : Fin 16) :
    remainingRoute (i.val + 1) ∈ mol.canonicalChildren (remainingRoute i.val) := by
  fin_cases i <;> decide +kernel

theorem covering_raw_descent : Descends mol (nodeOf [0, 28]) coveringNode := by
  have all : ∀ n : Nat, n ≤ 16 → Descends mol (remainingRoute 0) (remainingRoute n) := by
    intro n
    induction n with
    | zero => intro _; exact .refl
    | succ n ih =>
        intro bound
        exact (ih (by omega)).tail (remaining_edges ⟨n, by omega⟩)
  exact all 16 le_rfl

theorem covering_reached : Reached mol coveringNode := by
  have first : Reached mol (nodeOf [0, 28]) :=
    reached_child mol (canonicalCenterRoot 0) (nodeOf [0, 28])
      (reached_root mol 0 (by decide)) (by decide +kernel)
  exact LocalizedMarkedTerminalReferenceScope.descendant_reached first covering_raw_descent

theorem covering_structural_budget :
    coveringNode.history.length ≤ structuralDepth mol (canonicalCenterRoot 0) +
      (canonicalCenterRoot 0).history.length := by decide +kernel

theorem covering_stabilizer (e : graph.Aut)
    (historyFixed : ∀ a ∈ coveringPath, (e : Equiv.Perm (Fin 46)) a = a)
    (referenceFixed : (e : Equiv.Perm (Fin 46)) reference = reference) :
    (e : Equiv.Perm (Fin 46)) = 1 := by
  have fixed5 : (e : Equiv.Perm (Fin 46)) (5 : Fin 46) = 5 := by
    apply fixed_of_signature graph e [2, 8] 5
    · intro a member
      have subset : ([2, 8] : List (Fin 46)) ⊆ coveringPath := by decide +kernel
      exact historyFixed a (subset member)
    · unfold SignatureUnique
      decide +kernel
  apply shortcut_stabilizer e _ referenceFixed
  intro a present
  have covered : a ∈ coveringPath ∨ a = (5 : Fin 46) := by
    have finite : ∀ a : Fin 46, a ∈ shortcutPath → a ∈ coveringPath ∨ a = 5 := by
      decide +kernel
    exact finite a present
  rcases covered with covered | same
  · exact historyFixed a covered
  · simpa only [same] using fixed5

noncomputable section
open scoped Classical

theorem raw_covering_stabilizer (e : physical.Aut)
    (historyFixed : ∀ value ∈ coveringNode.history, relabelOf certified e.val value = value)
    (referenceFixed : e.val reference = reference) : e = 1 := by
  apply Subtype.ext
  apply covering_stabilizer ⟨e.val, e.2.1⟩ _ referenceFixed
  intro a present
  have inHistory : a.val ∈ coveringNode.history :=
    List.mem_reverse.mpr (List.mem_map.mpr ⟨a, present, rfl⟩)
  have fixed := historyFixed a.val inHistory
  rw [relabelOf_val] at fixed
  exact Fin.ext fixed

def coveringData : OccurrenceData certified mol current coveringNode :=
  Classical.choice (occurrenceData_exists certified mol structure_agreement admissible supported
    single_bonded current coveringNode covering_reached rfl rfl)

theorem covering_history : coveringData.target.1.node.history = coveringPath.reverse := by
  apply List.map_injective_iff.mpr Fin.val_injective
  have history := (LocalizedMarkedCarrierLookup.lookup?_sound certified _ _ coveringData.found).history
  simpa only [coveringNode, nodeOf, List.map_reverse] using history

theorem covering_tied_branch : Nonempty (TiedRootBranch certified coveringData.target) := by
  let old := Classical.choice (shortcut_tied_branch current shortcutData)
  have oldHistory := shortcut_history current shortcutData
  have oldPacked := certified.legitimateOccurrence_transport single_bonded 1
    (certified.carrierOccurrence_legitimate single_bonded shortcutData.target)
  have packed := certified.legitimateOccurrence_transport single_bonded 1
    (certified.carrierOccurrence_legitimate single_bonded coveringData.target)
  have oldRoot : shortcutData.target.1.root = (0 : Fin 46) := by
    apply Option.some.inj
    simpa only [oldHistory, List.reverse_reverse, shortcutPath, List.head?_cons] using
      oldPacked.sourceHead.symm
  have newRoot : coveringData.target.1.root = (0 : Fin 46) := by
    apply Option.some.inj
    simpa only [covering_history, List.reverse_reverse, coveringPath, List.head?_cons] using
      packed.sourceHead.symm
  have edge := (LocalizedMarkedRetainedVirtualTarget.edge_facts old.rootCursor old.arm old.member).2.2
  have armLength : old.arm.occurrence.1.address.length = 1 := by
    rcases edge.2 with shorter | longer
    · rw [old.rootAddress] at shorter
      simp only [List.length_nil] at shorter
      omega
    · rw [old.rootAddress] at longer
      simpa only [List.length_nil, Nat.zero_add] using longer.1.symm
  have sameHead : shortcutData.target.1.address.take 1 = coveringData.target.1.address.take 1 := by
    rw [oldPacked.sourceAddress, packed.sourceAddress, oldRoot, newRoot]
    simp only [canonicalAddress, oldHistory, covering_history, List.reverse_reverse,
      shortcutPath, coveringPath, List.tail_cons]
    rfl
  have inside : certified.RootBranchContains old.arm.occurrence coveringData.target := by
    refine ⟨old.inside.1.trans (oldRoot.trans newRoot.symm), ?_⟩
    have initial := old.inside.2.take 1
    have takeArm : old.arm.occurrence.1.address.take 1 = old.arm.occurrence.1.address := by
      rw [← armLength, List.take_length]
    rw [takeArm, sameHead] at initial
    exact initial.trans (List.take_prefix _ _)
  have nonroot : coveringData.target.1.address ≠ [] := by
    intro empty
    have lengths := congrArg List.length packed.sourceAddress
    rw [empty] at lengths
    simp only [canonicalAddress, covering_history, List.reverse_reverse, coveringPath,
      List.tail_cons, foldSlots_length, List.length_cons, List.length_nil] at lengths
    omega
  exact ⟨{ old with inside := inside, nonroot := nonroot }⟩

theorem covering_descriptor_exists (depth : Nat) :
    ∃ value, LocalizedChemicalRingInheritedFallback.descriptor? mol (sparseOperations certified mol)
      depth (inputGeometry certified) [] (some reference.val) coveringNode = some value := by
  exact LocalizedChemicalRingReferenceStabilizerSuccess.descriptor_exists certified mol
    structure_agreement admissible supported single_bonded cfg current calibrated coveringNode
    coveringData (Classical.choice covering_tied_branch) depth reference ⟨0, constant_charge⟩
    raw_covering_stabilizer

theorem covering_snapshot_label_present :
    ((snapshotWith LocalizedChemicalRingInheritedFallback.rawStep? certified mol
      (structuralDepth mol (canonicalCenterRoot 0)) (inputGeometry certified)
      (canonicalCenterRoot 0) reference.val).factAt? coveringNode).map factLabel ≠ none := by
  intro absent
  have refused := LocalizedChemicalRingSelectedFactCompleteness.candidate_absence_refusal
    certified mol (structuralDepth mol (canonicalCenterRoot 0)) (inputGeometry certified)
    (canonicalCenterRoot 0) (nodeOf [0, 28]) coveringNode reference.val
    shortcut_selected_first_child covering_raw_descent covering_structural_budget absent
  obtain ⟨value, computed⟩ := covering_descriptor_exists
    (structuralDepth mol (canonicalCenterRoot 0) + (canonicalCenterRoot 0).history.length -
      coveringNode.history.length)
  rw [computed] at refused
  cases refused

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCoveringPath

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCoveringPath.covering_simple
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCoveringPath.covering_detected
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCoveringPath.covering_raw_descent
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCoveringPath.covering_reached
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCoveringPath.covering_structural_budget
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCoveringPath.covering_stabilizer
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCoveringPath.raw_covering_stabilizer
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCoveringPath.covering_history
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCoveringPath.covering_tied_branch
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCoveringPath.covering_descriptor_exists
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCoveringPath.covering_snapshot_label_present
