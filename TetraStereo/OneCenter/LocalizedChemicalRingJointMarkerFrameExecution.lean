import TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerRanking
import TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerEligibility
import TetraStereo.OneCenter.LocalizedChemicalRingInheritedRefusalCases
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Concrete joint callbacks at reached detected molecular frames

The actual frame lookup, cursor sort and raw position conversion all succeed for the occurrence
data derived by `occurrenceData_exists`. These theorems apply to arbitrary raw auxiliary states
and arbitrary lists of actual reference atoms, so they can consume prepared child states.
The marked geometric reading succeeds exactly when the actual joint keys are distinct and the
coordinate reading succeeds. No desired sort, callback success, label correctness or parity is
assumed. Physical interpretation of generated labels remains open.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerFrameExecution

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedChemicalRingJointMarkerOperations LocalizedChemicalRingJointMarkerRanking
open LocalizedMarkedRetainedMolecularSelection LocalizedMarkedRetainedOrdinaryRanking
open LocalizedMarkedRetainedPromotedOperations (adjacentPromotionCount?_exists)
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData rank)
open LocalizedChemicalRingCompletenessMarked (enumeration strict_iff_injective)
open LocalizedChemicalRingMultiMarkRecursion (markedReadingJoint?)
open LocalizedGenericMarkedRecalculation

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput)

/-- An accumulated list of actual atom identities passes the runtime membership check. -/
theorem referenceAtoms?_map (references : List input.Atom) :
    referenceAtoms? input (references.map Fin.val) = some references := by
  induction references with
  | nil => rfl
  | cons reference rest ih =>
      simpa [referenceAtoms?, List.mapM_cons, reference.isLt] using
        congrArg (fun value : Option (List input.Atom) =>
          value.bind (fun tail => some (reference :: tail))) ih

variable (mol : RawMolecule) (single : input.moleculeGraph.SimpleBonded)
  (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
  (data : OccurrenceData input mol c node)
  (state : OccurrenceAuxState) (references : List input.Atom)

abbrev slotKeys : Fin 4 → RefinedKey :=
  refinedKey input single state data.target data.real
    ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl references
    (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1))

abbrev slotOrder : List (Fin 4) :=
  keyOrder (slotKeys input mol single c node data state references) (List.finRange 4)

abbrev slotAdjacent : List (Option Ordering) :=
  adjacentBy (fun a b => some (compare (slotKeys input mol single c node data state references a)
    (slotKeys input mol single c node data state references b)))
    (slotOrder input mol single c node data state references)

/-- Successful actual lookup, sorting, promotion counting and raw slot-to-atom positioning. -/
theorem jointPartition?_eq_exists :
    ∃ count,
      jointPartition? input mol state node references (retainedCarrierFuel input)
        (2 * (retainedCarrierFuel input + 1)) =
      some ((slotOrder input mol single c node data state references).map data.read.index,
        slotAdjacent input mol single c node data state references, count) := by
  let unit : DetectedOccurrence input.moleculeGraph :=
    ⟨input.molecularFrameUnit data.target.1, data.detected⟩
  have frameEq : (rawStateFrames input single state data.target data.real unit rfl).frame = data.frame := by
    have h := (rawStateFrames input single state data.target data.real unit rfl).frameComputed
    rw [data.frameExec] at h
    exact (Option.some.inj h).symm
  have callback : ∀ a b,
      jointBefore input state data.target data.frame references (retainedCarrierFuel input)
        (2 * (retainedCarrierFuel input + 1)) a b =
      some (compare (slotKeys input mol single c node data state references a)
        (slotKeys input mol single c node data state references b)) := by
    intro a b
    have h := jointBefore_eq_refined input single state data.target data.real unit rfl references
      (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) a b
    rw [frameEq] at h
    exact h
  have ordinaryTotal : ∀ a b, ∃ decision,
      rawStateBefore input state data.target data.frame a b = some decision := by
    intro a b
    have h := rawStateBefore_eq_keys input single state data.target data.real unit rfl a b
    rw [frameEq] at h
    exact ⟨_, h⟩
  let sorted := slotOrder input mol single c node data state references
  obtain ⟨count, hc⟩ := adjacentPromotionCount?_exists
    (rawStateBefore input state data.target data.frame)
    (jointBefore input state data.target data.frame references (retainedCarrierFuel input)
      (2 * (retainedCarrierFuel input + 1))) ordinaryTotal
    (fun a b => ⟨_, callback a b⟩) sorted
  refine ⟨count, ?_⟩
  have callbackEq := funext fun a => funext fun b => callback a b
  simp only [jointPartition?, jointFrame?, data.found, data.rawFrame, data.frameExec,
    Option.bind_eq_bind, Option.bind_some, partitionBy?]
  rw [callbackEq, sortBy?_key compare refined_compare_lt_iff]
  simp only [Option.bind_some]
  rw [callbackEq] at hc
  change LocalizedMarkedRetainedPromotedOperations.adjacentPromotionCount? _ _ sorted = _ at hc
  rw [hc]
  simp only [Option.bind_some, data.read.positions]

/-- The actual current-context callback returns the derived raw-frame ordering. -/
theorem contextOrder?_eq :
    contextOrder? input mol state node (references.map Fin.val) =
      some ((slotOrder input mol single c node data state references).map data.read.index,
        slotAdjacent input mol single c node data state references) := by
  obtain ⟨count, partition⟩ := jointPartition?_eq_exists input mol single c node data state references
  simp [contextOrder?, referenceAtoms?_map, partition]

/-- The actual marked callback returns a ranking from the very same comparison pass. -/
theorem markedJoint?_eq_exists (mark : Nat) :
    ∃ count,
      markedJoint? input mol state node (references.map Fin.val) mark =
      some { positions := (slotOrder input mol single c node data state references).map data.read.index
             unique := strict (slotAdjacent input mol single c node data state references)
             pseudoComparisons := count } := by
  obtain ⟨count, partition⟩ := jointPartition?_eq_exists input mol single c node data state references
  exact ⟨count, by simp [markedJoint?, referenceAtoms?_map, partition]⟩

/-- Concrete marked execution, without a desired order or a successful-sort assumption. -/
theorem markedReadingJoint?_eq (geom : Geometry) (mark : Nat) :
    markedReadingJoint? mol (jointOperations input mol) geom state node
        (references.map Fin.val) mark =
      if Function.Injective (slotKeys input mol single c node data state references) then
        readback? geom (enumeration input c
          (rank input mol c node data (slotKeys input mol single c node data state references)))
      else none := by
  obtain ⟨count, ranking⟩ := markedJoint?_eq_exists input mol single c node data state references mark
  unfold markedReadingJoint?
  rw [data.rawFrame]
  simp only [Option.bind_eq_bind, Option.bind_some, jointOperations]
  rw [ranking]
  simp only [Option.bind_some, rankedAtoms?]
  have atoms := LocalizedChemicalRingInheritedRefusalCases.ranked_eq input mol c node data
    (slotKeys input mol single c node data state references)
  unfold atomsAt? at atoms
  by_cases injective : Function.Injective (slotKeys input mol single c node data state references)
  · rw [if_pos ((strict_iff_injective compare refined_compare_lt_iff
      refined_compare_eq_iff _).mpr injective), atoms, Option.bind_some, if_pos injective]
  · rw [if_neg (fun h => injective ((strict_iff_injective compare refined_compare_lt_iff
      refined_compare_eq_iff _).mp h)), Option.bind_none, if_neg injective]


/-- Eligible slots of the actual joint partition. -/
def selectedSlots : List (Fin 4) :=
  LocalizedChemicalRingOrderingTransport.tiedEntries false
    (slotOrder input mol single c node data state references)
    (slotAdjacent input mol single c node data state references)

/-- Runtime eligible atom identities are the actual ligands at the eligible certified slots. -/
theorem eligible_eq :
    eligibleOf data.atoms
        ((slotOrder input mol single c node data state references).map data.read.index)
        (slotAdjacent input mol single c node data state references) =
      (selectedSlots input mol single c node data state references).map
        (fun i => (LocalizedChemicalRingInheritedRefusalCases.referenceAt input mol c node data i).val) := by
  rw [LocalizedChemicalRingOrderingTransport.eligibleOf_tiedEntries]
  apply LocalizedChemicalRingCompletenessMarked.filterMap_eq_map_of
  intro slot _
  simp only [data.read.atom slot, data.atomAt_eq slot,
    LocalizedChemicalRingInheritedRefusalCases.referenceAt]

/-- Every selected raw fallback mark passes the actual atom-range check. -/
theorem eligible_atom_inRange (mark : Nat)
    (member : mark ∈ eligibleOf data.atoms
      ((slotOrder input mol single c node data state references).map data.read.index)
      (slotAdjacent input mol single c node data state references)) :
    mark < input.certified.input.molecule.atomCount := by
  rw [eligible_eq input mol single c node data state references] at member
  obtain ⟨slot, _, rfl⟩ := List.mem_map.mp member
  exact (LocalizedChemicalRingInheritedRefusalCases.referenceAt input mol c node data slot).isLt

/-- The non-strict joint partition supplies a nonempty population for consensus. -/
theorem selectedSlots_nonempty
    (notInj : ¬ Function.Injective (slotKeys input mol single c node data state references)) :
    selectedSlots input mol single c node data state references ≠ [] := by
  intro empty
  apply notInj
  intro a b equal
  by_contra ne
  have member : b ∈ selectedSlots input mol single c node data state references := by
    apply (LocalizedChemicalRingOrderingTransport.tiedEntries_mem compare refined_compare_eq_iff _ _
      ((keyOrder_perm _ _).nodup_iff.mpr (List.nodup_finRange 4))
      (keyOrder_pairwise _ _) b).mpr
    exact ⟨(keyOrder_perm _ _).mem_iff.mpr (List.mem_finRange b), a,
      (keyOrder_perm _ _).mem_iff.mpr (List.mem_finRange a), ne, equal⟩
  rw [empty] at member
  simp at member

/-- In recursive tied root arms, the actual selected slots belong to one joint-key class. -/
theorem selectedSlots_key_eq
    (branch : LocalizedChemicalRingSelectedRefusalWitness.TiedRootBranch input data.target)
    (a b : Fin 4)
    (ha : a ∈ selectedSlots input mol single c node data state references)
    (hb : b ∈ selectedSlots input mol single c node data state references) :
    slotKeys input mol single c node data state references a =
      slotKeys input mol single c node data state references b :=
  LocalizedChemicalRingJointMarkerEligibility.eligible_key_eq input single state data.target
    data.real ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl references
    (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) branch a b ha hb

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerFrameExecution

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerFrameExecution.referenceAtoms?_map
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerFrameExecution.jointPartition?_eq_exists
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerFrameExecution.contextOrder?_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerFrameExecution.markedJoint?_eq_exists
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerFrameExecution.markedReadingJoint?_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerFrameExecution.eligible_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerFrameExecution.eligible_atom_inRange
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerFrameExecution.selectedSlots_nonempty
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerFrameExecution.selectedSlots_key_eq
