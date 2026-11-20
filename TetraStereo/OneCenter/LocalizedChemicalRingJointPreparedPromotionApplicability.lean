import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedActualTiePhysical
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRefusalCharacterization
import TetraStereo.OneCenter.LocalizedChemicalRingMovedSlotEligibility
import TetraStereo.OneCenter.LocalizedChemicalRingTwoFixedNeighbors
import TetraStereo.OneCenter.LocalizedChemicalRingSelectedParentEligibility
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceConsensusCorrectionInduction
import TetraStereo.OneCenter.LocalizedChemicalRingProperRotationConsensus
import TetraStereo.OneCenter.LocalizedChemicalRingCompletenessOrbit
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedTieBoundary
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionBalance
import TetraStereo.OneCenter.LocalizedChemicalRingFixedParentParity
import TetraStereo.OneCenter.LocalizedActualFrameChildClassification
import TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback
import TetraStereo.OneCenter.LocalizedMarkedCarrierLookup
import TetraStereo.OneCenter.LocalizedMarkedRetainedPromotedRanking
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 3200000

/-!
# Source Rule 6 applicability from an actual tied-branch auxiliary assignment

The proposed 2018 source rule (as saved in the repository's preprint snapshot) only treats the
partitions `2+2`, `3+1` and `4` of the four frame ligands. This module derives the missing
partition premise from the actual evaluator data instead of assuming it.

The scenario is one reached non-root detected occurrence inside a tied root branch, an accumulated
reference list, either geometry side, and an actual refined joint-key tie between two distinct
frame slots.  From that tie the actual evaluator reconstructs a molecular automorphism fixing the
whole occurrence history and every accumulated reference, and proper on the source component of
the moved slot (`tie_sourceProper`).  The empty-state ordinary comparison matrix is invariant
under that automorphism (`actual_slot_key_action`), so the tied slots have equal ordinary keys.

* `base_key_eq_of_slotKeys_tie`: an actual refined tie forces equality of the two empty-state
  ordinary keys.  This is the actual key invariance consumed by the partition argument.
* `oddBoundary_of_baseTiedPairExcluded`: if no third slot shares the ordinary key of the tied
  pair (the `2+1+1` partition shape), the ineligible incoming parent slot and a fourth slot are
  the only remaining slots.  The parent is fixed because it lies in the history; the fourth slot
  is fixed because its key is a singleton class.  Re-extension of the source-proper map to the
  reversed history (`reextend_proper`) preserves both fixes and stays proper off the history, so
  a two-fixed-neighbor automorphism is odd at the detected center and proper at every center
  outside the occurrence history: an `OddBoundarySymmetry`.
* `preparedDescriptor_refuses_of_baseTiedPairExcluded`: hence the actual prepared descriptor at
  the structural depth, original geometry and accumulated references refuses.  This is the
  `2+1+1` refusal; in particular a uniform fallback at a middle pair of such a partition cannot
  produce an actual supported assignment.
* `exists_three_element_tied_class_of_success`: conversely, an actual successful descriptor plus
  an actual refined tie forces a third slot with the same ordinary key.  Together with the
  equality of the two tied keys this is a three-element tied class of the base comparison.
* `exists_parent_and_third_tied_slot_of_success`: the third slot is not the unique ineligible
  incoming parent slot, so the three tied slots are exactly the three outward slots and the
  parent is the separated singleton: the `3+1` shape.
* `exists_current_third_tied_slot_of_success`: the same three-plus-one conclusion holds for
  the actual current generated/refined keys. Global proper transport, the even three-cycle,
  and actual selected-slot covariance derive equality at every non-parent slot.

All hypotheses are actual evaluator data (lookup, reached occurrence, branch, accumulated
references, geometry side, refined keys).  There is no desired descriptor, comparator data,
child agreement, selected-set covariance or runtime policy change. The finite sorting bridge
is supplied by `LocalizedChemicalRingThreeOnePartition`; its independent source-model
application and inapplicable-case refusal are in `LocalizedChemicalRingSourcePromotionApplicability`.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionApplicability

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedChemicalRingInheritedRefusalCases
open LocalizedChemicalRingSelectedRefusalWitness (TiedRootBranch)
open LocalizedChemicalRingJointPreparedActualTiePhysical (tie_sourceProper)
open LocalizedChemicalRingJointPreparedCorrectionWitness (sideState)
open LocalizedChemicalRingJointMarkerFrameExecution (slotKeys)
open LocalizedChemicalRingReferenceConsensusCorrectionInduction (reextend_proper)
open LocalizedChemicalRingSelectedParentEligibility (eligible_iff_other parent_not_eligible)
open LocalizedChemicalRingTwoFixedNeighbors (local_odd_of_two_fixed_neighbors)
open LocalizedChemicalRingMovedSlotEligibility (actual_slot_key_action)
open LocalizedChemicalRingProperRotationConsensus (referenceAt_injective)
open LocalizedChemicalRingCompletenessOrbit (relativeSign_fixed)
open LocalizedChemicalRingJointPreparedRefusalCharacterization
  (OddBoundarySymmetry refusal_of_oddBoundary)
open LocalizedChemicalRingPhysicalSense (inputGeometry relabelOf relabelOf_val)
open LocalizedActualBoundaryObservationReadback (occurrence_history_facts)
open LocalizedMarkedCarrierLookup (lookup?_sound)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedGenericMarkedRecalculation (structuralDepth)
open LocalizedChemicalRingJointMarkerOperations (jointOperations)
open LocalizedChemicalRingPreparedContextRecursion (preparedDescriptor?)
open LocalizedMarkedRetainedPromotedRanking (frames)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

noncomputable section
open scoped Classical

/-! ## Finite slot combinatorics -/

/-- Among four slots, one slot is different from any three pairwise distinct slots. -/
private theorem exists_fourth_slot (left right parent : Fin 4)
    (distinct : left ≠ right) (parentLeft : parent ≠ left) (parentRight : parent ≠ right) :
    ∃ t : Fin 4, t ≠ left ∧ t ≠ right ∧ t ≠ parent := by
  revert left right parent
  decide +kernel

/-- A slot different from one member of a pairwise distinct four-slot family is one of the
other three members. -/
private theorem fourth_slot_trichotomy (x left right parent t : Fin 4)
    (distinct : left ≠ right) (parentLeft : parent ≠ left) (parentRight : parent ≠ right)
    (tLeft : t ≠ left) (tRight : t ≠ right) (tParent : t ≠ parent) (different : x ≠ t) :
    x = left ∨ x = right ∨ x = parent := by
  revert x left right parent t
  decide +kernel

/-! ## The actual evaluator context -/

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
    ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)

/-! ## Basic slot atoms and the ineligible incoming parent -/

private theorem current_of_value {value : Option input.Atom} {atom : input.Atom}
    (equal : value.map Fin.val = some atom.val) : value = some atom := by
  cases value with
  | none => cases equal
  | some a =>
      simp only [Option.map_some, Option.some.injEq] at equal
      exact congrArg some (Fin.ext equal)

private theorem frame_slot_current (c : input.detectedMultiCenterMolecule.Center)
    (node : RawMolecule.CanonicalBranchNode) (data : OccurrenceData input mol c node)
    (slot : Fin 4) :
    (data.frame.cursorAt slot).occurrence.1.node.current? =
      some (referenceAt input mol c node data slot) :=
  current_of_value input (data.atomAt_eq slot)

/-- The ligand atom of an actual parent-cursor slot lies in the official target history and is
adjacent to the detected center.  This is the passage from the structural parent certificate to
the physical neighbor used by the odd two-fixed-neighbor argument. -/
private theorem parent_atom_facts (c : input.detectedMultiCenterMolecule.Center)
    (node : RawMolecule.CanonicalBranchNode) (data : OccurrenceData input mol c node)
    (parent : Fin 4)
    (parentClass : IsLocalizedActualFrameParentCursor input data.target
      ((frames input single [] data.target data.real
        ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl).frame.cursorAt parent)) :
    referenceAt input mol c node data parent ∈ data.target.1.node.history ∧
      input.moleculeGraph.Adj c.1 (referenceAt input mol c node data parent) := by
  let unit : DetectedOccurrence input.moleculeGraph :=
    ⟨input.molecularFrameUnit data.target.1, data.detected⟩
  let execution := frames input single [] data.target data.real unit rfl
  have frameEq : execution.frame = data.frame :=
    Option.some.inj (execution.frameComputed.symm.trans data.frameExec)
  have computed : input.localizedOccurrenceFourLigandFrame? data.target = some execution.frame := by
    rw [← input.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?
      data.target]
    exact execution.frameComputed
  have present : execution.frame.cursorAt parent ∈ execution.frame.cursors :=
    List.get_mem execution.frame.cursors (Fin.cast execution.frame.length_eq.symm parent)
  obtain ⟨certificate, parentEq⟩ :=
    input.localizedOccurrenceFourLigandFrame_parent_cursor_history data.target execution.frame
      computed _ present parentClass
  have parentCurrent : certificate.parent.1.node.current? =
      some (referenceAt input mol c node data parent) := by
    rw [← parentEq, frameEq]
    exact frame_slot_current input mol c node data parent
  have history := occurrence_history_facts input certificate.parent
    (certificate.parent_provenance input)
  refine ⟨?_, input.detectedMultiCenterMolecule.ligandAtomAt_adj c (data.ligandOf parent)⟩
  rw [certificate.history_eq]
  exact List.mem_cons_of_mem _ (List.mem_of_head? (history.2.symm.trans parentCurrent))

/-- The empty-state ordinary comparison class of `left` contains no slot outside the pair
`left`, `right`: the `2+1+1` partition shape with `left`/`right` as the pair.  This is a premise
only for the refusal direction; the success direction derives its negation. -/
def BaseTiedPairExcluded (c : input.detectedMultiCenterMolecule.Center)
    (node : RawMolecule.CanonicalBranchNode) (data : OccurrenceData input mol c node)
    (left right : Fin 4) : Prop :=
  ∀ other : Fin 4, other ≠ left → other ≠ right →
    ordinaryKeys input mol single c node data other ≠
      ordinaryKeys input mol single c node data left

/-! ## Actual key invariance from an actual refined tie -/

include agreement admissible supported charge calibrated in
/-- An actual refined joint-key tie between two distinct slots forces the two empty-state
ordinary keys to be equal.  The proof uses the actual molecular symmetry reconstructed from the
tie and the actual empty-state comparison transport; no sorting or selection premise occurs. -/
theorem base_key_eq_of_slotKeys_tie
    (node : RawMolecule.CanonicalBranchNode) (reached : Reached mol node)
    (c : input.detectedMultiCenterMolecule.Center) (current : node.atom = c.1.val)
    (data : OccurrenceData input mol c node) (branch : TiedRootBranch input data.target)
    (references : List input.Atom) (reflected : Bool) (left right : Fin 4)
    (distinct : left ≠ right)
    (tie : slotKeys input mol single c node data
        (sideState input mol node (inputGeometry input) references reflected) references left =
      slotKeys input mol single c node data
        (sideState input mol node (inputGeometry input) references reflected) references right) :
    ordinaryKeys input mol single c node data right =
      ordinaryKeys input mol single c node data left := by
  obtain ⟨e, fixedE, entryE, _, _⟩ :=
    tie_sourceProper input mol agreement admissible supported single charge cfg calibrated node
      reached c current data branch references reflected left right distinct tie
  have historyFixed : ∀ atom ∈ node.history,
      relabelOf input (e : Equiv.Perm input.Atom) atom = atom := by
    intro value member
    have correspondence := lookup?_sound input node data.target data.found
    rw [← correspondence.history] at member
    obtain ⟨atom, present, valueEq⟩ := List.mem_map.mp member
    rw [← valueEq, relabelOf_val, fixedE atom present]
  obtain ⟨p, atomAction, keyAction⟩ :=
    actual_slot_key_action input mol agreement admissible supported single e c node data reached
      historyFixed
  have image : p left = right := by
    apply referenceAt_injective input mol c node data
    rw [atomAction left, entryE]
  rw [← image]
  exact keyAction left

/-! ## The odd boundary obstruction in the two-slot case -/

include agreement admissible supported charge calibrated in
/-- **The `2+1+1` case constructs an odd boundary symmetry.**  If the empty-state ordinary class
of the actually tied pair has no third member, an actual refined joint-key tie produces a
molecular automorphism fixing the reversed history and every accumulated reference, odd at the
detected center, and proper at every center outside the history. -/
theorem oddBoundary_of_baseTiedPairExcluded
    (node : RawMolecule.CanonicalBranchNode) (reached : Reached mol node)
    (c : input.detectedMultiCenterMolecule.Center) (current : node.atom = c.1.val)
    (data : OccurrenceData input mol c node) (branch : TiedRootBranch input data.target)
    (references : List input.Atom) (reflected : Bool) (left right : Fin 4)
    (distinct : left ≠ right)
    (tie : slotKeys input mol single c node data
        (sideState input mol node (inputGeometry input) references reflected) references left =
      slotKeys input mol single c node data
        (sideState input mol node (inputGeometry input) references reflected) references right)
    (pairExcluded : BaseTiedPairExcluded input mol single c node data left right)
    (tail : List input.Atom) (historyEq : data.target.1.node.history = c.1 :: tail) :
    OddBoundarySymmetry input cfg c tail.reverse references := by
  obtain ⟨e, fixedE, entryE, referencesE, properE⟩ :=
    tie_sourceProper input mol agreement admissible supported single charge cfg calibrated node
      reached c current data branch references reflected left right distinct tie
  have atomDifferent : referenceAt input mol c node data left ≠
      referenceAt input mol c node data right := by
    intro same
    exact distinct (referenceAt_injective input mol c node data same)
  have historyFixed : ∀ atom ∈ node.history,
      relabelOf input (e : Equiv.Perm input.Atom) atom = atom := by
    intro value member
    have correspondence := lookup?_sound input node data.target data.found
    rw [← correspondence.history] at member
    obtain ⟨atom, present, valueEq⟩ := List.mem_map.mp member
    rw [← valueEq, relabelOf_val, fixedE atom present]
  obtain ⟨p, atomAction, keyAction⟩ :=
    actual_slot_key_action input mol agreement admissible supported single e c node data reached
      historyFixed
  have image : p left = right := by
    apply referenceAt_injective input mol c node data
    rw [atomAction left, entryE]
  have keyRightLeft : ordinaryKeys input mol single c node data right =
      ordinaryKeys input mol single c node data left := by
    rw [← image]
    exact keyAction left
  obtain ⟨parent, parentClass, parentNotEligible⟩ :=
    parent_not_eligible input mol single c node data branch
  have parentSeparated : ∀ other : Fin 4, other ≠ parent →
      ordinaryKeys input mol single c node data other ≠
        ordinaryKeys input mol single c node data parent := by
    intro other different equal
    exact parentNotEligible
      ((eligible_iff_other input mol single c node data parent).mpr
        ⟨other, different, equal⟩)
  have leftEligible : left ∈ eligibleSlots input mol single c node data :=
    (eligible_iff_other input mol single c node data left).mpr
      ⟨right, distinct.symm, keyRightLeft⟩
  have rightEligible : right ∈ eligibleSlots input mol single c node data :=
    (eligible_iff_other input mol single c node data right).mpr
      ⟨left, distinct, keyRightLeft.symm⟩
  have parentNeLeft : parent ≠ left := by
    intro same
    exact parentNotEligible (same.symm ▸ leftEligible)
  have parentNeRight : parent ≠ right := by
    intro same
    exact parentNotEligible (same.symm ▸ rightEligible)
  obtain ⟨t, tNeLeft, tNeRight, tNeParent⟩ :=
    exists_fourth_slot left right parent distinct parentNeLeft parentNeRight
  have fixedT : p t = t := by
    by_contra different
    have cases := fourth_slot_trichotomy (p t) left right parent t distinct parentNeLeft
      parentNeRight tNeLeft tNeRight tNeParent different
    rcases cases with sameLeft | sameRight | sameParent
    · have equal := keyAction t
      rw [sameLeft] at equal
      exact pairExcluded t tNeLeft tNeRight equal.symm
    · have equal := keyAction t
      rw [sameRight] at equal
      exact pairExcluded t tNeLeft tNeRight (equal.symm.trans keyRightLeft)
    · have equal := keyAction t
      rw [sameParent] at equal
      exact parentSeparated t tNeParent equal.symm
  have fixedTAtom : (e : Equiv.Perm input.Atom) (referenceAt input mol c node data t) =
      referenceAt input mol c node data t := by
    have equal := atomAction t
    rw [fixedT] at equal
    exact equal.symm
  obtain ⟨parentHistory, parentAdjacent⟩ :=
    parent_atom_facts input mol single c node data parent parentClass
  have parentFixedE : (e : Equiv.Perm input.Atom)
      (referenceAt input mol c node data parent) = referenceAt input mol c node data parent :=
    fixedE (referenceAt input mol c node data parent) parentHistory
  have tAdjacent : input.moleculeGraph.Adj c.1 (referenceAt input mol c node data t) :=
    input.detectedMultiCenterMolecule.ligandAtomAt_adj c (data.ligandOf t)
  have parentNeT : referenceAt input mol c node data parent ≠
      referenceAt input mol c node data t := by
    intro same
    exact tNeParent (referenceAt_injective input mol c node data same).symm
  have reversedFixed : ∀ atom ∈ data.target.1.node.history.reverse,
      (e : Equiv.Perm input.Atom) atom = atom := by
    intro atom member
    exact fixedE atom (List.mem_reverse.mp member)
  obtain ⟨g, fixedG, _supportG, movedG, keepsG, properG⟩ :=
    reextend_proper input cfg data.target.1.node.history.reverse
      (referenceAt input mol c node data left) (referenceAt input mol c node data right) e
      reversedFixed entryE atomDifferent properE
  have historyReverse : data.target.1.node.history.reverse = tail.reverse ++ [c.1] := by
    rw [historyEq, List.reverse_cons]
  have centerMember : c.1 ∈ data.target.1.node.history.reverse := by
    rw [historyReverse]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have centerFixedG : (g : Equiv.Perm input.Atom) c.1 = c.1 := fixedG c.1 centerMember
  have parentFixedG : (g : Equiv.Perm input.Atom)
      (referenceAt input mol c node data parent) = referenceAt input mol c node data parent :=
    keepsG _ parentFixedE
  have tFixedG : (g : Equiv.Perm input.Atom) (referenceAt input mol c node data t) =
      referenceAt input mol c node data t :=
    keepsG _ fixedTAtom
  have movedGNe : (g : Equiv.Perm input.Atom) (referenceAt input mol c node data left) ≠
      referenceAt input mol c node data left := by
    rw [movedG]
    exact atomDifferent.symm
  have oddG :=
    local_odd_of_two_fixed_neighbors input.detectedMultiCenterMolecule g c centerFixedG
      (referenceAt input mol c node data parent) (referenceAt input mol c node data t)
      parentNeT parentAdjacent tAdjacent parentFixedG tFixedG
      ⟨referenceAt input mol c node data left,
        input.detectedMultiCenterMolecule.ligandAtomAt_adj c (data.ligandOf left), movedGNe⟩
  refine ⟨g, ?_, ?_, ?_, ?_⟩
  · intro atom member
    exact fixedG atom (historyReverse.symm ▸ member)
  · intro atom member
    exact keepsG atom (referencesE atom member)
  · rw [relativeSign_fixed input cfg g c (Subtype.ext centerFixedG)]
    exact oddG.2
  · intro d outsideD
    exact properG d (historyReverse.symm ▸ outsideD)

/-! ## The `2+1+1` refusal and its `3+1` success consequence -/

include agreement admissible supported charge calibrated in




theorem preparedDescriptor_refuses_of_baseTiedPairExcluded
    (node : RawMolecule.CanonicalBranchNode) (reached : Reached mol node)
    (c : input.detectedMultiCenterMolecule.Center) (current : node.atom = c.1.val)
    (data : OccurrenceData input mol c node) (branch : TiedRootBranch input data.target)
    (references : List input.Atom) (reflected : Bool) (left right : Fin 4)
    (distinct : left ≠ right)
    (tie : slotKeys input mol single c node data
        (sideState input mol node (inputGeometry input) references reflected) references left =
      slotKeys input mol single c node data
        (sideState input mol node (inputGeometry input) references reflected) references right)
    (pairExcluded : BaseTiedPairExcluded input mol single c node data left right) :
    preparedDescriptor? mol (jointOperations input mol) (structuralDepth mol node)
      (inputGeometry input) [] (references.map Fin.val) node = none := by
  have targetCurrent : data.target.1.node.current? = some c.1 := by
    apply current_of_value input
    have h := (lookup?_sound input node data.target data.found).current
    rw [current] at h
    exact h
  have facts := occurrence_history_facts input data.target data.real
  have headSome : data.target.1.node.history.head? = some c.1 :=
    facts.2.symm.trans targetCurrent
  obtain ⟨tail, tailEq⟩ := List.head?_eq_some_iff.mp headSome
  have boundary : data.target.1.node.history.reverse = tail.reverse ++ [c.1] := by
    rw [tailEq, List.reverse_cons]
  have notMemTail : c.1 ∉ tail := by
    have consNodup : (c.1 :: tail).Nodup := by
      rw [← tailEq]
      exact facts.1
    exact (List.nodup_cons.mp consNodup).1
  have outside : c.1 ∉ tail.reverse := fun member =>
    notMemTail (List.mem_reverse.mp member)
  have obstruction :=
    oddBoundary_of_baseTiedPairExcluded input mol agreement admissible supported single charge cfg
      calibrated node reached c current data branch references reflected left right distinct tie
      pairExcluded tail tailEq
  exact refusal_of_oddBoundary input mol agreement admissible supported single cfg calibrated c
    node data reached current tail.reverse references boundary outside obstruction

include agreement admissible supported charge calibrated in
/-- **Success forces a three-element tied class.**  An actual successful descriptor together with
an actual refined joint-key tie between the two slots forces a third slot with the same
empty-state ordinary key.  With the two tied keys, the base comparison class has at least three
members; this is the semantic `3+1` partition premise that the `2+1+1` shape excludes. -/
theorem exists_three_element_tied_class_of_success
    (node : RawMolecule.CanonicalBranchNode) (reached : Reached mol node)
    (c : input.detectedMultiCenterMolecule.Center) (current : node.atom = c.1.val)
    (data : OccurrenceData input mol c node) (branch : TiedRootBranch input data.target)
    (references : List input.Atom) (reflected : Bool) (left right : Fin 4)
    (distinct : left ≠ right)
    (tie : slotKeys input mol single c node data
        (sideState input mol node (inputGeometry input) references reflected) references left =
      slotKeys input mol single c node data
        (sideState input mol node (inputGeometry input) references reflected) references right)
    (success : ∃ label, preparedDescriptor? mol (jointOperations input mol)
      (structuralDepth mol node) (inputGeometry input) [] (references.map Fin.val) node =
        some label) :
    ∃ t : Fin 4, t ≠ left ∧ t ≠ right ∧
      ordinaryKeys input mol single c node data t =
        ordinaryKeys input mol single c node data left ∧
      ordinaryKeys input mol single c node data right =
        ordinaryKeys input mol single c node data left := by
  have keyRightLeft :=
    base_key_eq_of_slotKeys_tie input mol agreement admissible supported single charge cfg
      calibrated node reached c current data branch references reflected left right distinct tie
  by_contra absent
  have pairExcluded : BaseTiedPairExcluded input mol single c node data left right := by
    intro other otherLeft otherRight equal
    exact absent ⟨other, otherLeft, otherRight, equal, keyRightLeft⟩
  obtain ⟨label, successEq⟩ := success
  have refused :=
    preparedDescriptor_refuses_of_baseTiedPairExcluded input mol agreement admissible supported
      single charge cfg calibrated node reached c current data branch references reflected left
      right distinct tie pairExcluded
  rw [successEq] at refused
  cases refused

include agreement admissible supported charge calibrated in
/-- **The third tied slot is outward.**  Under a successful actual descriptor and an actual
refined tie, there are an ineligible incoming parent slot and a third slot outside the pair and
outside the parent slot that shares the tied ordinary key.  The parent slot is the unique
ineligible slot, so the tied class `left`, `right`, `t` occupies the three non-parent (outward)
slots and the parent is the separated singleton: the `3+1` shape. -/
theorem exists_parent_and_third_tied_slot_of_success
    (node : RawMolecule.CanonicalBranchNode) (reached : Reached mol node)
    (c : input.detectedMultiCenterMolecule.Center) (current : node.atom = c.1.val)
    (data : OccurrenceData input mol c node) (branch : TiedRootBranch input data.target)
    (references : List input.Atom) (reflected : Bool) (left right : Fin 4)
    (distinct : left ≠ right)
    (tie : slotKeys input mol single c node data
        (sideState input mol node (inputGeometry input) references reflected) references left =
      slotKeys input mol single c node data
        (sideState input mol node (inputGeometry input) references reflected) references right)
    (success : ∃ label, preparedDescriptor? mol (jointOperations input mol)
      (structuralDepth mol node) (inputGeometry input) [] (references.map Fin.val) node =
        some label) :
    ∃ parent t : Fin 4,
      IsLocalizedActualFrameParentCursor input data.target
        ((frames input single [] data.target data.real
          ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl).frame.cursorAt parent) ∧
      parent ∉ eligibleSlots input mol single c node data ∧
      t ≠ left ∧ t ≠ right ∧ t ≠ parent ∧
      ordinaryKeys input mol single c node data t =
        ordinaryKeys input mol single c node data left ∧
      ordinaryKeys input mol single c node data right =
        ordinaryKeys input mol single c node data left := by
  obtain ⟨t, tNeLeft, tNeRight, tKey, keyRightLeft⟩ :=
    exists_three_element_tied_class_of_success input mol agreement admissible supported single
      charge cfg calibrated node reached c current data branch references reflected left right
      distinct tie success
  obtain ⟨parent, parentClass, parentNotEligible⟩ :=
    parent_not_eligible input mol single c node data branch
  have leftEligible : left ∈ eligibleSlots input mol single c node data :=
    (eligible_iff_other input mol single c node data left).mpr
      ⟨right, distinct.symm, keyRightLeft⟩
  have parentNeLeft : parent ≠ left := by
    intro same
    exact parentNotEligible (same.symm ▸ leftEligible)
  have tNeParent : t ≠ parent := by
    intro same
    have keyLeftParent : ordinaryKeys input mol single c node data left =
        ordinaryKeys input mol single c node data parent :=
      tKey.symm.trans
        (congrArg (fun slot => ordinaryKeys input mol single c node data slot) same)
    exact parentNotEligible
      ((eligible_iff_other input mol single c node data parent).mpr
        ⟨left, parentNeLeft.symm, keyLeftParent⟩)
  exact ⟨parent, t, parentClass, parentNotEligible, tNeLeft, tNeRight, tNeParent, tKey,
    keyRightLeft⟩

/-! ## The actual refined `3+1` tied class under a successful descriptor -/

open RetainedCoherentSymmetry (InComponent inComponent_not_mem)
open LocalizedMarkedRetainedMolecularSelection (retainedCarrierFuel)
open LocalizedChemicalRingJointPreparedTieBoundary (tie_boundaryProper)
open LocalizedChemicalRingJointPreparedPromotionBalance (selectedSlots_perm_slotAction)
open LocalizedChemicalRingJointMarkerFrameExecution (selectedSlots selectedSlots_key_eq)
open LocalizedChemicalRingResidualThreeCycleRefusal (slotAction referenceAt_action center_fixed)
open LocalizedChemicalRingResidualOrientationStep (agreeOn_strictDescendants)
open LocalizedChemicalRingSenseTransport (AgreeOn)
open LocalizedChemicalRingRelabel (pullback mirror_pullback)
open LocalizedMarkedTerminalReferenceScope (StrictDescendant)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign relativeSign_eq_one_or_neg_one)
open LocalizedChemicalRingFixedParentParity (fixed_parent_dichotomy)

include agreement admissible supported charge calibrated in
/-- **The actual refined `3+1` class.**  For an actual refined joint-key tie under the prepared
generated side state at the structural depth, either geometry side and arbitrary accumulated
references, a successful actual prepared descriptor forces an incoming parent slot and a third
slot outside the tied pair and the parent such that the three outward slots carry one actual
generated refined key and the parent is separated from it.  Unlike the base-class results, all
key equalities here are stated for the current generated slot keys (`selectedSlots`/`slotKeys`),
not for the empty-state ordinary comparison.  The returned `∀ other ≠ parent` equality and the
parent separation are exactly the `outsideEqual`/`separated` pair consumed by the finite
three-one partition bridge; no sorting exhaustiveness is assumed. -/
theorem exists_current_third_tied_slot_of_success
    (node : RawMolecule.CanonicalBranchNode) (reached : Reached mol node)
    (c : input.detectedMultiCenterMolecule.Center) (current : node.atom = c.1.val)
    (data : OccurrenceData input mol c node) (branch : TiedRootBranch input data.target)
    (references : List input.Atom) (reflected : Bool) (left right : Fin 4)
    (distinct : left ≠ right)
    (tie : slotKeys input mol single c node data
        (sideState input mol node (inputGeometry input) references reflected) references left =
      slotKeys input mol single c node data
        (sideState input mol node (inputGeometry input) references reflected) references right)
    (success : ∃ label, preparedDescriptor? mol (jointOperations input mol)
      (structuralDepth mol node) (inputGeometry input) [] (references.map Fin.val) node =
        some label) :
    ∃ parent t : Fin 4,
      IsLocalizedActualFrameParentCursor input data.target
        ((frames input single [] data.target data.real
          ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl).frame.cursorAt parent) ∧
      t ≠ left ∧ t ≠ right ∧ t ≠ parent ∧
      slotKeys input mol single c node data
          (sideState input mol node (inputGeometry input) references reflected) references t =
        slotKeys input mol single c node data
          (sideState input mol node (inputGeometry input) references reflected) references left ∧
      slotKeys input mol single c node data
          (sideState input mol node (inputGeometry input) references reflected) references right =
        slotKeys input mol single c node data
          (sideState input mol node (inputGeometry input) references reflected) references left ∧
      (∀ other : Fin 4, other ≠ parent →
        slotKeys input mol single c node data
            (sideState input mol node (inputGeometry input) references reflected) references other =
          slotKeys input mol single c node data
            (sideState input mol node (inputGeometry input) references reflected) references left) ∧
      slotKeys input mol single c node data
          (sideState input mol node (inputGeometry input) references reflected) references left ≠
        slotKeys input mol single c node data
          (sideState input mol node (inputGeometry input) references reflected) references parent := by
  obtain ⟨e, fixedE, entryE, refsE, properOffE⟩ :=
    tie_boundaryProper input mol agreement admissible supported single charge cfg calibrated node
      reached c current data branch references reflected left right distinct tie
  have correspondence := lookup?_sound input node data.target data.found
  have historyFixed : ∀ value ∈ node.history,
      relabelOf input (e : Equiv.Perm input.Atom) value = value := by
    intro value member
    rw [← correspondence.history] at member
    obtain ⟨atom, present, rfl⟩ := List.mem_map.mp member
    rw [relabelOf_val, fixedE atom present]
  have centerFixedPer := center_fixed input mol e c node reached current historyFixed
  have targetCurrent : data.target.1.node.current? = some c.1 := by
    apply current_of_value input
    have h := correspondence.current
    rw [current] at h
    exact h
  have facts := occurrence_history_facts input data.target data.real
  have headSome : data.target.1.node.history.head? = some c.1 :=
    facts.2.symm.trans targetCurrent
  obtain ⟨tail, tailEq⟩ := List.head?_eq_some_iff.mp headSome
  have boundary : data.target.1.node.history.reverse = tail.reverse ++ [c.1] := by
    rw [tailEq, List.reverse_cons]
  have notMemTail : c.1 ∉ tail := by
    have consNodup : (c.1 :: tail).Nodup := by
      rw [← tailEq]
      exact facts.1
    exact (List.nodup_cons.mp consNodup).1
  have outside : c.1 ∉ tail.reverse := fun member =>
    notMemTail (List.mem_reverse.mp member)
  have handed : permHandedness (input.detectedMultiCenterMolecule.ligandPermAt e c) = 1 := by
    rw [← relativeSign_fixed input cfg e c centerFixedPer]
    rcases relativeSign_eq_one_or_neg_one input.detectedMultiCenterMolecule cfg e c with even | odd
    · exact even
    · exfalso
      have fixedBoundary : ∀ atom ∈ tail.reverse ++ [c.1],
          (e : Equiv.Perm input.Atom) atom = atom := by
        intro atom member
        apply fixedE
        have reversed : atom ∈ data.target.1.node.history.reverse := by
          rw [boundary]
          exact member
        exact List.mem_reverse.mp reversed
      have properBoundaryOff : ∀ d : input.detectedMultiCenterMolecule.Center,
          d.1 ∉ tail.reverse ++ [c.1] →
            relativeSign input.detectedMultiCenterMolecule cfg e d = 1 := by
        intro d outsideD
        apply properOffE
        intro present
        apply outsideD
        rw [← boundary]
        exact List.mem_reverse.mpr present
      have obstruction : OddBoundarySymmetry input cfg c tail.reverse references :=
        ⟨e, fixedBoundary, refsE, odd, properBoundaryOff⟩
      have refused := refusal_of_oddBoundary input mol agreement admissible supported single cfg
        calibrated c node data reached current tail.reverse references boundary outside obstruction
      obtain ⟨label, successEq⟩ := success
      rw [successEq] at refused
      cases refused
  have slotHanded : permHandedness (slotAction input mol e c node data) = 1 := by
    have compose : slotAction input mol e c node data =
        data.ligandOf⁻¹ * input.detectedMultiCenterMolecule.ligandPermAt e c *
          data.ligandOf := by
      ext i
      rfl
    rw [compose, permHandedness_conj_inv]
    exact handed
  obtain ⟨parent, parentClassState, parentSeparatedRefined⟩ :=
    LocalizedChemicalRingJointMarkerEligibility.parent_joint_singleton input single
      (sideState input mol node (inputGeometry input) references reflected) data.target data.real
      ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl references
      (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) branch
  have parentSeparated : ∀ other : Fin 4, other ≠ parent →
      slotKeys input mol single c node data
          (sideState input mol node (inputGeometry input) references reflected) references other ≠
        slotKeys input mol single c node data
          (sideState input mol node (inputGeometry input) references reflected) references parent :=
    parentSeparatedRefined
  have stateFrame :
      (frames input single (sideState input mol node (inputGeometry input) references reflected)
        data.target data.real ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl).frame =
        data.frame := by
    have computed :=
      (frames input single (sideState input mol node (inputGeometry input) references reflected)
        data.target data.real
        ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl).frameComputed
    rw [data.frameExec] at computed
    exact (Option.some.inj computed).symm
  have emptyFrame :
      (frames input single [] data.target data.real
        ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl).frame = data.frame := by
    have computed :=
      (frames input single [] data.target data.real
        ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl).frameComputed
    rw [data.frameExec] at computed
    exact (Option.some.inj computed).symm
  have framesEqual :
      (frames input single [] data.target data.real
          ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl).frame =
        (frames input single (sideState input mol node (inputGeometry input) references reflected)
          data.target data.real
          ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl).frame :=
    emptyFrame.trans stateFrame.symm
  have parentClass :
      IsLocalizedActualFrameParentCursor input data.target
        ((frames input single [] data.target data.real
          ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl).frame.cursorAt parent) := by
    rw [framesEqual]
    exact parentClassState
  obtain ⟨parentHistory, _parentAdjacent⟩ :=
    parent_atom_facts input mol single c node data parent parentClass
  have parentFixedE : (e : Equiv.Perm input.Atom)
      (referenceAt input mol c node data parent) = referenceAt input mol c node data parent :=
    fixedE _ parentHistory
  have parentFixedSlot : slotAction input mol e c node data parent = parent := by
    apply referenceAt_injective input mol c node data
    rw [referenceAt_action input mol e c node data centerFixedPer parent, parentFixedE]
  have leftMoves : slotAction input mol e c node data left = right := by
    apply referenceAt_injective input mol c node data
    rw [referenceAt_action input mol e c node data centerFixedPer left, entryE]
  have parentNeLeft : parent ≠ left := by
    intro same
    have rightNeParent : right ≠ parent := fun equal => distinct (equal.trans same).symm
    have keyEqual : slotKeys input mol single c node data
        (sideState input mol node (inputGeometry input) references reflected) references right =
        slotKeys input mol single c node data
          (sideState input mol node (inputGeometry input) references reflected) references parent :=
      tie.symm.trans (congrArg (fun slot => slotKeys input mol single c node data
        (sideState input mol node (inputGeometry input) references reflected)
        references slot) same).symm
    exact parentSeparated right rightNeParent keyEqual
  have parentNeRight : parent ≠ right := by
    intro same
    have leftNeParent : left ≠ parent := fun equal => distinct (equal.trans same)
    have keyEqual : slotKeys input mol single c node data
        (sideState input mol node (inputGeometry input) references reflected) references left =
        slotKeys input mol single c node data
          (sideState input mol node (inputGeometry input) references reflected) references parent :=
      tie.trans (congrArg (fun slot => slotKeys input mol single c node data
        (sideState input mol node (inputGeometry input) references reflected)
        references slot) same).symm
    exact parentSeparated left leftNeParent keyEqual
  obtain ⟨t, tNeLeft, tNeRight, tNeParent⟩ :=
    exists_fourth_slot left right parent distinct parentNeLeft parentNeRight
  have pNontrivial : slotAction input mol e c node data ≠ 1 := by
    intro identity
    have applied := congrArg (fun σ : Equiv.Perm (Fin 4) => σ left) identity
    change slotAction input mol e c node data left = left at applied
    exact distinct (applied.symm.trans leftMoves)
  have imageNeParent : slotAction input mol e c node data t ≠ parent := by
    intro same
    have equal : slotAction input mol e c node data t =
        slotAction input mol e c node data parent := by
      rw [same, parentFixedSlot]
    exact tNeParent ((slotAction input mol e c node data).injective equal)
  have movesThird : slotAction input mol e c node data t = left := by
    rcases fixed_parent_dichotomy (slotAction input mol e c node data) parent parentFixedSlot
      pNontrivial with oddHand | ⟨_evenHand, _cube, moved⟩
    · rw [slotHanded] at oddHand
      norm_num at oddHand
    · have movedT : slotAction input mol e c node data t ≠ t := moved t tNeParent
      rcases fourth_slot_trichotomy (slotAction input mol e c node data t) left right parent t
        distinct parentNeLeft parentNeRight tNeLeft tNeRight tNeParent movedT with
        sameLeft | sameRight | sameParent
      · exact sameLeft
      · have equal : slotAction input mol e c node data t =
            slotAction input mol e c node data left := by
          rw [sameRight, leftMoves]
        exact absurd ((slotAction input mol e c node data).injective equal) tNeLeft
      · exact absurd sameParent imageNeParent
  have fixedReferencesVal : ∀ reference ∈ references,
      ((e : Equiv.Perm input.Atom) reference).val = reference.val :=
    fun reference member => congrArg (fun atom : input.Atom => atom.val) (refsE reference member)
  have carried : ∀ atom ∈ tail.reverse, atom.val ∈ node.history := by
    intro atom member
    have inBoundary : atom ∈ tail.reverse ++ [c.1] := List.mem_append_left [c.1] member
    have reversed : atom ∈ data.target.1.node.history.reverse := by
      rw [boundary]
      exact inBoundary
    have inHistory : atom ∈ data.target.1.node.history := List.mem_reverse.mp reversed
    rw [← correspondence.history]
    exact List.mem_map.mpr ⟨atom, inHistory, rfl⟩
  have properBoundary : ∀ d : input.detectedMultiCenterMolecule.Center,
      InComponent input.moleculeGraph tail.reverse c.1 d.1 → d.1 ≠ c.1 →
        relativeSign input.detectedMultiCenterMolecule cfg e d = 1 := by
    intro d member different
    apply properOffE
    intro present
    have reversed : d.1 ∈ data.target.1.node.history.reverse := List.mem_reverse.mpr present
    rw [boundary] at reversed
    rcases List.mem_append.mp reversed with inTail | last
    · exact inComponent_not_mem input.moleculeGraph member inTail
    · exact different (List.mem_singleton.mp last)
  have base := agreeOn_strictDescendants input mol agreement admissible supported single cfg e
    calibrated tail.reverse node c.1 current.symm outside carried reached properBoundary
  have childAgree : AgreeOn (StrictDescendant mol node) mol
      (pullback (relabelOf input (e : Equiv.Perm input.Atom))
        (observedGeometry input reflected))
      (observedGeometry input reflected) := by
    cases reflected with
    | false => exact base
    | true =>
        simpa only [observedGeometry, Bool.true_eq, if_true, mirror_pullback] using base.mirror
  have selectedPerm := selectedSlots_perm_slotAction input mol agreement admissible supported
    single c node data reached current e historyFixed references fixedReferencesVal
    (structuralDepth mol node) (observedGeometry input reflected) childAgree
  have selectedPermSide : List.Perm
      (selectedSlots input mol single c node data
        (sideState input mol node (inputGeometry input) references reflected) references)
      ((selectedSlots input mol single c node data
        (sideState input mol node (inputGeometry input) references reflected) references).map
        (slotAction input mol e c node data)) := by
    simpa only [sideState, observedGeometry] using selectedPerm
  have leftEligible :
      left ∈ LocalizedChemicalRingJointMarkerEligibility.eligibleSlots input single
        (sideState input mol node (inputGeometry input) references reflected) data.target
        data.real ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl references
        (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) :=
    (LocalizedChemicalRingJointMarkerEligibility.eligible_iff_other input single
      (sideState input mol node (inputGeometry input) references reflected) data.target data.real
      ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl references
      (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) left).mpr
      ⟨right, distinct.symm, tie.symm⟩
  have leftSelected : left ∈ selectedSlots input mol single c node data
      (sideState input mol node (inputGeometry input) references reflected) references :=
    leftEligible
  have imageMember : left ∈ (selectedSlots input mol single c node data
      (sideState input mol node (inputGeometry input) references reflected) references).map
      (slotAction input mol e c node data) :=
    selectedPermSide.subset leftSelected
  obtain ⟨source, sourceMember, sourceImage⟩ := List.mem_map.mp imageMember
  have sourceIsThird : source = t := by
    apply (slotAction input mol e c node data).injective
    rw [sourceImage, movesThird]
  have thirdSelected : t ∈ selectedSlots input mol single c node data
      (sideState input mol node (inputGeometry input) references reflected) references := by
    rw [← sourceIsThird]
    exact sourceMember
  have thirdKey : slotKeys input mol single c node data
      (sideState input mol node (inputGeometry input) references reflected) references t =
      slotKeys input mol single c node data
        (sideState input mol node (inputGeometry input) references reflected) references left :=
    selectedSlots_key_eq input mol single c node data
      (sideState input mol node (inputGeometry input) references reflected) references branch
      t left thirdSelected leftSelected
  have allNonParent : ∀ other : Fin 4, other ≠ parent →
      slotKeys input mol single c node data
          (sideState input mol node (inputGeometry input) references reflected) references other =
        slotKeys input mol single c node data
          (sideState input mol node (inputGeometry input) references reflected) references left := by
    intro other otherNeParent
    by_cases isThird : other = t
    · rw [isThird]
      exact thirdKey
    · rcases fourth_slot_trichotomy other left right parent t distinct parentNeLeft parentNeRight
        tNeLeft tNeRight tNeParent isThird with sameLeft | sameRight | sameParent
      · rw [sameLeft]
      · rw [sameRight]
        exact tie.symm
      · exact absurd sameParent otherNeParent
  have separated : slotKeys input mol single c node data
      (sideState input mol node (inputGeometry input) references reflected) references left ≠
      slotKeys input mol single c node data
        (sideState input mol node (inputGeometry input) references reflected) references parent :=
    parentSeparated left parentNeLeft.symm
  exact ⟨parent, t, parentClass, tNeLeft, tNeRight, tNeParent, thirdKey, tie.symm, allNonParent,
    separated⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionApplicability

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionApplicability.base_key_eq_of_slotKeys_tie
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionApplicability.oddBoundary_of_baseTiedPairExcluded
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionApplicability.preparedDescriptor_refuses_of_baseTiedPairExcluded
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionApplicability.exists_three_element_tied_class_of_success
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionApplicability.exists_parent_and_third_tied_slot_of_success
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionApplicability.exists_current_third_tied_slot_of_success
