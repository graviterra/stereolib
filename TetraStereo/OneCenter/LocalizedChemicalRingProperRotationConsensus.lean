import TetraStereo.OneCenter.LocalizedChemicalRingC3ReferenceObstruction
import TetraStereo.OneCenter.LocalizedChemicalRingResidualThreeCycleRefusal
import TetraStereo.OneCenter.LocalizedChemicalRingDefaultMarkerLayout
import TetraStereo.OneCenter.LocalizedChemicalRingActualComparisonLabelMatch
import TetraStereo.OneCenter.LocalizedChemicalRingDecodedRelation
import TetraStereo.OneCenter.RootedBranchFrameReindexInvariance
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2400000

/-!
**A detected root with a proper threefold rotation receives an actual descriptor.**

On the admitted eleven-atom cyclic input of `LocalizedChemicalRingC3ReferenceFixture`, the actual
no-context root call of the inherited-fallback evaluator returns a descriptor at carbon 0, while
the rotation is a `ProperTransport` between two of its ligands. So the independent criterion
`PairwiseProperDistinguishable` fails at a center the evaluator assigns.

Nothing about the output is supplied. Every eligible reference reads successfully, because an
actual marked-key tie would give a graph automorphism fixing that reference and moving a ligand,
and the three automorphisms of this input do not do that. The three readings agree by the actual
reading transport along the rotation. The fluorine slot is excluded from the eligible population
by the atomic numbers decoded from an actual prior-key tie.

Scope: one input and one center. The letter is not evaluated. This shows that
"assigned implies pairwise proper distinguishability" is not a theorem of the present evaluator
on the present ring domain; it says nothing about the converse direction.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingProperRotationConsensus

open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
open LocalizedCumulativeDecoratedTree
open LocalizedChemicalRingActualFullLabelMatch LocalizedChemicalRingDecodedRelation
open LocalizedChemicalRingActualComparisonLabelMatch
open LocalizedMarkedRetainedMolecularSelection LocalizedMarkedRetainedOrdinaryRanking
open LocalizedMarkedRetainedCanonicalFrame LocalizedMarkedRetainedStateReader
open LocalizedMarkedRetainedPromotedRanking
open LocalizedChemicalRingInheritedRefusalCases LocalizedChemicalRingPhysicalSense
open LocalizedChemicalRingResidualThreeCycleRefusal (slotAction referenceAt_action reading_action)
open LocalizedChemicalRingSelectedParentEligibility (eligible_iff_other)
open LocalizedMarkedRetainedSparsePromotedOperations (sparseOperations)
open LocalizedMarkedReachableConfigurations (Reached reached_root)
open LocalizedGenericMarkedRecalculation (structuralDepth)
open RootedTetrahedralBranchSymmetry

noncomputable section
open scoped Classical

/-! ## Slot atoms and atomic numbers, for any input -/

section Generic

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (single : input.moleculeGraph.SimpleBonded)
  (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
  (data : OccurrenceData input mol c node)

theorem referenceAt_injective : Function.Injective (referenceAt input mol c node data) := by
  intro i j same
  exact data.ligandOf.injective (input.detectedMultiCenterMolecule.ligandAtomAt_injective c same)

/-- The actual frame cursor of a slot carries that slot's ligand atom, in every auxiliary state. -/
theorem slot_current (state : OccurrenceAuxState) (slot : Fin 4) :
    ((frames input single state data.target data.real
      ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl).frame.cursorAt
        slot).occurrence.1.node.current? = some (referenceAt input mol c node data slot) := by
  have frameEq : (frames input single state data.target data.real
      ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl).frame = data.frame :=
    Option.some.inj ((frames input single state data.target data.real
      ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl).frameComputed.symm.trans
        data.frameExec)
  have value := data.atomAt_eq slot
  change (data.frame.cursorAt slot).occurrence.1.node.current?.map Fin.val =
    some (referenceAt input mol c node data slot).val at value
  rw [frameEq]
  cases found : (data.frame.cursorAt slot).occurrence.1.node.current? with
  | none =>
      rw [found, Option.map_none] at value
      exact absurd value (by simp)
  | some atom =>
      rw [found, Option.map_some] at value
      exact congrArg some (Fin.ext (Option.some.inj value))

/-- Equal actual prior keys at two frame slots give equal atomic numbers of the two ligand atoms.
The state is arbitrary. -/
theorem slot_tie_atomZ (state : OccurrenceAuxState) (left right : Fin 4)
    (tie : rawStateKeys input single state data.target data.real
        ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl left =
      rawStateKeys input single state data.target data.real
        ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl right) :
    input.moleculeGraph.atomZ (referenceAt input mol c node data left) =
      input.moleculeGraph.atomZ (referenceAt input mol c node data right) := by
  let frame := frames input single state data.target data.real
    ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl
  have full := frame.fullOrdering (rawStateDescriptorMap_tetrahedral input state) single
    ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl left right
  change frame.retainedKeys ⟨input.molecularFrameUnit data.target.1, data.detected⟩ left =
    frame.retainedKeys ⟨input.molecularFrameUnit data.target.1, data.detected⟩ right at tie
  rw [tie, (completeLigandRule5Key_compare_eq_iff _ _).mpr rfl] at full
  have leftBuilt := frame_uniform_built (rawStateDescriptorMap input state) data.target frame left
  have rightBuilt := frame_uniform_built (rawStateDescriptorMap input state) data.target frame right
  rw [(frame.stages left).a.sourceEq] at leftBuilt
  rw [(frame.stages right).a.sourceEq] at rightBuilt
  obtain ⟨treeL, treeR, sourceL, sourceR, realL, realR, same⟩ :=
    full_tie_same_observations _ _ _ _ _ _ _ _ leftBuilt rightBuilt full
  have labels := related_atomLabel (shape_eq_of_observation_eq treeL treeR same) realL realR
    (shapePositionCursorRelation_sources _ sourceL sourceR)
  have atomicEq := congrArg (fun label => (ofLex label).1) labels
  exact (MoleculeGraph.officialNodeAtomLabel_first_eq_atomZ_of_current input.moleculeGraph _ _
      (slot_current input mol single c node data state left)).symm.trans
    (atomicEq.trans (MoleculeGraph.officialNodeAtomLabel_first_eq_atomZ_of_current
      input.moleculeGraph _ _ (slot_current input mol single c node data state right)))

end Generic

/-! ## The eleven-atom input -/

section Fixture

open LocalizedChemicalRingC3ReferenceFixture LocalizedChemicalRingC3ReferenceObstruction

private theorem rotation_fixed_cases : ∀ x : Fin 11, rotation x = x → x = 0 ∨ x = 1 := by
  decide +kernel

private theorem rotation_sq_fixed_cases :
    ∀ x : Fin 11, (rotation * rotation) x = x → x = 0 ∨ x = 1 := by
  decide +kernel

private theorem fluorine_unique (x : Fin 11) (same : graph.atomZ x = graph.atomZ (1 : Fin 11)) :
    x = 1 := by
  revert same
  fin_cases x <;> decide +kernel

private theorem neighbor_cases (x : Fin 11) (adjacent : graph.Adj (0 : Fin 11) x) :
    x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 := by
  revert adjacent
  fin_cases x <;> decide +kernel

private theorem boron_orbit : ∀ x y : Fin 11, (x = 2 ∨ x = 3 ∨ x = 4) → (y = 2 ∨ y = 3 ∨ y = 4) →
    y = x ∨ y = rotation x ∨ y = rotation (rotation x) := by
  decide +kernel

private theorem root_reached : Reached mol (canonicalCenterRoot 0) :=
  reached_root mol 0 (by decide)

private theorem rotation_history_fixed : ∀ atom ∈ (canonicalCenterRoot 0).history,
    relabelOf certified (physicalRotation : Equiv.Perm certified.Atom) atom = atom := by
  intro atom member
  have same : atom = 0 := List.mem_singleton.mp member
  subst same
  rfl

variable (data : OccurrenceData certified mol center (canonicalCenterRoot 0))

private theorem root_history : data.target.1.node.history = [(0 : Fin 11)] := by
  apply List.map_injective_iff.mpr Fin.val_injective
  exact (LocalizedMarkedCarrierLookup.lookup?_sound certified _ _ data.found).history

private theorem root_address : data.target.1.address = [] := by
  have address := (certified.legitimateOccurrence_transport single_bonded 1
    (certified.carrierOccurrence_legitimate single_bonded data.target)).sourceAddress
  rw [address]
  simp [CertifiedLocalizedCIPInput.canonicalAddress, root_history data]

/-- The actual reading is unchanged along the rotation's action on the frame slots. -/
private theorem reading_turn (depth : Nat) (reflected : Bool) (slot : Fin 4) :
    generatedReading certified mol center (canonicalCenterRoot 0) data depth reflected
        (slotAction certified mol physicalRotation center (canonicalCenterRoot 0) data slot) =
      generatedReading certified mol center (canonicalCenterRoot 0) data depth reflected slot :=
  reading_action certified mol single_bonded physicalRotation center (canonicalCenterRoot 0) data
    structure_agreement admissible supported root_reached rfl rotation_history_fixed cfg calibrated
    rfl [] (by simp) (by intro atom member; cases member)
    (fun d _ different => absurd (congrArg Subtype.val (center_unique d)) different)
    (every_automorphism_proper cfg physicalRotation) depth reflected slot

/-- No actually eligible reference is the fluorine: a prior tie preserves the atomic number. -/
private theorem eligible_ne_fluorine (slot : Fin 4)
    (member : slot ∈ eligibleSlots certified mol single_bonded center (canonicalCenterRoot 0) data) :
    referenceAt certified mol center (canonicalCenterRoot 0) data slot ≠ (1 : Fin 11) := by
  intro fluorine
  obtain ⟨other, different, equal⟩ :=
    (eligible_iff_other certified mol single_bonded center (canonicalCenterRoot 0) data slot).mp member
  have z := slot_tie_atomZ certified mol single_bonded center (canonicalCenterRoot 0) data [] other
    slot equal
  rw [fluorine] at z
  have same := fluorine_unique _ z
  exact different (referenceAt_injective certified mol center (canonicalCenterRoot 0) data
    (same.trans fluorine.symm))

private theorem eligible_boron (slot : Fin 4)
    (member : slot ∈ eligibleSlots certified mol single_bonded center (canonicalCenterRoot 0) data) :
    referenceAt certified mol center (canonicalCenterRoot 0) data slot = (2 : Fin 11) ∨
      referenceAt certified mol center (canonicalCenterRoot 0) data slot = (3 : Fin 11) ∨
      referenceAt certified mol center (canonicalCenterRoot 0) data slot = (4 : Fin 11) := by
  have adjacent : graph.Adj (0 : Fin 11)
      (referenceAt certified mol center (canonicalCenterRoot 0) data slot) :=
    physical.ligandAtomAt_adj center (data.ligandOf slot)
  rcases neighbor_cases _ adjacent with fluorine | boron
  · exact absurd fluorine (eligible_ne_fluorine data slot member)
  · exact boron

/-- Neither actual failure mode of the no-context step occurs, at any depth and on either
geometry side. -/
private theorem no_reading_failure (depth : Nat) (reflected : Bool) :
    ¬ ReadingFailure certified mol single_bonded center (canonicalCenterRoot 0) data depth
      reflected := by
  intro failure
  rcases failure with ⟨slot, member, left, right, distinct, tie⟩ |
    ⟨first, memberF, second, memberS, a, b, readF, readS, different⟩
  · change refinedKey certified single_bonded
        (generated certified mol (canonicalCenterRoot 0) depth reflected
          (referenceAt certified mol center (canonicalCenterRoot 0) data slot).val)
        data.target data.real ⟨certified.molecularFrameUnit data.target.1, data.detected⟩ rfl
        (referenceAt certified mol center (canonicalCenterRoot 0) data slot)
        (retainedCarrierFuel certified) (2 * (retainedCarrierFuel certified + 1)) left =
      refinedKey certified single_bonded
        (generated certified mol (canonicalCenterRoot 0) depth reflected
          (referenceAt certified mol center (canonicalCenterRoot 0) data slot).val)
        data.target data.real ⟨certified.molecularFrameUnit data.target.1, data.detected⟩ rfl
        (referenceAt certified mol center (canonicalCenterRoot 0) data slot)
        (retainedCarrierFuel certified) (2 * (retainedCarrierFuel certified + 1)) right at tie
    obtain ⟨π, aut, _, entry, fixedReference⟩ :=
      LocalizedChemicalRingDefaultMarkerLayout.actual_root_default_tie_reference_fixed_aut certified
        single_bonded _ data.target data.real
        ⟨certified.molecularFrameUnit data.target.1, data.detected⟩ rfl (root_address data)
        (referenceAt certified mol center (canonicalCenterRoot 0) data slot) left right tie
        (referenceAt certified mol center (canonicalCenterRoot 0) data left)
        (referenceAt certified mol center (canonicalCenterRoot 0) data right)
        (slot_current certified mol single_bonded center (canonicalCenterRoot 0) data _ left)
        (slot_current certified mol single_bonded center (canonicalCenterRoot 0) data _ right)
        ⟨0, constant_charge⟩
    have notCenter : referenceAt certified mol center (canonicalCenterRoot 0) data slot ≠
        (0 : Fin 11) := ligandAtomAt_ne_center physical center (data.ligandOf slot)
    have notFluorine := eligible_ne_fluorine data slot member
    rcases graph_aut_classification (⟨π, aut⟩ : graph.Aut) with one | turn | turnTwice
    · have identity : π = 1 := one
      rw [identity] at entry
      exact distinct (referenceAt_injective certified mol center (canonicalCenterRoot 0) data entry)
    · have rotated : π = rotation := turn
      rw [rotated] at fixedReference
      rcases rotation_fixed_cases _ fixedReference with zero | fluorine
      · exact notCenter zero
      · exact notFluorine fluorine
    · have rotated : π = rotation * rotation := turnTwice
      rw [rotated] at fixedReference
      rcases rotation_sq_fixed_cases _ fixedReference with zero | fluorine
      · exact notCenter zero
      · exact notFluorine fluorine
  · have turnAt (slot : Fin 4) := referenceAt_action certified mol physicalRotation center
      (canonicalCenterRoot 0) data rotation_center slot
    have same : generatedReading certified mol center (canonicalCenterRoot 0) data depth reflected
          second =
        generatedReading certified mol center (canonicalCenterRoot 0) data depth reflected
          first := by
      rcases boron_orbit _ _ (eligible_boron data first memberF) (eligible_boron data second memberS)
        with equal | once | twice
      · rw [referenceAt_injective certified mol center (canonicalCenterRoot 0) data equal]
      · have slotEq : second =
            slotAction certified mol physicalRotation center (canonicalCenterRoot 0) data first :=
          referenceAt_injective certified mol center (canonicalCenterRoot 0) data
            (once.trans (turnAt first).symm)
        rw [slotEq]
        exact reading_turn data depth reflected first
      · have slotEq : second =
            slotAction certified mol physicalRotation center (canonicalCenterRoot 0) data
              (slotAction certified mol physicalRotation center (canonicalCenterRoot 0) data
                first) :=
          referenceAt_injective certified mol center (canonicalCenterRoot 0) data
            (twice.trans ((turnAt _).trans
              (congrArg (fun x => (physicalRotation : Equiv.Perm certified.Atom) x)
                (turnAt first))).symm)
        rw [slotEq, reading_turn data depth reflected, reading_turn data depth reflected]
    rw [readF, readS] at same
    exact different (Option.some.inj same).symm

end Fixture

open LocalizedChemicalRingC3ReferenceFixture LocalizedChemicalRingC3ReferenceObstruction in
/-- **The actual no-context root call assigns a descriptor at carbon 0.** Both failure modes of
the actual step are excluded on both geometry sides; no output or comparison is supplied. -/
theorem root_descriptor_exists :
    ∃ d, LocalizedChemicalRingInheritedFallback.assignCenter? mol (sparseOperations certified mol)
      (inputGeometry certified) 0 = some d := by
  obtain ⟨data⟩ := occurrenceData_exists certified mol structure_agreement admissible supported
    single_bonded center (canonicalCenterRoot 0) root_reached rfl rfl
  apply Option.ne_none_iff_exists'.mp
  intro refused
  change LocalizedChemicalRingInheritedFallback.descriptor? mol (sparseOperations certified mol)
    (structuralDepth mol (canonicalCenterRoot 0)) (inputGeometry certified) [] none
    (canonicalCenterRoot 0) = none at refused
  have failures := (descriptor_none_iff certified mol single_bonded cfg center (calibrated center)
    (canonicalCenterRoot 0) data structure_agreement admissible supported
    (structuralDepth mol (canonicalCenterRoot 0)) none).mp refused
  rcases failures.2 with failure | failure
  · exact no_reading_failure data _ false failure.2
  · exact no_reading_failure data _ true failure.2

open LocalizedChemicalRingC3ReferenceFixture in
/-- The rotation is an independent physical proper transport between two distinct ligands. -/
theorem rotation_proper_transport :
    ∃ i j : Fin 4, i ≠ j ∧ ProperTransport physical cfg center i j := by
  have adjacent : graph.Adj (0 : Fin 11) (2 : Fin 11) := by decide
  obtain ⟨i, atI⟩ := physical.ligandAtomAt_surjective center (2 : Fin 11) adjacent
  have moved : (physicalRotation : Equiv.Perm certified.Atom) (2 : Fin 11) = (3 : Fin 11) := rfl
  refine ⟨i, physical.ligandPermAt physicalRotation center i, ?_, ?_⟩
  · intro same
    have image := physical.ligandAtomAt_ligandPermAt physicalRotation center i
    rw [rotation_center, ← same, atI, moved] at image
    exact absurd image (by decide)
  · refine ⟨physicalRotation, rotation_center, rfl, ?_⟩
    intro d _
    have unique := center_unique d
    subst unique
    rw [rotation_even, rotation_center]
    simp

open LocalizedChemicalRingC3ReferenceFixture in
theorem not_pairwise_proper_distinguishable :
    ¬ physical.PairwiseProperDistinguishable cfg center := by
  intro distinguishable
  obtain ⟨i, j, different, transport⟩ := rotation_proper_transport
  exact distinguishable i j different transport

open LocalizedChemicalRingC3ReferenceFixture in
/-- **Assigned, yet not pairwise proper distinguishable.** On this admitted cyclic input the actual
evaluator assigns a descriptor to a center two of whose ligands are related by a proper transport. -/
theorem assigned_without_proper_distinguishability :
    (∃ d, LocalizedChemicalRingInheritedFallback.assignCenter? mol (sparseOperations certified mol)
      (inputGeometry certified) 0 = some d) ∧
    ¬ physical.PairwiseProperDistinguishable cfg center :=
  ⟨root_descriptor_exists, not_pairwise_proper_distinguishable⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingProperRotationConsensus

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingProperRotationConsensus.referenceAt_injective
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingProperRotationConsensus.slot_current
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingProperRotationConsensus.slot_tie_atomZ
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingProperRotationConsensus.root_descriptor_exists
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingProperRotationConsensus.rotation_proper_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingProperRotationConsensus.not_pairwise_proper_distinguishable
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingProperRotationConsensus.assigned_without_proper_distinguishability
