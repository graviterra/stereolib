import TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerFrameExecution
import TetraStereo.OneCenter.LocalizedMarkedRetainedCanonicalFrame
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# Independent mathematical joint marker keys at prepared frame slots

`LocalizedChemicalRingJointMarkerRanking.refinedKey` is the ordinary independent retained
Rules-1--5 key followed by the marker of an **actual** compiled joint-key build. This module
replaces the marker half by the independent mathematical construction `jointMarkerKey` on the
actual Rule-4a stage graph of the same compiled frame, with the independent deep prior of
`LocalizedMarkedRetainedCanonicalFrame` and the actual reference marks.

The main theorem `slotKeys_eq_independent` proves, for an arbitrary occurrence-data frame of a
single-bonded certified input, an arbitrary raw auxiliary state (hence either generated side by
instantiation), and an arbitrary accumulated list of reference atoms,

`slotKeys ... = independentSlotKeys ...`,

where `independentSlotKeys` contains neither the compiled marker nor any production comparator.

The equality is a result about the fixed supplied raw state: it does not assert chemical
correctness of that state, physical meaning of generated labels, or faithfulness of the
experimental accumulated-reference policy to IUPAC rules.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentKeys

open CertifiedLocalizedCIPInput DeclarativeCIP DeclarativeCIP.PromotedCanonical Rule4aTableBridge
open LocalizedCumulativeDecoratedTree
open LocalizedMarkedRetainedMolecularSelection (retainedCarrierFuel)
open LocalizedMarkedRetainedStateReader LocalizedMarkedRetainedOrdinaryRanking
open LocalizedMarkedRetainedCanonicalFrame
open LocalizedChemicalRingJointMarkerKey LocalizedChemicalRingJointMarkerRanking
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData)

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput)
  (single : input.moleculeGraph.SimpleBonded) (state : OccurrenceAuxState)
  (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
  (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
  (unit : DetectedOccurrence input.moleculeGraph)
  (targetUnit : input.molecularFrameUnit target.1 = unit.1)
  (references : List input.Atom) (W D : Nat)

/-- The actual Rule-4a stage tree compiled for one frame slot by the raw-state frame. -/
abbrev jointSlotTree (slot : Fin 4) :
    LocalizedCumulativeDecoratedTree input (retainedCarrierFuel input) :=
  ((LocalizedChemicalRingJointMarkerRanking.frames input single state target real unit
    targetUnit).stages slot).a.tree

/-- An independent fallback for the deep prior. It is itself an independently defined retained
Rules-1--5 key of a compiled frame slot. The fallback value is only the prior of the root of a
joint key, and `jointMarkerKey` projects that component away, so it has no mathematical effect on
the marker below. -/
abbrev rootFallback : CompleteLigandRule5Key :=
  rawStateKeys input single state target real unit targetUnit (0 : Fin 4)

/-- The independent joint marker of one frame slot: the mathematical `jointMarkerKey` of the
actual stage graph, with independent deep priors and actual reference marks, at the supplied
layout bounds. No actual compiled marker or production comparator is used. -/
def independentJointMarker (slot : Fin 4) : JointMarker :=
  jointMarkerKey (ruleMajorTreeGraph (jointSlotTree input single state target real unit targetUnit slot))
    (deepPrior (rawStateDescriptorMap input state) target
      (rootFallback input single state target real unit targetUnit)
      (jointSlotTree input single state target real unit targetUnit slot))
    (referenceMarks input references
      (jointSlotTree input single state target real unit targetUnit slot))
    W D references.length
    (ruleMajorTreeGraph
      (jointSlotTree input single state target real unit targetUnit slot)).root

/-- Independent slot key: the independent retained Rules-1--5 key followed by the independent
joint marker. -/
def independentRefinedKey (slot : Fin 4) :
    Lex (CompleteLigandRule5Key × JointMarker) :=
  toLex (rawStateKeys input single state target real unit targetUnit slot,
    independentJointMarker input single state target real unit targetUnit references W D slot)

/-- **The actual refined key of every compiled frame slot is the independent key.** The actual
joint build is identified with `jointMarkerKey` by the accepted realized-tree bridge, whose only
premise, sibling prior agreement, is discharged by `deepPrior_agreement` on the actual stage graph
of the real detected target. -/
theorem refinedKey_eq_independent (slot : Fin 4) :
    refinedKey input single state target real unit targetUnit references W D slot =
      independentRefinedKey input single state target real unit targetUnit references W D slot := by
  have source :=
    ((LocalizedChemicalRingJointMarkerRanking.frames input single state target real unit
      targetUnit).stages slot).a.sourceEq
  have realizes := LocalizedRuleMajorSortTrace.realizes_of_trace
    ((LocalizedChemicalRingJointMarkerRanking.frames input single state target real unit
      targetUnit).stages slot).a.trace
  have rootChild : (jointSlotTree input single state target real unit targetUnit slot).source ∈
      input.executableLocalizedRerootChildren ⟨target, none⟩ := by
    rw [source]
    exact (LocalizedChemicalRingJointMarkerRanking.frames input single state target real unit
      targetUnit).childAt slot
  have built := compiled_built input single state target real unit targetUnit references W D slot
  rw [rawStateView_eq_molecularView, ← source] at built
  unfold refinedKey independentRefinedKey independentJointMarker
  exact congrArg
    (fun marker => toLex (rawStateKeys input single state target real unit targetUnit slot, marker))
    (root_jointMarkerKey_eq input target
      (input.molecularView (rawStateDescriptorMap input state) target) references W D
      (jointSlotTree input single state target real unit targetUnit slot) realizes
      (deepPrior (rawStateDescriptorMap input state) target
        (rootFallback input single state target real unit targetUnit)
        (jointSlotTree input single state target real unit targetUnit slot))
      (deepPrior_agreement (rawStateDescriptorMap input state) target
        (rootFallback input single state target real unit targetUnit)
        (jointSlotTree input single state target real unit targetUnit slot) realizes
        (rawStateDescriptorMap_tetrahedral input state) single rootChild)
      (2 * (retainedCarrierFuel input + 1))
      (compiled input single state target real unit targetUnit references W D slot) built)

end

/-! ## The frame-execution slot keys -/

section OccurrenceFrame

open LocalizedChemicalRingJointMarkerFrameExecution

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (single : input.moleculeGraph.SimpleBonded)
  (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
  (data : OccurrenceData input mol c node)

noncomputable section
open scoped Classical

/-- Independent joint slot keys of an actual detected occurrence frame. This is the independent
counterpart of `LocalizedChemicalRingJointMarkerFrameExecution.slotKeys`, with the same ordinary
Rules-1--5 component and the independently defined joint marker. -/
abbrev independentSlotKeys (state : OccurrenceAuxState) (references : List input.Atom) :
    Fin 4 → Lex (CompleteLigandRule5Key × JointMarker) :=
  independentRefinedKey input single state data.target data.real
    ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl references
    (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1))

/-- **The actual frame-execution slot keys are the independent slot keys**, for every actual
detected occurrence frame, arbitrary supplied raw state, and arbitrary accumulated reference list.
Rings are admitted; no acyclicity, auxiliary-label, comparison-success, desired-order or
desired-label hypothesis is used. -/
theorem slotKeys_eq_independent (state : OccurrenceAuxState)
    (references : List input.Atom) :
    slotKeys input mol single c node data state references =
      independentSlotKeys input mol single c node data state references := by
  funext slot
  exact refinedKey_eq_independent input single state data.target data.real
    ⟨input.molecularFrameUnit data.target.1, data.detected⟩ rfl references
    (retainedCarrierFuel input) (2 * (retainedCarrierFuel input + 1)) slot

end

end OccurrenceFrame

end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentKeys

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentKeys.refinedKey_eq_independent
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedIndependentKeys.slotKeys_eq_independent
