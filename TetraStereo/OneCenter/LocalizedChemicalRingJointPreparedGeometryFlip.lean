import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedGeometryCongruence
import TetraStereo.OneCenter.LocalizedChemicalRingOrientationReadback
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Uniform frame-readback sign changes transport through the concrete prepared step,
including consensus and separate extended-context fallbacks. When the two generated child
continuations agree, this changes the resulting descriptor by the same physical sign.
The calibration and descendant-properness arguments producing those premises are separate. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedGeometryFlip

open LocalizedChemicalRingPreparedContextRecursion
open LocalizedChemicalRingMultiMarkRecursion (MultiOperations markedReadingJoint?)
open LocalizedChemicalRingOrientationReadback
open LocalizedChemicalRingSenseTransport (atomsAt_subset)
open LocalizedMarkedCyclicDiscardedReference (rankedAtoms_subset)
open LocalizedGenericMarkedRecalculation
  (Geometry frameAtoms? readback? atomsAt? rankedAtoms? mirror readback_mirror consensus)

variable (mol : RawMolecule) (ops : MultiOperations)

theorem markedReadingJoint_flip (s : ℝ) (first second : Geometry)
    (node : Node) (atoms : List Nat) (frame : frameAtoms? mol node = some atoms)
    (flip : ∀ L : List Nat, (∀ x ∈ L, x ∈ atoms) →
      readback? first L = flipBy s (readback? second L))
    (state : OccurrenceAuxState) (M : MarkContext) (mark : Nat) :
    markedReadingJoint? mol ops first state node M mark =
      flipBy s (markedReadingJoint? mol ops second state node M mark) := by
  unfold markedReadingJoint?
  rw [frame]
  simp only [Option.bind_eq_bind, Option.bind_some]
  cases ops.markedJoint state node M mark with
  | none => simp only [Option.bind_none, flipBy_none]
  | some ranking =>
      simp only [Option.bind_some]
      cases found : rankedAtoms? atoms ranking with
      | none => simp only [Option.bind_none, flipBy_none]
      | some ranked =>
          simp only [Option.bind_some]
          exact flip ranked (rankedAtoms_subset atoms ranking ranked found)

theorem evaluateFallback_flip (s : ℝ) (first second : Geometry)
    (node : Node) (atoms : List Nat) (frame : frameAtoms? mol node = some atoms)
    (flip : ∀ L : List Nat, (∀ x ∈ L, x ∈ atoms) →
      readback? first L = flipBy s (readback? second L))
    (state : OccurrenceAuxState) (M : MarkContext) (under : ChildStates) (mark : Nat) :
    evaluateFallback? mol ops first state node M under mark =
      flipBy s (evaluateFallback? mol ops second state node M under mark) :=
  flipBy_bind s _ _ _ fun temp =>
    markedReadingJoint_flip mol ops s first second node atoms frame flip temp (M ++ [mark]) mark

theorem rawStepPrepared_flip (s : ℝ) (first second : Geometry)
    (node : Node) (atoms : List Nat) (frame : frameAtoms? mol node = some atoms)
    (flip : ∀ L : List Nat, (∀ x ∈ L, x ∈ atoms) →
      readback? first L = flipBy s (readback? second L))
    (state : OccurrenceAuxState) (M : MarkContext) (under : ChildStates) :
    rawStepPrepared? ops mol first state M node under =
      flipBy s (rawStepPrepared? ops mol second state M node under) := by
  have fallback : ∀ mark, evaluateFallback? mol ops first state node M under mark =
      flipBy s (evaluateFallback? mol ops second state node M under mark) :=
    evaluateFallback_flip mol ops s first second node atoms frame flip state M under
  unfold rawStepPrepared?
  rw [frame]
  simp only [Option.bind_eq_bind, Option.bind_some]
  apply flipBy_bind
  intro prepared
  unfold comparisonAt?
  cases ops.contextOrder prepared node M with
  | none => exact (flipBy_none s).symm
  | some result =>
      obtain ⟨sorted, adjacent⟩ := result
      dsimp only
      split_ifs
      · exact (flipBy_none s).symm
      · cases found : atomsAt? atoms sorted with
        | none => exact (flipBy_none s).symm
        | some ranked => exact flip ranked (atomsAt_subset atoms sorted ranked found)
      · rw [← consensus_flipBy, List.map_map]
        apply congrArg consensus
        exact List.map_congr_left fun mark _ => fallback mark

theorem preparedDescriptor_flip (s : ℝ) (first second : Geometry)
    (depth : Nat) (node : Node) (atoms : List Nat)
    (frame : frameAtoms? mol node = some atoms)
    (flip : ∀ L : List Nat, (∀ x ∈ L, x ∈ atoms) →
      readback? first L = flipBy s (readback? second L))
    (state : OccurrenceAuxState) (M : MarkContext)
    (below : ∀ L,
      childrenUnder mol (preparedFacts mol ops depth) first state node L =
        childrenUnder mol (preparedFacts mol ops depth) second state node L)
    (belowMirror : ∀ L,
      childrenUnder mol (preparedFacts mol ops depth) (mirror first) state node L =
        childrenUnder mol (preparedFacts mol ops depth) (mirror second) state node L) :
    preparedDescriptor? mol ops depth first state M node =
      flipDescriptorBy s (preparedDescriptor? mol ops depth second state M node) := by
  have flipMirror : ∀ L : List Nat, (∀ x ∈ L, x ∈ atoms) →
      readback? (mirror first) L = flipBy s (readback? (mirror second) L) := by
    intro L subset
    rw [readback_mirror, readback_mirror, flip L subset, flipBy_map_swap]
  unfold preparedDescriptor? descriptorOfStep descriptorWithPrepared
  change LocalizedGenericMarkedRecalculation.caseFromMirror?
      (rawStepPrepared? ops mol first state M node
        (childrenUnder mol (preparedFacts mol ops depth) first state node))
      (rawStepPrepared? ops mol (mirror first) state M node
        (childrenUnder mol (preparedFacts mol ops depth) (mirror first) state node)) = _
  rw [funext below, funext belowMirror,
    rawStepPrepared_flip mol ops s first second node atoms frame flip state M,
    rawStepPrepared_flip mol ops s (mirror first) (mirror second) node atoms frame flipMirror state M,
    caseFromMirror_flipBy]
  rfl

end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedGeometryFlip

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedGeometryFlip.markedReadingJoint_flip
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedGeometryFlip.evaluateFallback_flip
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedGeometryFlip.rawStepPrepared_flip
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedGeometryFlip.preparedDescriptor_flip
