import TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion
import TetraStereo.OneCenter.LocalizedChemicalRingSenseTransport
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The prepared evaluator depends on geometry only through frame readbacks. All child
states and every extended context are covered. The concrete step satisfies the required
congruence law; deriving frame readback agreement from physical signs is separate. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedGeometryCongruence

open LocalizedChemicalRingPreparedContextRecursion
open LocalizedChemicalRingMultiMarkRecursion (MultiOperations markedReadingJoint?)
open LocalizedChemicalRingSenseTransport (AgreeOn atomsAt_subset)
open LocalizedMarkedCyclicDiscardedReference (rankedAtoms_subset)
open LocalizedGenericMarkedRecalculation
  (Geometry frameAtoms? readback? atomsAt? rankedAtoms? mirror flatMap_congr_mem)

def PreparedStepCongr (step : PreparedStep) (mol : RawMolecule) : Prop :=
  ∀ (first second : Geometry) (node : Node),
    (∀ atoms, frameAtoms? mol node = some atoms →
      ∀ L : List Nat, (∀ x ∈ L, x ∈ atoms) → readback? first L = readback? second L) →
    ∀ state M under, step mol first state M node under = step mol second state M node under

theorem markedReadingJoint_congr_geom (mol : RawMolecule) (ops : MultiOperations)
    (first second : Geometry) (node : Node) (atoms : List Nat)
    (frame : frameAtoms? mol node = some atoms)
    (agree : ∀ L : List Nat, (∀ x ∈ L, x ∈ atoms) → readback? first L = readback? second L)
    (state : OccurrenceAuxState) (M : MarkContext) (mark : Nat) :
    markedReadingJoint? mol ops first state node M mark =
      markedReadingJoint? mol ops second state node M mark := by
  unfold markedReadingJoint?
  rw [frame]
  simp only [Option.bind_eq_bind, Option.bind_some]
  cases ops.markedJoint state node M mark with
  | none => rfl
  | some ranking =>
      simp only [Option.bind_some]
      cases found : rankedAtoms? atoms ranking with
      | none => rfl
      | some ranked => exact agree ranked (rankedAtoms_subset atoms ranking ranked found)

theorem rawStepPrepared_congr_geom (mol : RawMolecule) (ops : MultiOperations) :
    PreparedStepCongr (rawStepPrepared? ops) mol := by
  intro first second node agree state M under
  cases frame : frameAtoms? mol node with
  | none => simp [rawStepPrepared?, frame]
  | some atoms =>
      have key := agree atoms frame
      have marked : ∀ temp L mark, markedReadingJoint? mol ops first temp node L mark =
          markedReadingJoint? mol ops second temp node L mark :=
        fun temp L mark => markedReadingJoint_congr_geom mol ops first second node atoms frame
          key temp L mark
      have fallback : ∀ mark, evaluateFallback? mol ops first state node M under mark =
          evaluateFallback? mol ops second state node M under mark := by
        intro mark
        unfold evaluateFallback?
        simp only [marked]
      unfold rawStepPrepared?
      rw [frame]
      simp only [Option.bind_eq_bind, Option.bind_some]
      cases prepareComparison? state under M with
      | none => rfl
      | some prepared =>
          simp only [Option.bind_some]
          unfold comparisonAt?
          cases ops.contextOrder prepared node M with
          | none => rfl
          | some result =>
              obtain ⟨sorted, adjacent⟩ := result
              dsimp only
              split_ifs
              · rfl
              · cases found : atomsAt? atoms sorted with
                | none => rfl
                | some ranked => exact key ranked (atomsAt_subset atoms sorted ranked found)
              · rw [funext fallback]

theorem factsOfStep_congr (mol : RawMolecule) (step : PreparedStep) (P : Node → Prop)
    (closed : ∀ parent child, P parent → child ∈ mol.canonicalChildren parent → P child)
    (stepCongr : PreparedStepCongr step mol) (depth : Nat) :
    ∀ (first second : Geometry), AgreeOn P mol first second →
      ∀ (state : OccurrenceAuxState) (M : MarkContext) (node : Node), P node →
        factsOfStep step mol depth first state M node =
          factsOfStep step mol depth second state M node := by
  induction depth with
  | zero => intros; rfl
  | succ depth ih =>
      intro first second agree state M node member
      have under : ∀ (f s : Geometry), AgreeOn P mol f s →
          childrenUnder mol (factsOfStep step mol depth) f state node =
            childrenUnder mol (factsOfStep step mol depth) s state node := by
        intro f s same
        funext L
        unfold childrenUnder
        exact flatMap_congr_mem _ _ _ fun child edge =>
          ih f s same state L child (closed node child member edge)
      have head : descriptorOfStep step mol depth first state M node =
          descriptorOfStep step mol depth second state M node := by
        unfold descriptorOfStep descriptorWithPrepared
        rw [under first second agree, under (mirror first) (mirror second) agree.mirror,
          stepCongr first second node (agree node member) state M,
          stepCongr (mirror first) (mirror second) node (agree.mirror node member) state M]
      rw [factsOfStep_succ, factsOfStep_succ, head]
      congr 1
      exact flatMap_congr_mem _ _ _ fun child edge =>
        ih first second agree state M child (closed node child member edge)

theorem preparedFacts_congr (mol : RawMolecule) (ops : MultiOperations) (P : Node → Prop)
    (closed : ∀ parent child, P parent → child ∈ mol.canonicalChildren parent → P child)
    (depth : Nat) (first second : Geometry) (agree : AgreeOn P mol first second)
    (state : OccurrenceAuxState) (M : MarkContext) (node : Node) (member : P node) :
    preparedFacts mol ops depth first state M node =
      preparedFacts mol ops depth second state M node :=
  factsOfStep_congr mol (rawStepPrepared? ops) P closed (rawStepPrepared_congr_geom mol ops)
    depth first second agree state M node member

end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedGeometryCongruence

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedGeometryCongruence.markedReadingJoint_congr_geom
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedGeometryCongruence.rawStepPrepared_congr_geom
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedGeometryCongruence.factsOfStep_congr
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedGeometryCongruence.preparedFacts_congr
