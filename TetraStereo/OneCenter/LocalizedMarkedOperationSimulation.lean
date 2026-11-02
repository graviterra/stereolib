import TetraStereo.OneCenter.LocalizedMarkedOperationEvaluator
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Local replacement of comparison operations in the shared recursion

Only actually selected references need matching readbacks. This permits finite operation
checks to transfer a recursive derivation without evaluating its full state or assuming that
the two implementations agree at unrelated supplied states.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedOperationSimulation

open LocalizedMarkedOperationEvaluator
open LocalizedGenericMarkedRecalculation
  (Geometry frameAtoms? caseFromMirror? consistent strict eligibleOf consensus appendFacts?
    flatMap_congr_mem flatMap_nil_fun)

theorem descriptor_none_of_frame (mol : RawMolecule) (ops : Operations) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : Node)
    (sub : Geometry → OccurrenceAuxState → Option Nat → Node → OccurrenceAuxState)
    (noFrame : frameAtoms? mol node = none) :
    descriptorWith? mol ops geom state ctx node sub = none := by
  simp [descriptorWith?, rawWith?, rawStep?, noFrame, caseFromMirror?]

theorem facts_succ_noFrame (mol : RawMolecule) (ops : Operations) (depth : Nat) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : Node)
    (noFrame : frameAtoms? mol node = none) :
    facts mol ops (depth + 1) geom state ctx node =
      (mol.canonicalChildren node).flatMap (facts mol ops depth geom state ctx) := by
  rw [facts_succ]
  unfold descriptor?
  rw [descriptor_none_of_frame mol ops geom state ctx node _ noFrame]
  rfl

theorem facts_eq_nil_of_leafChildren (mol : RawMolecule) (ops : Operations) (depth : Nat)
    (geom : Geometry) (state : OccurrenceAuxState) (ctx : Option Nat) (node : Node)
    (noFrame : frameAtoms? mol node = none)
    (leaves : ∀ child ∈ mol.canonicalChildren node, child.forcedLeaf = true) :
    facts mol ops depth geom state ctx node = [] := by
  cases depth with
  | zero => rfl
  | succ depth =>
      rw [facts_succ_noFrame mol ops depth geom state ctx node noFrame,
        flatMap_congr_mem _ _ (fun _ => []) fun child member =>
          facts_forcedLeaf mol ops depth geom state ctx child (leaves child member)]
      exact flatMap_nil_fun _

theorem flatMap_facts_eq_nil (mol : RawMolecule) (ops : Operations) (depth : Nat)
    (geom : Geometry) (state : OccurrenceAuxState) (ctx : Option Nat) (nodes : List Node)
    (leafy : ∀ n ∈ nodes, frameAtoms? mol n = none ∧
      ∀ c ∈ mol.canonicalChildren n, c.forcedLeaf = true) :
    nodes.flatMap (facts mol ops depth geom state ctx) = [] := by
  rw [flatMap_congr_mem _ _ (fun _ => []) fun n member =>
    facts_eq_nil_of_leafChildren mol ops depth geom state ctx n (leafy n member).1
      (leafy n member).2]
  exact flatMap_nil_fun _

/-- Equal ordinary partitions and equal evaluated chosen references suffice for one raw step.
The hypotheses preserve refusals as well as successful letters. Temporary states may differ
between implementations; only their consumed marked-readback options must agree. -/
theorem rawStep_eq_of_selected (mol : RawMolecule) (left right : Operations) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : Node)
    (underLeft underRight : Nat → OccurrenceAuxState)
    (atoms sorted : List Nat) (adjacent : List (Option Ordering))
    (frame : frameAtoms? mol node = some atoms)
    (leftOrder : left.ordinary state node = some (sorted, adjacent))
    (rightOrder : right.ordinary state node = some (sorted, adjacent))
    (selected : ∀ mark,
      (ctx = some mark ∧ mark ∈ atoms) ∨ mark ∈ eligibleOf atoms sorted adjacent →
      (appendFacts? state (underLeft mark)).bind (fun temp =>
        markedReading? mol left geom temp node mark) =
      (appendFacts? state (underRight mark)).bind (fun temp =>
        markedReading? mol right geom temp node mark)) :
    rawStep? mol left geom state ctx node underLeft =
      rawStep? mol right geom state ctx node underRight := by
  simp only [rawStep?, frame, leftOrder, rightOrder]
  dsimp only [Bind.bind, Option.bind]
  by_cases bad : ¬ atoms.Nodup ∨ consistent adjacent = false
  · simp [bad]
  · simp only [bad, ↓reduceIte]
    by_cases separated : strict adjacent = true
    · simp [separated]
    · simp only [separated]
      have localEq := List.map_congr_left (l := eligibleOf atoms sorted adjacent)
        (fun mark member => selected mark (Or.inr member))
      cases ctx with
      | none => exact congrArg consensus localEq
      | some mark =>
          by_cases member : mark ∈ atoms
          · simpa only [List.contains_iff_mem.mpr member, ↓reduceIte] using
              selected mark (Or.inl ⟨rfl, member⟩)
          · have absent : atoms.contains mark = false := by simp [member]
            simpa only [absent, Bool.false_eq_true, ↓reduceIte] using congrArg consensus localEq

end TetraStereo.OneCenter.LocalizedMarkedOperationSimulation

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedOperationSimulation.facts_succ_noFrame
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedOperationSimulation.flatMap_facts_eq_nil
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedOperationSimulation.rawStep_eq_of_selected
