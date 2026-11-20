import TetraStereo.OneCenter.LocalizedChemicalRingInheritedFallback
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
An exact computational optimization of the isolated inherited-fallback candidate. The
existing distant step already attempts local consensus for an out-of-frame inherited mark.
If that entire step refuses, repeating consensus cannot change the answer. Retry only a
refused in-frame mark; preserve the original continuation and every successful first result.

The equality below holds for arbitrary molecules, operations, geometry, states and child
continuations. It introduces no molecular restriction and changes no running evaluator.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingInheritedFallbackOptimization

open LocalizedChemicalRingSenseTransport (Step)
open LocalizedMarkedOperationEvaluator (Operations)
open LocalizedGenericMarkedRecalculation (Geometry frameAtoms? strict consistent)
open LocalizedPhysicalMarkedDistantReference (inheritedRead? chooseInherited)

abbrev Node := RawMolecule.CanonicalBranchNode

/-- Outside the frame, a refused distant step has already refused its no-context fallback. -/
theorem distant_none_implies_consensus_none (mol : RawMolecule) (ops : Operations)
    (geom : Geometry) (state : OccurrenceAuxState) (node : Node)
    (under : Nat → OccurrenceAuxState) (atoms : List Nat) (mark : Nat)
    (frame : frameAtoms? mol node = some atoms) (absent : mark ∉ atoms)
    (refused : LocalizedPhysicalMarkedDistantReference.rawStep? mol ops geom state
      (some mark) node under = none) :
    LocalizedPhysicalMarkedDistantReference.rawStep? mol ops geom state none node under = none := by
  unfold LocalizedPhysicalMarkedDistantReference.rawStep? at refused ⊢
  rw [frame] at refused ⊢
  cases ordered : ops.ordinary state node with
  | none => simp
  | some result =>
      obtain ⟨sorted, adjacent⟩ := result
      rw [ordered] at refused
      simp only [Option.bind_eq_bind, Option.bind_some] at refused ⊢
      by_cases bad : ¬ atoms.Nodup ∨ consistent adjacent = false
      · simp only [if_pos bad]
      · rw [if_neg bad] at refused ⊢
        by_cases strictOrder : strict adjacent = true
        · simpa only [if_pos strictOrder] using refused
        · rw [if_neg strictOrder] at refused ⊢
          simp only [chooseInherited, if_neg absent] at refused ⊢
          cases reading : inheritedRead? mol ops geom state node under mark with
          | none => simpa only [reading] using refused
          | some value =>
              rw [reading] at refused
              cases refused

/-- Execute the initial step once; only a failed local inherited mark can trigger a retry.
The frame test is performed after refusal, so successful inherited steps incur no new test. -/
def rawStep? (mol : RawMolecule) (ops : Operations) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : Node)
    (under : Nat → OccurrenceAuxState) : Option RS :=
  match ctx with
  | none => LocalizedPhysicalMarkedDistantReference.rawStep? mol ops geom state none node under
  | some mark =>
      match LocalizedPhysicalMarkedDistantReference.rawStep? mol ops geom state (some mark) node under with
      | some value => some value
      | none =>
          match frameAtoms? mol node with
          | none => none
          | some atoms =>
              if mark ∈ atoms then
                LocalizedPhysicalMarkedDistantReference.rawStep? mol ops geom state none node under
              else none

/-- Exact pointwise equality, including malformed inputs, absent frames and arbitrary states. -/
theorem rawStep_eq_candidate (mol : RawMolecule) (ops : Operations) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : Node)
    (under : Nat → OccurrenceAuxState) :
    rawStep? mol ops geom state ctx node under =
      LocalizedChemicalRingInheritedFallback.rawStep? mol ops geom state ctx node under := by
  cases ctx with
  | none => rfl
  | some mark =>
      cases previous : LocalizedPhysicalMarkedDistantReference.rawStep? mol ops geom state
          (some mark) node under with
      | some value =>
          rw [LocalizedChemicalRingInheritedFallback.rawStep_preserves_some
            mol ops geom state (some mark) node under value previous]
          simp only [rawStep?, previous]
      | none =>
          have candidate : LocalizedChemicalRingInheritedFallback.rawStep? mol ops geom state
              (some mark) node under =
              LocalizedPhysicalMarkedDistantReference.rawStep? mol ops geom state none node under := by
            unfold LocalizedChemicalRingInheritedFallback.rawStep?
            dsimp only []
            rw [previous]
            rfl
          rw [candidate]
          cases frame : frameAtoms? mol node with
          | none => simp [rawStep?, LocalizedPhysicalMarkedDistantReference.rawStep?, frame]
          | some atoms =>
              by_cases present : mark ∈ atoms
              · simp only [rawStep?, previous, frame, if_pos present]
              · have fallback := distant_none_implies_consensus_none mol ops geom state node under
                  atoms mark frame present previous
                simp only [rawStep?, previous, frame, if_neg present, fallback]

/-- Function equality lets every generic recursive theorem and execution use this
representation without re-proving covariance, stability or descriptor preservation. -/
theorem step_eq : rawStep? = LocalizedChemicalRingInheritedFallback.rawStep? := by
  funext mol ops geom state ctx node under
  exact rawStep_eq_candidate mol ops geom state ctx node under

end TetraStereo.OneCenter.LocalizedChemicalRingInheritedFallbackOptimization

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedFallbackOptimization.distant_none_implies_consensus_none
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedFallbackOptimization.rawStep?
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedFallbackOptimization.rawStep_eq_candidate
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingInheritedFallbackOptimization.step_eq
