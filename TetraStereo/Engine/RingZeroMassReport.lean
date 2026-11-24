import TetraStereo.Engine.RingZeroDuplicateMass
import TetraStereo.Engine.RingSphereQueue

/-! # Zero-mass constitutional early exits throughout a ring report -/

set_option autoImplicit false
namespace TetraStereo.Engine.RingZeroMassReport
open OneCenter RingSphereQueue
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (Cell View evaluate)
open RingGeometryCriterion (Signature)
open RingActivePairReport (Slot)
attribute [local instance] lexOrd

/-- Rebuild the constitutional priorities with zero closure mass before
testing for four distinct ligands at this occurrence. -/
def zeroEarly? (i : Input) (q : Site i) : Option Signature := do
  let fr ← RingNestedActivePair.frame? i q
  let parity := RingOrientation.orientation fun k =>
    RingRetainedChemicalPreorder.orderWord (RingZeroDuplicateMass.rebuiltFor (fr.direction k))
  if parity = 0 then none else some ⟨RingOrientation.baseline fr * parity,0⟩

private theorem orientation_congr {α β : Type} [Ord α] [Ord β] (x : Slot → α) (y : Slot → β)
    (same : ∀ j k, compare (x j) (x k) = compare (y j) (y k)) :
    RingOrientation.orientation x = RingOrientation.orientation y := by
  have pred (target : Ordering) :
      (fun p : Slot × Slot => compare (x p.1) (x p.2) == target) =
      (fun p : Slot × Slot => compare (y p.1) (y p.2) == target) :=
    funext fun p => congrArg (fun v => v == target) (same p.1 p.2)
  unfold RingOrientation.orientation
  rw [pred .eq,pred .lt]

theorem zero_early_exact (i : Input) (q : Site i) : zeroEarly? i q = early? i q := by
  unfold zeroEarly? early?
  apply congrArg (fun next => (RingNestedActivePair.frame? i q).bind next)
  funext fr
  let x (j : Slot) := RingRetainedChemicalPreorder.orderWord (RingZeroDuplicateMass.rebuiltFor (fr.direction j))
  let y (j : Slot) := RingRetainedChemicalPreorder.orderWord (RingRetainedChemicalPreorder.keyFor (fr.direction j))
  have cmp (j k : Slot) : compare (x j) (x k) = compare (y j) (y k) :=
    (RingZeroDuplicateMass.prefixes_agree (fr.direction j) (fr.direction k)).2
  exact congrArg (fun parity : Int => if parity = 0 then none else
    some (⟨RingOrientation.baseline fr * parity,0⟩ : Signature)) (orientation_congr x y cmp)

/-- A strict constitutional decision can also skip the stereo work at an
auxiliary site. Tied sites use the grouped local rules on the frozen store. -/
def recursivePublish (i : Input) (q : Site i) (r : View i) : Cell :=
  match zeroEarly? i q with
  | some s => some s.letters
  | none => RingGroupedPublication.publish? i q r

theorem recursive_state (i : Input) (coord : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    evaluate (recursivePublish i) = RingGroupedPublication.state i := by
  symm
  apply RingActiveDistanceSchedule.unique
  intro q
  unfold recursivePublish
  rw [zero_early_exact]
  cases found : early? i q with
  | some s => exact early_exact coord found
  | none => exact RingGroupedPublication.state_eq i q

private theorem recursive_skips (i : Input) : SkipsNoncentres (recursivePublish i) := by
  intro q r no
  have absent : RingNestedActivePair.frame? i q = none := by simp [RingNestedActivePair.frame?,no]
  simp [recursivePublish,zeroEarly?,absent,grouped_skips i q r no]

/-- Use the zero-mass early exit at the requested root and at every queued
auxiliary. The full original-root inventory is needed only on a root tie. -/
def recursiveRoot (i : Input) (root : i.certified.Atom) : Cell :=
  match zeroEarly? i (RingGroupedReport.origin i root) with
  | some s => some s.letters
  | none => finalCell (recursivePublish i) root (molecularQueue i root)

theorem recursive_root_exact (i : Input) (coord : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (root : i.certified.Atom) :
    recursiveRoot i root = RingGroupedPublication.state i (RingGroupedReport.origin i root) := by
  unfold recursiveRoot
  cases found : zeroEarly? i (RingGroupedReport.origin i root) with
  | some s => exact (early_exact coord ((zero_early_exact ..).symm.trans found)).symm
  | none => rw [final_exact (recursive_skips i) (inventory i root),recursive_state i coord]

def recursiveReport (i : Input) (atoms : List i.certified.Atom) : Option RingGroupedReport.Report :=
  atoms.mapM fun a => (recursiveRoot i a).map fun v => (a.val,v)

theorem recursive_report_exact (i : Input) (coord : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (atoms : List i.certified.Atom) : recursiveReport i atoms = RingGroupedReport.forAtoms? i atoms := by
  unfold recursiveReport
  simp only [recursive_root_exact i coord]
  rfl

end TetraStereo.Engine.RingZeroMassReport

assert_kernel_only TetraStereo.Engine.RingZeroMassReport.recursive_state
assert_kernel_only TetraStereo.Engine.RingZeroMassReport.recursive_report_exact
