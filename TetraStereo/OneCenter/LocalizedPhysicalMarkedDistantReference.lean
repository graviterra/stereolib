import TetraStereo.OneCenter.LocalizedMarkedOperationEvaluator
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Distant inherited references: an explicit successor policy

An inherited reference in the current frame behaves exactly as before. A reference outside
the frame is tried directly; a refused reading falls back to the existing local consensus.
Absent context uses the existing consensus. Ordinary strict decisions and malformed-input
refusals precede this choice unchanged. The fallback is lazy.

This is a separately named experimental policy, not a production default or a claim of chemical
sufficiency. In particular, a successful distant reading may replace a successful local
consensus; no unrestricted preservation of old answers is claimed. The preservation theorems
state the exact circumstances where the old and new steps agree.
-/

namespace TetraStereo.OneCenter.LocalizedPhysicalMarkedDistantReference

open LocalizedGenericMarkedRecalculation (Geometry frameAtoms? atomsAt? readback? strict
  consistent eligibleOf consensus appendFacts?)
open LocalizedMarkedOperationEvaluator (Operations markedReading?)

abbrev Node := RawMolecule.CanonicalBranchNode

/-- Retain an available distant reading, with the existing local rule as a lazy fallback. -/
def chooseInherited {α : Type} (atoms : List Nat) (ctx : Option Nat)
    (reading : Nat → Option α) (fallback : Unit → Option α) : Option α :=
  match ctx with
  | none => fallback ()
  | some mark =>
      if mark ∈ atoms then reading mark else
        match reading mark with
        | some value => some value
        | none => fallback ()

@[simp] theorem chooseInherited_none {α : Type} (atoms : List Nat)
    (reading : Nat → Option α) (fallback : Unit → Option α) :
    chooseInherited atoms none reading fallback = fallback () := rfl

theorem chooseInherited_local {α : Type} (atoms : List Nat) (mark : Nat)
    (reading : Nat → Option α) (fallback : Unit → Option α) (present : mark ∈ atoms) :
    chooseInherited atoms (some mark) reading fallback = reading mark := by
  simp [chooseInherited, present]

theorem chooseInherited_distant_success {α : Type} (atoms : List Nat) (mark : Nat)
    (reading : Nat → Option α) (fallback : Unit → Option α) (value : α)
    (read : reading mark = some value) :
    chooseInherited atoms (some mark) reading fallback = some value := by
  simp [chooseInherited, read]

theorem chooseInherited_distant_refusal {α : Type} (atoms : List Nat) (mark : Nat)
    (reading : Nat → Option α) (fallback : Unit → Option α)
    (absent : mark ∉ atoms) (read : reading mark = none) :
    chooseInherited atoms (some mark) reading fallback = fallback () := by
  simp [chooseInherited, absent, read]

/-- The policy itself commutes with any transformation of successful readings, including
reflection. Reader covariance is a separate proof obligation. -/
theorem chooseInherited_map {α β : Type} (f : α → β) (atoms : List Nat) (ctx : Option Nat)
    (reading : Nat → Option α) (fallback : Unit → Option α) :
    chooseInherited atoms ctx (fun mark => (reading mark).map f)
        (fun u => (fallback u).map f) =
      (chooseInherited atoms ctx reading fallback).map f := by
  cases ctx with
  | none => rfl
  | some mark =>
      by_cases present : mark ∈ atoms
      · simp [chooseInherited, present]
      · cases h : reading mark <;> simp [chooseInherited, present, h]

def inheritedRead? (mol : RawMolecule) (ops : Operations) (geom : Geometry)
    (state : OccurrenceAuxState) (node : Node) (under : Nat → OccurrenceAuxState)
    (mark : Nat) : Option RS := do
  let temporary ← appendFacts? state (under mark)
  markedReading? mol ops geom temporary node mark

def rawStep? (mol : RawMolecule) (ops : Operations) (geom : Geometry)
    (state : OccurrenceAuxState) (ctx : Option Nat) (node : Node)
    (under : Nat → OccurrenceAuxState) : Option RS := do
  let atoms ← frameAtoms? mol node
  let (sorted, adjacent) ← ops.ordinary state node
  if ¬ atoms.Nodup ∨ consistent adjacent = false then none
  else if strict adjacent then
    let ranked ← atomsAt? atoms sorted
    readback? geom ranked
  else
    let reading := inheritedRead? mol ops geom state node under
    chooseInherited atoms ctx reading
      (fun _ => consensus ((eligibleOf atoms sorted adjacent).map reading))

/-- No inherited context changes neither the step nor its fallback. Recursive child data
are held fixed here; their preservation is a separate induction. -/
theorem rawStep_none (mol : RawMolecule) (ops : Operations) (geom : Geometry)
    (state : OccurrenceAuxState) (node : Node) (under : Nat → OccurrenceAuxState) :
    rawStep? mol ops geom state none node under =
      LocalizedMarkedOperationEvaluator.rawStep? mol ops geom state none node under := rfl

theorem rawStep_local (mol : RawMolecule) (ops : Operations) (geom : Geometry)
    (state : OccurrenceAuxState) (node : Node) (under : Nat → OccurrenceAuxState)
    (atoms : List Nat) (mark : Nat) (frame : frameAtoms? mol node = some atoms)
    (present : mark ∈ atoms) :
    rawStep? mol ops geom state (some mark) node under =
      LocalizedMarkedOperationEvaluator.rawStep? mol ops geom state (some mark) node under := by
  simp [rawStep?, LocalizedMarkedOperationEvaluator.rawStep?, frame, chooseInherited,
    present, inheritedRead?]

theorem rawStep_distant_refusal (mol : RawMolecule) (ops : Operations) (geom : Geometry)
    (state : OccurrenceAuxState) (node : Node) (under : Nat → OccurrenceAuxState)
    (atoms : List Nat) (mark : Nat) (frame : frameAtoms? mol node = some atoms)
    (absent : mark ∉ atoms)
    (refused : inheritedRead? mol ops geom state node under mark = none) :
    rawStep? mol ops geom state (some mark) node under =
      LocalizedMarkedOperationEvaluator.rawStep? mol ops geom state (some mark) node under := by
  simp [rawStep?, LocalizedMarkedOperationEvaluator.rawStep?, frame, chooseInherited,
    absent, refused]
  rfl

/-- A successful inherited reading is actually used even outside the current frame. -/
theorem rawStep_inherited_success (mol : RawMolecule) (ops : Operations) (geom : Geometry)
    (state : OccurrenceAuxState) (node : Node) (under : Nat → OccurrenceAuxState)
    (atoms sorted : List Nat) (adjacent : List (Option Ordering)) (mark : Nat) (value : RS)
    (frame : frameAtoms? mol node = some atoms)
    (ordered : ops.ordinary state node = some (sorted, adjacent)) (nodup : atoms.Nodup)
    (consistentOrder : consistent adjacent = true) (tied : strict adjacent = false)
    (reading : inheritedRead? mol ops geom state node under mark = some value) :
    rawStep? mol ops geom state (some mark) node under = some value := by
  simp [rawStep?, frame, ordered, nodup, consistentOrder, tied,
    chooseInherited_distant_success atoms mark _ _ value reading]

/-- A callback-local structural property, not an assumed final descriptor correspondence. -/
def FrameLocalOperations (mol : RawMolecule) (ops : Operations) : Prop :=
  ∀ state node atoms mark, frameAtoms? mol node = some atoms → mark ∉ atoms →
    ops.marked state node mark = none

theorem inheritedRead_none_of_frameLocal (mol : RawMolecule) (ops : Operations)
    (localOps : FrameLocalOperations mol ops) (geom : Geometry) (state : OccurrenceAuxState)
    (node : Node) (under : Nat → OccurrenceAuxState) (atoms : List Nat) (mark : Nat)
    (frame : frameAtoms? mol node = some atoms) (absent : mark ∉ atoms) :
    inheritedRead? mol ops geom state node under mark = none := by
  unfold inheritedRead?
  cases h : appendFacts? state (under mark) with
  | none => rfl
  | some temporary =>
      simp [markedReading?, frame, localOps temporary node atoms mark frame absent]

/-- For frame-local rankers every step is preserved, with arbitrary geometry and child data. -/
theorem rawStep_eq_of_frameLocal (mol : RawMolecule) (ops : Operations)
    (localOps : FrameLocalOperations mol ops) (geom : Geometry) (state : OccurrenceAuxState)
    (ctx : Option Nat) (node : Node) (under : Nat → OccurrenceAuxState) :
    rawStep? mol ops geom state ctx node under =
      LocalizedMarkedOperationEvaluator.rawStep? mol ops geom state ctx node under := by
  cases ctx with
  | none => exact rawStep_none mol ops geom state node under
  | some mark =>
      cases h : frameAtoms? mol node with
      | none => simp [rawStep?, LocalizedMarkedOperationEvaluator.rawStep?, h]
      | some atoms =>
          by_cases present : mark ∈ atoms
          · exact rawStep_local mol ops geom state node under atoms mark h present
          · exact rawStep_distant_refusal mol ops geom state node under atoms mark h present
              (inheritedRead_none_of_frameLocal mol ops localOps geom state node under
                atoms mark h present)

end TetraStereo.OneCenter.LocalizedPhysicalMarkedDistantReference

assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalMarkedDistantReference.chooseInherited_map
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalMarkedDistantReference.rawStep_none
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalMarkedDistantReference.rawStep_local
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalMarkedDistantReference.rawStep_distant_refusal
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalMarkedDistantReference.rawStep_inherited_success
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalMarkedDistantReference.rawStep_eq_of_frameLocal
