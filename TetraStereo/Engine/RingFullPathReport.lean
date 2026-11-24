import TetraStereo.Engine.RingFullPathPublication
import TetraStereo.Engine.RingSphereQueue

/-! # Full-path ring reports for requested molecular atoms -/
set_option autoImplicit false

namespace TetraStereo.Engine.RingFullPathReport
open OneCenter RingFullPathPublication
open LocalizedChemicalRing (Input)
open RingGroupedReport (Report origin)
open RingSphereQueue (Inventory molecularQueue)
open RingNestedActivePair (Labels)

theorem skips (i : Input) : RingSphereQueue.SkipsNoncentres (publish? i) := by
  intro q r no
  cases hf : RingNestedActivePair.frame? i q with
  | none => simp [publish?,hf]
  | some fr => exact nomatch no.symm.trans fr.recognized

def rootCell (i : Input) (a : i.certified.Atom) :=
  RingSphereQueue.finalCell (publish? i) a (molecularQueue i a)

/-- The complete source derivation determines the same result under any
enumeration of the molecular sites within each sphere. -/
theorem root_exact {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (a : i.certified.Atom) {queue} (listed : Inventory a queue) (v : Option Labels) :
    RingSphereQueue.finalCell (publish? i) a queue = some v ↔ Molecular i (origin i a) v := by
  rw [RingSphereQueue.final_exact (skips i) listed]
  exact molecular_iff geom _ v

private def row? {i : Input} (a : i.certified.Atom) : Option (Nat × Option Labels) :=
  (rootCell i a).map fun v => (a.val,v)

def forAtoms? (i : Input) (atoms : List i.certified.Atom) : Option Report :=
  atoms.mapM row?

def Correct (i : Input) (atoms : List i.certified.Atom) (report : Report) : Prop :=
  List.Forall₂ (fun a (p : Nat × Option Labels) => p.1 = a.val ∧ Molecular i (origin i a) p.2) atoms report

theorem report_iff (i : Input) (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (atoms : List i.certified.Atom) (report : Report) : forAtoms? i atoms = some report ↔ Correct i atoms report := by
  have one (a : i.certified.Atom) (p : Nat × Option Labels) :
      row? a = some p ↔ p.1 = a.val ∧ Molecular i (origin i a) p.2 := by
    rcases p with ⟨n,v⟩
    rw [← root_exact geom a (RingSphereQueue.inventory i a)]
    simp only [row?,rootCell,Option.map_eq_some_iff,Prod.mk.injEq]
    constructor
    · rintro ⟨_,h,eqn,rfl⟩; exact ⟨eqn.symm,h⟩
    · rintro ⟨eqn,h⟩; exact ⟨_,h,eqn.symm,rfl⟩
  induction atoms generalizing report with
  | nil => cases report <;> simp [forAtoms?,Correct]
  | cons a as ih =>
    cases report with
    | nil =>
      unfold forAtoms? Correct
      rw [List.mapM_cons]
      cases row? a <;> cases as.mapM row? <;> simp
    | cons p ps =>
      change (a::as).mapM _ = some _ ↔ List.Forall₂ _ _ _
      rw [List.mapM_cons,List.forall₂_cons]
      apply Iff.trans ?_ (and_congr (one a p) (ih ps))
      unfold forAtoms?
      cases row? a <;> cases as.mapM row? <;> simp

/-- Every requested list, including repeated atoms, has exactly one complete
report of original and mirror letters or completed absences. -/
theorem total_unique (i : Input) (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (atoms : List i.certified.Atom) : ∃! report, forAtoms? i atoms = some report ∧ Correct i atoms report := by
  obtain ⟨out,h⟩ := RingRetainedUnitPass.collect row? atoms (fun a _ => by
    obtain ⟨v,hv⟩ := Option.isSome_iff_exists.mp (complete geom (origin i a))
    have root := (RingSphereQueue.final_exact (skips i) (RingSphereQueue.inventory i a)).trans hv
    exact ⟨(a.val,v),by simp [row?,rootCell,root]⟩)
  exact ⟨out,⟨h,(report_iff i geom atoms out).mp h⟩,fun _ other => Option.some.inj (other.1.symm.trans h)⟩

end TetraStereo.Engine.RingFullPathReport
assert_kernel_only TetraStereo.Engine.RingFullPathReport.root_exact
assert_kernel_only TetraStereo.Engine.RingFullPathReport.report_iff
assert_kernel_only TetraStereo.Engine.RingFullPathReport.total_unique
