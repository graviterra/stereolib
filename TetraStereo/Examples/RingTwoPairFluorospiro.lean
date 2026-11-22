import TetraStereo.Engine.PublicAPI

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 50000
set_option Elab.async false

namespace TetraStereo.Examples.RingTwoPairFluorospiro
open OneCenter Engine CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open RingChemicalPriority Recursive
open CentresRingSpiroCasing (molecule spatial renumbered moved)

def geometry : Geometry := fun i => spatial.positions[i]?
def movedGeometry : Geometry := fun i => moved.positions[i]?

structure TrialView where
  mark : Nat
  actual : List Nat
  reflected : List Nat
  deriving DecidableEq, Repr

structure Observed where
  reading : Reading
  orders : List TrialView
  deriving DecidableEq, Repr

/-- Read back only the certified two-pair branch. Its trial type certifies
that each displayed order is the unique strict permutation for that mark and
geometry, and the parent certificate proves unanimity across all four marks. -/
def view {m g p} : RingAuxiliaryInventory.Result m g p → Option Observed
  | .paired c => some ⟨c.reading,c.trials.map fun t => ⟨t.mark,t.actual,t.reflected⟩⟩
  | _ => none

def inspect (m : RawMolecule) (g : Geometry) (root : Nat) :=
  (inspectRingOccurrence? m g [root] (m.atomCount+2) (fun _ => none) (fun _ => 2)).bind
    (fun r => view r.val)

private theorem view_reading {m g p} {r : RingAuxiliaryInventory.Result m g p} {v : Observed}
    (observed : view r = some v) : r.reading = some v.reading := by
  cases r <;> simp [view] at observed
  cases observed
  rfl

def orders : List TrialView :=
  [⟨1,[1,3,2,4],[2,4,1,3]⟩, ⟨2,[1,3,2,4],[2,4,1,3]⟩,
   ⟨3,[3,1,4,2],[4,2,3,1]⟩, ⟨4,[3,1,4,2],[4,2,3,1]⟩]

/-- Apply the same atom transposition used on every bond and coordinate. -/
def move (t : TrialView) : TrialView :=
  ⟨CentresRingSpiroCasing.rename t.mark,t.actual.map CentresRingSpiroCasing.rename,
    t.reflected.map CentresRingSpiroCasing.rename⟩

def reflect (t : TrialView) : TrialView := ⟨t.mark,t.reflected,t.actual⟩

theorem original_trials :
    inspect molecule geometry 0 = some ⟨⟨.S,.R⟩,orders⟩ := by decide +kernel
theorem mirror_trials :
    inspect molecule (mirror geometry) 0 = some ⟨⟨.R,.S⟩,orders.map reflect⟩ := by decide +kernel
theorem renumbered_trials :
    inspect renumbered movedGeometry 3 = some ⟨⟨.S,.R⟩,orders.map move⟩ := by decide +kernel
theorem renumbered_mirror_trials :
    inspect renumbered (mirror movedGeometry) 3 =
      some ⟨⟨.R,.S⟩,(orders.map move).map reflect⟩ := by decide +kernel

/-- Compare with the independent graph-and-coordinate criterion. Its exhaustive
permutation search selects a senior R pair and assigns third place to the
ring partner of the first ligand. Both analyses must yield exactly the same
set of admissible orders. -/
def coversScaffold (m : RawMolecule) (s : SpatialConfiguration) (root : Nat)
    (ts : List TrialView) : Bool :=
  let allowed := CentresRingSpiroCasing.scaffoldOrders m s root
  let actual := ts.map TrialView.actual
  allowed.length == 2 && allowed.all actual.contains && actual.all allowed.contains

theorem all_marks_follow_scaffold :
    coversScaffold molecule spatial 0 orders = true ∧
    coversScaffold molecule (CentresRingSpiroCasing.reflected spatial) 0 (orders.map reflect) = true ∧
    coversScaffold renumbered moved 3 (orders.map move) = true ∧
    coversScaffold renumbered (CentresRingSpiroCasing.reflected moved) 3 ((orders.map move).map reflect) = true := by
  exact ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel⟩

/-- The orders returned by the public occurrence entry point exhaust the
independent scaffold orders on both geometries and in both numberings. -/
theorem inspected_orders_follow_scaffold :
    (inspect molecule geometry 0).any (fun v => coversScaffold molecule spatial 0 v.orders) = true ∧
    (inspect molecule (mirror geometry) 0).any
        (fun v => coversScaffold molecule (CentresRingSpiroCasing.reflected spatial) 0 v.orders) = true ∧
    (inspect renumbered movedGeometry 3).any (fun v => coversScaffold renumbered moved 3 v.orders) = true ∧
    (inspect renumbered (mirror movedGeometry) 3).any
        (fun v => coversScaffold renumbered (CentresRingSpiroCasing.reflected moved) 3 v.orders) = true := by
  rw [original_trials,mirror_trials,renumbered_trials,renumbered_mirror_trials]
  exact all_marks_follow_scaffold

private def ids : List Nat := [0,1,2,3,4]

private def row (m : RawMolecule) (g : Geometry) (i : Nat) :=
  (RingCarbonReport.atCarbon? m g (m.atomCount+2) (fun _ => none) (fun _ => 2) i).map
    RingCarbonReport.Verdict.label

private theorem centerRow {m : RawMolecule} {g : Geometry} {i : Nat} {v : Observed}
    (domain : saturatedWithHalogens m = true)
    (carbon : (m.atoms[i]?).any (fun a => a.element == .C) = true)
    (noH : (RingCarbonReport.hydrogens? m i).isNone = true)
    (observed : inspect m g i = some v) : row m g i = some v.reading.label := by
  unfold row
  rw [RingCarbonReport.atCarbon?_label_of_no_hydrogens domain carbon noH]
  cases found : RingAuxiliaryInventory.classify? m g (fun _ => none) (fun _ => 2) (m.atomCount+2) [i] with
  | none => simp [inspect,inspectRingOccurrence?,domain,found] at observed
  | some r =>
    have h : view r = some v := by simpa [inspect,inspectRingOccurrence?,domain,found] using observed
    simp [view_reading h]

private def expected (a b c d e : RS) (i : Nat) : Option LocalizedAuxiliaryLabel :=
  [a,b,c,d,e][i]?.map (fun x => .chiral x)

private theorem census {m : RawMolecule} {g : Geometry} {a b c d e : RS}
    (domain : saturatedWithHalogens m = true) (carbons : RingCarbonReport.carbons m = ids)
    (c0 : row m g 0 = some (some (.chiral a))) (c1 : row m g 1 = some (some (.chiral b)))
    (c2 : row m g 2 = some (some (.chiral c))) (c3 : row m g 3 = some (some (.chiral d)))
    (c4 : row m g 4 = some (some (.chiral e))) :
    (classifyRingCarbonsAtBound? m g 2).map (·.labels) =
      some (ids.map fun i => (i,expected a b c d e i)) := by
  have answer := classifyRingCarbons?_labels_of_rows
    (g := g) (fuel := m.atomCount+2) (hint := fun _ => none) (radius := fun _ => 2)
    (expected a b c d e) domain (by
      intro i inside
      rw [carbons] at inside
      simp only [ids,List.mem_cons,List.not_mem_nil,or_false] at inside
      rcases inside with rfl | rfl | rfl | rfl | rfl
      · exact c0
      · exact c1
      · exact c2
      · exact c3
      · exact c4)
  rw [carbons] at answer
  exact answer

/-- All five carbon rows, explicitly tied to their fresh-root indices. -/
def labels (a b c d e : RS) : List (Nat × Option LocalizedAuxiliaryLabel) :=
  [(0,some (.chiral a)),(1,some (.chiral b)),(2,some (.chiral c)),
   (3,some (.chiral d)),(4,some (.chiral e))]

theorem original_report :
    (classifyRingCarbonsAtBound? molecule geometry 2).map (·.labels) =
      some (labels .S .R .S .R .S) := by
  apply census (a := .S) (b := .R) (c := .S) (d := .R) (e := .S) (by decide +kernel) (by decide +kernel)
  · exact centerRow (m := molecule) (i := 0) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) original_trials
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem mirror_report :
    (classifyRingCarbonsAtBound? molecule (mirror geometry) 2).map (·.labels) =
      some (labels .R .S .R .S .R) := by
  apply census (a := .R) (b := .S) (c := .R) (d := .S) (e := .R) (by decide +kernel) (by decide +kernel)
  · exact centerRow (m := molecule) (i := 0) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) mirror_trials
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem renumbered_report :
    (classifyRingCarbonsAtBound? renumbered movedGeometry 2).map (·.labels) =
      some (labels .R .R .S .S .S) := by
  apply census (a := .R) (b := .R) (c := .S) (d := .S) (e := .S) (by decide +kernel) (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact centerRow (m := renumbered) (i := 3) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) renumbered_trials
  · decide +kernel

theorem renumbered_mirror_report :
    (classifyRingCarbonsAtBound? renumbered (mirror movedGeometry) 2).map (·.labels) =
      some (labels .S .S .R .R .R) := by
  apply census (a := .S) (b := .S) (c := .R) (d := .R) (e := .R) (by decide +kernel) (by decide +kernel)
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact centerRow (m := renumbered) (i := 3) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) renumbered_mirror_trials
  · decide +kernel

/-- The constructed fluorospiro molecule is the same under the transposition
of C0 and C3. Its central descriptor stays uppercase S in both indexings,
and becomes uppercase R under geometric reflection. -/
theorem presentations :
    inspect molecule geometry 0 = some ⟨⟨.S,.R⟩,orders⟩ ∧
    inspect renumbered movedGeometry 3 = some ⟨⟨.S,.R⟩,orders.map move⟩ ∧
    inspect molecule (mirror geometry) 0 = some ⟨⟨.R,.S⟩,orders.map reflect⟩ ∧
    inspect renumbered (mirror movedGeometry) 3 = some ⟨⟨.R,.S⟩,(orders.map move).map reflect⟩ :=
  ⟨original_trials,renumbered_trials,mirror_trials,renumbered_mirror_trials⟩

end TetraStereo.Examples.RingTwoPairFluorospiro

assert_kernel_only TetraStereo.Examples.RingTwoPairFluorospiro.presentations
assert_kernel_only TetraStereo.Examples.RingTwoPairFluorospiro.original_report
assert_kernel_only TetraStereo.Examples.RingTwoPairFluorospiro.renumbered_report
assert_kernel_only TetraStereo.Examples.RingTwoPairFluorospiro.mirror_report
assert_kernel_only TetraStereo.Examples.RingTwoPairFluorospiro.renumbered_mirror_report
assert_kernel_only TetraStereo.Examples.RingTwoPairFluorospiro.all_marks_follow_scaffold
assert_kernel_only TetraStereo.Examples.RingTwoPairFluorospiro.inspected_orders_follow_scaffold
