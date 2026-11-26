import TetraStereo.Engine.RingEligibleGraph
import TetraStereo.Engine.RingRawComparisonLift

/-! One forward traversal of simple graph spheres followed by native inward row commits. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingRootLayerStore
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (Cell View Rule height)
open RingGraphCache (Visit sphere)

private def next {i : Input} {r : i.certified.Atom} (layer : List (Visit i r)) : List (Visit i r) :=
  layer.flatMap fun v =>
    (List.finRange i.certified.certified.input.molecule.atomCount).filterMap fun b =>
      if ok : i.certified.moleculeGraph.Adj v.atom b ∧ b ∉ v.history then
        some ⟨b :: v.history,b,.step v.path ok.1 ok.2⟩ else none

private theorem next_sphere (i : Input) (r : i.certified.Atom) (n : Nat) :
    next (sphere i r n) = sphere i r (n+1) := rfl

private def select {i : Input} (eligible : i.certified.Atom → Bool)
    {r : i.certified.Atom} (v : Visit i r) : Option (Site i) :=
  if v.atom ≠ r ∧ eligible v.atom = true then some (RingGraphPaths.site v.path) else none

/-- Preserve empty eligible layers: only atom-count fuel ends the traversal.
Each complete graph frontier is extended once. -/
def collect {i : Input} (eligible : i.certified.Atom → Bool) {r : i.certified.Atom} :
    Nat → List (Visit i r) → List (List (Site i))
  | 0, _ => []
  | fuel+1, layer => layer.filterMap (select eligible) :: collect eligible fuel (next layer)

private def specification {i : Input} (queue : Nat → List (Site i)) : Nat → Nat → List (List (Site i))
  | _, 0 => []
  | n, fuel+1 => queue n :: specification queue (n+1) fuel

private theorem collect_spec (i : Input) (eligible : i.certified.Atom → Bool)
    (r : i.certified.Atom) (fuel n : Nat) :
    collect eligible fuel (sphere i r n) = specification (RingEligibleGraph.queue i eligible r) n fuel := by
  induction fuel generalizing n with
  | zero => rfl
  | succ fuel ih =>
    simp only [collect, specification, next_sphere, ih]
    rfl

private theorem specification_get {i : Input} (queue : Nat → List (Site i)) (fuel n d : Nat) :
    (specification queue n fuel).getD d [] = if d < fuel then queue (n+d) else [] := by
  induction fuel generalizing n d with
  | zero => simp [specification]
  | succ fuel ih =>
    cases d with
    | zero => simp [specification]
    | succ d => simpa [specification, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (n+1) d

private theorem queue_empty_of_atomCount (i : Input) (eligible : i.certified.Atom → Bool)
    (r : i.certified.Atom) (n : Nat) (beyond : i.certified.certified.input.molecule.atomCount ≤ n) :
    RingEligibleGraph.queue i eligible r n = [] := by
  have empty : sphere i r n = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro v mem
    have size := (RingGraphCache.sphere_iff v n).mp mem
    have upper := RingGraphAuxiliaries.length_bound v.path
    omega
  simp [RingEligibleGraph.queue, empty]

private theorem queue_empty_of_height (i : Input) (eligible : i.certified.Atom → Bool)
    (r : i.certified.Atom) (n : Nat) (beyond : height i < n) :
    RingEligibleGraph.queue i eligible r n = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro q mem
  have depth := ((RingEligibleGraph.inventory i eligible r) n q).mp mem
  have upper := RingActiveDistanceSchedule.distance_bound q
  omega

/-- Captured layers reproduce every native distance queue, including empty internal layers. -/
theorem collected_queue (i : Input) (eligible : i.certified.Atom → Bool) (r : i.certified.Atom) (d : Nat) :
    (collect eligible i.certified.certified.input.molecule.atomCount (sphere i r 0)).getD d [] =
      RingEligibleGraph.queue i eligible r d := by
  rw [collect_spec, specification_get]
  by_cases small : d < i.certified.certified.input.molecule.atomCount
  · simp [small]
  · simp [small, queue_empty_of_atomCount i eligible r d (by omega)]

private theorem stored_shift {i : Input} (rule : Rule i) (r : i.certified.Atom)
    (queue : Nat → List (Site i)) (top k : Nat) (empty : queue (top+1) = []) :
    RingSphereQueue.stored rule r queue (top+1) (k+1) = RingSphereQueue.stored rule r queue top k := by
  induction k with
  | zero => simp [RingSphereQueue.stored, empty]
  | succ k ih =>
    rw [RingSphereQueue.stored, ih]
    simp only [Nat.add_sub_add_right]
    rfl

private theorem stored_full_stable {i : Input} (rule : Rule i) (r : i.certified.Atom)
    (queue : Nat → List (Site i)) (a b : Nat) (order : a ≤ b)
    (empty : ∀ d, a < d → queue d = []) :
    RingSphereQueue.stored rule r queue b (b+1) = RingSphereQueue.stored rule r queue a (a+1) := by
  induction b with
  | zero =>
    have zero : a = 0 := by omega
    subst a
    rfl
  | succ b ih =>
    by_cases same : a = b+1
    · subst a; rfl
    · rw [stored_shift rule r queue b (b+1) (empty _ (by omega))]
      exact ih (by omega)

private theorem stored_prefix_stable {i : Input} (rule : Rule i) (r : i.certified.Atom)
    (queue : Nat → List (Site i)) (a b cut : Nat) (order : a ≤ b)
    (empty : ∀ d, a < d → queue d = []) :
    RingSphereQueue.stored rule r queue b (b+1-cut) =
      RingSphereQueue.stored rule r queue a (a+1-cut) := by
  induction b with
  | zero =>
    have zero : a = 0 := by omega
    subst a
    rfl
  | succ b ih =>
    by_cases same : a = b+1
    · subst a; rfl
    · by_cases active : cut ≤ b+1
      · have step : b+1+1-cut = (b+1-cut)+1 := by omega
        rw [step, stored_shift rule r queue b (b+1-cut) (empty _ (by omega))]
        exact ih (by omega)
      · have left : b+1+1-cut = 0 := by omega
        have right : a+1-cut = 0 := by omega
        rw [left, right]
        rfl

/-- After all distances at least `cut` have been committed, the captured table
is literally the native table at the same boundary. A cut beyond either top
correctly gives the empty prefix; empty internal eligible layers are retained. -/
theorem prefix_rows_eq (i : Input) (eligible : i.certified.Atom → Bool) (rule : Rule i)
    (r : i.certified.Atom) (cut : Nat) :
    RingSphereQueue.stored rule r
      (fun d => (collect eligible i.certified.certified.input.molecule.atomCount
        (sphere i r 0)).getD d [])
      (i.certified.certified.input.molecule.atomCount-1)
      (i.certified.certified.input.molecule.atomCount-cut) =
    RingSphereQueue.stored rule r (RingEligibleGraph.queue i eligible r)
      (height i) (height i+1-cut) := by
  have positive : 0 < i.certified.certified.input.molecule.atomCount := by
    have upper := r.isLt
    omega
  simp only [collected_queue]
  let top := i.certified.certified.input.molecule.atomCount - 1
  have count : i.certified.certified.input.molecule.atomCount = top+1 := by dsimp [top]; omega
  rw [count]
  by_cases order : top ≤ height i
  · exact (stored_prefix_stable rule r _ top (height i) cut order
      (fun d h => queue_empty_of_atomCount i eligible r d (by omega))).symm
  · exact stored_prefix_stable rule r _ (height i) top cut (by omega)
      (fun d h => queue_empty_of_height i eligible r d h)

/-- Materialized rows use atom-count fuel and captured layer lookup, with no global height. -/
def rows (i : Input) (eligible : i.certified.Atom → Bool) (rule : Rule i)
    (r : i.certified.Atom) : List (Site i × Cell) :=
  let count := i.certified.certified.input.molecule.atomCount
  let layers := collect eligible count (sphere i r 0)
  RingSphereQueue.stored rule r (fun d => layers.getD d []) (count-1) count

/-- Literal native final-row equality for arbitrary rules and eligibility predicates. -/
theorem rows_eq (i : Input) (eligible : i.certified.Atom → Bool) (rule : Rule i) (r : i.certified.Atom) :
    rows i eligible rule r = RingSphereQueue.stored rule r
      (RingEligibleGraph.queue i eligible r) (height i) (height i+1) := by
  have positive : 0 < i.certified.certified.input.molecule.atomCount := by
    have upper := r.isLt
    omega
  unfold rows
  simp only [collected_queue]
  let top := i.certified.certified.input.molecule.atomCount - 1
  have count : i.certified.certified.input.molecule.atomCount = top+1 := by dsimp [top]; omega
  rw [count]
  by_cases order : top ≤ height i
  · exact (stored_full_stable rule r _ top (height i) order
      (fun d h => queue_empty_of_atomCount i eligible r d (by omega))).symm
  · exact stored_full_stable rule r _ (height i) top (by omega)
      (fun d h => queue_empty_of_height i eligible r d h)

def root (i : Input) (eligible : i.certified.Atom → Bool) (rule : Rule i) (r : i.certified.Atom) : Cell :=
  rule (RingGroupedReport.origin i r) (RingSphereQueue.reader r (RingSphereQueue.viewOf (rows i eligible rule r)))

theorem root_eq (i : Input) (eligible : i.certified.Atom → Bool) (rule : Rule i) (r : i.certified.Atom) :
    root i eligible rule r = RingEligibleGraph.root i eligible rule r := by
  simp only [root, rows_eq, RingSphereQueue.stored_eq, RingEligibleGraph.root, RingSphereQueue.finalCell]

/-- Opt-in typed report; the publication rule and eligibility policy are the public ones. -/
def report (i : Input) (atoms : List i.certified.Atom) : Option RingGroupedReport.Report :=
  atoms.mapM fun a =>
    (root i (RingPyramidalPublication.eligible i) (RingPyramidalPublication.publish i) a).map
      fun v => (a.val,v)

theorem report_eq (i : Input) (atoms : List i.certified.Atom) :
    report i atoms = RingChemicalReport.report? i atoms := by
  unfold report
  simp only [root_eq]
  rfl

/-- Preserve the full public raw admission, coordinate, hydrogen-completion and
P–H placement-consensus pipeline while opting into captured root layers. -/
def fromRaw? (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat) :
    Option RingGroupedReport.Report := RingRawComparisonLift.fromRaw report m g ids

theorem raw_exact (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat) :
    fromRaw? m g ids = RingHydrogenReport.fromRaw? m g ids := by
  apply RingRawComparisonLift.eq_native
  intro i atoms _
  exact report_eq i atoms

end TetraStereo.Engine.RingRootLayerStore
assert_kernel_only TetraStereo.Engine.RingRootLayerStore.collected_queue
assert_kernel_only TetraStereo.Engine.RingRootLayerStore.prefix_rows_eq
assert_kernel_only TetraStereo.Engine.RingRootLayerStore.rows_eq
assert_kernel_only TetraStereo.Engine.RingRootLayerStore.root_eq
assert_kernel_only TetraStereo.Engine.RingRootLayerStore.report_eq
assert_kernel_only TetraStereo.Engine.RingRootLayerStore.raw_exact
