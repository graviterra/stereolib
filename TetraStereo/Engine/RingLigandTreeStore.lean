import TetraStereo.Engine.RingLigandTreeComparison
import TetraStereo.Engine.RingRootLayerStore
import TetraStereo.Engine.RingSphereStore

/-! Execute the public constitutional decision on unordered zero-mass ligand
trees at each tetrahedral publication and recover every public sphere. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingLigandTreeStore
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (Cell Rule height)
open RingLigandTreeComparison
attribute [local instance] lexOrd

private def key {i : Input} {f : Site i} (a : RingRetainedChemicalPreorder.Direction i f) :=
  (reconstruct (depth i) (zeroTree a)).get (by simp [reconstruct_zero])

private theorem key_eq {i : Input} {f : Site i} (a : RingRetainedChemicalPreorder.Direction i f) :
    key a = RingZeroDuplicateMass.rebuiltFor a := by
  exact Option.some.inj ((Option.some_get _).trans (reconstruct_zero a))

def early? (i : Input) (q : Site i) : Option RingGeometryCriterion.Signature := do
  let fr ← RingNestedActivePair.frame? i q
  let parity := RingOrientation.orientation fun k =>
    RingRetainedChemicalPreorder.orderWord (key (fr.direction k))
  if parity = 0 then none else some ⟨RingOrientation.baseline fr * parity,0⟩

theorem early_exact (i : Input) (q : Site i) : early? i q = RingZeroMassReport.zeroEarly? i q := by
  simp only [early?,RingZeroMassReport.zeroEarly?,key_eq]

def publish (i : Input) : Rule i := fun q r =>
  match RingPyramidalPublication.focusP i q with
  | some a => some (RingPyramidalPublication.pLabels i q r a)
  | none => match early? i q with
    | some s => some s.letters
    | none => RingFullPathPublication.publish? i q r

theorem publish_exact (i : Input) : publish i = RingPyramidalPublication.publish i := by
  funext q r
  cases hp : RingPyramidalPublication.focusP i q <;>
    cases he : RingZeroMassReport.zeroEarly? i q <;>
    simp [publish,RingPyramidalPublication.publish,RingFullPathConstitution.fastPublish,early_exact,hp,he]

def rows (i : Input) (r : i.certified.Atom) (cut : Nat) :=
  let n := i.certified.certified.input.molecule.atomCount
  let layers := RingRootLayerStore.collect (RingPyramidalPublication.eligible i) n (RingGraphCache.sphere i r 0)
  RingSphereQueue.stored (publish i) r (fun d => layers.getD d []) (n-1) (n-cut)

/-- The tree-based publication runs on its own preceding store. At every cut,
every occurrence address, value and row position agrees with the public run. -/
theorem rows_exact (i : Input) (r : i.certified.Atom) (cut : Nat) :
    rows i r cut = RingSphereStore.rows i r (height i+1-cut) := by
  unfold rows
  rw [publish_exact]
  exact RingRootLayerStore.prefix_rows_eq ..

def report (i : Input) (atoms : List i.certified.Atom) : Option RingGroupedReport.Report :=
  atoms.mapM fun r => (RingRootLayerStore.root i (RingPyramidalPublication.eligible i) (publish i) r).map
    fun labels => (r.val,labels)

def fromRaw? := RingRawComparisonLift.fromRaw report

theorem raw_exact : fromRaw? = RingHydrogenReport.fromRaw? := by
  funext m g ids
  change RingRawComparisonLift.fromRaw report m g ids = _
  apply RingRawComparisonLift.eq_native
  intro i atoms _
  simpa only [report,RingRootLayerStore.report,publish_exact] using RingRootLayerStore.report_eq i atoms

end TetraStereo.Engine.RingLigandTreeStore
assert_kernel_only TetraStereo.Engine.RingLigandTreeStore.rows_exact
assert_kernel_only TetraStereo.Engine.RingLigandTreeStore.raw_exact
