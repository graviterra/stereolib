import TetraStereo.Engine.RingOrdinaryLigandInventory
import TetraStereo.Engine.RingLigandTreeStore

/-! Public sphere publication from one through-4c signed inventory per ordinary ligand key. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingStereoInventoryReport
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (Cell Rule View height)
open RingNestedActivePair (Frame Reader)
open RingFullPathEligibility (Key)
open RingActivePairReport (Slot)
open private centreWithKeys centreWithKeys_exact from TetraStereo.Engine.RingFullPathPublication

def keys? {i f} (fr : @Frame i f) (r : Reader i) (rev : Bool) : Option (Slot → Key) :=
  RingActivePairReport.four? fun k =>
    RingOrdinaryLigandInventory.key? i r rev (RingGroupedCentre.cursor fr k)

theorem keys_exact {i f} (fr : @Frame i f) (r : Reader i) (rev : Bool) :
    keys? fr r rev = RingFullPathPublication.keys? fr r rev := by
  simp only [keys?,RingFullPathPublication.keys?,RingOrdinaryLigandInventory.key_exact]

def centre? {i f} (fr : @Frame i f) (r : Reader i) : Cell := do
  let ks ← keys? fr r false
  let ms ← keys? fr r true
  let out ← RingFullPathTrialReadings.readingsWith fr r false ks
  return RingFullPathPublication.letters ks ms (out.map Prod.snd)

theorem centre_exact {i f} (fr : @Frame i f) (r : Reader i) :
    centre? fr r = RingFullPathPublication.centre? fr r := by
  rw [centreWithKeys_exact]
  simp only [centre?,centreWithKeys,keys_exact]

def tetra? (i : Input) (q : Site i) (r : Reader i) : Cell :=
  match RingNestedActivePair.frame? i q with
  | none => some none
  | some fr => centre? fr r

theorem tetra_exact (i : Input) (q : Site i) (r : Reader i) :
    tetra? i q r = RingFullPathPublication.publish? i q r := by
  simp only [tetra?,RingFullPathPublication.publish?,centre_exact]
  rfl

def ligands? (i : Input) (q : Site i) (r : View i) (rev : Bool) :=
  (RingRetainedAuxiliary.frame i.certified q).mapM fun arm => do
    let atom ← arm.occurrence.val.node.current?
    let priority ← RingOrdinaryLigandInventory.key? i r rev arm
    return (⟨arm,atom.val,priority⟩ : RingPyramidalPublication.Ligand i)

theorem ligands_exact (i : Input) (q : Site i) (r : View i) (rev : Bool) :
    ligands? i q r rev = RingPyramidalPublication.ligands? i q r rev := by
  simp only [ligands?,RingPyramidalPublication.ligands?,RingOrdinaryLigandInventory.key_exact]

def hands? (i : Input) (q : Site i) (r : View i) (a : i.certified.Atom) (rev : Bool) :
    Option (List (Option RS)) := do
  let xs ← ligands? i q r rev
  let marks : List (Option Nat) := match xs with
    | [x,y,z] => if x.priority == y.priority && y.priority == z.priority then
        [some x.atom,some y.atom,some z.atom] else [none]
    | _ => []
  marks.mapM (RingPyramidalPublication.trial? r a rev xs)

theorem hands_exact (i : Input) (q : Site i) (r : View i) (a : i.certified.Atom) (rev : Bool) :
    hands? i q r a rev = RingPyramidalPublication.hands? i q r a rev := by
  simp only [hands?,RingPyramidalPublication.hands?,ligands_exact]
  rfl

def pLabels (i : Input) (q : Site i) (r : View i) (a : i.certified.Atom) := do
  guard ((RingRetainedAuxiliary.frame i.certified q).length = 3)
  let hs ← hands? i q r a false
  let ms ← hands? i q r a true
  RingFullPathPublication.crossed hs ms

theorem pLabels_exact (i : Input) (q : Site i) (r : View i) (a : i.certified.Atom) :
    pLabels i q r a = RingPyramidalPublication.pLabels i q r a := by
  simp only [pLabels,RingPyramidalPublication.pLabels,hands_exact]

def publish (i : Input) : Rule i := fun q r =>
  match RingPyramidalPublication.focusP i q with
  | some a => some (pLabels i q r a)
  | none => match RingLigandTreeStore.early? i q with
    | some s => some s.letters
    | none => tetra? i q r

theorem publish_exact (i : Input) : publish i = RingPyramidalPublication.publish i := by
  rw [← RingLigandTreeStore.publish_exact]
  funext q r
  simp only [publish,RingLigandTreeStore.publish,pLabels_exact,tetra_exact]
  rfl

def rows (i : Input) (r : i.certified.Atom) (cut : Nat) :=
  let n := i.certified.certified.input.molecule.atomCount
  let layers := RingRootLayerStore.collect (RingPyramidalPublication.eligible i) n (RingGraphCache.sphere i r 0)
  RingSphereQueue.stored (publish i) r (fun d => layers.getD d []) (n-1) (n-cut)

/-- The inventory publication runs on its own preceding store. At every cut,
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

end TetraStereo.Engine.RingStereoInventoryReport
assert_kernel_only TetraStereo.Engine.RingStereoInventoryReport.rows_exact
assert_kernel_only TetraStereo.Engine.RingStereoInventoryReport.raw_exact
