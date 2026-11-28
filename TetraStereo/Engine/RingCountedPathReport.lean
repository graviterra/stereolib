import TetraStereo.Engine.RingCountedPathVerdict
import TetraStereo.Engine.RingOriginPyramidalTrials
import TetraStereo.Engine.RingRawComparisonLift
import TetraStereo.Engine.RingSphereStore

/-! Independent outside-in publication using interval-counted ligand keys. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingCountedPathReport
open OneCenter
open LocalizedChemicalRing (Input)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open RingActivePairs (Site)
open RingNestedActivePair (Frame Reader)
open RingActiveDistanceSchedule (Rule Cell height)
open private keys? keys_eq from TetraStereo.Engine.RingCountedPathVerdict
open private centreWithKeys centreWithKeys_exact from TetraStereo.Engine.RingFullPathPublication
open private native_data from TetraStereo.Engine.RingOriginPyramidalTrials

def tetrahedral {i : Input} {f : Site i} (fr : Frame i f) (read : Reader i) : Cell := do
  let actual ← keys? fr read false
  let mirrored ← keys? fr read true
  let hands ← RingFullPathTrialReadings.readingsWith fr read false actual
  return RingFullPathPublication.letters actual mirrored (hands.map Prod.snd)

theorem tetrahedral_exact {i : Input} {f : Site i} (fr : Frame i f) (read : Reader i) :
    tetrahedral fr read = RingFullPathPublication.centre? fr read := by
  rw [centreWithKeys_exact]
  simp only [tetrahedral,centreWithKeys,keys_eq]

def pyramidal (i : Input) (f : Site i) (read : Reader i) (a : i.certified.Atom) :=
  (RingOriginPyramidalTrials.dataWith i f (RingCountedPathVerdict.key? i read)
    (RingFrameTransport.markWord? i read)).publish (inputGeometry i.certified) a.val

theorem pyramidal_exact (i : Input) (f : Site i) (read : Reader i) (a : i.certified.Atom) :
    pyramidal i f read a = RingPyramidalPublication.pLabels i f read a := by
  have keys : RingCountedPathVerdict.key? i read = RingFullPathEligibility.key? i read :=
    funext fun rev => funext fun q => RingCountedPathVerdict.key_exact i read rev q
  rw [pyramidal,keys,native_data]
  exact (RingOriginPyramidalTrials.pLabels_exact i f read a _ ⟨rfl,fun _ => rfl,fun _ _ => rfl⟩).symm

/-- Preserve centre selection and the constitutional early result. All later
ordinary and promoted ballots use interval-counted keys on both geometries. -/
def publish (i : Input) : Rule i := fun f read =>
  match RingPyramidalPublication.focusP i f with
  | some a => some (pyramidal i f read a)
  | none => match RingZeroMassReport.zeroEarly? i f with
    | some s => some s.letters
    | none => match RingNestedActivePair.frame? i f with
      | none => some none
      | some fr => tetrahedral fr read

theorem publish_exact (i : Input) : publish i = RingPyramidalPublication.publish i := by
  funext f read
  simp only [publish,RingPyramidalPublication.publish,RingFullPathConstitution.fastPublish,
    RingFullPathPublication.publish?,pyramidal_exact,tetrahedral_exact]
  cases RingPyramidalPublication.focusP i f <;> simp
  cases RingZeroMassReport.zeroEarly? i f <;> simp
  cases RingNestedActivePair.frame? i f <;> rfl

/-- The reader for each batch is built from this evaluator's own earlier writes. -/
def rows (i : Input) (root : i.certified.Atom) (k : Nat) :=
  RingSphereQueue.stored (publish i) root
    (RingEligibleGraph.queue i (RingPyramidalPublication.eligible i) root) (height i) k

theorem rows_exact (i : Input) (root : i.certified.Atom) (k : Nat) :
    rows i root k = RingSphereStore.rows i root k := by
  unfold rows RingSphereStore.rows
  rw [publish_exact]

def root (i : Input) (a : i.certified.Atom) :=
  RingEligibleGraph.root i (RingPyramidalPublication.eligible i) (publish i) a

theorem root_exact (i : Input) (a : i.certified.Atom) :
    root i a = RingChemicalGraphProof.root i a := by
  unfold root RingChemicalGraphProof.root
  rw [publish_exact]

def report (i : Input) (atoms : List i.certified.Atom) : Option RingGroupedReport.Report :=
  atoms.mapM fun a => (root i a).map fun v => (a.val,v)

theorem report_exact (i : Input) (atoms : List i.certified.Atom) :
    report i atoms = RingChemicalReport.report? i atoms := by
  simp only [report,root_exact]
  rfl

def fromRaw? := RingRawComparisonLift.fromRaw report

/-- Complete raw responses agree, including failed admission or preparation,
implicit-hydrogen placement consensus, repeated requests, and refusals. -/
theorem raw_exact : fromRaw? = RingHydrogenReport.fromRaw? :=
  RingRawComparisonLift.eq_native_of_admitted report (fun i atoms _ => report_exact i atoms)

end TetraStereo.Engine.RingCountedPathReport
assert_kernel_only TetraStereo.Engine.RingCountedPathReport.publish_exact
assert_kernel_only TetraStereo.Engine.RingCountedPathReport.rows_exact
assert_kernel_only TetraStereo.Engine.RingCountedPathReport.raw_exact
