import TetraStereo.Engine.RingHistoryObservation
import TetraStereo.Engine.RingOriginMetricReport

/-! Execute the fixed-digraph reading of Rule 1b throughout a raw ring
report. Every constitutional key identifies closures and their origin
spheres from the visited atom list. Later stereochemical and marked
comparisons read those keys at every level of their own recursion. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingHistoryReport
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open RingActiveDistanceSchedule (Rule height)
open RingRetainedChemicalPreorder (orderWord)
open RingOriginPyramidalTrials (KeyReader WordReader)
attribute [local instance] lexOrd

def early? (i : Input) (q : Site i) : Option RingGeometryCriterion.Signature := do
  let fr ← RingNestedActivePair.frame? i q
  let parity := RingOrientation.orientation fun j =>
    ((RingHistoryObservation.key? i (RingGroupedCentre.cursor fr j)).map orderWord).getD []
  if parity = 0 then none else some ⟨RingOrientation.baseline fr * parity,0⟩

theorem early_exact (i : Input) (q : Site i) : early? i q = RingZeroMassReport.zeroEarly? i q := by
  rw [RingZeroMassReport.zero_early_exact]
  unfold early? RingSphereQueue.early?
  apply congrArg (fun next => (RingNestedActivePair.frame? i q).bind next)
  funext fr
  have words : (fun j => ((RingHistoryObservation.key? i (RingGroupedCentre.cursor fr j)).map orderWord).getD []) =
      (fun j => orderWord (RingRetainedChemicalPreorder.keyFor (fr.direction j))) := by
    funext j
    rw [RingHistoryObservation.keys_exact]
    change ((RingRetainedChemicalTrace.key? i ⟨(fr.direction j).val,some q⟩).map orderWord).getD [] = _
    rw [RingRetainedChemicalPreorder.read_key (fr.direction j)]
    rfl
  rw [words]
  rfl

def keys (i : Input) (read : Reader i) : KeyReader i := fun rev =>
  RingOriginFullKeys.fullKey i read rev
    (RingOriginStereoRanking.priorityWith i (RingHistoryObservation.key? i) read rev)

theorem keys_exact (i : Input) (read : Reader i) : keys i read = RingFullPathEligibility.key? i read := by
  funext rev q
  unfold keys
  rw [RingHistoryObservation.keys_exact,RingOriginFullKeys.native]
  have eqn := funext fun stages => funext (RingOriginStereoRanking.priorityWith_native i read rev stages)
  rw [eqn]

def marks (i : Input) (read : Reader i) : WordReader i
  | none,_ => some []
  | some atom,q => (RingGroupedMark.build i read atom (RingHistoryObservation.key? i)
      i.certified.executableLocalizedRerootChildren (i.certified.localizedRerootCursorBudget q + 1) q).map
        fun b => b.2.word

theorem marks_exact (i : Input) (read : Reader i) : marks i read = RingFrameTransport.markWord? i read := by
  funext atom q
  cases atom with
  | none => rfl
  | some a => unfold marks; rw [RingHistoryObservation.keys_exact]; rfl

def publish (i : Input) : Rule i := fun q read =>
  match RingPyramidalPublication.focusP i q with
  | some a => some ((RingOriginPyramidalTrials.dataWith i q (keys i read) (marks i read)).publish
      (inputGeometry i.certified) a.val)
  | none => match early? i q with
    | some s => some s.letters
    | none => RingOriginTetrahedralTrials.publishWith i q (keys i read) (marks i read)

section
open private native_data from TetraStereo.Engine.RingOriginPyramidalTrials

private theorem pyramid (i : Input) (q : Site i) (read : Reader i) (a : i.certified.Atom) :
    (RingOriginPyramidalTrials.dataWith i q (keys i read) (marks i read)).publish
      (inputGeometry i.certified) a.val = RingPyramidalPublication.pLabels i q read a := by
  rw [keys_exact,marks_exact,native_data,← RingPyramidalPairwise.pLabelsG_native,RingFrameTransport.pLabelsG_input]

end

section
open private native_data from TetraStereo.Engine.RingOriginTetrahedralTrials

private theorem tetra {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (q : Site i) (read : Reader i) :
    RingOriginTetrahedralTrials.publishWith i q (keys i read) (marks i read) =
      RingFullPathPublication.publish? i q read := by
  unfold RingOriginTetrahedralTrials.publishWith RingFullPathPublication.publish?
  cases hf : RingNestedActivePair.frame? i q with
  | none => rfl
  | some fr =>
    change RingOriginTetrahedralTrials.centreWith fr (keys i read) (marks i read) =
      RingFullPathPublication.centre? fr read
    unfold RingOriginTetrahedralTrials.centreWith
    rw [keys_exact,marks_exact,native_data fr read]
    exact (RingPairwisePublication.centreG_exact fr read _).symm.trans (RingFrameTransport.centreG_input geom fr read)

end

theorem publish_exact {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    publish i = RingPyramidalPublication.publish i := by
  funext q read
  unfold publish RingPyramidalPublication.publish
  cases hp : RingPyramidalPublication.focusP i q with
  | some a => exact congrArg some (pyramid i q read a)
  | none =>
    simp only [RingFullPathConstitution.fastPublish,early_exact]
    cases RingZeroMassReport.zeroEarly? i q with
    | none => exact tetra geom q read
    | some _ => rfl

def rows (i : Input) (r : i.certified.Atom) (batches : Nat) :=
  RingSphereQueue.stored (publish i) r (RingEligibleGraph.queue i (RingPyramidalPublication.eligible i) r)
    (height i) batches

theorem rows_exact {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (r : i.certified.Atom) (batches : Nat) : rows i r batches = RingSphereStore.rows i r batches := by
  unfold rows RingSphereStore.rows
  rw [publish_exact geom]

def root (i : Input) (r : i.certified.Atom) :=
  publish i (RingGroupedReport.origin i r)
    (RingSphereQueue.reader r (RingSphereQueue.viewOf (rows i r (height i + 1))))

theorem root_exact {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (r : i.certified.Atom) : root i r = RingChemicalGraphProof.root i r := by
  unfold root
  rw [rows_exact geom,publish_exact geom]
  unfold RingSphereStore.rows
  rw [RingSphereQueue.stored_eq]
  rfl

def report (i : Input) (atoms : List i.certified.Atom) : Option RingGroupedReport.Report :=
  atoms.mapM fun r => (root i r).map fun labels => (r.val,labels)

def fromRaw? := RingRawComparisonLift.fromRaw report

theorem raw_exact : fromRaw? = RingHydrogenReport.fromRaw? := by
  funext m g ids
  apply RingRawComparisonLift.eq_native
  intro i atoms reached
  unfold report RingChemicalReport.report?
  apply RingFrameTransport.mapM_congr_mem
  intro r _
  rw [root_exact reached.admitted r]
  rfl

end TetraStereo.Engine.RingHistoryReport
assert_kernel_only TetraStereo.Engine.RingHistoryReport.rows_exact
assert_kernel_only TetraStereo.Engine.RingHistoryReport.raw_exact
