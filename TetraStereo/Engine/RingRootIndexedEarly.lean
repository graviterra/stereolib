import TetraStereo.Engine.RingSecondShellDecision
import TetraStereo.Engine.RingOriginTwinStore
import TetraStereo.Engine.RingSparseTwinReport

/-! Share a single original-root occurrence list across all four complete
constitutional ligand keys at an auxiliary focus and the full stereo calculation
on its frozen store. The active-focus comparison has its own checked exit. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingRootIndexedEarly
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site Arm)
open RingActivePairReport (Slot)
open RingSecondShellDecision (rootFrames)
open private neighborsFast_eq armsFast_eq frameWith? frameWith_eq attachMap_congr
  from TetraStereo.Engine.RingSecondShellDecision
attribute [local instance] lexOrd

private def near {i : Input} (frames : List i.certified.LocalizedCIPOccurrenceFrame) (q : Site i) :=
  (frames.filter fun f => f.root == q.val.root && f.address.length+1 == q.val.address.length &&
    f.address == q.val.address.dropLast) ++
  (frames.filter fun f => f.root == q.val.root && f.address.length == q.val.address.length+1 &&
    f.address.dropLast == q.val.address)

private def intended {i : Input} (f : Site i) (frames : List i.certified.LocalizedCIPOccurrenceFrame)
    (a : Arm i) :=
  if a.occurrence.val.node.isDuplicateLeaf then [] else
    let ns := if a.occurrence.val.root = f.val.root then near frames a.occurrence
      else RingSecondShellDecision.neighborsFast i a.occurrence
    match a.previous? with
    | none => ns
    | some prev => ns.filter (fun t => t.address != prev.val.address)

private theorem intended_eq {i : Input} (f : Site i) (a : Arm i) :
    intended f (rootFrames i f) a = i.certified.intendedLocalizedRerootChildFrames a := by
  have ns : (if a.occurrence.val.root = f.val.root then near (rootFrames i f) a.occurrence
      else RingSecondShellDecision.neighborsFast i a.occurrence) =
      i.certified.localizedRerootNeighborFrames (fuel := i.certified.certified.input.molecule.atomCount+1) a.occurrence.val := by
    rw [← neighborsFast_eq]
    split
    · rename_i h
      unfold RingSecondShellDecision.neighborsFast near rootFrames
      rw [h]
    · rfl
  simp only [intended,intendedLocalizedRerootChildFrames,ns]
  cases a.previous? <;> rfl

private def reader {i : Input} (f : Site i) :
    i.certified.LocalizedRerootChildReader (i.certified.certified.input.molecule.atomCount+1) :=
  let frames := rootFrames i f
  { readChildren := fun a => some ((intended f frames a).attach.map fun t =>
      ⟨⟨t.val, i.certified.mem_localizedOccurrences_of_mem_intendedLocalizedRerootChildFrames
        a t.val ((intended_eq f a) ▸ t.property)⟩,some a.occurrence⟩)
    readChildren_eq := by
      intro a
      unfold executableLocalizedRerootChildren? executableLocalizedRerootChildren
      congr 1
      exact attachMap_congr _ _ (intended_eq f a) _ _ (by intros; rfl) }

private def slots {i : Input} {q : Site i} (arms : List (Arm i))
    (exactArms : arms = RingRetainedAuxiliary.frame i.certified q) (fr : RingNestedActivePair.Frame i q)
    (s : Slot) : Arm i :=
  let a := arms.get (Fin.cast (by rw [exactArms,fr.four]) s)
  ⟨a.occurrence,some q⟩

private theorem slots_eq {i : Input} {q : Site i} (arms : List (Arm i))
    (eq : arms = RingRetainedAuxiliary.frame i.certified q) (fr : RingNestedActivePair.Frame i q) (s : Slot) :
    slots arms eq fr s = RingGroupedCentre.cursor fr s := by subst arms; rfl

private def words {i : Input} (arm : Arm i) (r : i.certified.LocalizedRerootChildReader
    (i.certified.certified.input.molecule.atomCount+1)) :=
  ((RingRetainedChemicalTrace.keyWith i r arm).map RingRetainedChemicalPreorder.orderWord).getD []

def early? (i : Input) (q : Site i) : Option RingGeometryCriterion.Signature := do
  let r := reader q
  let arms := RingSecondShellDecision.armsFast i q
  let fr ← frameWith? i q arms (armsFast_eq i q)
  let parity := RingOrientation.orientation (fun s => words (slots arms (armsFast_eq i q) fr s) r)
  if parity = 0 then none else some ⟨RingOrientation.baseline fr * parity,0⟩

open private constitutional from TetraStereo.Engine.RingSphereQueue
theorem early_exact (i : Input) (q : Site i) : early? i q = RingSphereQueue.early? i q := by
  unfold early? RingSphereQueue.early?
  simp only [frameWith_eq]
  apply congrArg (fun f => (RingNestedActivePair.frame? i q).bind f)
  funext fr
  have word (s : Slot) : words (slots _ (armsFast_eq i q) fr s) (reader q) = constitutional fr s := by
    rw [slots_eq]
    unfold words
    rw [RingRetainedChemicalTrace.keyWith_eq]
    change ((RingRetainedChemicalTrace.key? i ⟨(fr.direction s).val,some q⟩).map _).getD [] = _
    rw [RingRetainedChemicalPreorder.read_key]
    rfl
  simp only [word]

private def fastRoot (i : Input) (a : i.certified.Atom) :=
  let q := RingGroupedReport.origin i a
  if (RingPyramidalPublication.focusP i q).isNone then
    match early? i q with
    | some s => some s.letters
    | none => RingChemicalGraphProof.root i a
  else RingChemicalGraphProof.root i a

private theorem root_exact (i : Input) (a : i.certified.Atom) :
    fastRoot i a = RingChemicalGraphProof.root i a := by
  rw [← RingChemicalGraphProof.fastRoot_exact]
  unfold fastRoot RingChemicalGraphProof.fastRoot
  simp only [early_exact,← RingZeroMassReport.zero_early_exact]
  cases RingPyramidalPublication.focusP i (RingGroupedReport.origin i a) <;> simp [RingChemicalGraphProof.root]
  cases RingZeroMassReport.zeroEarly? i (RingGroupedReport.origin i a) <;> rfl

def fromRaw? := RingRawComparisonLift.fromRaw (fun i atoms => atoms.mapM fun a =>
  (fastRoot i a).map fun v => (a.val,v))

theorem raw_exact : fromRaw? = RingHydrogenReport.fromRaw? := by
  apply RingRawComparisonLift.eq_native_of_admitted
  intros
  simp only [root_exact]
  rfl

open private Access Access.mk Access.run canonical_run from TetraStereo.Engine.RingOccurrenceStereo
open private centreWithKeys centreWithKeys_exact from TetraStereo.Engine.RingFullPathPublication

private def fullKey {i : Input} (r : i.certified.LocalizedRerootChildReader
    (i.certified.certified.input.molecule.atomCount+1)) (view : RingNestedActivePair.Reader i)
    (rev : Bool) (arm : Arm i) : Option RingFullPathEligibility.Key := do
  let edges := fun (t : Arm i) => (r.readChildren t).getD []
  let access : Access i := Access.mk edges (RingRetainedChemicalTrace.keyWith i r)
  let ordinary := Access.run access view rev []
  let lower := Access.run access view rev [.lowercase]
  let u ← ordinary arm
  let l ← lower arm
  let ar ← RingFullPathPairs.wordWith view rev edges ordinary .R arm
  let as' ← RingFullPathPairs.wordWith view rev edges ordinary .S arm
  let fixed ← RingFullPathPairs.wordWith view rev edges lower .R arm
  return ⟨u.deep,max ar as',l.word,fixed⟩

private theorem fullKey_eq {i : Input} (r : i.certified.LocalizedRerootChildReader
    (i.certified.certified.input.molecule.atomCount+1)) (view : RingNestedActivePair.Reader i)
    (rev : Bool) (arm : Arm i) : fullKey r view rev arm = RingFullPathEligibility.key? i view rev arm := by
  unfold fullKey
  simp only [LocalizedRerootChildReader.readChildren_eq, RingRetainedChemicalTrace.keyWith_eq,
    executableLocalizedRerootChildren?,Option.getD_some,canonical_run]
  rfl

private def fullCentre {i : Input} (q : Site i) (arms : List (Arm i))
    (eq : arms = RingRetainedAuxiliary.frame i.certified q) (fr : RingNestedActivePair.Frame i q)
    (view : RingNestedActivePair.Reader i) : RingActiveDistanceSchedule.Cell := do
  let r := reader q
  let keys := fun rev => RingActivePairReport.four? fun s => fullKey r view rev (slots arms eq fr s)
  let orig ← keys false
  let mirror ← keys true
  let out ← RingFullPathTrialReadings.readingsWith fr view false orig
  return RingFullPathPublication.letters orig mirror (out.map Prod.snd)

private theorem fullCentre_eq {i : Input} (q : Site i) (arms : List (Arm i))
    (eq : arms = RingRetainedAuxiliary.frame i.certified q) (fr : RingNestedActivePair.Frame i q)
    (view : RingNestedActivePair.Reader i) : fullCentre q arms eq fr view =
      RingFullPathPublication.centre? fr view := by
  rw [show RingFullPathPublication.centre? fr view = centreWithKeys fr view from
    congrFun (congrFun (congrFun (congrFun centreWithKeys_exact i) q) fr) view]
  simp only [fullCentre,fullKey_eq,slots_eq]
  rfl

private def indexedPublish (i : Input) (q : Site i) (v : RingNestedActivePair.Reader i) :
    RingActiveDistanceSchedule.Cell :=
  match RingPyramidalPublication.focusP i q with
  | some a => some (RingPyramidalPublication.pLabels i q v a)
  | none => match early? i q with
    | some s => some s.letters
    | none =>
      let arms := RingSecondShellDecision.armsFast i q
      match frameWith? i q arms (armsFast_eq i q) with
      | none => some none
      | some fr => fullCentre q arms (armsFast_eq i q) fr v

private theorem indexedPublish_eq (i : Input) : indexedPublish i = RingPyramidalPublication.publish i := by
  funext q view
  simp only [indexedPublish, RingPyramidalPublication.publish, RingFullPathConstitution.fastPublish,
    early_exact,← RingZeroMassReport.zero_early_exact,frameWith_eq,fullCentre_eq,RingFullPathPublication.publish?]
  rfl

private def indexedRoot (i : Input) (a : i.certified.Atom) : RingActiveDistanceSchedule.Cell :=
  let q := RingGroupedReport.origin i a
  let rule := RingResidualPriority.splice (RingSparseTwinReport.facts i) (indexedPublish i)
  if RingSparseTwinReport.keep i q then
    match RingSparseTwinReport.facts i q with
    | some result => result
    | none =>
      let n := i.certified.certified.input.molecule.atomCount
      let layers := RingSparseTwinReport.layers i a
      let rows := RingSparseRefusalStore.rows (RingSparseTwinReport.keep i) rule a
        (fun d => layers.getD d []) (n-1) n
      indexedPublish i q (RingSphereQueue.reader a (RingSphereQueue.viewOf rows))
  else some none

private theorem indexedRoot_eq (i : Input) (a : i.certified.Atom) : indexedRoot i a = RingSparseTwinReport.root i a := by
  simp only [indexedRoot,indexedPublish_eq,RingSparseTwinReport.root,RingSparseTwinReport.sparse,
    RingSparseTwinReport.residual,Nat.sub_zero]
  cases RingSparseTwinReport.facts i (RingGroupedReport.origin i a) <;> rfl

def sparseFromRaw? := RingRawComparisonLift.fromRaw (fun i atoms => atoms.mapM fun a =>
  (indexedRoot i a).map fun v => (a.val,v))

theorem sparse_raw_exact : sparseFromRaw? = RingHydrogenReport.fromRaw? := by
  apply RingRawComparisonLift.eq_native_of_admitted
  intro i atoms ok
  simp only [indexedRoot_eq,RingSparseTwinReport.root_exact ok]
  rfl


open RingSingleCycleComparison (weight)
open RingSingleCycleOrigin (originPath)
open private word from TetraStereo.Engine.RingOriginPriorityStore

private def activeWord {i : Input} (q : Site i) (r : i.certified.LocalizedRerootChildReader
    (i.certified.certified.input.molecule.atomCount+1)) (arm : Arm i) :=
  let edges := fun (t : Arm i) => (r.readChildren t).getD []
  let observe := fun (t : Arm i) => (RingRetainedChemicalTrace.observation? i t (edges t).isEmpty).map fun o =>
    match t.occurrence.val.node.provenance with
    | .ringDuplicate d => {o with duplicate := weight i q.val.node.history.reverse (originPath t.occurrence.val.node d)}
    | _ => o
  ((RingDuplicateScale.build observe edges (2*(i.certified.certified.input.molecule.atomCount+1+1)+1) arm).map
    RingRetainedChemicalPreorder.orderWord).getD []

/-- Constitutional exit when duplicate distances are measured from the auxiliary focus. -/
def activeEarly? (i : Input) (q : Site i) : Option RingGeometryCriterion.Signature := do
  let r := reader q
  let arms := RingSecondShellDecision.armsFast i q
  let fr ← frameWith? i q arms (armsFast_eq i q)
  let parity := RingOrientation.orientation (fun s => activeWord q r (slots arms (armsFast_eq i q) fr s))
  if parity = 0 then none else some ⟨RingOrientation.baseline fr * parity,0⟩

theorem activeEarly_exact (i : Input) (q : Site i) : activeEarly? i q = RingOriginPriorityStore.early? i q := by
  unfold activeEarly? RingOriginPriorityStore.early?
  simp only [frameWith_eq]
  apply congrArg (fun f => (RingNestedActivePair.frame? i q).bind f)
  funext fr
  have same (s : Slot) : activeWord q (reader q) (slots _ (armsFast_eq i q) fr s) = word (fr.direction s) := by
    rw [slots_eq]
    simp only [activeWord,LocalizedRerootChildReader.readChildren_eq,executableLocalizedRerootChildren?,Option.getD_some]
    rfl
  simp only [same]

end TetraStereo.Engine.RingRootIndexedEarly
assert_kernel_only TetraStereo.Engine.RingRootIndexedEarly.early_exact
assert_kernel_only TetraStereo.Engine.RingRootIndexedEarly.raw_exact
assert_kernel_only TetraStereo.Engine.RingRootIndexedEarly.sparse_raw_exact
assert_kernel_only TetraStereo.Engine.RingRootIndexedEarly.activeEarly_exact
