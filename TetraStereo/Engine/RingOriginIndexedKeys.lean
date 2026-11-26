import TetraStereo.Engine.RingOriginRootAll

/-! Shared root-slice readers for the active-focus full-key calculation. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOriginIndexedKeys
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader)
open RingStereoSiblingPass (Branch)
open RingRetainedStereoRefinement (Observation)
private abbrev kids (i : Input) (q : Arm i) := i.certified.executableLocalizedRerootChildren q
private abbrev budget (i : Input) (q : Arm i) := i.certified.localizedRerootCursorBudget q
open RingStereoSiblingPass (order)
private structure Access (i : Input) where
  edges : Arm i → List (Arm i)
  key : Arm i → Option RingRetainedChemicalTrace.Key

private def Access.unitPass {i : Input} (access : Access i) (r : Reader i) : Nat → Arm i → Option Branch
  | 0,_ => none
  | n+1,q => do
    let k ← access.key q
    let v ← r q.occurrence
    let cs := access.edges q
    guard (v.all RingNestedActivePair.consistent = true ∧ (cs = [] → v = none))
    let bs ← cs.mapM (access.unitPass r n)
    return RingRetainedUnitPass.branch k (RingNestedActivePair.unit (v.map Prod.fst))
      (order Branch.shallow bs) (order Branch.deep bs)

private def Access.refinePass {i : Input} (access : Access i) (r : Reader i) (rev : Bool) (o : Observation)
    (prior : Arm i → Option Branch) : Nat → Arm i → Option Branch
  | 0,_ => none
  | n+1,q => do
    let p ← prior q
    let v ← r q.occurrence
    let bs ← (access.edges q).mapM (access.refinePass r rev o prior n)
    return RingRetainedStereoRefinement.extend p (o.value v rev) (order Branch.shallow bs) (order Branch.deep bs)

private def Access.run {i : Input} (access : Access i) (r : Reader i) (rev : Bool) :
    List Observation → Arm i → Option Branch
  | [],q => access.unitPass r (budget i q + 1) q
  | o::os,q => access.refinePass r rev o (access.run r rev os) (budget i q + 1) q


private def accessFor (i : Input) (f : Site i) (q : Arm i) : Access i :=
  let slice := localizedRerootRootSliceCache (i.certified.localizedRerootCarrierCache
    (i.certified.certified.input.molecule.atomCount + 1)) q.occurrence.val.root
  let edges := fun c : Arm i => (slice.reader.readChildren c).getD []
  let observe := fun c : Arm i =>
    (RingRetainedChemicalTrace.observation? i c (edges c).isEmpty).map fun o =>
      match c.occurrence.val.node.provenance with
      | .ringDuplicate d => {o with duplicate := (RingSingleCycleComparison.weight i
          f.val.node.history.reverse (RingSingleCycleOrigin.originPath c.occurrence.val.node d))}
      | _ => o
  ⟨edges,RingDuplicateScale.build observe edges
    (2 * (i.certified.certified.input.molecule.atomCount + 1 + 1) + 1)⟩

private theorem access_same (i : Input) (f : Site i) (q : Arm i) :
    accessFor i f q = ⟨kids i,RingSingleCycleComparison.rebuilt i f⟩ := by
  dsimp only [accessFor]
  simp only [LocalizedRerootChildReader.readChildren_eq]
  rfl

private theorem canonical_run (i : Input) (f : Site i) (read : Reader i) (rev : Bool) :
    ∀ stages, (Access.mk (kids i) (RingSingleCycleComparison.rebuilt i f)).run read rev stages =
      RingOriginStereoRanking.priorityWith i (RingSingleCycleComparison.rebuilt i f) read rev stages := by
  let ac : Access i := ⟨kids i,RingSingleCycleComparison.rebuilt i f⟩
  have unit (n : Nat) : ac.unitPass read n =
      RingOriginStereoRanking.unitWith i (RingSingleCycleComparison.rebuilt i f) read n := by
    induction n with
    | zero => rfl
    | succ n ih => funext c; simp only [Access.unitPass,RingOriginStereoRanking.unitWith,ih,ac]
  have step (o : Observation) (p : Arm i → Option Branch) (n : Nat) :
      ac.refinePass read rev o p n = RingRetainedStereoRefinement.build i p read o rev n := by
    induction n with
    | zero => rfl
    | succ n ih => funext c; simp only [Access.refinePass,RingRetainedStereoRefinement.build,ih,ac]
  intro stages
  induction stages with
  | nil => funext c; exact congrFun (unit _) c
  | cons o stages ih =>
    funext c
    simp only [Access.run,RingOriginStereoRanking.priorityWith,ih]
    exact congrFun (step o _ _) c

/-- A single cached molecular child reader supplies every constitutional,
unit, lowercase and seeded traversal in one full key. -/
def fullKey (i : Input) (f : Site i) (read : Reader i) (rev : Bool) (q : Arm i) :
    Option RingFullPathEligibility.Key :=
  let access := accessFor i f q
  let unitRank := access.run read rev []
  let lowerRank := access.run read rev [.lowercase]
  do
    let u ← unitRank q
    let l ← lowerRank q
    let r ← RingFullPathPairs.wordWith read rev access.edges unitRank .R q
    let s ← RingFullPathPairs.wordWith read rev access.edges unitRank .S q
    let fixed ← RingFullPathPairs.wordWith read rev access.edges lowerRank .R q
    return ⟨u.deep,max r s,l.word,fixed⟩

@[csimp] theorem fullKey_exact : @RingOriginFullKeys.active = @fullKey := by
  funext i f read rev q
  unfold fullKey
  simp only [access_same,canonical_run]
  rfl

/-- Named executable publisher ensures callers compiled after this module use
the shared active-key implementation even when the producer was built earlier. -/
def publish (i : Input) : RingActiveDistanceSchedule.Rule i := fun f read =>
  let keys := fullKey i f read
  let words := RingOriginMetricReport.marks i f read
  match RingPyramidalPublication.focusP i f with
  | some a => some ((RingOriginPyramidalTrials.dataWith i f keys words).publish
      (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified) a.val)
  | none => match RingOriginPriorityStore.early? i f with
    | some s => some s.letters
    | none => RingOriginTetrahedralTrials.publishWith i f keys words

theorem publish_exact : @publish = @RingOriginMetricReport.publish := by
  unfold publish RingOriginMetricReport.publish
  rw [←fullKey_exact]
  rfl

def rows (i : Input) (r : i.certified.Atom) (batches : Nat) :=
  RingSphereQueue.stored (publish i) r (RingEligibleGraph.queue i (RingPyramidalPublication.eligible i) r)
    (RingActiveDistanceSchedule.height i) batches

theorem rows_exact (i : Input) (r : i.certified.Atom) (batches : Nat) :
    rows i r batches = RingOriginMetricReport.rows i r batches := by
  unfold rows RingOriginMetricReport.rows
  rw [publish_exact]

/-- The final original-root call uses the native publisher on the active
auxiliary store; the unconditional original-root theorem justifies this. -/
def root (i : Input) (r : i.certified.Atom) :=
  RingPyramidalPublication.publish i (RingGroupedReport.origin i r)
    (RingSphereQueue.reader r (RingSphereQueue.viewOf
      (rows i r (RingActiveDistanceSchedule.height i + 1))))

theorem root_exact {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (r : i.certified.Atom) : root i r = RingOriginMetricReport.root i r := by
  unfold root RingOriginMetricReport.root
  rw [rows_exact,RingOriginRootAll.publish_origin geom]

def report (i : Input) (atoms : List i.certified.Atom) : Option RingGroupedReport.Report :=
  atoms.mapM fun r => (root i r).map fun labels => (r.val,labels)

theorem report_exact {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (atoms : List i.certified.Atom) : report i atoms = RingOriginMetricReport.report i atoms := by
  unfold report RingOriginMetricReport.report
  apply RingFrameTransport.mapM_congr_mem
  intro r _
  rw [root_exact geom]

def fromRaw? := RingRawComparisonLift.fromRaw report

theorem fromRaw?_exact : fromRaw? = RingOriginMetricReport.fromRaw? := by
  funext m g ids
  apply RingRawComparisonLift.congr
  intro i atoms trace
  exact report_exact trace.admitted atoms

/-- Calls compiled through the public API can share the indexed evaluation. -/
@[csimp] theorem raw_indexed : RingOriginMetricReport.fromRaw? = fromRaw? := fromRaw?_exact.symm

end TetraStereo.Engine.RingOriginIndexedKeys
assert_kernel_only TetraStereo.Engine.RingOriginIndexedKeys.fullKey_exact
assert_kernel_only TetraStereo.Engine.RingOriginIndexedKeys.fromRaw?_exact
