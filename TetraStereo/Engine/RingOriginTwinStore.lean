import TetraStereo.Engine.RingOriginOrderRawCheck
import TetraStereo.Engine.RingOriginTriplePublication
import TetraStereo.Engine.RingOriginTwinAtomicRefusal
import TetraStereo.Engine.RingOriginTwinBallots
import TetraStereo.Engine.RingAtomicMetricPublication
import TetraStereo.Engine.RingRootTwinDecision
import TetraStereo.Engine.RingOriginIndexedKeys
import TetraStereo.Engine.RingGlobalComparison

/-! Compare independently computed active-focus trials with the graph symmetry
of the public store. The trial certificate uses the two slots for the actual
terminal twins and is evaluated on the preceding public batch. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOriginTwinStore
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActivePairReport (Slot)
open RingNestedActivePair (Reader Frame)
open RingPairwisePublication (Data)
open RingActiveDistanceSchedule (height)
open RingHydrogenSpelling (TwinPair)
open RingPyramidalPublication (eligible)
open private lookup from TetraStereo.Engine.RingSphereQueue
open private readers from TetraStereo.Engine.RingAtomicMetricPublication

private def select (i : Input) (f : Site i) : Option (TwinPair i) := do
  let c ← i.certified.localizedOccurrenceDescriptorCenter? f
  RingRootTwinDecision.detectedTwinPair? i f.val.root c

private theorem direct {i : Input} {f : Site i} {p : TwinPair i} (h : select i f = some p) :
    RingRootTwinDecision.direct i f = some (some none) := by
  cases hc : i.certified.localizedOccurrenceDescriptorCenter? f with
  | none => simp [select,hc] at h
  | some c =>
    have hit : RingRootTwinDecision.detectedTwinPair? i f.val.root c = some p := by simpa [select,hc] using h
    simp [RingRootTwinDecision.direct,hc,hit]

def data {i : Input} {f : Site i} (fr : Frame i f) (read : Reader i) :=
  RingOriginTetrahedralTrials.dataWith fr (RingOriginIndexedKeys.fullKey i f read)
    (RingOriginMetricReport.marks i f read)

/-- The only exchange considered is the exchange of the graph-selected atoms
at this frame. Compare trial parities before consulting either geometry. -/
private def ballots {i : Input} {f : Site i} (fr : Frame i f) (p : TwinPair i) (d : Data) : Bool :=
  (List.finRange 4).any fun a => RingGroupedTrials.atom fr a == p.u.val &&
    (List.finRange 4).any fun b => RingGroupedTrials.atom fr b == p.v.val && RingOriginTwinBallots.check d a b

private theorem ballots_refuse {i : Input} {f : Site i} (fr : Frame i f) (p : TwinPair i) (d : Data)
    (ok : ballots fr p d = true) :
    d.publish (fun _ row => readback? (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified) (fr.atoms row)) =
      some none := by
  obtain ⟨a,_,ha⟩ := List.any_eq_true.mp ok
  obtain ⟨b,_,hb⟩ := List.any_eq_true.mp (Bool.and_eq_true_iff.mp ha).2
  exact RingOriginTwinBallots.frame_refusal fr _ d a b
    (RingOriginTwinBallots.check_sound d a b (Bool.and_eq_true_iff.mp hb).2)

/-- True requires complete ordered comparisons from the real active publisher.
An unavailable frame, key or mark supplies no certificate. -/
def twin (i : Input) (f : Site i) (read : Reader i) : Bool :=
  ((select i f).any fun p => (RingPyramidalPublication.focusP i f).isNone &&
    (RingOriginPriorityStore.early? i f).isNone &&
    (RingNestedActivePair.frame? i f).any fun fr => (data fr read).any (ballots fr p))

theorem twin_exact {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {f : Site i} {read : Reader i} (hit : twin i f read = true) :
    RingOriginMetricReport.publish i f read = some none ∧ RingChemicalGraphProof.state i f = some none := by
  cases sel : select i f with
  | none => simp [twin,sel] at hit
  | some p =>
    have native := RingRootTwinDecision.sound i f geom _ (direct sel)
    cases hp : RingPyramidalPublication.focusP i f
    case some => simp [twin,sel,hp] at hit
    cases he : RingOriginPriorityStore.early? i f
    case some => simp [twin,sel,hp,he] at hit
    cases hf : RingNestedActivePair.frame? i f with
    | none => simp [twin,sel,hp,he,hf] at hit
    | some fr =>
      cases hd : data fr read with
      | none => simp [twin,sel,hp,he,hf,hd] at hit
      | some d =>
        have yes : ballots fr p d = true := by simpa [twin,sel,hp,he,hf,hd] using hit
        have hdata := hd
        unfold data at hdata
        rw [←RingOriginIndexedKeys.fullKey_exact] at hdata
        exact ⟨by simp [RingOriginMetricReport.publish,hp,he,RingOriginTetrahedralTrials.publishWith,
          hf,RingOriginTetrahedralTrials.centreWith,hdata,ballots_refuse fr p d yes],native⟩

/-- A strict constitutional disagreement at a scheduled tetrahedral site
forces the actual row lists to differ at the boundary that publishes it.
Each evaluator may have any prior rows at that boundary. -/
theorem strict_sphere_difference {i : Input} {r : i.certified.Atom} {f : Site i} {n : Nat}
    (scheduled : f ∈ RingGlobalComparison.queue i r (height i - n))
    (tetra : RingPyramidalPublication.focusP i f = none)
    {active native : RingGeometryCriterion.Signature}
    (a : RingOriginPriorityStore.early? i f = some active)
    (b : RingSphereQueue.early? i f = some native)
    (different : active.letters ≠ native.letters) :
    RingOriginMetricReport.rows i r (n + 1) ≠ RingSphereStore.rows i r (n + 1) := by
  intro same
  have obs := congrArg (fun rows => RingSphereQueue.viewOf rows f) same
  simp only [RingOriginMetricReport.rows,RingSphereStore.rows,RingSphereQueue.stored_eq,
      RingSphereQueue.run,lookup,show f ∈ RingEligibleGraph.queue i (eligible i) r (height i - n) from scheduled,
      if_true,RingOriginMetricReport.publish,RingPyramidalPublication.publish,tetra,
      RingFullPathConstitution.fastPublish,RingZeroMassReport.zero_early_exact,a,b,Option.some.injEq] at obs
  exact different obs

/-- Equality of any later ordered stores entails equality at every earlier
boundary: the new batch has the same number of addresses in both runs. -/
theorem rows_prefix_of_equal {i : Input} {r : i.certified.Atom} {n k : Nat}
    (le : n ≤ k) (same : RingOriginMetricReport.rows i r k = RingSphereStore.rows i r k) :
    RingOriginMetricReport.rows i r n = RingSphereStore.rows i r n := by
  induction k with
  | zero => simpa [Nat.eq_zero_of_le_zero le] using same
  | succ k ih =>
    rcases eq_or_lt_of_le le with eq | lt
    · simpa only [eq] using same
    · apply ih (by omega)
      simp only [RingOriginMetricReport.rows,RingSphereStore.rows,RingSphereQueue.stored] at same
      exact List.append_inj_right same (by simp only [List.length_map])

/-- A strict constitutional decision at the requested tetrahedral atom fixes
both complete root cells even if their auxiliary stores differ. -/
theorem strict_root_cells {i : Input} {r : i.certified.Atom}
    (tetra : RingPyramidalPublication.focusP i (RingGroupedReport.origin i r) = none)
    {s : RingGeometryCriterion.Signature}
    (hit : RingSphereQueue.early? i (RingGroupedReport.origin i r) = some s) :
    RingOriginMetricReport.root i r = some s.letters ∧
      RingChemicalGraphProof.root i r = some s.letters := by
  have active := RingOriginRootAll.early_exact (RingGroupedReport.origin i r) rfl
  rw [RingZeroMassReport.zero_early_exact,hit] at active
  constructor
  · simp only [RingOriginMetricReport.root,RingOriginMetricReport.publish,tetra,active]
  · simp only [RingChemicalGraphProof.root,RingEligibleGraph.root,RingSphereQueue.finalCell,
      RingPyramidalPublication.publish,tetra,RingFullPathConstitution.fastPublish,
      RingZeroMassReport.zero_early_exact,hit]

def structural {i : Input} (f : Site i) : Bool :=
  RingOriginOrderCheck.focus f ||
    ((RingPyramidalPublication.focusP i f).isNone && (RingAtomicMetricPublication.early? i f).isSome) ||
    RingOriginTwinAtomicRefusal.simple i f || RingOriginTriplePublication.check i f

/-- Check every eligible occurrence before computing any auxiliary stores. -/
def structuralCheck (i : Input) (r : i.certified.Atom) : Bool :=
  (RingActiveDistanceSchedule.sites i).all fun f =>
    if RingEligibleGraph.candidate (eligible i) r f then structural f else true

private abbrev KeyReader (i : Input) :=
  i.certified.LocalizedRerootChildReader (i.certified.certified.input.molecule.atomCount + 1)

private def wordWith {i : Input} {f : Site i} (reader : KeyReader i) (fr : Frame i f) (s : Slot) :=
  ((RingRetainedChemicalTrace.keyWith i reader (RingGroupedCentre.cursor fr s)).map
    (fun k => k.atomic.word)).getD []

private theorem wordWith_eq {i : Input} {f : Site i} (reader : KeyReader i) (fr : Frame i f) (s : Slot) :
    wordWith reader fr s = RingAtomicMetricPublication.atomic (fr.direction s) := by
  simp only [wordWith,RingRetainedChemicalTrace.keyWith_eq,RingGroupedCentre.cursor,
    RingRetainedChemicalPreorder.read_key,Option.map_some,Option.getD_some,RingAtomicMetricPublication.atomic]

attribute [local instance] lexOrd

private def frameCheck {i : Input} {f : Site i} (reader : KeyReader i) (fr : Frame i f) : Bool :=
  RingOriginTripleFrame.check fr || (
    let words := Vector.ofFn (wordWith reader fr)
    let twins := (List.finRange 4).filter fun a => (List.finRange 4).any fun b =>
      a != b && words[a.val] == words[b.val]
    RingOrientation.orientation (fun a : Slot => words[a.val]) != 0 ||
      ((RingRootTwinDecision.detectedTwinPair? i f.val.root fr.center).isSome && twins.length < 3))

/-- Reuse the closure inventory and the child index for the requested root.
Each reached tetrahedral frame computes each of its four atomic words once. -/
private def cachedCheck (i : Input) (r : i.certified.Atom) : Bool :=
  let leaves := RingOriginOrderCheck.closures i r
  let index := localizedRerootRootSliceCache
    (i.certified.localizedRerootCarrierCache (i.certified.certified.input.molecule.atomCount + 1)) r
  (RingActiveDistanceSchedule.sites i).all fun f =>
    if RingEligibleGraph.candidate (eligible i) r f then
      (leaves.all fun q => leaves.all fun p => RingOriginOrderCheck.pair f q p) ||
        ((RingPyramidalPublication.focusP i f).isNone &&
          (RingNestedActivePair.frame? i f).any (frameCheck index.reader))
    else true

private theorem frameCheck_eq {i : Input} {f : Site i} (reader : KeyReader i) (fr : Frame i f) :
    frameCheck reader fr =
      ((RingOrientation.orientation (fun s => RingAtomicMetricPublication.atomic (fr.direction s)) != 0) ||
      ((RingRootTwinDecision.detectedTwinPair? i f.val.root fr.center).isSome &&
        (RingOriginTwinAtomicRefusal.repeated fr).length < 3) || RingOriginTripleFrame.check fr) := by
  simp only [frameCheck,Vector.getElem_ofFn,wordWith_eq,RingOriginTwinAtomicRefusal.repeated]
  exact Bool.or_comm ..

@[csimp] private theorem structural_cached : structuralCheck = cachedCheck := by
  funext i r
  unfold structuralCheck cachedCheck
  congr 1
  funext f
  split_ifs with cand
  · simp only [structural,RingOriginOrderCheck.focus,cand.1]
    cases hp : RingPyramidalPublication.focusP i f with
    | some p => simp [RingOriginTwinAtomicRefusal.simple,RingOriginTriplePublication.check,hp]
    | none =>
      cases hf : RingNestedActivePair.frame? i f with
      | none =>
        simp [RingAtomicMetricPublication.early?,RingOriginTwinAtomicRefusal.simple,
          RingOriginTriplePublication.check,hp,hf]
      | some fr =>
        let v := RingOrientation.orientation (fun s => RingAtomicMetricPublication.atomic (fr.direction s))
        by_cases hz : v = 0
        · simp only [RingAtomicMetricPublication.early?,RingOriginTwinAtomicRefusal.simple,
            RingOriginTriplePublication.check,hp,hf,frameCheck_eq,Option.isNone_none,
            Option.any_some,Option.bind_eq_bind,Option.bind_some,Bool.true_and,←show v = RingOrientation.orientation (fun s => RingAtomicMetricPublication.atomic (fr.direction s)) from rfl]
          simp [hz,Bool.or_assoc]
        · simp only [RingAtomicMetricPublication.early?,RingOriginTwinAtomicRefusal.simple,
            RingOriginTriplePublication.check,hp,hf,frameCheck_eq,Option.isNone_none,
            Option.any_some,Option.bind_eq_bind,Option.bind_some,Bool.true_and,←show v = RingOrientation.orientation (fun s => RingAtomicMetricPublication.atomic (fr.direction s)) from rfl]
          simp [hz]
  · rfl

def localCheck (i : Input) (f : Site i) (read : Reader i) : Bool := structural f || twin i f read

private theorem local_exact {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {r : i.certified.Atom} {n : Nat} {f : Site i} (bound : n < height i + 1)
    (mem : f ∈ RingGlobalComparison.queue i r (height i - n))
    (hit : localCheck i f (RingGlobalComparison.prior i r n) = true) :
    RingOriginMetricReport.publish i f (RingGlobalComparison.prior i r n) =
      RingPyramidalPublication.publish i f (RingGlobalComparison.prior i r n) := by
  rcases Bool.or_eq_true_iff.mp hit with static | twins
  · rcases Bool.or_eq_true_iff.mp static with original | triple
    case inr =>
      rw [RingGlobalComparison.prior_exact (Or.inl ⟨bound,mem⟩ : RingGlobalComparison.Called i r n f),
        ←RingChemicalGraphProof.state_eq]
      obtain ⟨a,b⟩ := RingOriginTriplePublication.exact_cell geom triple _ (RingChemicalGraphProof.ready geom f)
      exact a.trans b.symm
    rcases Bool.or_eq_true_iff.mp original with easy | simple
    case inr =>
      rw [RingGlobalComparison.prior_exact (Or.inl ⟨bound,mem⟩ : RingGlobalComparison.Called i r n f),
        ←RingChemicalGraphProof.state_eq]
      obtain ⟨a,b⟩ := RingOriginTwinAtomicRefusal.simple_exact geom simple _ (RingChemicalGraphProof.ready geom f)
      exact a.trans b.symm
    rcases Bool.or_eq_true_iff.mp easy with order | early
    · have cand := ((RingEligibleGraph.inventory i _ r _ f).mp mem).1
      exact RingOriginOrderTransport.publish_exact geom f (RingOriginOrderDomain.factors f cand.2.2.1
        ((RingOriginOrderCheck.focus_iff f).mp order)) _
    · obtain ⟨tetra,yes⟩ := Bool.and_eq_true_iff.mp early
      obtain ⟨s,hs⟩ := Option.isSome_iff_exists.mp yes
      exact readers (Option.isNone_iff_eq_none.mp tetra) hs _ _
  · obtain ⟨active,native⟩ := twin_exact geom twins
    rw [active,RingGlobalComparison.prior_exact (Or.inl ⟨bound,mem⟩ : RingGlobalComparison.Called i r n f),
      ←RingChemicalGraphProof.state_eq,native]

/-- Certify the prefix by testing each scheduled site against its preceding
public rows. No alternate store or final descriptor is an input to the test. -/
def check (i : Input) (r : i.certified.Atom) (batches : Nat) : Bool :=
  (List.range batches).all fun n => (RingGlobalComparison.queue i r (height i - n)).all
    fun f => localCheck i f (RingGlobalComparison.prior i r n)

/-- Build the public rows once, carrying the completed prefix into the next
batch. The partial result is absent if any scheduled site lacks a certificate. -/
def audit (i : Input) (r : i.certified.Atom) :
    Nat → Option (List (Site i × RingActiveDistanceSchedule.Cell))
  | 0 => some []
  | n+1 => do
    let before ← audit i r n
    let read := RingSphereQueue.reader r (RingSphereQueue.viewOf before)
    let queue := RingGlobalComparison.queue i r (height i - n)
    guard (queue.all (fun f => localCheck i f read))
    return queue.map (fun f => (f,RingPyramidalPublication.publish i f read)) ++ before

theorem audit_eq (i : Input) (r : i.certified.Atom) (n : Nat) :
    audit i r n = if check i r n then some (RingSphereStore.rows i r n) else none := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have next : check i r (n+1) =
        (check i r n && (RingGlobalComparison.queue i r (height i - n)).all
          (fun f => localCheck i f (RingGlobalComparison.prior i r n))) := by
      simp [check,List.range_succ,List.all_append]
    rw [next]
    simp only [audit,ih]
    cases hc : check i r n with
    | false => rfl
    | true =>
      let accepted := (RingGlobalComparison.queue i r (height i - n)).all
        (fun f => localCheck i f (RingGlobalComparison.prior i r n))
      change (do
        let _ ← (guard (accepted = true) : Option Unit)
        return RingSphereStore.rows i r (n+1)) = if true && accepted then some _ else none
      cases accepted <;> rfl

theorem rows_exact {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {r : i.certified.Atom} {batches : Nat} (bounded : batches ≤ height i + 1)
    (ok : check i r batches = true) :
    RingOriginMetricReport.rows i r batches = RingSphereStore.rows i r batches := by
  unfold check at ok
  induction batches with
  | zero => rfl
  | succ n ih =>
    have smaller := (List.all_eq_true.mp ok)
    have prev := ih (by omega) (List.all_eq_true.mpr fun k hk =>
      smaller k (List.mem_range.mpr (by have := List.mem_range.mp hk; omega)))
    unfold RingOriginMetricReport.rows RingSphereStore.rows at prev ⊢
    simp only [RingSphereQueue.stored,prev]
    congr 1
    apply List.map_congr_left
    intro f mem
    congr 1
    apply local_exact geom (by omega) mem
    exact List.all_eq_true.mp (smaller n (List.mem_range.mpr (by omega))) f mem



theorem audit_stores {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {r : i.certified.Atom} {rows} (hit : audit i r (height i+1) = some rows) :
    rows = RingSphereStore.rows i r (height i+1) ∧
      ∀ k ≤ height i+1, RingOriginMetricReport.rows i r k = RingSphereStore.rows i r k := by
  rw [audit_eq] at hit
  split at hit
  · rename_i all
    refine ⟨(Option.some.inj hit).symm,?_⟩
    intro k bound
    apply rows_exact geom bound
    exact List.all_eq_true.mpr fun n hn => List.all_eq_true.mp all n
      (List.mem_range.mpr (lt_of_lt_of_le (List.mem_range.mp hn) bound))
  · contradiction

theorem of_structural {i : Input} {r : i.certified.Atom} (ok : structuralCheck i r = true) (n : Nat) :
    check i r n = true := by
  apply List.all_eq_true.mpr
  intro k _
  apply List.all_eq_true.mpr
  intro f mem
  have cand := ((RingEligibleGraph.inventory i _ r _ f).mp mem).1
  have static := List.all_eq_true.mp ok f (List.mem_attach ..)
  exact Bool.or_eq_true_iff.mpr (Or.inl (by simpa only [if_pos cand] using static))

theorem structural_stores {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {r : i.certified.Atom} (ok : structuralCheck i r = true) (n : Nat) (bound : n ≤ height i + 1) :
    RingOriginMetricReport.rows i r n = RingSphereStore.rows i r n :=
  rows_exact geom bound (of_structural ok n)

theorem raw_exact (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat)
    (ok : ∀ i atoms, RingRawComparisonLift.RawTrace m g ids i atoms →
      ∀ r ∈ atoms, check i r (height i + 1) = true) :
    RingOriginMetricReport.fromRaw? m g ids = RingHydrogenReport.fromRaw? m g ids := by
  apply RingRawComparisonLift.eq_native
  intro i atoms trace
  unfold RingOriginMetricReport.report RingChemicalReport.report?
  apply RingFrameTransport.mapM_congr_mem
  intro r mem
  have root : RingOriginMetricReport.root i r = RingChemicalGraphProof.root i r := by
    unfold RingOriginMetricReport.root
    rw [rows_exact trace.admitted le_rfl (ok i atoms trace r mem),RingOriginRootAll.publish_origin trace.admitted]
    unfold RingSphereStore.rows
    rw [RingSphereQueue.stored_eq]
    rfl
  rw [root]
  rfl

private def placement (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat) : Option Bool := do
  let source ← LocalizedChemicalRing.admitRawSpatial? m g
  let original ← RingMolecularReport.resolve source ids
  let i ← RingChemicalReport.prepared? source
  let atoms ← RingMolecularReport.resolve i (original.map Fin.val)
  return atoms.all (structuralCheck i)

/-- Apply the structural certificate to the public input and each reached
hydrogen placement. A failed preparation is preserved as an absent result. -/
def structuralFromRaw? (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat) : Option Bool := do
  let p ← RingHydrogenReport.preparedGeometry? m g ids
  RingOriginOrderRawCheck.search (fun ps => placement p.molecule ⟨ps⟩ ids) p.sites p.positions

theorem raw_sound {m g ids} (hit : structuralFromRaw? m g ids = some true)
    {i atoms} (trace : RingRawComparisonLift.RawTrace m g ids i atoms) :
    ∀ r ∈ atoms, structuralCheck i r = true := by
  obtain ⟨p,hp,ps,mem,source,admit,original,oldIDs,prepared,newIDs⟩ := trace
  have all : RingOriginOrderRawCheck.search (fun ps => placement p.molecule ⟨ps⟩ ids) p.sites p.positions =
      some true := by simpa [structuralFromRaw?,hp] using hit
  have one := (RingOriginOrderRawCheck.search_true _ _ _).mp all ps mem
  simpa [placement,admit,oldIDs,prepared,newIDs] using one

theorem raw_certified {m g ids} (ok : structuralFromRaw? m g ids = some true) :
    RingOriginMetricReport.fromRaw? m g ids = RingHydrogenReport.fromRaw? m g ids :=
  raw_exact m g ids fun _ _ trace r mem => of_structural (raw_sound ok trace r mem) _

theorem raw_stores {m g ids} (ok : structuralFromRaw? m g ids = some true)
    {i atoms} (trace : RingRawComparisonLift.RawTrace m g ids i atoms) {r : i.certified.Atom} (mem : r ∈ atoms)
    {n : Nat} (bound : n ≤ height i+1) :
    RingOriginMetricReport.rows i r n = RingSphereStore.rows i r n :=
  structural_stores trace.admitted (raw_sound ok trace r mem) n bound

end TetraStereo.Engine.RingOriginTwinStore
assert_kernel_only TetraStereo.Engine.RingOriginTwinStore.twin_exact
assert_kernel_only TetraStereo.Engine.RingOriginTwinStore.rows_exact
assert_kernel_only TetraStereo.Engine.RingOriginTwinStore.raw_exact
assert_kernel_only TetraStereo.Engine.RingOriginTwinStore.audit_stores
assert_kernel_only TetraStereo.Engine.RingOriginTwinStore.structural_stores
assert_kernel_only TetraStereo.Engine.RingOriginTwinStore.raw_stores
assert_kernel_only TetraStereo.Engine.RingOriginTwinStore.raw_certified

assert_kernel_only TetraStereo.Engine.RingOriginTwinStore.strict_sphere_difference
assert_kernel_only TetraStereo.Engine.RingOriginTwinStore.rows_prefix_of_equal
assert_kernel_only TetraStereo.Engine.RingOriginTwinStore.strict_root_cells
