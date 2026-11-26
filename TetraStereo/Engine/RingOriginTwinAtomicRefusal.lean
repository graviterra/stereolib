import TetraStereo.Engine.RingOriginTwinFrame
import TetraStereo.Engine.RingOriginMetricTotal
import TetraStereo.Engine.RingAtomicMetricPublication
import TetraStereo.Engine.RingRootTwinDecision

/-! A pair of exchangeable terminal atoms is enough for a completed
tetrahedral refusal if Rule 1a leaves fewer than three tied slots.
No stereo comparisons or trial data are hypotheses. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOriginTwinAtomicRefusal
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Site Arm)
open RingNestedActivePair (Frame Reader)
open RingActivePairReport (Slot)
open RingGroupedCentre (cursor)
open RingPairwisePublication (ordinary tiedSlots strictData trials)
open RingFullPathEligibility (Key)
open RingHydrogenSpelling (TwinPair)
open RingAtomicMetricPublication (atomic)
open RingSingleCycleComparison (rebuilt)
open RingOriginTetrahedralTrials (keysWith wordsWith)
open private word from TetraStereo.Engine.RingOriginPriorityStore

/-- Count the slots belonging to a repeated complete atomic word. -/
def repeated {i : Input} {f : Site i} (fr : Frame i f) :=
  (List.finRange 4).filter fun s => (List.finRange 4).any fun t =>
    s != t && atomic (fr.direction s) == atomic (fr.direction t)

private def cachedRepeated {i : Input} {f : Site i} (fr : Frame i f) :=
  let words := Vector.ofFn (fun s => atomic (fr.direction s))
  (List.finRange 4).filter fun s => (List.finRange 4).any fun t =>
    s != t && words[s] == words[t]

@[csimp] private theorem repeated_cached : @repeated = @cachedRepeated := by
  funext i f fr
  simp [repeated,cachedRepeated]

private theorem prefix_eq {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i)
    (rev : Bool) (s : Slot) {k : Key}
    (h : RingOriginFullKeys.active i f r rev (cursor fr s) = some k) :
    k.throughFourA.head? = some (atomic (fr.direction s)) := by
  unfold RingOriginFullKeys.active RingOriginFullKeys.fullKey at h
  obtain ⟨u,hu,h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_,_,h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_,_,h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_,_,h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_,_,h⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl := Option.some.inj h
  simp only [RingOriginStereoRanking.priorityWith,RingOriginStereoRanking.unitWith] at hu
  obtain ⟨c,hc,hu⟩ := Option.bind_eq_some_iff.mp hu
  obtain ⟨_,_,hu⟩ := Option.bind_eq_some_iff.mp hu
  obtain ⟨_,_,hu⟩ := Option.bind_eq_some_iff.mp hu
  obtain ⟨_,_,hu⟩ := Option.bind_eq_some_iff.mp hu
  obtain rfl := Option.some.inj hu
  have eqn := RingAtomicMetricIndependence.direction_atomic (fr.direction s)
  change (rebuilt i f (cursor fr s)).map _ = _ at eqn
  rw [hc] at eqn
  exact congrArg (fun z : RingRetainedChemicalTrace.Column => some z.word) (Option.some.inj eqn)

private theorem few_full {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i)
    {x : Slot → Key} (hx : keysWith fr (RingOriginFullKeys.active i f r) false = some x)
    (few : (repeated fr).length < 3) : (tiedSlots (ordinary x)).length < 3 := by
  have smaller : (tiedSlots (ordinary x)).Sublist (repeated fr) := by
    apply List.sublist_filter_iff.mpr
    refine ⟨tiedSlots (ordinary x),List.filter_sublist,?_⟩
    symm
    apply List.filter_eq_self.mpr
    intro s hs
    obtain ⟨t,ht,hst⟩ := List.any_eq_true.mp (List.mem_filter.mp hs).2
    obtain ⟨ne,tie⟩ := Bool.and_eq_true_iff.mp hst
    rw [RingPairwisePublication.ordinary_tied] at tie
    have h (a : Slot) := prefix_eq fr r false a (RingActivePairReport.four_at hx a)
    have eqn := (h s).symm.trans ((congrArg (fun k : Key => k.throughFourA.head?)
      (beq_iff_eq.mp tie)).trans (h t))
    exact List.any_eq_true.mpr ⟨t,ht,Bool.and_eq_true_iff.mpr ⟨ne,beq_iff_eq.mpr (Option.some.inj eqn)⟩⟩
  exact lt_of_le_of_lt smaller.length_le few

private theorem only_unmarked (x y : Slot → Key)
    (few : (tiedSlots (ordinary x)).length < 3) {u v : Slot} (ne : u ≠ v) (tie : x u = x v)
    (marks : Option Slot → Option (Slot → RingRetainedChemicalTrace.Word))
    (empty : marks none = some (fun _ => [])) (sense : Bool → List Slot → Option RS) :
    (RingOriginTetrahedralTrials.data x y marks).publish sense = some none := by
  have nons : strictData (ordinary x) = false := by
    apply Bool.eq_false_iff.mpr
    intro yes
    have h := List.all_eq_true.mp (List.all_eq_true.mp yes u (List.mem_finRange _)) v (List.mem_finRange _)
    simp [RingPairwisePublication.ordinary_tied,tie,ne] at h
  have ts : trials (ordinary x) = [none] := by
    simp [trials,RingPairwisePublication.candidates,Nat.not_le.mpr few]
  unfold ordinary at nons
  simp [RingPairwisePublication.Data.publish,RingPairwisePublication.Data.ballots,
    RingOriginTetrahedralTrials.data,ts,empty,RingPairwisePublication.ballot,
    nons,RingPairwisePublication.Data.letters]
  rfl

/-- The claim applies on every ready reader and for any admitted ring
topology. The equality of the two terminal keys, successful full keys on
both geometries, and the absence of any marked trials are all derived. -/
theorem refusal {i : Input} {f : Site i} (fr : Frame i f) (frame : RingNestedActivePair.frame? i f = some fr)
    (tetra : RingPyramidalPublication.focusP i f = none) (p : TwinPair i) (center : fr.center = p.c)
    (offU : f.val.root ≠ p.u) (offV : f.val.root ≠ p.v) (few : (repeated fr).length < 3)
    (r : Reader i) (ready : RingGroupedStereo.Ready f r) :
    RingOriginMetricReport.publish i f r = some none := by
  obtain ⟨u,v,ne,constitution,full⟩ := RingOriginTwinFrame.twin_slots p fr center offU offV r ready false
  have ord : word (fr.direction u) = word (fr.direction v) := congrArg
    (fun z => (Option.map RingRetainedChemicalPreorder.orderWord z).getD []) constitution
  have parity := (RingOrientation.orientation_zero (fun s => word (fr.direction s))).mpr (fun inj => ne (inj ord))
  have early : RingOriginPriorityStore.early? i f = none := by simp [RingOriginPriorityStore.early?,frame,parity]
  have all (rev : Bool) : ∃ x, keysWith fr (RingOriginFullKeys.active i f r) rev = some x := by
    apply Option.isSome_iff_exists.mp
    apply RingActivePairReport.four_full
    intro s
    exact Option.isSome_iff_exists.mpr (RingOriginMetricTotal.active_total ready rev _
      (RingGroupedCentre.valid fr s) (fr.direction s).property.1)
  obtain ⟨x,hx⟩ := all false
  obtain ⟨y,hy⟩ := all true
  have xeq := Option.some.inj ((RingActivePairReport.four_at hx u).symm.trans
    (full.trans (RingActivePairReport.four_at hx v)))
  simp only [RingOriginMetricReport.publish,tetra,early,RingOriginTetrahedralTrials.publishWith,frame,
    RingOriginTetrahedralTrials.centreWith,RingOriginTetrahedralTrials.dataWith,hx,hy,Option.bind_eq_bind,
    Option.bind_some,Option.pure_def]
  exact only_unmarked x y (few_full fr r hx few) ne xeq _ rfl _

/-- This local test only inspects the graph, frame and atomic ligand words. -/
def simple (i : Input) (f : Site i) : Bool :=
  (RingPyramidalPublication.focusP i f).isNone &&
    (RingNestedActivePair.frame? i f).any (fun fr =>
      (RingRootTwinDecision.detectedTwinPair? i f.val.root fr.center).isSome && (repeated fr).length < 3)

theorem simple_exact {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {f : Site i} (ok : simple i f = true) (r : Reader i) (ready : RingGroupedStereo.Ready f r) :
    RingOriginMetricReport.publish i f r = some none ∧ RingChemicalGraphProof.state i f = some none := by
  obtain ⟨hp,h⟩ := Bool.and_eq_true_iff.mp ok
  have tetra := Option.isNone_iff_eq_none.mp hp
  cases hf : RingNestedActivePair.frame? i f with
  | none => simp [hf] at h
  | some fr =>
    simp only [hf,Option.any_some,Bool.and_eq_true,decide_eq_true_eq] at h
    obtain ⟨p,found⟩ := Option.isSome_iff_exists.mp h.1
    obtain ⟨center,offU,offV⟩ := RingRootTwinDecision.detected_sound i f.val.root fr.center p found
    have direct : RingRootTwinDecision.direct i f = some (some none) := by
      simp [RingRootTwinDecision.direct,fr.recognized,found]
    exact ⟨refusal fr hf tetra p center.symm offU offV h.2 r ready,
      RingRootTwinDecision.sound i f geom _ direct⟩

end TetraStereo.Engine.RingOriginTwinAtomicRefusal
assert_kernel_only TetraStereo.Engine.RingOriginTwinAtomicRefusal.refusal
assert_kernel_only TetraStereo.Engine.RingOriginTwinAtomicRefusal.simple_exact
