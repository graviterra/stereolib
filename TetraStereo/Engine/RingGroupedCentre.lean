import TetraStereo.Engine.RingGroupedRanking

set_option autoImplicit false

namespace TetraStereo.Engine.RingGroupedCentre
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site Arm molecularValues)
open RingNestedActivePair (Frame Reader)
open RingActivePairReport (Slot Matrix Score Ranking)
open RingRetainedStereoDecision (Reads ArmProfile)
open RingRetainedChemicalPreorder (orderWord keyFor)
open RingRetainedSeedFrames (State)
open RingSingleTieCompletion (unitScore)
attribute [local instance] lexOrd

def cursor {i f} (fr : Frame i f) (k : Slot) : Arm i := ⟨(fr.direction k).val,some f⟩

theorem valid {i f} (fr : Frame i f) (k : Slot) : i.certified.LocalizedRerootCursorValid (cursor fr k) :=
  (i.certified.mem_localizedRerootNeighborFrames_iff _ _).mpr ⟨(fr.direction k).val.property,(fr.direction k).property⟩

/-- Four independent molecular profiles share the frozen state and the
centre's actual incident directions. This includes an inward parent edge. -/
structure Arms {i f} (fr : Frame i f) (read : Reader i) where
  profiles : Slot → ArmProfile
  computed : ∀ k, RingGroupedStereo.arm? i read (cursor fr k) = some (profiles k)
  source : ∀ k, Reads i read false (cursor fr k) (profiles k)

def arms? {i f} (fr : Frame i f) (read : Reader i) : Option (Arms fr read) := do
  let ⟨p,h⟩ ← (RingActivePairReport.four? fun k => RingGroupedStereo.arm? i read (cursor fr k)).attach
  return ⟨p,RingActivePairReport.four_at h,fun k => RingGroupedStereo.arm_source (RingActivePairReport.four_at h k)⟩

theorem arms_ready {i f read} (fr : Frame i f) (ready : RingGroupedStereo.Ready f read) :
    (arms? fr read).isSome = true := by
  have all (k : Slot) := RingGroupedStereo.arm_ready ready (cursor fr k) (valid fr k) (fr.direction k).property.1
  obtain ⟨p,h⟩ := Option.isSome_iff_exists.mp (RingActivePairReport.four_full _ fun k => Option.isSome_iff_exists.mpr (all k))
  simp [arms?,Option.attach_eq_some _ ⟨p,h⟩]

def Arms.state {i f fr read} (a : @Arms i f fr read) (rev : Bool) (k : Slot) : State i read rev :=
  match rev with
  | false => ⟨cursor fr k,valid fr k,a.profiles k,a.source k⟩
  | true => ⟨cursor fr k,valid fr k,(a.profiles k).reflect,(a.source k).reflect⟩

def Arms.key {i f fr read} (a : @Arms i f fr read) (rev : Bool) (k : Slot) :=
  RingGroupedRanking.key (if rev then (a.profiles k).reflect else a.profiles k) rev

theorem Arms.constitution {i f fr read} (a : @Arms i f fr read) (rev : Bool) (k : Slot) :
    (a.state rev k).profile.unit.priorDeep = orderWord (keyFor (fr.direction k)) := by
  obtain ⟨p,h,prior,_⟩ := RingRetainedSeedFrames.constitution (a.state rev k)
  have same : (a.state rev k).q = cursor fr k := by cases rev <;> rfl
  rw [same] at h
  have eqn := Option.some.inj (h.symm.trans (RingRetainedChemicalPreorder.read_key (fr.direction k)))
  exact prior.trans (congrArg orderWord eqn)

/-- A strict constitutional outcome has unit magnitude. At equality the
same first-rule evaluator supplies both signed magnitudes. -/
def Arms.edge {i f fr read} (a : @Arms i f fr read) (j k : Slot) : Option Score := do
  let x := a.profiles j
  let y := a.profiles k
  match compare x.unit.priorDeep y.unit.priorDeep with
  | .lt => return (-1,-1)
  | .gt => return (1,1)
  | .eq =>
    let v ← RingRetainedStereoDecision.decide? x y false
    let w ← RingRetainedStereoDecision.decide? x.reflect y.reflect true
    return (v.score,w.score)

/-- The actual signed comparison at every pair of slots is represented by
the same four keys on each geometry, including pairs tied after Rule 5. -/
theorem Arms.represented {i f fr read} (a : @Arms i f fr read) (j k : Slot) :
    ∃ z ∈ molecularValues, a.edge j k = some z ∧
      ∀ rev : Bool, compare (if rev then z.2 else z.1) 0 = compare (a.key rev j) (a.key rev k) := by
  let x := a.profiles j
  let y := a.profiles k
  have cmp (rev : Bool) : compare (a.key rev j) (a.key rev k) =
      (compare x.unit.priorDeep y.unit.priorDeep).then
        (compare (RingGroupedRanking.stereoKey (a.state rev j).profile rev)
          (RingGroupedRanking.stereoKey (a.state rev k).profile rev)) := by cases rev <;> rfl
  cases h : compare x.unit.priorDeep y.unit.priorDeep with
  | lt => exact ⟨(-1,-1),by decide,by simp only [Arms.edge,← show x = a.profiles j from rfl,← show y = a.profiles k from rfl,h,Option.pure_def],
      fun rev => by rw [cmp,h]; cases rev <;> rfl⟩
  | gt => exact ⟨(1,1),by decide,by simp only [Arms.edge,← show x = a.profiles j from rfl,← show y = a.profiles k from rfl,h,Option.pure_def],
      fun rev => by rw [cmp,h]; cases rev <;> rfl⟩
  | eq =>
    have eqn := Std.compare_eq_eq_iff_eq.mp h
    obtain ⟨v,hv⟩ := RingRetainedStereoDecision.decide_total (a.source j) (a.source k)
    obtain ⟨w,hw⟩ := RingRetainedStereoDecision.decide_total (a.source j).reflect (a.source k).reflect
    change RingRetainedStereoDecision.decide? (a.profiles j).reflect (a.profiles k).reflect true = some w at hw
    have values : (v.score,w.score) ∈ molecularValues := RingGroupedStereo.reading_values _ _ (a.source j) (a.source k)
      (RingRetainedSeedFrames.state_fixed_equality (a.state false j) (a.state false k) eqn) hv hw
    refine ⟨_,values,?_,?_⟩
    · simp [Arms.edge,show compare (a.profiles j).unit.priorDeep (a.profiles k).unit.priorDeep = .eq from h,hv,hw]
    · rintro (_|_)
      · exact RingGroupedRanking.first_order (a.state false j) (a.state false k) eqn (RingRetainedStereoDecision.first_iff.mpr hv)
      · exact RingGroupedRanking.first_order (a.state true j) (a.state true k) eqn (RingRetainedStereoDecision.first_iff.mpr hw)

/-- Read one directed edge without the four-arm cache. The constitutional
trace supplies strict signs, and a tied trace uses the signed molecular evaluator. -/
def incidentScore? (i : Input) (f a b : Site i) (read : Reader i) : Option Score := do
  let p ← RingRetainedChemicalTrace.compareAt? i f a b
  match cipTraceOutcome p with
  | .lt => return (-1,-1)
  | .gt => return (1,1)
  | .eq => RingGroupedStereo.score? i f a b read

theorem Arms.edge_source {i f fr read} (a : @Arms i f fr read) (j k : Slot) (ne : j ≠ k) :
    incidentScore? i f (fr.direction j).val (fr.direction k).val read = a.edge j k := by
  have traced := (RingRetainedChemicalPreorder.table_source (fr.direction j) (fr.direction k) (fr.incident ne)).trans
    (RingRetainedChemicalPreorder.table_order ..)
  obtain ⟨p,hp,order⟩ := Option.map_eq_some_iff.mp traced
  have x : (a.profiles j).unit.priorDeep = orderWord (keyFor (fr.direction j)) := a.constitution false j
  have y : (a.profiles k).unit.priorDeep = orderWord (keyFor (fr.direction k)) := a.constitution false k
  rw [← x,← y] at order
  obtain ⟨z,allowed,got,_⟩ := a.represented j k
  rw [got]
  cases stage : cipTraceOutcome p with
  | lt | gt => simpa [incidentScore?,hp,stage,Arms.edge,← order] using got
  | eq =>
    have compareEq : compare (a.profiles j).unit.priorDeep (a.profiles k).unit.priorDeep = .eq := order.symm.trans stage
    have atArm (n : Slot) : RingGroupedStereo.arm? i read ⟨(fr.direction n).val,some f⟩ = some (a.profiles n) := a.computed n
    have both : (do let v ← RingRetainedStereoDecision.decide? (a.profiles j) (a.profiles k) false
                    let w ← RingRetainedStereoDecision.decide? (a.profiles j).reflect (a.profiles k).reflect true
                    return (v.score,w.score)) = some z := by simpa only [Arms.edge,compareEq] using got
    obtain ⟨v,hv,more⟩ := Option.bind_eq_some_iff.mp both
    obtain ⟨w,hw,out⟩ := Option.bind_eq_some_iff.mp more
    have value : (v.score,w.score) = z := Option.some.inj out
    simp [incidentScore?,hp,stage,RingGroupedStereo.score?,RingGroupedStereo.comparison?,atArm,hv,hw,
      RingGroupedStereo.scores,value,allowed]

theorem Arms.matrix_total {i f fr read} (a : @Arms i f fr read) :
    (RingActivePairReport.matrix? a.edge).isSome = true :=
  (RingActivePairReport.matrix?_complete _).mpr fun j k _ => by
    obtain ⟨_,_,h,_⟩ := a.represented j k
    rw [h]; rfl

theorem Arms.matrix_order {i f fr read} (a : @Arms i f fr read) (m : Matrix a.edge)
    (rev : Bool) (j k : Slot) : compare (RingOrdinaryPairRefusal.score m rev j k) 0 = compare (a.key rev j) (a.key rev k) := by
  by_cases ne : j = k
  · subst k; simp [RingOrdinaryPairRefusal.score]
  · obtain ⟨z,_,got,order⟩ := a.represented j k
    have same := Option.some.inj ((m.found j k ne).symm.trans got)
    simpa only [RingOrdinaryPairRefusal.score,if_neg ne,same] using order rev

theorem Arms.coherent {i f fr read} (a : @Arms i f fr read) (m : Matrix a.edge) (rev : Bool) :
    RingChemicalPriority.ReferenceFrame.coherent RingOrdinaryPairRefusal.ids (RingOrdinaryPairRefusal.table m rev) false = true :=
  RingSingleTieCompletion.keys_coherent (a.key rev) m rev fun j k => by rw [RingOrdinaryPairRefusal.read_table,a.matrix_order]

theorem Arms.shared_tie {i f fr read} (a : @Arms i f fr read) (j k : Slot) :
    a.key false j = a.key false k ↔ a.key true j = a.key true k := by
  obtain ⟨z,inSet,_,order⟩ := a.represented j k
  have same (rev : Bool) := (Std.compare_eq_eq_iff_eq (a := a.key rev j) (b := a.key rev k))
  rw [← same false,← same true,← order false,← order true]
  simp only [RingActivePairs.molecularValues,List.mem_cons,List.not_mem_nil,or_false] at inSet
  rcases inSet with h | h | h | h | h <;> rw [h] <;> decide

end TetraStereo.Engine.RingGroupedCentre

assert_kernel_only TetraStereo.Engine.RingGroupedCentre.Arms.represented
assert_kernel_only TetraStereo.Engine.RingGroupedCentre.Arms.coherent
assert_kernel_only TetraStereo.Engine.RingGroupedCentre.Arms.shared_tie
