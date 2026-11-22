import TetraStereo.Engine.RingNestedActivePair
import TetraStereo.Engine.RingRetainedChemicalPreorder

set_option autoImplicit false

namespace TetraStereo.Engine.RingPairGateCount
open OneCenter CertifiedLocalizedCIPInput RingNestedActivePair

private def classAt (rev : Bool) (v : Visit) := unit (v.label rev)

private theorem zero_iff {a b : List Nat} (same : a.length = b.length) :
    lowerScore a b = 0 ↔ a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [lowerScore]
  | cons x xs ih =>
    cases b with
    | nil => simp at same
    | cons y ys =>
      by_cases eqn : x = y
      · subst y
        simpa [lowerScore] using ih (b := ys) (by simpa using same)
      · by_cases lt : y < x <;> simp [lowerScore,eqn,lt]

private theorem shape_size {a b : List (List Visit)} (rev : Bool)
    (shape : a.map (List.map topology) = b.map (List.map topology)) :
    (unitWord a rev).length = (unitWord b rev).length := by
  have equal := congrArg (fun rows : List (List (Nat × Nat)) => rows.flatten.length) shape
  simpa [unitWord,List.length_flatten,List.map_map,Function.comp_def] using equal

private theorem rowUnits {a b : List Visit} (rev : Bool)
    (same : a.map topology = b.map topology)
    (units : a.map (classAt rev) = b.map (classAt rev)) :
    (a.filter (fun v => 0 < v.children)).map (classAt rev) =
      (b.filter (fun v => 0 < v.children)).map (classAt rev) := by
  induction a generalizing b with
  | nil => cases b <;> simp_all
  | cons x xs ih =>
    cases b with
    | nil => simp at same
    | cons y ys =>
      obtain ⟨top,below⟩ := List.cons.inj same
      obtain ⟨value,cells⟩ := List.cons.inj units
      have degree : x.children = y.children := congrArg Prod.snd top
      by_cases keep : 0 < y.children <;>
        simp [degree,keep,value,ih below cells]

/-- The first sphere is kept in full. On every later sphere the molecular
PairList queue drops the terminal occurrences on both sides in lockstep. -/
private def selected (first : Bool) : List (List Visit) → List Visit
  | [] => []
  | row::rows => (if first then row else row.filter (fun v => 0 < v.children)) ++ selected false rows

private theorem selected_units {a b : List (List Visit)} (rev first : Bool)
    (shape : a.map (List.map topology) = b.map (List.map topology))
    (gate : unitWord a rev = unitWord b rev) :
    (selected first a).map (classAt rev) = (selected first b).map (classAt rev) := by
  induction a generalizing b first with
  | nil => cases b <;> simp_all [selected]
  | cons x xs ih =>
    cases b with
    | nil => simp at shape
    | cons y ys =>
      obtain ⟨this,tail⟩ := List.cons.inj shape
      have size : (x.map (classAt rev)).length = (y.map (classAt rev)).length := by
        simpa using congrArg List.length this
      change x.map (classAt rev) ++ unitWord xs rev = y.map (classAt rev) ++ unitWord ys rev at gate
      obtain ⟨left,right⟩ := List.append_inj gate size
      cases first <;> simp [selected,left,rowUnits rev this left,ih false tail right]

private theorem selected_tail (rows : List (List Visit)) :
    selected false rows = rows.flatMap (fun vs => vs.filter (fun v => 0 < v.children)) := by
  induction rows with
  | nil => rfl
  | cons _ _ ih => simp [selected,ih]

private theorem selected_first (rows : List (List Visit)) : selected true rows = descriptors rows := by
  cases rows <;> simp [selected,descriptors,selected_tail]

/-- The two real gates of the nested comparator force pointwise equality of
the unit classes at every selected PairList position, even for arbitrary
terminal labels and repeated molecular occurrences. -/
theorem projected_units {a b : List (List Visit)} (rev : Bool)
    (shape : a.map (List.map topology) = b.map (List.map topology))
    (gate : lowerScore (unitWord a rev) (unitWord b rev) = 0) :
    (descriptors a).map (fun v => unit (v.label rev)) =
      (descriptors b).map (fun v => unit (v.label rev)) := by
  simpa only [selected_first,classAt] using selected_units rev true shape
    ((zero_iff (shape_size rev shape)).mp gate)

def readings (rev : Bool) (rows : List (List Visit)) :=
  (descriptors rows).map (fun v => upper (v.label rev))

private theorem kept (h : Option LocalizedAuxiliaryLabel) :
    (upper h).isSome = decide (unit h = 2) := by
  rcases h with _ | (_ | _) <;> rfl

/-- This statement retains the gap positions needed by per-ligand Rule 4b,
before Rule 5 compacts the same observations. -/
theorem occupied_mask {a b : List (List Visit)} (rev : Bool)
    (shape : a.map (List.map topology) = b.map (List.map topology))
    (gate : lowerScore (unitWord a rev) (unitWord b rev) = 0) :
    (readings rev a).map Option.isSome = (readings rev b).map Option.isSome := by
  have equal := congrArg (List.map (fun n => decide (n = 2))) (projected_units rev shape gate)
  simpa [readings,List.map_map,Function.comp_def,kept] using equal

private theorem length_by_mask (xs : List (Option RS)) :
    (xs.filterMap id).length = ((xs.map Option.isSome).filter id).length := by
  induction xs with
  | nil => rfl
  | cons h _ ih => cases h <;> simp [ih]

theorem accepted_length {a b : List (List Visit)} (rev : Bool)
    (shape : a.map (List.map topology) = b.map (List.map topology))
    (gate : lowerScore (unitWord a rev) (unitWord b rev) = 0) :
    ((readings rev a).filterMap id).length = ((readings rev b).filterMap id).length := by
  rw [length_by_mask,length_by_mask,occupied_mask rev shape gate]

/-- Neither fixed seed can fail the source comparator's length check after
the nested comparator has reached its stereo stages. -/
theorem fixed_seed_total {a b : List (List Visit)} (rev : Bool) (seed : RS)
    (shape : a.map (List.map topology) = b.map (List.map topology))
    (gate : lowerScore (unitWord a rev) (unitWord b rev) = 0) :
    RingSeededPairs.listSign? seed (readings rev a) (readings rev b) =
      some (RingSeededPairs.compareBits (((readings rev a).filterMap id).map (· == seed))
        (((readings rev b).filterMap id).map (· == seed))) := by
  simp [RingSeededPairs.listSign?,accepted_length rev shape gate]

private theorem local_total {x y : List (Option RS)}
    (size : (x.filterMap id).length = (y.filterMap id).length) :
    (RingSeededPairs.localSign? x y).isSome = true := by
  have starts : (x.findSome? id).isSome = (y.findSome? id).isSome := by
    rw [← List.head?_filterMap,← List.head?_filterMap]
    cases hx : x.filterMap id <;> cases hy : y.filterMap id <;> simp_all
  cases hx : x.findSome? id <;> cases hy : y.findSome? id <;>
    simp [RingSeededPairs.localSign?,hx,hy] at starts ⊢

/-- Every pair of supplied, topologically aligned molecular profiles yields a
signed result in either geometry. Conversely, the topology guard precludes a
result on different profiles. Thus the later PairList gates introduce no
additional incompleteness in the nested comparator. -/
theorem decide_iff {a b : List (List Visit)} (rev : Bool) :
    (decide? a b rev).isSome = true ↔ a.map (List.map topology) = b.map (List.map topology) := by
  by_cases shape : a.map (List.map topology) = b.map (List.map topology)
  · refine iff_of_true ?_ shape
    by_cases gate : lowerScore (unitWord a rev) (unitWord b rev) = 0
    · obtain ⟨v,hv⟩ := Option.isSome_iff_exists.mp (local_total (accepted_length rev shape gate))
      have r := fixed_seed_total rev .R shape gate
      have s := fixed_seed_total rev .S shape gate
      unfold readings at hv r s
      simp [decide?,shape,gate,hv,r,s]
      split_ifs <;> rfl
    · simp [decide?,shape,gate]
  · simp [decide?,shape]

/-- On an actual constitutionally tied edge with two materialized profiles,
the topology test is the exact remaining condition for an issued comparison
on both geometries. -/
theorem edge_iff {i f a b read t xs ys}
    (prior : RingRetainedChemicalTrace.compareAt? i f a b = some t) (tie : cipTraceOutcome t = .eq)
    (left : retainedLevels? i read (2*(i.certified.certified.input.molecule.atomCount+2)+2) [⟨a,some f⟩] = some xs)
    (right : retainedLevels? i read (2*(i.certified.certified.input.molecule.atomCount+2)+2) [⟨b,some f⟩] = some ys) :
    (edge? i f a b read).isSome = true ↔ xs.map (List.map topology) = ys.map (List.map topology) := by
  have ht := Option.attach_eq_some _ ⟨t,prior⟩
  have hl := Option.attach_eq_some _ ⟨xs,left⟩
  have hr := Option.attach_eq_some _ ⟨ys,right⟩
  by_cases shape : xs.map (List.map topology) = ys.map (List.map topology)
  · obtain ⟨actual,ha⟩ := Option.isSome_iff_exists.mp ((decide_iff false).mpr shape)
    obtain ⟨mirror,hm⟩ := Option.isSome_iff_exists.mp ((decide_iff true).mpr shape)
    have va := Option.attach_eq_some _ ⟨actual,ha⟩
    have vm := Option.attach_eq_some _ ⟨mirror,hm⟩
    simp [edge?,ht,hl,hr,va,vm,shape]
    split <;> rfl
  · have no : decide? xs ys false = none := by
      cases h : decide? xs ys false with
      | none => rfl
      | some v => exact False.elim (shape ((decide_iff false).mp (by rw [h]; rfl)))
    have stop : (decide? xs ys false).attach = none := Option.attach_eq_none_iff.mpr no
    simp [edge?,ht,hl,hr,stop,shape]
    split <;> first | rfl | rename_i h; rw [tie] at h; contradiction

open RingRetainedChemicalTrace (Key Stage Column WellFormed Framed)
open RingRetainedChemicalPreorder (orderWord Direction keyFor table compareIn?)

private theorem column_eq {x y : Column} (values : x.word = y.word) (layers : x.levels = y.levels) : x = y := by
  cases x; cases y; cases values; cases layers; rfl

/-- The serialized constitutional words are injective on well-formed keys.
They determine each root observation and all stored rows at every depth. -/
theorem key_eq {a b : Key} (ha : WellFormed a) (hb : WellFormed b) (equal : orderWord a = orderWord b) :
    a = b := by
  have recover (s : Stage) (values : (a.column s).word = (b.column s).word) :
      a.root.atStage s = b.root.atStage s ∧ a.column s = b.column s := by
    have eqn := values
    rw [(ha s).2,(hb s).2] at eqn
    obtain ⟨first,flat⟩ := List.cons.inj eqn
    exact ⟨(List.cons.inj first).1,column_eq values (Framed.unique (ha s).1 (hb s).1 flat)⟩
  obtain ⟨aw,tail⟩ := List.cons.inj equal
  obtain ⟨dw,tail⟩ := List.cons.inj tail
  have mw := (List.cons.inj tail).1
  have atoms := recover .atomic aw
  have duplicates := recover .duplicate dw
  have masses := recover .mass mw
  cases a with
  | mk r a d m =>
    cases b with
    | mk s a' d' m' =>
      have r1 : r.atomic = s.atomic := atoms.1
      have r2 : r.duplicate = s.duplicate := duplicates.1
      have r3 : r.mass = s.mass := masses.1
      have root : r = s := by cases r; cases s; cases r1; cases r2; cases r3; rfl
      have ca : a = a' := atoms.2
      have cd : d = d' := duplicates.2
      have cm : m = m' := masses.2
      rw [root,ca,cd,cm]

/-- At actual molecular incidences, a constitutional tie recovers equality
of both complete keys, including their per-stage parent and sphere framing. -/
theorem table_key_iff {i : LocalizedChemicalRing.Input} {f} (a b : Direction i f) :
    compareIn? (table i f) a b = some .eq ↔ keyFor a = keyFor b := by
  rw [RingRetainedChemicalPreorder.table_tie]
  exact ⟨key_eq (RingRetainedChemicalTrace.key_source (RingRetainedChemicalPreorder.read_key a)).formed
    (RingRetainedChemicalTrace.key_source (RingRetainedChemicalPreorder.read_key b)).formed,congrArg orderWord⟩

end TetraStereo.Engine.RingPairGateCount
assert_kernel_only TetraStereo.Engine.RingPairGateCount.projected_units
assert_kernel_only TetraStereo.Engine.RingPairGateCount.occupied_mask
assert_kernel_only TetraStereo.Engine.RingPairGateCount.accepted_length
assert_kernel_only TetraStereo.Engine.RingPairGateCount.fixed_seed_total
assert_kernel_only TetraStereo.Engine.RingPairGateCount.decide_iff
assert_kernel_only TetraStereo.Engine.RingPairGateCount.edge_iff
assert_kernel_only TetraStereo.Engine.RingPairGateCount.key_eq
assert_kernel_only TetraStereo.Engine.RingPairGateCount.table_key_iff
