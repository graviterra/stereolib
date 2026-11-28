import TetraStereo.Examples.DecalinAuxiliary
import TetraStereo.Examples.DecalinLigandOrder
import TetraStereo.Examples.DecalinAuxiliaryInventory
import TetraStereo.Engine.RingFullPathRule5

/-! Outward walks at either fusion root never turn toward a parent. The
finite molecular history census therefore computes native reference words
for every accepted coordinate realization of the decalin graph. -/
set_option autoImplicit false
namespace TetraStereo.Examples.DecalinRootWords
open Engine OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingGroupedCentre (cursor)
open RingGroupedTrials (atom)
open RingGroupedReport (origin)
open DecalinFrames (molecule)
open DecalinLigandOrder (History expand history graphCheck)
open private graph_rows frame_perm from TetraStereo.Examples.DecalinFrames

private theorem outward_next (a b : Nat) (t : History) :
    DecalinAuxiliary.next (b::t) (a::b::t) = expand (a::b::t) := by
  cases hc : (b::t).contains a with
  | true => simp only [DecalinAuxiliary.next,expand,hc,if_true]
  | false =>
    simp only [DecalinAuxiliary.next,expand,hc,Bool.false_eq_true,if_false]
    change ((molecule.writtenNeighbors a).filter (fun n => some b != some n)).map _ =
      ((molecule.writtenNeighbors a).filter (fun n => n != b)).map _
    have cut (w : Nat) : (some b != some w) = (w != b) := by
      apply Bool.eq_iff_iff.mpr
      simp only [bne_iff_ne,ne_eq,Option.some.injEq]
      exact ne_comm
    simp_rw [cut]
    apply List.map_congr_left
    intro w mem
    obtain ⟨_,off⟩ := List.mem_filter.mp mem
    have ne : b ≠ w := (bne_iff_ne.mp off).symm
    simp [DecalinAuxiliary.advance,ne]

private def Forward {i : Input} (q : Arm i) : Prop :=
  ∃ p : Site i, q.previous? = some p ∧ ∃ a b t,
    DecalinAuxiliary.history p = b::t ∧ history q = a::b::t

private theorem children {i : Input} (graph : i.molecule = molecule) (q : Arm i)
    (valid : i.certified.LocalizedRerootCursorValid q) (fwd : Forward q) :
    ((i.certified.executableLocalizedRerootChildren q).map history).Perm (expand (history q)) ∧
      ∀ c ∈ i.certified.executableLocalizedRerootChildren q, Forward c := by
  obtain ⟨p,prev,a,b,t,hp,hq⟩ := fwd
  have perm := DecalinAuxiliary.child_histories graph q p prev valid
  change ((i.certified.executableLocalizedRerootChildren q).map history).Perm
    (DecalinAuxiliary.next (DecalinAuxiliary.history p) (history q)) at perm
  rw [hp,hq,outward_next,←hq] at perm
  refine ⟨perm,?_⟩
  intro c mem
  have child := perm.mem_iff.mp (List.mem_map_of_mem (f := history) mem)
  rw [hq,expand] at child
  split at child
  · contradiction
  obtain ⟨w,_,eq⟩ := List.mem_map.mp child
  exact ⟨q.occurrence,i.certified.executableLocalizedRerootChildren_previous _ _ mem,
    w,a,b::t,hq,eq.symm⟩

private def bounded : Nat → History → Bool
  | 0,_ => false
  | n+1,p => (expand p).all (bounded n)

private theorem root_depth : ∀ j : Fin 2, ∀ a ∈ DecalinLigandOrder.arms j,
    bounded 12 [a,j.val] = true := by decide +kernel

private theorem checked {i : Input} (graph : i.molecule = molecule)
    (edges : Arm i → List (Arm i)) (correct : ∀ q, edges q = i.certified.executableLocalizedRerootChildren q)
    (n : Nat) (q : Arm i) (valid : i.certified.LocalizedRerootCursorValid q) (fwd : Forward q)
    (bound : bounded n (history q) = true) : graphCheck edges n q = true := by
  induction n generalizing q with
  | zero => contradiction
  | succ n ih =>
    obtain ⟨perm,sub⟩ := children graph q valid fwd
    rw [graphCheck,correct,Bool.and_eq_true_iff]
    refine ⟨decide_eq_true perm,List.all_eq_true.mpr ?_⟩
    intro c mem
    exact ih c (i.certified.localizedRerootChild_valid q c _
      (i.certified.executableLocalizedRerootChildren_declarative q) mem)
      (sub c mem) (List.all_eq_true.mp bound _ (perm.mem_iff.mp (List.mem_map_of_mem mem)))

private theorem start {i : Input} (root : i.certified.Atom)
    (fr : RingNestedActivePair.Frame i (origin i root)) (s : Fin 4) :
    history (cursor fr s) = [atom fr s,root.val] := by
  have present : fr.arm s ∈ i.certified.executableLocalizedRerootChildren
      ⟨origin i root,none⟩ := List.get_mem ..
  obtain ⟨w,atW,h⟩ := DecalinAuxiliary.child_history (a := root) rfl rfl present
  have atId := fr.point_at s
  rw [atW] at atId
  have eq : w.val = atom fr s := Option.some.inj atId
  change DecalinAuxiliary.history (fr.arm s).occurrence = _
  rw [h]
  change DecalinAuxiliary.advance [root.val] w.val = _
  simp [DecalinAuxiliary.advance,eq]

private theorem member {i : Input} (graph : i.molecule = molecule) (root : i.certified.Atom)
    (small : root.val < 2) (fr : RingNestedActivePair.Frame i (origin i root)) (s : Fin 4) :
    atom fr s ∈ DecalinLigandOrder.arms ⟨root.val,small⟩ := by
  have perm := frame_perm fr
  have h := ((i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff _ _).mp fr.recognized).2
  have same : root = fr.center.val := Option.some.inj h
  rw [graph,←same] at perm
  apply (perm.trans (graph_rows ⟨root.val,small⟩)).mem_iff.mp
  exact List.mem_map_of_mem (List.mem_finRange s)

/-- No computational incidence premise: the native molecular arm check holds
for all four slots of either junction, including ring duplicates and hydrogens. -/
theorem root_graphCheck {i : Input} (graph : i.molecule = molecule) (root : i.certified.Atom)
    (small : root.val < 2) (fr : RingNestedActivePair.Frame i (origin i root)) (s : Fin 4)
    (edges : Arm i → List (Arm i)) (correct : ∀ q, edges q = i.certified.executableLocalizedRerootChildren q) :
    graphCheck edges 12 (cursor fr s) = true := by
  have h := start root fr s
  apply checked graph edges correct 12 _ (RingGroupedCentre.valid fr s)
  · exact ⟨origin i root,rfl,atom fr s,root.val,[],rfl,h⟩
  · rw [h]
    exact root_depth ⟨root.val,small⟩ _ (member graph root small fr s)

/-- Only the uppercase observations on descendants remain: native Rule 4b
and fixed-reference Rule 5 read the exact zero- or one-bit arm word. -/
theorem stage_word {i : Input} (graph : i.molecule = molecule) (root : i.certified.Atom)
    (small : root.val < 2) (fr : RingNestedActivePair.Frame i (origin i root)) (s : Fin 4)
    {r : RingNestedActivePair.Reader i} (ready : RingGroupedStereo.Ready (origin i root) r)
    (rev : Bool) (h : RS)
    (seen : ∀ c, DecalinLigandOrder.Descendant (cursor fr s) c →
      RingFullPathPairs.handAt i r rev c = DecalinLigandOrder.frozen ⟨root.val,small⟩ h (history c))
    (os : List RingRetainedStereoRefinement.Observation) (seed : RS) :
    RingFullPathPairs.stageWords i r rev os seed (cursor fr s) =
    some (DecalinLigandOrder.word ⟨root.val,small⟩ h seed
      (DecalinLigandOrder.census root.val (atom fr s))) :=
  DecalinLigandOrder.native_stage_word ready rev _ (RingGroupedCentre.valid fr s) (fr.direction s).property.1
    ⟨root.val,small⟩ _ (member graph root small fr s) h _ (fun _ => rfl) (start root fr s)
    (root_graphCheck graph root small fr s _ (fun _ => rfl)) seen os seed

open RingActiveDistanceSchedule (distance)
open OneCenter.LocalizedGenericMarkedRecalculation (readback?)
open private at_route from TetraStereo.Examples.DecalinAuxiliary
open private history_length from TetraStereo.Examples.DecalinAuxiliaryInventory

private theorem one_longer {p h : History} (mem : h ∈ expand p) : h.length = p.length + 1 := by
  rcases p with _|⟨a,_|⟨b,t⟩⟩ <;> simp only [expand] at mem
  · contradiction
  · contradiction
  split at mem
  · contradiction
  obtain ⟨w,_,rfl⟩ := List.mem_map.mp mem
  rfl

private theorem descends {i : Input} (graph : i.molecule = molecule) (root : i.certified.Atom)
    (fr : RingNestedActivePair.Frame i (origin i root)) (s : Fin 4)
    {c : Arm i} (reach : DecalinLigandOrder.Descendant (cursor fr s) c) :
    i.certified.LocalizedRerootCursorValid c ∧ Forward c ∧ c.occurrence.val.root = root ∧
      2 ≤ (history c).length ∧
      ((history c).length = 2 → history c = [atom fr s,root.val]) := by
  induction reach with
  | root =>
    have h := start root fr s
    exact ⟨RingGroupedCentre.valid fr s,⟨_,rfl,atom fr s,root.val,[],rfl,h⟩,
      (fr.direction s).property.1,by simp [h],fun _ => h⟩
  | @child q c _ mem ih =>
    obtain ⟨valid,fwd,on,len,_⟩ := ih
    have frame := i.certified.executableLocalizedRerootChildren_declarative q
    obtain ⟨perm,sub⟩ := children graph q valid fwd
    have inc := one_longer (perm.mem_iff.mp (List.mem_map_of_mem (f := history) mem))
    exact ⟨i.certified.localizedRerootChild_valid q c _ frame mem,sub c mem,
      (i.certified.localizedRerootChildren_root_eq q c _ frame mem).trans on,by omega,by omega⟩

def publicRead (i : Input) (root : i.certified.Atom) :=
  RingActiveDistanceSchedule.frozen (RingChemicalGraphProof.state i) (origin i root)

private theorem route_bits {i : Input} (graph : i.molecule = molecule)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (root : i.certified.Atom)
    (j : Fin 2) (num : root.val = j.val) (q : Arm i) (on : q.occurrence.val.root = root)
    (t : Fin 2) (route : history q = DecalinAuxiliary.route j t)
    (h : RS) (sense : readback? (RingWrittenPHReadings.geometry i.spatial)
      (DecalinFrames.junctionRow (1-j.val)) = some h) (rev : Bool) :
    RingFullPathPairs.handAt i (publicRead i root) rev q =
      some (if t.val = 0 then (if rev then h.swap else h) else (if rev then h.swap else h).swap) := by
  have len : (DecalinAuxiliary.route j t).length = 6 := by fin_cases j <;> fin_cases t <;> rfl
  have d := history_length q.occurrence
  change (history q).length = distance q.occurrence + 1 at d
  rw [route,len] at d
  have off : q.occurrence.val.node.current? ≠ some root := by
    intro e
    have a := (at_route j t route).2
    have equal := Option.some.inj ((RingAllLigandTwoShell.site_current i q.occurrence).symm.trans e)
    rw [equal,num] at a
    have bound := j.isLt
    omega
  have active : publicRead i root q.occurrence = RingChemicalGraphProof.state i q.occurrence := by
    change (if q.occurrence.val.root ≠ root then _ else if 0 < distance q.occurrence ∧ _ then _ else _) = _
    rw [if_neg (not_not_intro on),if_pos ⟨by omega,off⟩]
  have state := DecalinAuxiliary.public_state graph geom j t route
  rw [sense] at state
  unfold RingFullPathPairs.handAt
  rw [active,state]
  fin_cases t <;> cases rev <;> cases h <;> rfl

private theorem route_list (j : Fin 2) : DecalinAuxiliaryInventory.routes j.val =
    [[1-j.val,j.val],DecalinLigandOrder.firstRoute j,DecalinLigandOrder.secondRoute j] := by
  fin_cases j <;> rfl

private theorem different_routes (j : Fin 2) :
    DecalinLigandOrder.secondRoute j ≠ DecalinLigandOrder.firstRoute j := by fin_cases j <;> decide

private theorem public_hand {i : Input} (graph : i.molecule = molecule)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (root : i.certified.Atom)
    (small : root.val < 2) (fr : RingNestedActivePair.Frame i (origin i root)) (s : Fin 4)
    (away : atom fr s ≠ 1-root.val) (rev : Bool) (h : RS)
    (sense : readback? (RingWrittenPHReadings.geometry i.spatial)
      (DecalinFrames.junctionRow (1-root.val)) = some h)
    {c : Arm i} (reach : DecalinLigandOrder.Descendant (cursor fr s) c) :
    RingFullPathPairs.handAt i (publicRead i root) rev c =
      DecalinLigandOrder.frozen ⟨root.val,small⟩ (if rev then h.swap else h) (history c) := by
  let j : Fin 2 := ⟨root.val,small⟩
  obtain ⟨_,_,on,_,short⟩ := descends graph root fr s reach
  have listEq := route_list j
  have direct : history c ≠ [1-root.val,root.val] := by
    intro eq
    have e := short (by simp [eq])
    rw [eq] at e
    exact away (List.cons.inj e).1.symm
  have different := different_routes j
  by_cases first : history c = DecalinLigandOrder.firstRoute j
  · have r : history c = DecalinAuxiliary.route j 0 := first
    rw [route_bits graph geom root j rfl c on 0 r h sense rev]
    simp [DecalinLigandOrder.frozen,first,j]
  by_cases second : history c = DecalinLigandOrder.secondRoute j
  · have r : history c = DecalinAuxiliary.route j 1 := second
    rw [route_bits graph geom root j rfl c on 1 r h sense rev]
    simp [DecalinLigandOrder.frozen,second,different,j] at *
  have off : history c ∉ DecalinAuxiliaryInventory.routes root.val := by
    change history c ∉ DecalinAuxiliaryInventory.routes j.val
    simp [listEq,direct,first,second,j] at *
  have no : publicRead i root c.occurrence = some none := by
    unfold publicRead
    rw [DecalinAuxiliaryInventory.reader graph geom small _ rfl]
    change (if c.occurrence.val.root ≠ root then _ else if _ then (if history c ∈ _ then _ else _) else _) = _
    rw [if_neg (not_not_intro on),if_neg off]
    split <;> rfl
  simp only [RingFullPathPairs.handAt,no,Option.join_some,Option.map_none,RingNestedActivePair.upper]
  change none = DecalinLigandOrder.frozen j _ _
  simp [DecalinLigandOrder.frozen,first,second]

/-- Every reference stage, including native Rule 4b and Rule 5, on a long
fusion route reads the circularly independent determinant of the opposite
junction. Reflection reverses the auxiliary hand. -/
theorem public_stage_word {i : Input} (graph : i.molecule = molecule)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (root : i.certified.Atom)
    (small : root.val < 2) (fr : RingNestedActivePair.Frame i (origin i root)) (s : Fin 4)
    (away : atom fr s ≠ 1-root.val) (rev : Bool) (h : RS)
    (sense : readback? (RingWrittenPHReadings.geometry i.spatial)
      (DecalinFrames.junctionRow (1-root.val)) = some h)
    (os : List RingRetainedStereoRefinement.Observation) (seed : RS) :
    RingFullPathPairs.stageWords i (publicRead i root) rev os seed (cursor fr s) =
      some (DecalinLigandOrder.word ⟨root.val,small⟩ (if rev then h.swap else h) seed
        (DecalinLigandOrder.census root.val (atom fr s))) :=
  stage_word graph root small fr s (RingChemicalGraphProof.ready geom _) rev _
    (fun _ reach => public_hand graph geom root small fr s away rev h sense reach) os seed

/-- The written neighbor starting each of the two long paths. -/
def routeAtom (j side : Fin 2) :=
  if side.val = 0 then (if j.val = 0 then 2 else 3) else (if j.val = 0 then 6 else 8)

private theorem long_word : ∀ (j side : Fin 2) (h seed : RS),
    DecalinLigandOrder.word j h seed (DecalinLigandOrder.census j.val (routeAtom j side)) =
      [((if side.val = 0 then h else h.swap) == seed)] := by decide +kernel

private theorem away_route : ∀ j side : Fin 2, routeAtom j side ≠ 1-j.val := by decide +kernel

theorem public_long_word {i : Input} (graph : i.molecule = molecule)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (root : i.certified.Atom)
    (small : root.val < 2) (fr : RingNestedActivePair.Frame i (origin i root))
    (s : Fin 4) (side : Fin 2) (id : atom fr s = routeAtom ⟨root.val,small⟩ side)
    (rev : Bool) (h : RS) (sense : readback? (RingWrittenPHReadings.geometry i.spatial)
      (DecalinFrames.junctionRow (1-root.val)) = some h)
    (os : List RingRetainedStereoRefinement.Observation) (seed : RS) :
    RingFullPathPairs.stageWords i (publicRead i root) rev os seed (cursor fr s) =
      some [((if side.val = 0 then (if rev then h.swap else h)
              else (if rev then h.swap else h).swap) == seed)] := by
  have step := public_stage_word graph geom root small fr s
    (id ▸ away_route ⟨root.val,small⟩ side) rev h sense os seed
  rw [id] at step
  exact step.trans (congrArg some (long_word ⟨root.val,small⟩ side _ seed))

/-- Actual native Rule 4b gives both long arms the same best seed word
`[true]`. Actual Rule 5 distinguishes them by a signed magnitude of two.
The opposite junction hand exists by geometry admission; it is never supplied
as a premise here. -/
theorem public_long_pair {i : Input} (graph : i.molecule = molecule)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (root : i.certified.Atom)
    (small : root.val < 2) (fr : RingNestedActivePair.Frame i (origin i root))
    (a b : Fin 4) (left : atom fr a = routeAtom ⟨root.val,small⟩ 0)
    (right : atom fr b = routeAtom ⟨root.val,small⟩ 1) :
    ∃ h : RS, readback? (RingWrittenPHReadings.geometry i.spatial)
      (DecalinFrames.junctionRow (1-root.val)) = some h ∧ ∀ rev : Bool,
      (∀ s ∈ [a,b], (do
        let x ← RingFullPathPairs.pairs? i (publicRead i root) rev .R (cursor fr s)
        let y ← RingFullPathPairs.pairs? i (publicRead i root) rev .S (cursor fr s)
        return max x y) = some [true]) ∧
      RingFullPathRule5.score? i (publicRead i root) rev (cursor fr a) (cursor fr b) =
        some (if (if rev then h.swap else h) = .R then 2 else -2) := by
  obtain ⟨h,sense⟩ := Option.isSome_iff_exists.mp
    (DecalinFrames.junction_nonflat i graph geom ⟨1-root.val,by omega⟩)
  refine ⟨h,sense,?_⟩
  intro rev
  have A := public_long_word graph geom root small fr a 0 left rev h sense
  have B := public_long_word graph geom root small fr b 1 right rev h sense
  constructor
  · intro s mem
    simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl
    · unfold RingFullPathPairs.pairs?
      rw [A [] .R,A [] .S]
      cases rev <;> cases h <;> rfl
    · unfold RingFullPathPairs.pairs?
      rw [B [] .R,B [] .S]
      cases rev <;> cases h <;> rfl
  · unfold RingFullPathRule5.score? RingFullPathRule5.word?
    rw [A _ .R,B _ .R,A _ .S,B _ .S]
    cases rev <;> cases h <;> rfl

end TetraStereo.Examples.DecalinRootWords
assert_kernel_only TetraStereo.Examples.DecalinRootWords.root_graphCheck
assert_kernel_only TetraStereo.Examples.DecalinRootWords.stage_word
assert_kernel_only TetraStereo.Examples.DecalinRootWords.public_stage_word
assert_kernel_only TetraStereo.Examples.DecalinRootWords.public_long_pair
