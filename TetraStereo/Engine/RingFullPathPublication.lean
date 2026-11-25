import TetraStereo.Engine.RingFullPathTrialParity

/-! # Local publication from full-path molecular readings

The original trial hands are counted after cancellation. The parity of the
six ordinary comparisons gives the case. On every reachable frame the
two independent signed majorities recover exactly the same label pair. -/
set_option autoImplicit false

namespace TetraStereo.Engine.RingFullPathPublication
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingNestedActivePair (Frame Reader Labels consistent)
open RingActivePairReport (Slot)
open RingActiveDistanceSchedule (View Cell Visible frozen distance height)
open RingFullPathEligibility (Key Reads key?)
open RingFullPathTrialReadings (trialKey trials MarkWords Outcome readings?)
open RingGroupedCentre (cursor)
open LocalizedChemicalRingPromotionAggregation (readingBalance)
open RingChemicalPriority.ReferenceFrame (survivingHand)

/-! ## Policy -/

abbrev reversals := RingFullPathTrialParity.reversals

/-- Signed balance of the actual hands gives the letter. An even number of
pair reversals gives opposite letters in the two geometries. -/
def letters (ks ms : Slot → Key) (hands : List (Option RS)) : Option Labels :=
  (survivingHand (readingBalance hands)).map fun h =>
    let k := if reversals ks ms % 2 = 0 then h.swap else h
    (RingNestedActivePair.label h k,RingNestedActivePair.label k h)

/-- The pair is a mirror-consistent publication for every parity. -/
theorem letters_consistent (ks ms : Slot → Key) (hands : List (Option RS)) :
    (letters ks ms hands).all consistent = true := by
  unfold letters
  cases survivingHand (readingBalance hands) with
  | none => rfl
  | some h =>
    by_cases even : reversals ks ms % 2 = 0 <;> cases h <;>
      simp [even,RingNestedActivePair.label,consistent,RS.swap,pseudoRSOfRS]

/-! ## Executable rule -/

def keys? {i f} (fr : @Frame i f) (r : Reader i) (rev : Bool) : Option (Slot → Key) :=
  RingActivePairReport.four? fun k => key? i r rev (cursor fr k)

def centre? {i f} (fr : @Frame i f) (r : Reader i) : Cell :=
  (keys? fr r false).bind fun ks => (keys? fr r true).bind fun ms =>
    (readings? fr r false).map fun out => letters ks ms (out.map Prod.snd)

private def centreWithKeys {i f} (fr : @Frame i f) (r : Reader i) : Cell := do
  let ks ← keys? fr r false
  let ms ← keys? fr r true
  let out ← RingFullPathTrialReadings.readingsWith fr r false ks
  return letters ks ms (out.map Prod.snd)

@[csimp] private theorem centreWithKeys_exact : @centre? = @centreWithKeys := by
  funext i f fr r
  unfold centre? centreWithKeys readings?
  change _ = (keys? fr r false).bind _
  change (keys? fr r false).bind (fun ks => (keys? fr r true).bind (fun ms =>
    ((keys? fr r false).bind (RingFullPathTrialReadings.readingsWith fr r false)).map
      (fun out => letters ks ms (out.map Prod.snd)))) = _
  cases keys? fr r false <;> cases keys? fr r true <;> simp
  all_goals cases RingFullPathTrialReadings.readingsWith fr r false _ <;> rfl

/-- A site without a recognized four-coordinate frame is a completed absence. -/
def publish? (i : Input) (f : Site i) (r : Reader i) : Cell :=
  match RingNestedActivePair.frame? i f with
  | none => some none
  | some fr => centre? fr r

private theorem publish_none {i f} {r : Reader i} (hf : RingNestedActivePair.frame? i f = none) :
    publish? i f r = some none := by simp [publish?,hf]

private theorem publish_some {i f} {r : Reader i} {fr : Frame i f}
    (hf : RingNestedActivePair.frame? i f = some fr) : publish? i f r = centre? fr r := by
  simp [publish?,hf]

theorem issued {i f} {r : Reader i} {v} (got : publish? i f r = some v) :
    v = none ∨ ∃ (_ : Frame i f) (ks ms : Slot → Key) (hands : List (Option RS)), v = letters ks ms hands := by
  cases hf : RingNestedActivePair.frame? i f with
  | none =>
    rw [publish_none hf] at got
    exact .inl (Option.some.inj got).symm
  | some fr =>
    rw [publish_some hf] at got
    unfold centre? at got
    obtain ⟨ks,_,got⟩ := Option.bind_eq_some_iff.mp got
    obtain ⟨ms,_,got⟩ := Option.bind_eq_some_iff.mp got
    obtain ⟨out,_,got⟩ := Option.map_eq_some_iff.mp got
    exact .inr ⟨fr,ks,ms,_,got.symm⟩

theorem issued_consistent {i f} {r : Reader i} {v} (got : publish? i f r = some v) :
    v.all consistent = true := by
  rcases issued got with rfl | ⟨_,ks,ms,hands,rfl⟩
  · rfl
  · exact letters_consistent ks ms hands

theorem issued_four {i f} {r : Reader i} {v} (got : publish? i f r = some (some v)) :
    (RingRetainedAuxiliary.frame i.certified f).length = 4 := by
  rcases issued got with no | ⟨fr,_⟩
  · exact nomatch no
  · exact fr.four

/-! ## Independent source relation -/

/-- A structural noncentre is absent. At a centre, any molecular readings of
the eight ordinary keys, any admissible mark words and any legal coordinate
reading of every trial in the complete list determine the publication. -/
inductive Source (i : Input) (f : Site i) (r : Reader i) : Option Labels → Prop where
  | absent (unrecognized : i.certified.localizedOccurrenceDescriptorCenter? f = none) : Source i f r none
  | centre (fr : Frame i f) (ks ms : Slot → Key)
      (actual : ∀ k, Reads i r false (cursor fr k) (ks k))
      (mirrored : ∀ k, Reads i r true (cursor fr k) (ms k))
      (hands : List (Option RS))
      (complete : List.Forall₂ (fun s v => ∃ ws, MarkWords fr r false s ws ∧
        Outcome fr false (fun k => trialKey (ks k) (ws k)) v) (trials ks) hands) :
      Source i f r (letters ks ms hands)

private theorem frame_unique {i f} (a b : Frame i f) : a = b := by
  obtain ⟨c,rc,_,ids,read,_⟩ := a
  obtain ⟨c',rc',_,ids',read',_⟩ := b
  obtain rfl := Option.some.inj (rc.symm.trans rc')
  obtain rfl := Option.some.inj (read.symm.trans read')
  rfl

private theorem keys_exact {i f} {r : Reader i} (fr : @Frame i f) (ready : RingGroupedStereo.Ready f r)
    (rev : Bool) : ∃ ks, keys? fr r rev = some ks ∧
      ∀ other : Slot → Key, (∀ k, Reads i r rev (cursor fr k) (other k)) ↔ other = ks := by
  have each (s : Slot) := RingFullPathEligibility.key_exact ready rev (cursor fr s)
    (RingGroupedCentre.valid fr s) (fr.direction s).property.1
  choose ks computed exactKey using each
  obtain ⟨keys,row⟩ := Option.isSome_iff_exists.mp
    (RingActivePairReport.four_full _ (fun s => Option.isSome_iff_exists.mpr ⟨ks s,computed s⟩))
  have same : keys = ks := funext fun s => Option.some.inj
    ((RingActivePairReport.four_at row s).symm.trans (computed s))
  subst keys
  refine ⟨ks,row,fun other => ⟨fun legal => funext fun s => (exactKey s _).mp (legal s),?_⟩⟩
  rintro rfl s
  exact (exactKey s _).mpr rfl

private theorem column {α β : Type} {P : α → β → Prop} (out : List (α × β)) (hands : List β)
    (rel : List.Forall₂ P (out.map Prod.fst) hands)
    (only : ∀ s v, (s,v) ∈ out → ∀ w, P s w → w = v) : hands = out.map Prod.snd := by
  induction out generalizing hands with
  | nil =>
    rw [List.map_nil] at rel
    cases rel
    rfl
  | cons x xs ih =>
    obtain ⟨s,v⟩ := x
    rw [List.map_cons] at rel
    cases rel with
    | cons head tail =>
      exact congrArg₂ List.cons (only s v (List.mem_cons.mpr (Or.inl rfl)) _ head)
        (ih _ tail fun a b mem => only a b (List.mem_cons_of_mem _ mem))

private theorem rows {α β : Type} {P : α → β → Prop} (out : List (α × β))
    (all : ∀ s v, (s,v) ∈ out → P s v) : List.Forall₂ P (out.map Prod.fst) (out.map Prod.snd) := by
  induction out with
  | nil => exact .nil
  | cons x xs ih =>
    obtain ⟨s,v⟩ := x
    show List.Forall₂ P (s :: xs.map Prod.fst) (v :: xs.map Prod.snd)
    exact .cons (all s v (List.mem_cons.mpr (Or.inl rfl)))
      (ih fun a b mem => all a b (List.mem_cons_of_mem _ mem))

/-- On every ready reader the rule is total, and its value is the unique
result admitted by the source relation. -/
theorem source_exact {i f} {r : Reader i} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (ready : RingGroupedStereo.Ready f r) :
    ∃ v, publish? i f r = some v ∧ ∀ w, Source i f r w ↔ w = v := by
  cases hf : RingNestedActivePair.frame? i f with
  | none =>
    have no : i.certified.localizedOccurrenceDescriptorCenter? f = none := by
      cases recog : i.certified.localizedOccurrenceDescriptorCenter? f with
      | none => rfl
      | some c =>
        obtain ⟨fr,ok⟩ := RingGroupedGeometry.frame_exists recog
        exact nomatch hf.symm.trans ok
    refine ⟨none,publish_none hf,fun w => ⟨fun src => ?_,?_⟩⟩
    · cases src with
      | absent => rfl
      | centre fr _ _ _ _ _ _ => exact nomatch no.symm.trans fr.recognized
    · rintro rfl
      exact .absent no
  | some fr =>
    obtain ⟨ks,hk,onlyK⟩ := keys_exact fr ready false
    obtain ⟨ms,hm,onlyM⟩ := keys_exact fr ready true
    obtain ⟨ks',out,hout,slots,reads,sound⟩ := RingFullPathTrialReadings.ready_readings geom fr ready false
    have sameKeys : ks' = ks := (onlyK ks').mp reads
    subst ks'
    refine ⟨letters ks ms (out.map Prod.snd),by simp [publish_some hf,centre?,hk,hm,hout],
      fun w => ⟨fun src => ?_,?_⟩⟩
    · cases src with
      | absent no => exact nomatch no.symm.trans fr.recognized
      | centre fr' ks₂ ms₂ actual mirrored hands complete =>
        obtain rfl := frame_unique fr' fr
        obtain rfl := (onlyK ks₂).mp actual
        obtain rfl := (onlyM ms₂).mp mirrored
        rw [← slots] at complete
        have same : hands = out.map Prod.snd := by
          refine column out hands complete ?_
          rintro s v mem w ⟨ws,marks,seen⟩
          exact ((RingFullPathTrialReadings.read_exact geom _ false _ _).mp seen).trans
            ((RingFullPathTrialReadings.read_exact geom _ false _ _).mp
              (sound s v mem _ ws actual marks)).symm
        rw [same]
    · rintro rfl
      refine .centre fr ks ms reads ((onlyM ms).mpr rfl) (out.map Prod.snd) ?_
      rw [← slots]
      refine rows out fun s v mem => ?_
      obtain ⟨ws,_,onlyW⟩ := RingFullPathTrialReadings.mark_exact fr ready false s
      exact ⟨ws,(onlyW ws).mpr rfl,sound s v mem ks ws reads ((onlyW ws).mpr rfl)⟩

/-! ## Distance recurrence -/

def state (i : Input) : View i := RingActiveDistanceSchedule.evaluate (publish? i)

theorem state_eq (i : Input) (q : Site i) : state i q = publish? i q (frozen (state i) q) :=
  RingActiveDistanceSchedule.evaluate_eq (publish? i) q

theorem unique_state {i : Input} (s : View i) (laws : ∀ q, s q = publish? i q (frozen s q)) :
    s = state i := RingActiveDistanceSchedule.unique _ s laws

private theorem observed {i : Input} {q : Site i}
    (known : ∀ t, Visible q t → (state i t).isSome = true) :
    RingGroupedStereo.Ready q (frozen (state i) q) := by
  intro t on
  by_cases visible : Visible q t.occurrence
  · obtain ⟨v,hv⟩ := Option.isSome_iff_exists.mp (known t.occurrence visible)
    have got := (state_eq i t.occurrence).symm.trans hv
    refine ⟨v,by simp [frozen,on,visible.2.1,visible.2.2,hv],issued_consistent got,?_⟩
    intro empty
    cases v with
    | none => rfl
    | some labels =>
      have four := issued_four got
      have size := RingFrontierProfileShape.cut_frame t
      change i.certified.executableLocalizedRerootChildren t = [] at empty
      rw [four,empty] at size
      contradiction
  · have masked : ¬(distance q < distance t.occurrence ∧ t.occurrence.val.node.current? ≠ some q.val.root) :=
      fun h => visible ⟨on,h⟩
    exact ⟨none,by simp [frozen,on,masked],rfl,fun _ => rfl⟩

/-- Every site of the schedule of this rule is resolved, by induction from
the greatest distance toward the root. -/
theorem complete {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (q : Site i) :
    (state i q).isSome = true := by
  suffices ∀ n (t : Site i), height i - distance t = n → (state i t).isSome = true from this _ q rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro t depth
    have ready := observed (q := t) (fun s vis => by
      have upper := RingActiveDistanceSchedule.distance_bound s
      have deeper := vis.2.1
      exact ih _ (by omega) s rfl)
    obtain ⟨v,hv,_⟩ := source_exact geom ready
    exact Option.isSome_iff_exists.mpr ⟨v,(state_eq i t).trans hv⟩

/-- Every frozen store reached by this rule is a ready reader. -/
theorem ready {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (q : Site i) :
    RingGroupedStereo.Ready q (frozen (state i) q) :=
  observed (fun s _ => complete geom s)

/-- The scheduled value at every site is exactly the result of the source
relation on the frozen store of that site. -/
theorem state_source {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (q : Site i) (v : Option Labels) :
    state i q = some v ↔ Source i q (frozen (state i) q) v := by
  obtain ⟨w,hw,only⟩ := source_exact geom (ready geom q)
  have eqn := (state_eq i q).trans hw
  exact ⟨fun h => (only v).mpr (Option.some.inj (h.symm.trans eqn)),
    fun h => eqn.trans (congrArg some ((only v).mp h).symm)⟩

/-- The source reads both physical configurations separately and cancels
opposite votes within each. -/
def crossed (hs ms : List (Option RS)) : Option Labels := do
  let h ← survivingHand (readingBalance hs)
  let m ← survivingHand (readingBalance ms)
  return (RingNestedActivePair.label h m,RingNestedActivePair.label m h)

def Ballots {i f} (fr : @Frame i f) (r : Reader i) (rev : Bool) (ks : Slot → Key)
    (hands : List (Option RS)) : Prop :=
  (∀ j, Reads i r rev (cursor fr j) (ks j)) ∧
    List.Forall₂ (fun s v => ∃ ws, MarkWords fr r rev s ws ∧
      Outcome fr rev (fun j => trialKey (ks j) (ws j)) v) (trials ks) hands

private theorem ballots_exact {i f r} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (fr : @Frame i f) (ready : RingGroupedStereo.Ready f r) (rev : Bool) :
    ∃ ks out, keys? fr r rev = some ks ∧ readings? fr r rev = some out ∧
      ∀ k hs, Ballots fr r rev k hs ↔ k = ks ∧ hs = out.map Prod.snd := by
  obtain ⟨ks,hk,only⟩ := keys_exact fr ready rev
  obtain ⟨k,out,ho,slots,reads,each⟩ := RingFullPathTrialReadings.ready_readings geom fr ready rev
  obtain rfl := (only k).mp reads
  refine ⟨_,out,hk,ho,?_⟩
  intro k hs
  constructor
  · rintro ⟨rd,all⟩
    obtain rfl := (only k).mp rd
    rw [← slots] at all
    refine ⟨rfl,column _ _ all ?_⟩
    rintro s v mem w ⟨ws,hm,hw⟩
    exact ((RingFullPathTrialReadings.read_exact geom fr rev _ _).mp hw).trans
      ((RingFullPathTrialReadings.read_exact geom fr rev _ _).mp (each s v mem _ ws rd hm)).symm
  · rintro ⟨rfl,rfl⟩
    refine ⟨reads,?_⟩
    rw [← slots]
    refine rows out fun s v mem => ?_
    obtain ⟨ws,_,legal⟩ := RingFullPathTrialReadings.mark_exact fr ready rev s
    exact ⟨ws,(legal _).mpr rfl,each s v mem _ ws reads ((legal _).mpr rfl)⟩

/-- Independent local specification. The source chooses all lawful trials
on each geometry and reads the two surviving hands directly. -/
inductive TwoGeometry (i : Input) (q : Site i) (r : Reader i) : Option Labels → Prop where
  | absent (no : i.certified.localizedOccurrenceDescriptorCenter? q = none) : TwoGeometry i q r none
  | centre {fr : Frame i q} {x y actual reflected}
      (a : Ballots fr r false x actual) (b : Ballots fr r true y reflected) :
      TwoGeometry i q r (crossed actual reflected)

private theorem letters_crossed {i f} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (fr : @Frame i f) (view : View i) (good : RingGroupedStereo.Ready f (frozen view f))
    {x y : Slot → Key} {as' bs : List (Option Slot × Option RS)} (a : Ballots fr (frozen view f) false x (as'.map Prod.snd))
    (b : Ballots fr (frozen view f) true y (bs.map Prod.snd))
    (left : readings? fr (frozen view f) false = some as')
    (right : readings? fr (frozen view f) true = some bs) :
    letters x y (as'.map Prod.snd) = crossed (as'.map Prod.snd) (bs.map Prod.snd) := by
  have law := (RingFullPathTrialParity.view_aggregates geom fr view good a.1 b.1 left right).1
  unfold letters crossed
  rw [law]
  by_cases even : reversals x y % 2 = 0 <;>
    cases h : survivingHand (readingBalance (as'.map Prod.snd)) <;>
    simp [even,RingChemicalPriority.ReferenceFrame.survivingHand_neg,h,reversals] at *

/-- The actual-only majority/parity computation and two independently
derived molecular majorities give identical letters, including refusals. -/
theorem two_geometry_iff {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (q : Site i) (view : View i) (good : RingGroupedStereo.Ready q (frozen view q)) (v : Option Labels) :
    publish? i q (frozen view q) = some v ↔ TwoGeometry i q (frozen view q) v := by
  let r := frozen view q
  cases hf : RingNestedActivePair.frame? i q with
  | none =>
    have no : i.certified.localizedOccurrenceDescriptorCenter? q = none := by
      cases recog : i.certified.localizedOccurrenceDescriptorCenter? q with
      | none => rfl
      | some c =>
        obtain ⟨_,h⟩ := RingGroupedGeometry.frame_exists recog
        exact nomatch hf.symm.trans h
    rw [publish_none hf]
    constructor
    · intro h
      obtain rfl := Option.some.inj h
      exact .absent no
    · intro deriv
      cases deriv with
      | absent => rfl
      | @centre fr _ _ _ _ _ _ => exact nomatch no.symm.trans fr.recognized
  | some fr =>
    obtain ⟨x,as',kx,ax,ex⟩ := ballots_exact geom fr good false
    obtain ⟨y,bs,ky,ay,ey⟩ := ballots_exact geom fr good true
    have a := (ex _ _).mpr ⟨rfl,rfl⟩
    have b := (ey _ _).mpr ⟨rfl,rfl⟩
    have law := letters_crossed geom fr view good a b ax ay
    rw [publish_some hf]
    simp only [centre?,kx,ky,ax,Option.bind_some,Option.map_some,Option.some.injEq,law]
    constructor
    · rintro rfl
      exact .centre a b
    · intro deriv
      cases deriv with
      | absent no => exact nomatch no.symm.trans fr.recognized
      | @centre fr' u w hs ms l m =>
        obtain rfl := frame_unique fr' fr
        obtain ⟨_,rfl⟩ := (ex _ _).mp l
        obtain ⟨_,rfl⟩ := (ey _ _).mp m
        rfl

/-- A complete derivation supplies all visible auxiliary assignments
recursively. Its definition makes no reference to the publication table. -/
inductive Molecular (i : Input) : Site i → Option Labels → Prop where
  | step {q v} (before : View i) (localRead : TwoGeometry i q (frozen before q) v)
      (covered : ∀ t, Visible q t → (before t).isSome = true)
      (deeper : ∀ t, Visible q t → ∀ w, before t = some w → Molecular i t w) : Molecular i q v

theorem molecular_iff {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (q : Site i) (v : Option Labels) : state i q = some v ↔ Molecular i q v := by
  constructor
  · suffices ∀ n (t : Site i), height i - distance t = n → ∀ w, state i t = some w → Molecular i t w from
      this _ q rfl v
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro t hn w got
      refine .step (state i) ((two_geometry_iff geom t _ (ready geom t) _).mp ((state_eq i t).symm.trans got))
        (fun s _ => complete geom s) ?_
      intro s vis z hz
      have upper := RingActiveDistanceSchedule.distance_bound s
      have deeper := vis.2.1
      exact ih _ (by omega) s rfl z hz
  · intro deriv
    induction deriv with
    | @step t w before loc covered _ ih =>
      have same : frozen before t = frozen (state i) t := by
        funext s
        unfold frozen
        split_ifs with off allowed
        · rfl
        · have vis : Visible t s := ⟨of_not_not off,allowed⟩
          obtain ⟨u,hu⟩ := Option.isSome_iff_exists.mp (covered s vis)
          exact hu.trans (ih s vis u hu).symm
        · rfl
      rw [same] at loc
      exact (state_eq i t).trans ((two_geometry_iff geom t _ (ready geom t) w).mpr loc)

/-- Read all comparison scores and promotion trials on the evaluator's own
reachable frozen frame. The four ligand keys and both ballot populations are
uniquely determined by the chemical source judgments. -/
theorem reachable_frame {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {f : Site i} (fr : Frame i f) :
    let r := frozen (state i) f
    ∃ (x y : Slot → Key) (xs ys : List (Option Slot × Option RS)),
      keys? fr r false = some x ∧ keys? fr r true = some y ∧
      readings? fr r false = some xs ∧ readings? fr r true = some ys ∧
      (∀ k hs, Ballots fr r false k hs ↔ k = x ∧ hs = xs.map Prod.snd) ∧
      (∀ k hs, Ballots fr r true k hs ↔ k = y ∧ hs = ys.map Prod.snd) ∧
      xs.map Prod.fst = trials x ∧ ys.map Prod.fst = trials x ∧
      (∀ j k, let cr := compare (x j).fixedR (x k).fixedR
              let cs := compare (y j).fixedR (y k).fixedR
              RingFullPathRule5.score? i r false (cursor fr j) (cursor fr k) = some (RingOccurrenceStereo.fixedScore cr cs) ∧
              RingFullPathRule5.score? i r true (cursor fr j) (cursor fr k) = some (RingOccurrenceStereo.fixedScore cs cr)) ∧
      state i f = some (crossed (xs.map Prod.snd) (ys.map Prod.snd)) := by
  intro r
  have good := ready geom f
  obtain ⟨x,xs,hx,ax,ex⟩ := ballots_exact geom fr good false
  obtain ⟨y,ys,hy,ay,ey⟩ := ballots_exact geom fr good true
  have a := (ex _ _).mpr ⟨rfl,rfl⟩
  have b := (ey _ _).mpr ⟨rfl,rfl⟩
  obtain ⟨k,out,got,marks,rd,_⟩ := RingFullPathTrialReadings.ready_readings geom fr good false
  obtain rfl := Option.some.inj (got.symm.trans ax)
  obtain ⟨u,_,only⟩ := keys_exact fr good false
  have same := ((only k).mp rd).trans ((only x).mp a.1).symm
  rw [same] at marks
  have paired := (RingFullPathTrialParity.view_hands geom fr _ good a.1 b.1 ax ay).1
  exact ⟨x,y,_,_,hx,hy,ax,ay,ex,ey,marks,paired.symm.trans marks,
    fun j k => RingFullPathTrialParity.fixed_scores_of_readings fr _ good x y j k a.1 b.1,
    (state_eq i f).trans ((two_geometry_iff geom f _ good _).mpr (.centre a b))⟩

/-- Hanson's four-list contest on the corrected evaluator's own frozen
state. Each ligand's best word is determined by any legal molecular reading.
The contest is available for every pair; it decides only after earlier ties. -/
theorem reachable_fourB {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {f : Site i} (fr : Frame i f) (rev : Bool) (j k : Slot) {x y : Key} :
    let r := frozen (state i) f
    Reads i r rev (cursor fr j) x → Reads i r rev (cursor fr k) y →
    RingFullPathPairs.hanson? i r rev (cursor fr j) (cursor fr k) =
      some (RingSingleTieCompletion.unitScore (compare x.bestFourB y.bestFourB)) := by
  intro r left right
  obtain ⟨_,_,ar,as',_,_,_,har,has,_,rfl⟩ := left
  obtain ⟨_,_,br,bs,_,_,_,hbr,hbs,_,rfl⟩ := right
  have word (slot : Slot) (seed : RS) (w : List Bool)
      (source : RingFullPathPairs.FullSource i r rev seed (cursor fr slot) w) :
      RingFullPathPairs.pairs? i r rev seed (cursor fr slot) = some w := by
    obtain ⟨u,hu,only⟩ := RingFullPathPairs.source_exact (ready geom f) rev seed _
      (RingGroupedCentre.valid fr slot) (fr.direction slot).property.1
    exact hu.trans (congrArg some ((only w).mp source).symm)
  unfold RingFullPathPairs.hanson?
  rw [word j .R _ har,word j .S _ has,word k .R _ hbr,word k .S _ hbs]
  simp only [Option.bind_eq_bind,Option.bind_some,Option.pure_def,RingOccurrenceStereo.fourLists_order]
  cases compare (max ar as') (max br bs) <;> rfl

end TetraStereo.Engine.RingFullPathPublication
assert_kernel_only TetraStereo.Engine.RingFullPathPublication.letters_consistent
assert_kernel_only TetraStereo.Engine.RingFullPathPublication.source_exact
assert_kernel_only TetraStereo.Engine.RingFullPathPublication.complete
assert_kernel_only TetraStereo.Engine.RingFullPathPublication.ready
assert_kernel_only TetraStereo.Engine.RingFullPathPublication.state_source
assert_kernel_only TetraStereo.Engine.RingFullPathPublication.molecular_iff
assert_kernel_only TetraStereo.Engine.RingFullPathPublication.reachable_frame
assert_kernel_only TetraStereo.Engine.RingFullPathPublication.reachable_fourB
