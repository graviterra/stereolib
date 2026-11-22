import TetraStereo.Engine.RingSeedEqualityTransport

set_option autoImplicit false

namespace TetraStereo.Engine.RingRetainedSeedFrames
open OneCenter CertifiedLocalizedCIPInput RingStereoSiblingPass
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader)
open RingRetainedStereoDecision (ArmProfile Reads)
open RingRetainedStereoRefinement (Derives Observation)
open RingRetainedChemicalTrace (Word Framed)

private abbrev children (i : Input) (q : Arm i) := i.certified.executableLocalizedRerootChildren q

/-- A molecular cursor and all the stereochemical readings needed to rerank
its children under either fixed reference. -/
structure State (i : Input) (read : Reader i) (rev : Bool) where
  q : Arm i
  valid : i.certified.LocalizedRerootCursorValid q
  profile : ArmProfile
  source : Reads i read rev q profile

private abbrev S {i : Input} (read : Reader i) (rev : Bool) := State i read rev

def Native {i read rev} (a : State i read rev) (xs : List (S read rev)) := xs.map State.q = children i a.q

def Shallow {α : Type} (key : α → Branch) := fun x => (key x).shallow
def Deep {α : Type} (key : α → Branch) := fun x => (key x).deep

private theorem framed {i read rev q b} : ∀ stages, Derives i read rev stages q b → Framed 2 b.levels
  | [],h => RingRetainedUnitPass.Reading.framed h
  | _::_,h => RingRetainedStereoRefinement.Pass.framed h

/-- The native list of states contains the exact branch readings of the
corresponding molecular row, in the original child order. -/
private theorem native_eq {i read rev stages} {a : State i read rev} {xs : List (S read rev)} (nat : Native a xs)
    (key : S read rev → Branch) (src : ∀ t, Derives i read rev stages t.q (key t)) {p sh de}
    (row : RingRetainedStereoRefinement.Row i read rev stages a.q p sh de) :
    xs.map key = row.native := by
  have pairs := TerminalTie.mapM_forall₂ _ _ _ row.complete
  change xs.map State.q = _ at nat
  change List.Forall₂ (fun x y => row.lookup x = some y) (children i a.q) row.native at pairs
  rw [← nat] at pairs
  apply List.ext_getElem
  · simpa using pairs.length_eq
  · intro j h k
    have hj : j < xs.length := by simpa using h
    have eqn := pairs.get (i := j) (by simpa using hj) k
    simp only [List.get_eq_getElem,List.getElem_map] at eqn ⊢
    have hc : xs[j].q ∈ children i a.q := nat ▸ List.mem_map_of_mem (List.getElem_mem hj)
    exact RingRetainedStereoRefinement.unique stages _ _ _ (src xs[j]) (row.derived _ hc eqn)

private theorem mapLegal {α : Type} {κ : Type} [LinearOrder κ] {key : Branch → κ} {f : α → Branch} {xs sh : List α}
    (l : Legal (fun x => key (f x)) xs sh) : Legal key (xs.map f) (sh.map f) :=
  ⟨l.perm.map f,by simpa only [List.map_map] using l.descending⟩

theorem layout {i read rev stages} {a : State i read rev} {xs sh de : List (S read rev)}
    (nat : Native a xs) (key : S read rev → Branch) (src : ∀ t, Derives i read rev stages t.q (key t))
    (first : Legal (Shallow key) xs sh) (second : Legal (Deep key) xs de) :
    (key a).levels = rows (sh.map key) (de.map key) := by
  obtain ⟨original,ordered,⟨row⟩⟩ := RingRetainedStereoRefinement.decomposition (src a)
  have eqn := native_eq nat key src row
  rw [row.layout]
  apply rows_unique row.shallow row.deep (eqn ▸ mapLegal first) (eqn ▸ mapLegal second)
  intro b hb
  rw [← eqn] at hb
  obtain ⟨t,_,rfl⟩ := List.mem_map.mp hb
  exact framed stages (src t)

abbrev unit {i read rev} (t : State i read rev) := t.profile.unit
abbrev lower {i read rev} (t : State i read rev) := t.profile.lower
abbrev fixed {i read rev} (s : RS) (t : State i read rev) := t.profile.fixedPair s
abbrev localP {i read rev} (s : RS) (t : State i read rev) := t.profile.localPair s

private theorem previous_keys {i read rev o os q p b} (pre : Derives i read rev os q p)
    (step : Derives i read rev (o::os) q b) : b.priorHead = p.shallow ∧ b.priorDeep = p.deep := by
  cases step with
  | node was _ _ _ _ _ _ =>
    obtain rfl := RingRetainedStereoRefinement.unique os _ _ _ was pre
    exact ⟨rfl,rfl⟩

theorem sizes {i read rev} : ∀ os q b, Derives i read rev os q b →
    b.shallow.length = 4 + os.length ∧ b.deep.length = 4 + os.length
  | [],q,b,r => by
    change RingRetainedUnitPass.Reading _ _ _ q b at r
    cases r with | node _ _ _ _ _ _ _ _ => exact ⟨rfl,rfl⟩
  | o::os,_,_,r => by
    cases r with
    | node pre _ _ _ _ _ _ =>
      obtain ⟨l,h⟩ := sizes os _ _ pre
      simp [RingRetainedStereoRefinement.extend,Branch.shallow,Branch.deep] at l h ⊢
      omega

/-- Removing the last observation from a legal order leaves a legal order for
the preceding pass. The fixed prefix width is proved by molecular derivation. -/
theorem earlier_order {i read rev o os} (prev cur : S (i := i) read rev → Branch)
    (pre : ∀ t, Derives i read rev os t.q (prev t))
    (now : ∀ t, Derives i read rev (o::os) t.q (cur t)) {xs sh de}
    (first : Legal (Shallow cur) xs sh) (second : Legal (Deep cur) xs de) :
    Legal (Shallow prev) xs sh ∧ Legal (Deep prev) xs de := by
  have preserved {α : Type} [LinearOrder α] (before after : S read rev → List α)
      (h : ∀ x, (after x).take (4 + os.length) = before x) {a b} (p : Legal after a b) : Legal before a b :=
    ⟨p.perm,List.pairwise_map.mpr ((List.pairwise_map.mp p.descending).imp fun {x y} xy => by
      simpa only [h] using RingChildKeyRecovery.take_le xy (4+os.length))⟩
  constructor
  · apply preserved _ _ _ first
    intro t
    have k := (previous_keys (pre t) (now t)).1
    have len := (sizes os _ _ (pre t)).1
    simp only [Shallow,Branch.shallow,k,← len,List.take_left]
  · apply preserved _ _ _ second
    intro t
    have k := (previous_keys (pre t) (now t)).2
    have len := (sizes os _ _ (pre t)).2
    simp only [Deep,Branch.deep,k,← len,List.take_left]

private theorem splitKeys {x y : Branch} (eqn : x.deep = y.deep) :
    x.priorDeep = y.priorDeep ∧ x.word = y.word := by
  exact ⟨by simpa [Branch.deep] using congrArg List.dropLast eqn,
    by simpa [Branch.deep] using congrArg List.getLast? eqn⟩

private theorem branch_eq {x y : Branch} (deep : x.deep = y.deep) (head : x.priorHead = y.priorHead)
    (a : Framed 2 x.levels) (b : Framed 2 y.levels) : x = y := by
  obtain ⟨before,word⟩ := splitKeys deep
  have parts := List.cons.inj word
  have levels := Framed.unique a b parts.2
  obtain ⟨h,t⟩ := List.cons.inj parts.1
  cases x; cases y; simp_all

private theorem constitution {i read rev} (a : State i read rev) :
    ∃ k, RingRetainedChemicalTrace.key? i a.q = some k ∧
      (unit a).priorDeep = RingRetainedChemicalPreorder.orderWord k ∧
      (unit a).priorHead = [k.root.atomic,k.root.duplicate,k.root.mass] := by
  have r : RingRetainedUnitPass.Reading i read rev a.q (unit a) := a.source.unit
  generalize eqn : unit a = b at r ⊢
  cases r with
  | node h _ _ _ _ _ _ _ => exact ⟨_,h,rfl,rfl⟩

private theorem unit_eq {i read rev} {a b : State i read rev} (eqn : Deep unit a = Deep unit b) :
    unit a = unit b := by
  obtain ⟨k,ka,pa,ha⟩ := constitution a
  obtain ⟨j,kb,pb,hb⟩ := constitution b
  have keys := RingPairGateCount.key_eq (RingRetainedChemicalTrace.key_source ka).formed
    (RingRetainedChemicalTrace.key_source kb).formed (pa.symm.trans ((splitKeys eqn).1.trans pb))
  exact branch_eq eqn (ha.trans (keys ▸ hb.symm)) (framed [] a.source.unit) (framed [] b.source.unit)

private theorem lower_earlier {i read rev} {a b : State i read rev} (eqn : Deep lower a = Deep lower b) :
    unit a = unit b ∧ lower a = lower b := by
  have left := previous_keys a.source.unit a.source.lower
  have right := previous_keys b.source.unit b.source.lower
  have u := unit_eq (a := a) (b := b) (left.2.symm.trans ((splitKeys eqn).1.trans right.2))
  exact ⟨u,branch_eq eqn (left.1.trans ((congrArg Branch.shallow u).trans right.1.symm))
    (framed _ a.source.lower) (framed _ b.source.lower)⟩

private theorem queue_using {i read rev} {a : State i read rev} {xs sh de : List (S read rev)}
    (nat : Native a xs) (first : Legal (Shallow unit) xs sh) (second : Legal (Deep unit) xs de) :
    ∃ q : RingRetainedUnitPass.Queue i read rev a.q (unit a), q.deep = de.map unit := by
  obtain ⟨src⟩ := RingRetainedUnitPass.Reading.queue a.source.unit
  let row : RingRetainedStereoRefinement.Row i read rev [] a.q (unit a) src.shallow src.deep :=
    ⟨_,src.lookup,src.complete,src.source,src.first,src.second,src.layout⟩
  have same : xs.map unit = src.childrenRead := native_eq nat unit (fun t => t.source.unit) row
  exact ⟨⟨src.childrenRead,src.lookup,src.complete,src.source,sh.map unit,de.map unit,
    same ▸ mapLegal first,same ▸ mapLegal second,layout nat unit (fun t => t.source.unit) first second⟩,rfl⟩

private theorem unit_children {i read rev} {a b : State i read rev} {xs ys sa da sb db}
    (na : Native a xs) (nb : Native b ys) (same : Deep unit a = Deep unit b)
    (left : Legal (Shallow unit) xs sa) (ld : Legal (Deep unit) xs da)
    (right : Legal (Shallow unit) ys sb) (rd : Legal (Deep unit) ys db) :
    da.map (Deep unit) = db.map (Deep unit) := by
  obtain ⟨k,ka,pa,_⟩ := constitution a
  obtain ⟨j,kb,pb,_⟩ := constitution b
  obtain rfl := RingPairGateCount.key_eq (RingRetainedChemicalTrace.key_source ka).formed
    (RingRetainedChemicalTrace.key_source kb).formed (pa.symm.trans ((splitKeys same).1.trans pb))
  obtain ⟨u,hu⟩ := queue_using na left ld
  obtain ⟨v,hv⟩ := queue_using nb right rd
  have kids := RingRetainedUnitPass.child_priorities ka kb u v (splitKeys same).2
  simpa only [hu,hv,List.map_map,Deep,Function.comp_def] using kids

/-- Tied parents through Rule 4c have the same complete child priorities in
every deep ordering that respects the lowercase comparison. -/
theorem lower_children {i read rev} {a b : State i read rev} {xs ys sa da sb db}
    (na : Native a xs) (nb : Native b ys) (same : Deep lower a = Deep lower b)
    (left : Legal (Shallow lower) xs sa) (ld : Legal (Deep lower) xs da)
    (right : Legal (Shallow lower) ys sb) (rd : Legal (Deep lower) ys db) :
    da.map (Deep lower) = db.map (Deep lower) := by
  have first := earlier_order unit lower (fun t => t.source.unit) (fun t => t.source.lower) left ld
  have second := earlier_order unit lower (fun t => t.source.unit) (fun t => t.source.lower) right rd
  obtain ⟨u,k⟩ := lower_earlier same
  have prior := unit_children na nb (congrArg Branch.deep u) first.1 first.2 second.1 second.2
  have rowsA := layout na lower (fun t => t.source.lower) left ld
  have rowsB := layout nb lower (fun t => t.source.lower) right rd
  have forms (t : S read rev) := framed [.lowercase] t.source.lower
  have all (xs : List (S read rev)) (c) (hc : c ∈ xs.map lower) : Framed 2 c.levels := by
    obtain ⟨_,_,rfl⟩ := List.mem_map.mp hc
    apply forms
  have words := recover_words (all da) (all db) (rowsA.symm.trans ((congrArg Branch.levels k).trans rowsB))
  apply List.ext_getElem
  · simpa using congrArg List.length prior
  · intro j hj hk
    simp only [List.length_map] at hj hk
    have p := List.getElem_of_eq prior (i := j) (by simpa using hj)
    have w := List.getElem_of_eq words (i := j) (by simpa using hj)
    simp only [List.getElem_map,Deep] at p w ⊢
    have ax := (previous_keys da[j].source.unit da[j].source.lower).2
    have bx := (previous_keys db[j].source.unit db[j].source.lower).2
    exact congrArg₂ List.append (ax.trans (p.trans bx.symm)) (congrArg List.singleton w)

def Directed {i read rev} (key : S (i := i) read rev → Branch) (a : S read rev) (sh de : List (S read rev)) :=
  ∃ xs, Native a xs ∧ Legal (Shallow key) xs sh ∧ Legal (Deep key) xs de

private theorem earlier {i read rev o os} (prev cur : S (i := i) read rev → Branch)
    (pre : ∀ t, Derives i read rev os t.q (prev t))
    (now : ∀ t, Derives i read rev (o::os) t.q (cur t)) {a sh de} (leg : Directed cur a sh de) :
    Directed prev a sh de := by
  obtain ⟨xs,nat,sh,de⟩ := leg
  exact ⟨xs,nat,earlier_order prev cur pre now sh de⟩

private theorem source_stream {i read rev os} (key : S (i := i) read rev → Branch)
    (src : ∀ t, Derives i read rev os t.q (key t))
    {leg : S read rev → List (S read rev) → List (S read rev) → Prop}
    (ok : ∀ a s d, leg a s d → Directed key a s d) {a out} (walk : Visits leg [a] [] out) :
    out.map (fun t => (key t).value) = (key a).stream := by
  let issued (b : Branch) (sh de : List Branch) := b.levels = rows sh de
  have map := walk.map (after := issued) key (fun a s d h => by
    obtain ⟨xs,nat,sh,de⟩ := ok _ _ _ h
    exact layout nat key src sh de)
  have projected := fifo_stream (allowed := issued) (fun _ _ _ h => h) map
  simpa only [List.map_map,Function.comp_def] using projected

def mark {i read rev} (key : S (i := i) read rev → Branch) (t : S read rev) : Option Bool :=
  if (unit t).value = 2 then some ((key t).value == 1) else none

private theorem packed {α : Type} (us ks : α → Nat) (out : List α) :
    ((out.map us).zip ((out.map ks).map (· == 1))).filterMap (fun (u,b) => if u = 2 then some b else none) =
      out.filterMap (fun t => if us t = 2 then some (ks t == 1) else none) := by
  induction out with
  | nil => rfl
  | cons t ts ih => simp only [List.map_cons,List.zip_cons_cons,List.filterMap_cons]; split <;> simp_all

theorem accepted_source {i read rev} (key : S (i := i) read rev → Branch) {os}
    (src : ∀ t, Derives i read rev os t.q (key t))
    (units : ∀ a sh de, Directed key a sh de → Directed unit a sh de)
    {a out} (walk : Visits (Directed key) [a] [] out) :
    RingRetainedStereoDecision.accepted (unit a) (key a) = out.filterMap (mark key) := by
  have u := source_stream unit (fun t => t.source.unit) units walk
  have k := source_stream key src (fun _ _ _ h => h) walk
  unfold RingRetainedStereoDecision.accepted RingRetainedStereoRefinement.bits
  rw [← u,← k,packed]
  rfl

theorem fixed_lower {i read rev} (s : RS) {a : State i read rev} {sh de}
    (h : Directed (fixed s) a sh de) : Directed lower a sh de :=
  earlier lower (fixed s) (fun t => t.source.lower) (fun t => t.source.fixed s) h

theorem lower_unit {i read rev} {a : State i read rev} {sh de} (h : Directed lower a sh de) :
    Directed unit a sh de := earlier unit lower (fun t => t.source.unit) (fun t => t.source.lower) h

theorem accepted_fixed {i read rev} (s : RS) {a : State i read rev} {out}
    (walk : Visits (Directed (fixed s)) [a] [] out) :
    RingRetainedStereoDecision.accepted (unit a) (fixed s a) = out.filterMap (mark (fixed s)) :=
  accepted_source _ (fun t => t.source.fixed s) (fun _ _ _ h => lower_unit (fixed_lower s h)) walk

theorem accepted_local {i read rev} (s : RS) {a : State i read rev} {out}
    (walk : Visits (Directed (localP s)) [a] [] out) :
    RingRetainedStereoDecision.accepted (unit a) (localP s a) = out.filterMap (mark (localP s)) :=
  accepted_source _ (fun t => t.source.paired s) (fun _ _ _ h =>
    earlier unit (localP s) (fun t => t.source.unit) (fun t => t.source.paired s) h) walk

private theorem unit_read {i read rev q b} (h : RingRetainedUnitPass.Reading i read rev q b) :
    ∃ v, read q.occurrence = some v ∧ b.value = RingNestedActivePair.unit (v.map fun p => if rev then p.2 else p.1) ∧
      (children i q = [] → v = none) := by
  cases h with | node _ seen physical _ _ _ _ _ => exact ⟨_,seen,rfl,physical.2⟩

private theorem at_observation {i read rev o os q b} (h : Derives i read rev (o::os) q b) {v}
    (seen : read q.occurrence = some v) : b.value = o.value v rev := by
  cases h with
  | node _ got _ _ _ _ _ => obtain rfl := Option.some.inj (seen.symm.trans got); rfl

/-- A terminal outward occurrence cannot contribute an accepted PairList bit. -/
theorem terminal_mark {i read rev} (key : S (i := i) read rev → Branch) (t : S read rev)
    (leaf : children i t.q = []) : mark key t = none := by
  obtain ⟨v,_,hu,absent⟩ := unit_read t.source.unit
  obtain rfl := absent leaf
  simp [mark,unit,hu,RingNestedActivePair.unit]

private theorem opposite_value {i read rev} (s : RS) (t : State i read rev) :
    (fixed s.swap t).value = (mark (fixed s) t == some false).toNat := by
  obtain ⟨v,seen,hu,_⟩ := unit_read t.source.unit
  have h := at_observation (t.source.fixed s) seen
  have hs := at_observation (t.source.fixed s.swap) seen
  simp only [fixed,mark,unit,hs,h,hu,Observation.value]
  generalize v.map (fun p => if rev then p.2 else p.1) = label
  rcases label with _ | ⟨(_|_)⟩ | ⟨(_|_)⟩ <;> cases s <;> rfl

private theorem same_levels {i read rev os} (key : S (i := i) read rev → Branch)
    (src : ∀ t, Derives i read rev os t.q (key t)) {a b xs ys}
    (na : Native a xs) (nb : Native b ys) (perm : (xs.map key).Perm (ys.map key)) :
    (key a).levels = (key b).levels := by
  let sa := legal_order (Shallow key) xs
  let da := legal_order (Deep key) xs
  let sb := legal_order (Shallow key) ys
  let db := legal_order (Deep key) ys
  rw [layout na key src sa da,layout nb key src sb db]
  have adjust {k : Branch → List Nat} {row} (h : Legal k (ys.map key) row) :
      Legal k (xs.map key) row := ⟨h.perm.trans perm.symm,h.descending⟩
  apply rows_unique (mapLegal sa) (mapLegal da) (adjust (mapLegal sb))
    ⟨(mapLegal db).perm.trans perm.symm,(mapLegal db).descending⟩
  rintro z hz
  obtain ⟨t,_,rfl⟩ := List.mem_map.mp hz
  exact framed _ (src t)

/-- Reconstruct a parent's opposite-seed key after the comparison walk has
recovered all its children's opposite-seed keys. -/
private theorem recover_node {i read rev} (s : RS) {a b : State i read rev} {sa da sb db}
    (la : Directed (fixed s) a sa da) (lb : Directed (fixed s) b sb db)
    (prior : Deep lower a = Deep lower b) :
    da.map (Deep lower) = db.map (Deep lower) ∧
    (mark (fixed s) a).isSome = (mark (fixed s) b).isSome ∧
    (mark (fixed s) a = mark (fixed s) b → da.map (fixed s.swap) = db.map (fixed s.swap) →
      fixed s.swap a = fixed s.swap b) := by
  obtain ⟨xs,na,xa,xd⟩ := la
  obtain ⟨ys,nb,ya,yd⟩ := lb
  have x := earlier_order lower (fixed s) (fun t => t.source.lower) (fun t => t.source.fixed s) xa xd
  have y := earlier_order lower (fixed s) (fun t => t.source.lower) (fun t => t.source.fixed s) ya yd
  obtain ⟨u,l⟩ := lower_earlier prior
  refine ⟨lower_children na nb prior x.1 x.2 y.1 y.2,?_,?_⟩
  · simp only [mark,u]
    split <;> rfl
  · intro bit kids
    have bag := ((xd.perm.map (fixed s.swap)).symm.trans (List.Perm.of_eq kids)).trans (yd.perm.map _)
    have lv := same_levels (fixed s.swap) (fun t => t.source.fixed s.swap) na nb bag
    have av := previous_keys a.source.lower (a.source.fixed s.swap)
    have bv := previous_keys b.source.lower (b.source.fixed s.swap)
    have prevHead := av.1.trans ((congrArg Branch.shallow l).trans bv.1.symm)
    have prevDeep := av.2.trans (prior.trans bv.2.symm)
    have value := (opposite_value s a).trans ((congrArg (fun w : Option Bool => (w == some false).toNat) bit).trans
      (opposite_value s b).symm)
    have ext (x y : Branch) (h : x.priorHead = y.priorHead) (d : x.priorDeep = y.priorDeep)
        (v : x.value = y.value) (z : x.levels = y.levels) : x = y := by cases x; cases y; simp_all
    exact ext _ _ prevHead prevDeep value lv

private theorem frontier_walk {i : Input} {root : i.certified.Atom} {f : Site i}
    (listed : f ∈ RingMolecularSchedule.frontier i root) (rev : Bool)
    (key : State i (RingNestedActivePair.masked f (RingMolecularSchedule.atRoot i root)) rev → Branch)
    (a : State i _ rev) (on : a.q.occurrence.val.root = f.val.root) :
    ∃ walk, Visits (Directed key) [a] [] walk := by
  classical
  let read := RingNestedActivePair.masked f (RingMolecularSchedule.atRoot i root)
  let good (n : Nat) (t : S read rev) := t.q.occurrence.val.root = f.val.root ∧ i.certified.localizedRerootCursorBudget t.q < n
  refine visits_exist good (fun _ h => Nat.not_lt_zero _ h.2) ?_ (i.certified.localizedRerootCursorBudget a.q+1) [a]
    (fun b hb => by obtain rfl := List.mem_singleton.mp hb; exact ⟨on,Nat.lt_succ_self _⟩)
  intro n t ht
  let raw := children i t.q
  have frame := i.certified.executableLocalizedRerootChildren_declarative t.q
  have valid (c : {c // c ∈ raw}) := i.certified.localizedRerootChild_valid t.q c.val _ frame c.property
  have same (c : {c // c ∈ raw}) := (i.certified.localizedRerootChildren_root_eq t.q c.val _ frame c.property).trans ht.1
  have ready (c : {c // c ∈ raw}) := RingRetainedStereoDecision.frontier_profile listed rev c.val (valid c) (same c)
  let lift (c : {c // c ∈ raw}) : S read rev := ⟨c.val,valid c,(ready c).choose,(ready c).choose_spec.2⟩
  let xs := raw.attach.map lift
  have nat : Native t xs := by simp [Native,xs,lift,List.map_map,Function.comp_def,raw]
  have sd := legal_order (Deep key) xs
  refine ⟨_,_,⟨xs,nat,legal_order (Shallow key) xs,sd⟩,?_⟩
  intro x hx
  obtain ⟨c,_,rfl⟩ := List.mem_map.mp (sd.perm.mem_iff.mp hx)
  have smaller := i.certified.localizedRerootChild_budget_lt t.q c.val _ t.valid frame c.property
  exact ⟨same c,by change i.certified.localizedRerootCursorBudget c.val < n; have := ht.2; omega⟩

private theorem count_marks {i read rev} (key : S (i := i) read rev → Branch) (out : List (S read rev)) :
    (out.filterMap (mark key)).length = (out.map (fun t => (unit t).value)).count 2 := by
  induction out with
  | nil => rfl
  | cons x xs ih =>
    by_cases eqn : (unit x).value = 2 <;> simp [mark,eqn,ih]

private theorem accepted_count {i read rev os} (key : S (i := i) read rev → Branch)
    (src : ∀ t, Derives i read rev os t.q (key t))
    (units : ∀ a sh de, Directed key a sh de → Directed unit a sh de)
    {a out} (walk : Visits (Directed key) [a] [] out) :
    (RingRetainedStereoDecision.accepted (unit a) (key a)).length = (unit a).stream.count 2 := by
  rw [accepted_source key src units walk,count_marks,source_stream unit (fun t => t.source.unit) units walk]

/-- All complete local and fixed PairLists contain exactly one entry per
uppercase occurrence. This supplies the equal-length condition for comparing
the two local references, and for comparing either fixed seed between arms. -/
theorem frontier_widths {i : Input} {root : i.certified.Atom} {f : Site i}
    (listed : f ∈ RingMolecularSchedule.frontier i root) (rev : Bool) (s : RS)
    (a : State i (RingNestedActivePair.masked f (RingMolecularSchedule.atRoot i root)) rev)
    (on : a.q.occurrence.val.root = f.val.root) :
    (RingRetainedStereoDecision.accepted (unit a) (fixed s a)).length = (unit a).stream.count 2 ∧
    (RingRetainedStereoDecision.accepted (unit a) (localP s a)).length = (unit a).stream.count 2 := by
  obtain ⟨_,w⟩ := frontier_walk listed rev (fixed s) a on
  obtain ⟨_,v⟩ := frontier_walk listed rev (localP s) a on
  exact ⟨accepted_count _ (fun t => t.source.fixed s) (fun _ _ _ h => lower_unit (fixed_lower s h)) w,
    accepted_count _ (fun t => t.source.paired s) (fun _ _ _ h =>
      earlier unit (localP s) (fun t => t.source.unit) (fun t => t.source.paired s) h) v⟩

/-- The accepted bit refers to the actual frozen hand at this cursor on this
geometry, for either the local Rule 4b seed or the fixed Rule 5 seed. -/
theorem molecular_mark {i read rev} (s : RS) (a : State i read rev) :
    ∃ v, read a.q.occurrence = some v ∧
      let h := (RingNestedActivePair.upper (v.map fun p => if rev then p.2 else p.1)).map (· == s)
      mark (fixed s) a = h ∧ mark (localP s) a = h := by
  obtain ⟨v,seen,u,_⟩ := unit_read a.source.unit
  refine ⟨v,seen,?_⟩
  have h := at_observation (a.source.fixed s) seen
  have k := at_observation (a.source.paired s) seen
  simp only [mark,fixed,localP,unit,u,h,k,Observation.value]
  generalize v.map (fun p => if rev then p.2 else p.1) = label
  rcases label with _ | ⟨(_|_)⟩ | ⟨(_|_)⟩ <;> cases s <;> constructor <;> rfl

private theorem bits_zero {a b : List Bool} (size : a.length = b.length) :
    RingSeededPairs.compareBits a b = 0 ↔ a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp_all [RingSeededPairs.compareBits]
  | cons x xs ih =>
    cases b with
    | nil => simp at size
    | cons y ys => cases x <;> cases y <;> simp_all [RingSeededPairs.compareBits]

/-- Equality of the accepted fixed-reference words recovers equality of the
complete opposite-reference keys. The two passes may visit an earlier tie
block in different orders. -/
theorem transfer {i : Input} {root : i.certified.Atom} {f : Site i}
    (listed : f ∈ RingMolecularSchedule.frontier i root) (rev : Bool) (s : RS)
    (a b : State i (RingNestedActivePair.masked f (RingMolecularSchedule.atRoot i root)) rev)
    (ra : a.q.occurrence.val.root = f.val.root) (rb : b.q.occurrence.val.root = f.val.root)
    (prior : Deep lower a = Deep lower b) :
    RingRetainedStereoDecision.seedSign a.profile b.profile s = 0 →
      RingRetainedStereoDecision.seedSign a.profile b.profile s.swap = 0 := by
  obtain ⟨wa,ha⟩ := frontier_walk listed rev (fixed s) a ra
  obtain ⟨wb,hb⟩ := frontier_walk listed rev (fixed s) b rb
  have both := RingSeedEqualityTransport.transport (Deep lower) (mark (fixed s)) (fixed s.swap)
    (fun _ _ _ _ _ _ x y eqn => recover_node s x y eqn) ha hb (by simp [prior]) rfl
  have ak := accepted_fixed s ha
  have bk := accepted_fixed s hb
  intro zero
  unfold RingRetainedStereoDecision.seedSign at zero ⊢
  change RingSeededPairs.compareBits (RingRetainedStereoDecision.accepted (unit a) (fixed s a))
    (RingRetainedStereoDecision.accepted (unit b) (fixed s b)) = 0 at zero
  rw [ak,bk] at zero
  have eqn := (both.2 ((bits_zero both.1).mp zero)).1
  have opp : fixed s.swap a = fixed s.swap b := (List.cons.inj eqn).1
  change RingSeededPairs.compareBits (RingRetainedStereoDecision.accepted (unit a) (fixed s.swap a))
    (RingRetainedStereoDecision.accepted (unit b) (fixed s.swap b)) = 0
  rw [opp,(lower_earlier prior).1]
  exact (bits_zero rfl).mpr rfl

private theorem constitutional_words {i : Input} {f a b : Site i} {t k j}
    (prior : RingRetainedChemicalTrace.compareAt? i f a b = some t)
    (tie : cipTraceOutcome t = .eq)
    (left : RingRetainedChemicalTrace.key? i ⟨a,some f⟩ = some k)
    (right : RingRetainedChemicalTrace.key? i ⟨b,some f⟩ = some j) :
    RingRetainedChemicalPreorder.orderWord k = RingRetainedChemicalPreorder.orderWord j := by
  have incident := (RingRetainedChemicalTrace.compareAt?_source prior).1
  simp [RingRetainedChemicalTrace.compareAt?,incident,RingRetainedChemicalTrace.trace?,left,right] at prior
  subst t
  change RingRetainedChemicalTrace.compareKeys k j = .eq at tie
  rw [RingRetainedChemicalPreorder.compare_word] at tie
  exact Std.compare_eq_eq_iff_eq.mp tie

/-- On real frontier arms, a constitutional tie, a Rule 4a tie and a Rule 4c
tie supply the entire hereditary prior key for either fixed seed. Equality
of just one fixed-seed comparison now implies equality of the other. -/
theorem fixed_equality {i : Input} {root : i.certified.Atom} {f a b : Site i} {t}
    (listed : f ∈ RingMolecularSchedule.frontier i root) (rev : Bool)
    (prior : RingRetainedChemicalTrace.compareAt? i f a b = some t) (tie : cipTraceOutcome t = .eq)
    {x y : ArmProfile}
    (lx : Reads i (RingNestedActivePair.masked f (RingMolecularSchedule.atRoot i root)) rev ⟨a,some f⟩ x)
    (ly : Reads i (RingNestedActivePair.masked f (RingMolecularSchedule.atRoot i root)) rev ⟨b,some f⟩ y)
    (u : x.unit.word = y.unit.word) (lo : x.lower.word = y.lower.word) :
    RingRetainedStereoDecision.seedSign x y .R = 0 ↔ RingRetainedStereoDecision.seedSign x y .S = 0 := by
  have inc := (RingRetainedChemicalTrace.compareAt?_source prior).1
  have valid (v : Site i) (adj : i.certified.LocalizedCarrierTreeAdjacent v.val f.val) :
      i.certified.LocalizedRerootCursorValid (⟨v,some f⟩ : Arm i) :=
    (i.certified.mem_localizedRerootNeighborFrames_iff _ _).mpr ⟨v.property,adj⟩
  let m : State i _ rev := ⟨⟨a,some f⟩,valid a inc.2.2.1,x,lx⟩
  let n : State i _ rev := ⟨⟨b,some f⟩,valid b inc.2.2.2,y,ly⟩
  obtain ⟨k,ka,pa,_⟩ := constitution m
  obtain ⟨j,kb,pb,_⟩ := constitution n
  have earlier := pa.trans ((constitutional_words prior tie ka kb).trans pb.symm)
  have full : Deep unit m = Deep unit n := congrArg₂ List.append earlier (congrArg List.singleton u)
  have eqn : Deep lower m = Deep lower n :=
    congrArg₂ List.append ((previous_keys lx.unit lx.lower).2.trans (full.trans (previous_keys ly.unit ly.lower).2.symm))
      (congrArg List.singleton lo)
  exact ⟨transfer listed rev .R m n inc.2.2.1.1 inc.2.2.2.1 eqn,transfer listed rev .S m n inc.2.2.1.1 inc.2.2.2.1 eqn⟩

end TetraStereo.Engine.RingRetainedSeedFrames

assert_kernel_only TetraStereo.Engine.RingRetainedSeedFrames.transfer
assert_kernel_only TetraStereo.Engine.RingRetainedSeedFrames.fixed_equality

assert_kernel_only TetraStereo.Engine.RingRetainedSeedFrames.frontier_widths
assert_kernel_only TetraStereo.Engine.RingRetainedSeedFrames.molecular_mark
