import TetraStereo.Engine.RingChildKeyRecovery

/-! # Molecular origin of deciding Rule 2 masses

The three ordered words can be read as projections of common molecular
observations. Each parent has two independent row orders, one based on
immediate values and one based on complete child words. -/

set_option autoImplicit false

namespace TetraStereo.Engine.RingMassDifference

open OneCenter RingRetainedChemicalTrace
open RingRetainedConstitution (Cursor)
open LocalizedChemicalRing (Input)
open RingChildKeyRecovery (interleave)

abbrev Layers (α : Type) := List (List (List α))

def stages : Stage → List Stage
  | .atomic => [.atomic]
  | .duplicate => [.atomic, .duplicate]
  | .mass => [.atomic, .duplicate, .mass]

def rank {α : Type} [LinearOrder α] (value : Stage → Key → α)
    (s : Stage) (ks : List Key) :=
  ks.mergeSort fun a b => decide (((stages s).map (value · b)) ≤ ((stages s).map (value · a)))

abbrev headAt (s : Stage) (k : Key) := k.root.atStage s
abbrev wordAt (s : Stage) (k : Key) := (k.column s).word
private abbrev heads (s : Stage) (ks : List Key) := ks.map (headAt s)
def forest (s : Stage) (ks : List Key) :=
  ks.foldr (fun k acc => interleave (k.column s).levels acc) []

private theorem layout (s : Stage) (o : Observation) (ks : List Key) :
    ((assemble o ks).column s).levels =
    [heads s (rank headAt s ks), heads s (rank wordAt s ks)] :: forest s (rank wordAt s ks) := by
  cases s <;> apply congrArg (List.cons _)
  all_goals
    unfold forest
    apply congrArg (fun g => List.foldr g [] _)
    funext k acc
  case' atomic.h.h => generalize (k.column .atomic).levels = xs
  case' duplicate.h.h => generalize (k.column .duplicate).levels = xs
  case' mass.h.h => generalize (k.column .mass).levels = xs
  all_goals
    induction xs generalizing acc with
    | nil => rfl
    | cons v vs ih =>
      cases acc with
      | nil => rfl
      | cons a as => exact congrArg (List.cons _) (ih as)

private theorem rank_prefix {α : Type} [LinearOrder α] (v : Stage → Key → α)
    (s : Stage) (ks : List Key) : rank v s (rank v .mass ks) = rank v .mass ks := by
  apply List.mergeSort_of_pairwise
  have ord := List.pairwise_mergeSort (le := fun a b : Key =>
    decide (((stages .mass).map (v · b)) ≤ ((stages .mass).map (v · a))))
    (fun _ _ _ h j => decide_eq_true (le_trans (of_decide_eq_true j) (of_decide_eq_true h)))
    (fun a b => by simpa using le_total ((stages .mass).map (v · b)) ((stages .mass).map (v · a))) ks
  apply ord.imp
  intro a b h
  apply decide_eq_true
  have full := of_decide_eq_true h
  cases s with
  | mass => exact full
  | atomic => exact RingChildKeyRecovery.take_le full 1
  | duplicate => exact RingChildKeyRecovery.take_le full 2

/-- Each earlier column can be read in the mass-stage order, for both impressions of
each parent and for every subsequent sphere. -/
theorem common_layout (s : Stage) (o : Observation) (ks : List Key)
    (valid : ∀ k ∈ ks, WellFormed k) :
    ((assemble o ks).column s).levels =
      [heads s (rank headAt .mass ks), heads s (rank wordAt .mass ks)] ::
        forest s (rank wordAt .mass ks) := by
  have reorder {α : Type} [LinearOrder α] (v : Stage → Key → α) :
      ((assemble o ks).column s).levels = ((assemble o (rank v .mass ks)).column s).levels := by
    rw [assemble_perm o (List.mergeSort_perm ..).symm valid (ds := rank v .mass ks)]
  have shallow := reorder headAt
  have deep := reorder wordAt
  rw [layout,layout,rank_prefix] at shallow deep
  obtain ⟨top,_⟩ := List.cons.inj shallow
  obtain ⟨both,tail⟩ := List.cons.inj deep
  have a := (List.cons.inj top).1
  have b := (List.cons.inj (List.cons.inj both).2).1
  rw [layout,a,b,tail]

def project {α : Type} (f : α → Nat) (ls : Layers α) := ls.map (List.map (List.map f))

theorem project_interleave {α : Type} (f : α → Nat) (xs ys : Layers α) :
    project f (interleave xs ys) = interleave (project f xs) (project f ys) := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih => cases ys with
    | nil => rfl
    | cons y ys =>
      exact congrArg₂ List.cons (List.map_append ..) (ih ys)

private theorem project_forest {α : Type} (f : α → Nat) (ls : Key → Layers α)
    (s : Stage) (ks : List Key) (h : ∀ k ∈ ks, project f (ls k) = (k.column s).levels) :
    project f (ks.foldr (fun k acc => interleave (ls k) acc) []) = forest s ks := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
    exact (project_interleave ..).trans (congrArg₂ interleave (h _ List.mem_cons_self)
      (ih fun _ hk => h _ (List.mem_cons_of_mem _ hk)))

private abbrev Entry (P : Observation → Prop) := Subtype P
private abbrev atRule {P : Observation → Prop} (s : Stage) (x : Entry P) := x.val.atStage s

private theorem map_origin {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) {v : β} (mem : v ∈ ys) : ∃ x ∈ xs, f x = some v := by
  induction xs generalizing ys with
  | nil => obtain rfl : [] = ys := Option.some.inj h; contradiction
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    cases hx : f x <;> cases hs : xs.mapM f <;> simp [hx,hs] at h
    subst ys
    rcases List.mem_cons.mp mem with rfl | more
    · exact ⟨x,List.mem_cons_self,hx⟩
    · obtain ⟨a,ha,read⟩ := ih hs more
      exact ⟨a,List.mem_cons_of_mem _ ha,read⟩

/-- Preserve a molecular predicate while assembling both row orders recursively.
The subtype keeps a source witness available even after flattening spheres. -/
private theorem aligned {i : Input} {d : Nat} {q : Cursor i.certified d} {k : Key}
    (expansion : Expansion i q k) (P : Observation → Prop)
    (source : ∀ c, Reaches i q c → ∀ o, observation? i c
      (i.certified.executableLocalizedRerootChildren c).isEmpty = some o → P o) :
    P k.root ∧ ∃ ls : Layers (Entry P), ∀ s, project (atRule s) ls = (k.column s).levels := by
  classical
  induction expansion with
  | @node q children o ks frame observed lookup complete branches ih =>
    have eqChildren := Option.some.inj (((i.certified.localizedRerootChildren?_eq_some_iff q children).mpr frame).symm.trans
      (i.certified.localizedRerootChildren?_eq_some_executable q))
    subst children
    have here := source q .here o observed
    have origin (k) (hk : k ∈ ks) : ∃ c ∈ i.certified.executableLocalizedRerootChildren q, lookup c = some k := by
      exact map_origin complete hk
    have child (k) (hk : k ∈ ks) : P k.root ∧ ∃ ls : Layers (Entry P), ∀ s, project (atRule s) ls = (k.column s).levels := by
      obtain ⟨c,mem,hit⟩ := origin k hk
      exact ih c mem hit (fun t ht => source t (.descend mem ht))
    let root (k : Key) : Entry P := if h : k ∈ ks then ⟨k.root,(child k h).1⟩ else ⟨o,here⟩
    let levels (k : Key) : Layers (Entry P) := if h : k ∈ ks then (child k h).2.choose else []
    let shallow := rank headAt .mass ks
    let deep := rank wordAt .mass ks
    have ps : shallow.Perm ks := List.mergeSort_perm ..
    have pd : deep.Perm ks := List.mergeSort_perm ..
    refine ⟨here, [shallow.map root,deep.map root] ::
      deep.foldr (fun k acc => interleave (levels k) acc) [], ?_⟩
    intro s
    have valid (k) (hk : k ∈ ks) : WellFormed k := by
      obtain ⟨c,mem,hit⟩ := origin k hk
      exact (branches c mem hit).formed
    rw [common_layout s o ks valid]
    have roots (xs : List Key) (perm : xs.Perm ks) :
        (xs.map root).map (atRule s) = heads s xs := by
      rw [List.map_map]
      exact List.map_congr_left fun x hx => by simp [root,perm.mem_iff.mp hx,atRule]
    exact congrArg₂ List.cons (congrArg₂ (fun a b => [a,b]) (roots shallow ps) (roots deep pd))
      (project_forest _ levels s deep fun k hk => by
        simpa [levels,pd.mem_iff.mp hk] using (child k (pd.mem_iff.mp hk)).2.choose_spec s)

private def Origin {i : Input} {d : Nat} (q : Cursor i.certified d) (o : Observation) :=
  ∃ c, Reaches i q c ∧ observation? i c (i.certified.executableLocalizedRerootChildren c).isEmpty = some o

private abbrev groupMap {P : Observation → Prop} (s : Stage) (rows : List (List (Entry P))) :=
  rows.map (List.map (atRule s))

private theorem words {i : Input} {d : Nat} {q : Cursor i.certified d} {k : Key} (e : Expansion i q k) :
    ∃ rows : List (List (Entry (Origin q))), ∀ s, groupMap s rows = (k.column s).word := by
  obtain ⟨hr,ls,h⟩ := aligned e (Origin q) (fun c reach o read => ⟨c,reach,read⟩)
  refine ⟨[⟨k.root,hr⟩] :: ls.flatten,fun s => ?_⟩
  rw [(e.formed s).2,← h]
  simp only [groupMap,List.map_cons,List.map_nil,List.map_flatten,project,atRule]

theorem observation_kind {i : Input} {d : Nat} {q : Cursor i.certified d} {t o}
    (read : observation? i q t = some o) :
    (q.occurrence.val.node.provenance = .realAtom ∧ o.duplicate = 0) ∨
      (0 < o.duplicate ∧ CIPRule2MassData.rule2MassPico? o.atomic none = some o.mass) := by
  unfold observation? at read
  obtain ⟨a,_,h⟩ := Option.bind_eq_some_iff.mp read
  obtain ⟨recd,_,h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_,_,h⟩ := Option.bind_eq_some_iff.mp h
  cases prov : q.occurrence.val.node.provenance <;> simp only [prov] at h <;> try contradiction
  case realAtom =>
    obtain ⟨_,_,out⟩ := Option.bind_eq_some_iff.mp h
    cases Option.some.inj out
    exact Or.inl ⟨rfl,rfl⟩
  case ringDuplicate n =>
    obtain ⟨_,guarded,h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨mass,found,out⟩ := Option.bind_eq_some_iff.mp h
    cases Option.some.inj out
    simp [guard] at guarded
    exact Or.inr ⟨closure_above_real _ _ (by tauto),found⟩

private theorem first {α : Type} [Ord α] [Std.LawfulEqOrd α] (xs ys : List α)
    (size : xs.length = ys.length) (strict : compare xs ys ≠ .eq) :
    ∃ n x y, xs[n]? = some x ∧ ys[n]? = some y ∧ xs.take n = ys.take n ∧
      compare xs ys = compare x y := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons a xs ih =>
    cases ys with
    | nil => simp at size
    | cons b ys =>
      by_cases eq : compare a b = .eq
      · obtain rfl := Std.compare_eq_eq_iff_eq.mp eq
        rw [List.compare_cons_cons,eq,Ordering.eq_then] at strict ⊢
        obtain ⟨n,x,y,hx,hy,hp,hc⟩ := ih ys (Nat.succ.inj size) strict
        exact ⟨n+1,x,y,hx,hy,by simp [hp],hc⟩
      · refine ⟨0,a,b,rfl,rfl,rfl,?_⟩
        rw [List.compare_cons_cons]
        cases h : compare a b <;> simp_all

/-- Look up one entry of an ordered parent group. Both indices start at zero. -/
def entry? {α : Type} (xs : List (List α)) (r c : Nat) : Option α :=
  xs[r]?.bind fun row => row[c]?

private theorem slot_map {α β : Type} (f : α → β) (xs : List (List α)) (r c : Nat) :
    entry? (xs.map (List.map f)) r c = (entry? xs r c).map f := by
  simp only [entry?,List.getElem?_map]
  cases xs[r]? <;> simp [List.getElem?_map]

/-- All three rule words identify this same slot. Its zero duplicate priority
and its recorded molecular source both identify a real occurrence in this arm. -/
structure RealMassAt {i : Input} {d : Nat} (q : Cursor i.certified d)
    (k : Key) (r c z m : Nat) : Prop where
  element : entry? k.atomic.word r c = some z
  realFlag : entry? k.duplicate.word r c = some 0
  mass : entry? k.mass.word r c = some m
  source : ∃ t o, Reaches i q t ∧
    observation? i t (i.certified.executableLocalizedRerootChildren t).isEmpty = some o ∧
    t.occurrence.val.node.provenance = .realAtom ∧ o = ⟨z,0,m⟩

/-- Every molecular observation with the duplicate priority read at this slot
has real provenance, including alternative witnesses for tied children. -/
theorem RealMassAt.real_of_read {i : Input} {d : Nat} {q t : Cursor i.certified d}
    {k r c z m terminal o} (atMass : RealMassAt q k r c z m)
    (read : observation? i t terminal = some o)
    (atFlag : entry? k.duplicate.word r c = some o.duplicate) :
    t.occurrence.val.node.provenance = .realAtom := by
  have zero := Option.some.inj (atFlag.symm.trans atMass.realFlag)
  rcases observation_kind read with real | duplicate
  · exact real.1
  · exact False.elim ((Nat.ne_of_gt duplicate.1) zero)

/-- Exact first differing group and position in the two mass words, together with
the signed comparison of the molecular masses read there. -/
structure FirstMass (x y : Key) (r c u v : Nat) : Prop where
  priorRows : x.mass.word.take r = y.mass.word.take r
  rows : ∃ a b, x.mass.word[r]? = some a ∧ y.mass.word[r]? = some b ∧
    a.take c = b.take c ∧ a[c]? = some u ∧ b[c]? = some v
  sign : compare x.mass.word y.mass.word = compare u v

/-- Whenever both earlier rule words tie and mass decides, its first unequal
slot contains two real occurrences of the same element, reachable in the respective arms. -/
theorem first_mass_real {i : Input} {d : Nat} {p q : Cursor i.certified d} {x y : Key}
    (left : Expansion i p x) (right : Expansion i q y)
    (atomic : x.atomic.word = y.atomic.word) (dup : x.duplicate.word = y.duplicate.word)
    (strict : compare x.mass.word y.mass.word ≠ .eq) :
    ∃ r c z u v, FirstMass x y r c u v ∧ u ≠ v ∧ RealMassAt p x r c z u ∧ RealMassAt q y r c z v := by
  obtain ⟨xs,hx⟩ := words left
  obtain ⟨ys,hy⟩ := words right
  have az := (hx .atomic).trans (atomic.trans (hy .atomic).symm)
  have size : xs.length = ys.length := by simpa using congrArg List.length az
  have msize : x.mass.word.length = y.mass.word.length := by
    change ((x.column .mass).word).length = ((y.column .mass).word).length
    rw [← hx,← hy]
    simpa using size
  obtain ⟨r,a,b,ha,hb,prior,rowSign⟩ := first _ _ msize strict
  have getRow {P : Observation → Prop} {ls : List (List (Entry P))} {k : Key}
      (cols : ∀ s, groupMap s ls = (k.column s).word) {row} (read : k.mass.word[r]? = some row) :
      ∃ l, ls[r]? = some l ∧ l.map (atRule .mass) = row := by
    change (k.column .mass).word[r]? = some row at read
    rw [← cols] at read
    exact Option.map_eq_some_iff.mp (by simpa [groupMap] using read)
  obtain ⟨l,hl,rfl⟩ := getRow hx ha
  obtain ⟨k,hk,rfl⟩ := getRow hy hb
  have rowEq := congrArg (fun w : Word => w[r]?) az
  simp only [groupMap,List.getElem?_map,hl,hk,Option.map_some,Option.some.injEq] at rowEq
  have len : (l.map (atRule .mass)).length = (k.map (atRule .mass)).length := by
    simpa using congrArg List.length rowEq
  obtain ⟨c,u,v,hu,hv,before,entrySign⟩ := first _ _ len (rowSign ▸ strict)
  obtain ⟨ox,oxAt,mx⟩ := Option.map_eq_some_iff.mp (List.getElem?_map ▸ hu)
  obtain ⟨oy,oyAt,my⟩ := Option.map_eq_some_iff.mp (List.getElem?_map ▸ hv)
  have projected {P : Observation → Prop} {ls : List (List (Entry P))} {key : Key}
      (cols : ∀ s, groupMap s ls = (key.column s).word) {row o}
      (atRow : ls[r]? = some row) (atEntry : row[c]? = some o) (s : Stage) :
      entry? (key.column s).word r c = some (o.val.atStage s) := by
    rw [← cols]
    change entry? (ls.map (List.map (atRule s))) r c = _
    rw [slot_map]
    simp [entry?,atRow,atEntry,atRule]
  have px := projected hx hl oxAt
  have py := projected hy hk oyAt
  have alignedAt (s : Stage) (same : (x.column s).word = (y.column s).word) :
      ox.val.atStage s = oy.val.atStage s :=
    Option.some.inj ((px s).symm.trans ((congrArg (fun w => entry? w r c) same).trans (py s)))
  have z := alignedAt .atomic atomic
  have flag := alignedAt .duplicate dup
  obtain ⟨cx,reachX,readX⟩ := ox.property
  obtain ⟨cy,reachY,readY⟩ := oy.property
  have sign := rowSign.trans entrySign
  have ne : u ≠ v := by rintro rfl; exact strict (sign.trans Std.ReflCmp.compare_self)
  refine ⟨r,c,ox.val.atomic,u,v,⟨prior,⟨_,_,ha,hb,before,hu,hv⟩,sign⟩,ne,?_⟩
  change ox.val.atomic = oy.val.atomic at z
  change ox.val.duplicate = oy.val.duplicate at flag
  change ox.val.mass = u at mx
  change oy.val.mass = v at my
  rcases observation_kind readX with ⟨rx,fx⟩ | ⟨dx,massX⟩ <;>
    rcases observation_kind readY with ⟨ry,fy⟩ | ⟨dy,massY⟩
  · have obsEq (o : Observation) (z m : Nat) (az : o.atomic = z) (fl : o.duplicate = 0)
        (ms : o.mass = m) : o = ⟨z,0,m⟩ := by cases o; simp_all
    exact ⟨⟨px .atomic,(px .duplicate).trans (congrArg some fx),(px .mass).trans (congrArg some mx),
        _,_,reachX,readX,rx,obsEq _ _ _ rfl fx mx⟩,
      ⟨(py .atomic).trans (congrArg some z.symm),(py .duplicate).trans (congrArg some fy),
        (py .mass).trans (congrArg some my),_,_,reachY,readY,ry,obsEq _ _ _ z.symm fy my⟩⟩
  · omega
  · omega
  · rw [z] at massX
    exact False.elim (ne (mx.symm.trans ((Option.some.inj (massX.symm.trans massY)).trans my)))

/-- A successful evaluator trace in which Rule 2 decides identifies its first
different mass and a real molecular occurrence on each side at any carrier depth. -/
theorem comparison_first_mass_real {i : Input} {d : Nat} {f a b : i.certified.LocalizedCIPOccurrence d}
    {order : Ordering} (strict : order ≠ .eq)
    (hit : compareAt? i f a b = some [⟨.atomicNumber,.eq⟩,⟨.duplicateAtom,.eq⟩,⟨.isotopeMass,order⟩]) :
    ∃ x y r c z u v, Expansion i ⟨a,some f⟩ x ∧ Expansion i ⟨b,some f⟩ y ∧
      FirstMass x y r c u v ∧ u ≠ v ∧ compare u v = order ∧
      RealMassAt ⟨a,some f⟩ x r c z u ∧ RealMassAt ⟨b,some f⟩ y r c z v := by
  obtain ⟨_,x,y,left,right,trace⟩ := compareAt?_source hit
  simp only [keyTrace,List.cons.injEq,CIPRuleDecision.mk.injEq,true_and,and_true] at trace
  obtain ⟨atom,dups,mass⟩ := trace
  obtain ⟨r,c,z,u,v,first,ne,ar,br⟩ := first_mass_real left right
    (Std.compare_eq_eq_iff_eq.mp atom.symm) (Std.compare_eq_eq_iff_eq.mp dups.symm) (mass ▸ strict)
  exact ⟨x,y,r,c,z,u,v,left,right,first,ne,first.sign.symm.trans mass.symm,ar,br⟩

end TetraStereo.Engine.RingMassDifference

assert_kernel_only TetraStereo.Engine.RingMassDifference.RealMassAt.real_of_read
assert_kernel_only TetraStereo.Engine.RingMassDifference.first_mass_real
assert_kernel_only TetraStereo.Engine.RingMassDifference.comparison_first_mass_real
