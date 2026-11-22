import TetraStereo.Engine.RingPairGateCount

set_option autoImplicit false

namespace TetraStereo.Engine.RingAtomicProfileShape

open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm)
open RingRetainedChemicalTrace
open RingNestedActivePair (Visit topology retainedLevels?)

/-- One complete, independently derived constitutional expansion at a cursor determines its key. -/
theorem expansion_unique {i : Input} {d : Nat} {q : RingRetainedConstitution.Cursor i.certified d}
    {k l : Key} (left : Expansion i q k) (right : Expansion i q l) : k = l := by
  induction left generalizing l with
  | @node q cs o ks frame obs lookup hit branches ih =>
    cases right with
    | @node _ ds p ls frame' obs' lookup' hit' branches' =>
      have frames := (i.certified.localizedRerootChildren?_eq_some_iff q cs).mpr frame
      have frames' := (i.certified.localizedRerootChildren?_eq_some_iff q ds).mpr frame'
      obtain rfl : cs = ds := Option.some.inj (frames.symm.trans frames')
      obtain rfl : o = p := Option.some.inj (obs.symm.trans obs')
      congr 1
      suffices ∀ (xs : List _) (sub : ∀ x ∈ xs, x ∈ cs) (as bs : List Key),
          xs.mapM lookup = some as → xs.mapM lookup' = some bs → as = bs from
        this cs (fun _ h => h) ks ls hit hit'
      intro xs
      induction xs with
      | nil => intro _ as bs ha hb; exact Option.some.inj (ha.symm.trans hb)
      | cons x xs ind =>
        intro sub as bs ha hb
        rw [List.mapM_cons] at ha hb
        obtain ⟨a,ra,ta⟩ := Option.bind_eq_some_iff.mp ha
        obtain ⟨b,rb,tb⟩ := Option.bind_eq_some_iff.mp hb
        obtain ⟨as',hsa,ea⟩ := Option.bind_eq_some_iff.mp ta
        obtain ⟨bs',hsb,eb⟩ := Option.bind_eq_some_iff.mp tb
        obtain rfl := Option.some.inj ea
        obtain rfl := Option.some.inj eb
        have member := sub x List.mem_cons_self
        exact congrArg₂ List.cons (ih x member ra (branches' x member rb))
          (ind (fun t ht => sub t (List.mem_cons_of_mem x ht)) _ _ hsa hsb)

private def cursorKey (i : Input) (q : Arm i) := (key? i q).getD (assemble ⟨0,0,0⟩ [])

private theorem read_valid {i : Input} {q : Arm i} (ok : i.certified.LocalizedRerootCursorValid q) :
    key? i q = some (cursorKey i q) := by
  obtain ⟨k,hk⟩ := RingRetainedChemicalCoverage.key_total i (RingRetainedChemicalCoverage.admitted_atoms i) q ok
  simp [cursorKey,hk]

private theorem source_children {i : Input} {q : Arm i} {k : Key}
    (src : Expansion i q k) {xs : List (Arm i)}
    (order : xs.Perm (i.certified.executableLocalizedRerootChildren q)) :
    ∃ o, observation? i q (i.certified.executableLocalizedRerootChildren q).isEmpty = some o ∧
      k = assemble o (xs.map (cursorKey i)) := by
  cases src with
  | @node _ cs o ks frame obs lookup hit branches =>
    have frames := (i.certified.localizedRerootChildren?_eq_some_iff q cs).mpr frame
    obtain rfl : cs = i.certified.executableLocalizedRerootChildren q :=
      Option.some.inj (frames.symm.trans (i.certified.localizedRerootChildren?_eq_some_executable q))
    let cs := i.certified.executableLocalizedRerootChildren q
    have valid (x : Arm i) (mem : x ∈ cs) := read_valid (i.certified.localizedRerootChild_valid q x _ frame mem)
    have mapped : ∀ (ys : List (Arm i)), (∀ y ∈ ys, y ∈ cs) → ∀ {ks'}, ys.mapM lookup = some ks' →
        ks' = ys.map (cursorKey i) := by
      intro ys
      induction ys with
      | nil => intro _ ks' h; exact (Option.some.inj h).symm
      | cons y ys ind =>
        intro sub ks' h
        rw [List.mapM_cons] at h
        obtain ⟨v,hv,tail⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨vs,hvs,out⟩ := Option.bind_eq_some_iff.mp tail
        obtain rfl := Option.some.inj out
        have mem := sub y List.mem_cons_self
        exact congrArg₂ List.cons (expansion_unique (branches y mem hv) (key_source (valid y mem)))
          (ind (fun t ht => sub t (List.mem_cons_of_mem y ht)) hvs)
    refine ⟨o,obs,?_⟩
    rw [mapped cs (fun _ h => h) hit]
    apply assemble_perm o (order.symm.map _)
    intro k hk
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hk
    exact (key_source (valid x hx)).formed

private theorem observed_number {i : Input} {q : Arm i} {term o z}
    (obs : observation? i q term = some o) (got : RingActivePairs.z? i q = some z) : o.atomic = z := by
  unfold observation? at obs
  obtain ⟨a,ha,more⟩ := Option.bind_eq_some_iff.mp obs
  obtain ⟨b,hb,more⟩ := Option.bind_eq_some_iff.mp more
  obtain ⟨_,positive,out⟩ := Option.bind_eq_some_iff.mp more
  have endpoint : RingActivePairs.endpointZ? i q = some b.element.atomicNumber := by
    simp [RingActivePairs.endpointZ?,ha,hb,positive]
  unfold RingActivePairs.z? at got
  cases hp : q.occurrence.val.node.provenance <;> simp only [hp] at got out
  all_goals first | contradiction | skip
  · obtain ⟨_,_,eqn⟩ := Option.bind_eq_some_iff.mp out
    obtain rfl := Option.some.inj eqn
    exact Option.some.inj (endpoint.symm.trans got)
  · split at got <;> try contradiction
    obtain ⟨_,_,more⟩ := Option.bind_eq_some_iff.mp out
    obtain ⟨_,_,eqn⟩ := Option.bind_eq_some_iff.mp more
    obtain rfl := Option.some.inj eqn
    exact Option.some.inj (endpoint.symm.trans got)

private theorem root_number {i : Input} {q : Arm i} {z : Nat} {k : Key}
    (src : Expansion i q k) (got : RingActivePairs.z? i q = some z) : k.root.atomic = z := by
  cases src with
  | node _ obs _ _ _ => exact observed_number obs got

private theorem root_lt_word {x y : Key} (hx : WellFormed x) (hy : WellFormed y)
    (lt : x.root.atomic < y.root.atomic) : x.atomic.word < y.atomic.word := by
  have ax := (hx .atomic).2
  have ay := (hy .atomic).2
  change x.atomic.word = [x.root.atomic] :: _ at ax
  change y.atomic.word = [y.root.atomic] :: _ at ay
  rw [ax,ay]
  exact List.cons_lt_cons_iff.mpr (.inl (List.cons_lt_cons_iff.mpr (.inl lt)))

private theorem list_gt {α : Type} [Ord α] [Std.LawfulEqOrd α] [LT α]
    (gt : ∀ a b : α, compare a b = .gt → b < a) :
    ∀ a b : List α, compare a b = .gt → b < a
  | [],[],h | [],_::_,h => by contradiction
  | _::_,[],_ => List.Lex.nil
  | a::as,b::bs,h => by
    rw [List.compare_cons_cons] at h
    cases e : compare a b with
    | lt => simp [e] at h
    | eq =>
      obtain rfl := Std.compare_eq_eq_iff_eq.mp e
      exact List.Lex.cons (list_gt gt as bs (by simpa [e] using h))
    | gt => exact List.Lex.rel (gt a b e)

private theorem word_le {x y : Key} (h : compareKeys x y = .gt ∨ compareKeys x y = .eq) :
    y.atomic.word ≤ x.atomic.word := by
  cases ha : compare x.atomic.word y.atomic.word with
  | lt => simp [compareKeys,keyTrace,ha] at h
  | eq => exact le_of_eq (Std.compare_eq_eq_iff_eq.mp ha).symm
  | gt => exact le_of_lt (list_gt (list_gt (fun _ _ => Nat.compare_eq_gt.mp)) _ _ ha)

private theorem child_ranked {i : Input} {q : Arm i}
    {v : {xs : List (Arm i) // RingRetainedSiblingOrder.Order i q xs}}
    (got : RingRetainedSiblingOrder.chemicalChildren? i q = some v) :
    (v.val.map (cursorKey i)).Pairwise (fun a b => b.atomic.word ≤ a.atomic.word) := by
  unfold RingRetainedSiblingOrder.chemicalChildren? at got
  split at got
  next es h _ =>
    obtain rfl := Option.some.inj got
    have strict := RingActivePairs.children_source h
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp_of_mem _ strict.descending
    intro a b ha hb lt
    have source (x : Arm i) (hx : x ∈ es.map Prod.fst) :=
      key_source (read_valid (i.certified.localizedRerootChild_valid q x _
        (i.certified.executableLocalizedRerootChildren_declarative q) (strict.complete.mem_iff.mp hx)))
    obtain ⟨za,hza⟩ := Option.isSome_iff_exists.mp (strict.present a ha)
    obtain ⟨zb,hzb⟩ := Option.isSome_iff_exists.mp (strict.present b hb)
    exact le_of_lt (root_lt_word (source b hb).formed (source a ha).formed (by
      rw [root_number (source a ha) hza,root_number (source b hb) hzb]
      simpa [hza,hzb] using lt))
  next =>
    obtain ⟨_,_,nextStep⟩ := Option.bind_eq_some_iff.mp got
    obtain ⟨⟨rs,_⟩,_,out⟩ := Option.bind_eq_some_iff.mp nextStep
    dsimp only at out
    split at out
    next strict =>
      obtain rfl := Option.some.inj out
      apply List.pairwise_map.mpr
      apply List.pairwise_map.mpr
      exact strict.imp (fun {a b} ab => by
        simpa [cursorKey,a.2.property,b.2.property] using word_le (ab.imp_right And.left))
    next => contradiction

private abbrev numbers (ks : List Key) := ks.map fun k => k.root.atomic

/-- Read one sphere's parent rows. Only the deep-ranked row sets the next FIFO order. -/
def readSphere : List Nat → Word → List (Nat × Nat) × List Nat × Word
  | [],w => ([],[],w)
  | z::zs,_::cs::w =>
    let rest := readSphere zs w
    ((z,cs.length)::rest.1,cs ++ rest.2.1,rest.2.2)
  | _::_,_ => ([],[],[])

/-- Recover the numbered, per-parent arities in breadth-first order directly from Rule 1a. -/
def profile : Nat → List Nat → Word → List (List (Nat × Nat))
  | 0,_,_ | _+1,[],_ => []
  | n+1,z::zs,w =>
    let sphere := readSphere (z::zs) w
    sphere.1 :: profile n sphere.2.1 sphere.2.2

private theorem queue_next (o : Observation) (children current waiting : List Key)
    (ranked : children.Pairwise fun a b => b.atomic.word ≤ a.atomic.word) :
    ∃ shallow, queueRows .atomic (assemble o children :: current) waiting =
      shallow :: numbers children :: queueRows .atomic current (waiting ++ children) := by
  have sorted : children.mergeSort (fun x y => decide ([y.atomic.word] ≤ [x.atomic.word])) = children := by
    apply List.mergeSort_of_pairwise
    exact ranked.imp (fun {x y} h => decide_eq_true (by
      rcases lt_or_eq_of_le h with lt | eqn
      · exact le_of_lt (List.Lex.rel lt)
      · rw [eqn]))
  have pop := queue_pop .atomic o children current waiting
  dsimp only at pop
  change _ = _ :: numbers (children.mergeSort (fun x y => decide ([y.atomic.word] ≤ [x.atomic.word]))) ::
    queueRows .atomic current (waiting ++ children.mergeSort (fun x y => decide ([y.atomic.word] ≤ [x.atomic.word]))) at pop
  rw [sorted] at pop
  exact ⟨_,pop⟩

private def step? (i : Input) (read : RingNestedActivePair.Reader i) (q : Arm i) :
    Option (Visit × List (Arm i)) := do
  let children ← (do
    let v ← RingRetainedSiblingOrder.chemicalChildren? i q
    if h : RingNestedActivePair.ShallowOrder i read v.val then
      return (⟨v.val,v.property,h⟩ : {xs // RingRetainedSiblingOrder.Order i q xs ∧ RingNestedActivePair.ShallowOrder i read xs})
    else none)
  let z ← RingActivePairs.z? i q
  let v ← RingNestedActivePair.visit read q z children.val.length
  return (v,children.val)

private structure Step (i : Input) (q : Arm i) (data : Visit × List (Arm i)) : Prop where
  z : (cursorKey i q).root.atomic = data.1.z
  arity : data.2.length = data.1.children
  valid : ∀ c ∈ data.2, i.certified.LocalizedRerootCursorValid c
  pop : ∀ current waiting, ∃ row, queueRows .atomic (cursorKey i q :: current) waiting =
      row :: numbers (data.2.map (cursorKey i)) :: queueRows .atomic current (waiting ++ data.2.map (cursorKey i))

private theorem step_source {i : Input} {read : RingNestedActivePair.Reader i} {q : Arm i} {data}
    (key : key? i q = some (cursorKey i q)) (hit : step? i read q = some data) : Step i q data := by
  unfold step? at hit
  obtain ⟨cs,chosen,more⟩ := Option.bind_eq_some_iff.mp hit
  obtain ⟨v,hv,rank⟩ := Option.bind_eq_some_iff.mp chosen
  split at rank <;> try contradiction
  obtain rfl := Option.some.inj rank
  obtain ⟨z,hz,more⟩ := Option.bind_eq_some_iff.mp more
  obtain ⟨w,hw,out⟩ := Option.bind_eq_some_iff.mp more
  obtain rfl := Option.some.inj out
  unfold RingNestedActivePair.visit at hw
  obtain ⟨labels,_,hw⟩ := Option.bind_eq_some_iff.mp hw
  split at hw <;> try contradiction
  obtain rfl := Option.some.inj hw
  obtain ⟨o,_,eqn⟩ := source_children (key_source key) v.property.complete
  refine ⟨root_number (key_source key) hz,rfl,?_,?_⟩
  · exact fun x hx => (v.property.branch hx).2.1
  · intro current waiting
    rw [eqn]
    exact queue_next o _ current waiting (child_ranked hv)

private theorem steps {i : Input} {read : RingNestedActivePair.Reader i} {qs : List (Arm i)} {data}
    (keys : ∀ q ∈ qs, key? i q = some (cursorKey i q))
    (hit : qs.mapM (step? i read) = some data) : List.Forall₂ (Step i) qs data := by
  induction qs generalizing data with
  | nil => obtain rfl : [] = data := Option.some.inj hit; exact .nil
  | cons q qs ih =>
    rw [List.mapM_cons] at hit
    obtain ⟨d,hd,more⟩ := Option.bind_eq_some_iff.mp hit
    obtain ⟨ds,hds,out⟩ := Option.bind_eq_some_iff.mp more
    obtain rfl := Option.some.inj out
    exact .cons (step_source (keys q List.mem_cons_self) hd)
      (ih (fun a ha => keys a (List.mem_cons_of_mem q ha)) hds)

private theorem layer {i : Input} {qs : List (Arm i)} {data} (src : List.Forall₂ (Step i) qs data)
    (waiting : List Key) :
    let current := qs.map (cursorKey i)
    let children := (data.flatMap Prod.snd).map (cursorKey i)
    readSphere (numbers current) (queueRows .atomic current waiting) =
      ((data.map Prod.fst).map topology,numbers children,queueRows .atomic (waiting ++ children) []) := by
  induction src generalizing waiting with
  | nil => simpa [readSphere] using queue_rotate .atomic waiting
  | @cons q d qs ds step _ ih =>
    obtain ⟨row,pop⟩ := step.pop (qs.map (cursorKey i)) waiting
    dsimp only
    simp only [List.map_cons, List.flatMap_cons, List.map_append]
    rw [pop]
    simp only [readSphere,ih]
    simp [numbers,topology,step.z,step.arity,List.append_assoc]

private theorem successors {i : Input} {qs : List (Arm i)} {data}
    (src : List.Forall₂ (Step i) qs data) :
    ∀ q ∈ data.flatMap Prod.snd, key? i q = some (cursorKey i q) := by
  induction src with
  | nil => simp
  | cons step _ ih =>
    intro q h
    rcases List.mem_append.mp h with mem | mem
    · exact read_valid (step.valid q mem)
    · exact ih q mem

/-- Every materialized retained molecular profile has precisely the topology obtained
by reading the complete atomic-number queue, regardless of its auxiliary publications. -/
private theorem realized {i : Input} (read : RingNestedActivePair.Reader i) :
    ∀ (n : Nat) (qs : List (Arm i)) {vs}, (∀ q ∈ qs, key? i q = some (cursorKey i q)) →
      retainedLevels? i read n qs = some vs →
      profile n (numbers (qs.map (cursorKey i))) (queueRows .atomic (qs.map (cursorKey i)) []) =
        vs.map (List.map topology)
  | 0,[],_,_,hit | _+1,[],_,_,hit => by obtain rfl := Option.some.inj hit; rfl
  | 0,_::_,_,_,hit => by contradiction
  | n+1,q::qs,vs,keys,hit => by
    change ((q::qs).mapM (step? i read) >>= fun data => retainedLevels? i read n (data.flatMap Prod.snd) >>=
      fun rest => some (data.map Prod.fst :: rest)) = some vs at hit
    obtain ⟨data,hd,more⟩ := Option.bind_eq_some_iff.mp hit
    obtain ⟨rest,hr,out⟩ := Option.bind_eq_some_iff.mp more
    obtain rfl := Option.some.inj out
    have src := steps keys hd
    have row := layer src []
    dsimp only at row
    simp only [List.nil_append] at row
    have head := congrArg (fun value : List (Nat × Nat) × List Nat × Word =>
      value.1 :: profile n value.2.1 value.2.2) row
    exact head.trans (congrArg (List.cons _) (realized read n _ (successors src) hr))

theorem shape_from_key {i : Input} {q : Arm i} {k : Key} {read : RingNestedActivePair.Reader i}
    {n vs} (key : key? i q = some k) (hit : retainedLevels? i read n [q] = some vs) :
    vs.map (List.map topology) = profile n [k.root.atomic] k.atomic.word.tail := by
  have own : cursorKey i q = k := by simp [cursorKey,key]
  have words := queue_start .atomic k (key_source key).formed
  change k.atomic.word = [k.root.atomic] :: queueRows .atomic [k] [] at words
  have build := realized read n [q] (by simpa [own] using key) hit
  simpa [numbers,own,words] using build.symm

/-- Equality of Rule 1a alone suffices. The molecules, cursors, auxiliary readers,
closure priorities and isotope columns may differ. -/
theorem atomic_word_shape {i j : Input} {a : Arm i} {b : Arm j} {x y : Key} {n xs ys}
    {ra : RingNestedActivePair.Reader i} {rb : RingNestedActivePair.Reader j}
    (kx : key? i a = some x) (ky : key? j b = some y) (eqn : x.atomic.word = y.atomic.word)
    (left : retainedLevels? i ra n [a] = some xs) (right : retainedLevels? j rb n [b] = some ys) :
    xs.map (List.map topology) = ys.map (List.map topology) := by
  have hx := queue_start .atomic x (key_source kx).formed
  have hy := queue_start .atomic y (key_source ky).formed
  change x.atomic.word = [x.root.atomic] :: _ at hx
  change y.atomic.word = [y.root.atomic] :: _ at hy
  have roots := (List.cons.inj (hx.symm.trans (eqn.trans hy))).1
  rw [shape_from_key kx left,shape_from_key ky right,roots,eqn]

/-- A constitutional tie forces the two molecular profiles to have identical sphere,
parent, atomic-number and arity boundaries, even for different frozen readers. -/
theorem tie_shape {i : Input} {f a b : RingActivePairs.Site i} {t n xs ys}
    {ra rb : RingNestedActivePair.Reader i}
    (prior : compareAt? i f a b = some t) (tie : cipTraceOutcome t = .eq)
    (left : retainedLevels? i ra n [⟨a,some f⟩] = some xs)
    (right : retainedLevels? i rb n [⟨b,some f⟩] = some ys) :
    xs.map (List.map topology) = ys.map (List.map topology) := by
  unfold compareAt? at prior
  split at prior <;> try contradiction
  unfold trace? at prior
  obtain ⟨x,hx,more⟩ := Option.bind_eq_some_iff.mp prior
  obtain ⟨y,hy,out⟩ := Option.bind_eq_some_iff.mp more
  obtain rfl := Option.some.inj out
  change compareKeys x y = .eq at tie
  rw [RingRetainedChemicalPreorder.compare_word] at tie
  have equal := RingPairGateCount.key_eq (key_source hx).formed (key_source hy).formed (Std.compare_eq_eq_iff_eq.mp tie)
  rw [shape_from_key hx left,shape_from_key hy right,equal]

/-- Once both retained molecular profiles exist, a tied constitutional comparison
always receives an actual and reflected nested score. -/
theorem edge_covered {i f a b read t xs ys}
    (prior : compareAt? i f a b = some t) (tie : cipTraceOutcome t = .eq)
    (left : retainedLevels? i read (2*(i.certified.certified.input.molecule.atomCount+2)+2) [⟨a,some f⟩] = some xs)
    (right : retainedLevels? i read (2*(i.certified.certified.input.molecule.atomCount+2)+2) [⟨b,some f⟩] = some ys) :
    (RingNestedActivePair.edge? i f a b read).isSome = true :=
  (RingPairGateCount.edge_iff prior tie left right).mpr (tie_shape prior tie left right)

/-- On a tied source comparison, the two materializations are exactly the remaining
precondition for this evaluator. A score already carries both witnesses. -/
theorem edge_iff_materialized {i f a b read t}
    (prior : compareAt? i f a b = some t) (tie : cipTraceOutcome t = .eq) :
    let fuel := 2*(i.certified.certified.input.molecule.atomCount+2)+2
    (RingNestedActivePair.edge? i f a b read).isSome = true ↔
      (retainedLevels? i read fuel [⟨a,some f⟩]).isSome = true ∧
      (retainedLevels? i read fuel [⟨b,some f⟩]).isSome = true := by
  dsimp only
  constructor
  · intro hit
    obtain ⟨⟨_,proof⟩,_⟩ := Option.isSome_iff_exists.mp hit
    cases proof with
    | below earlier strict | above earlier strict =>
      have eqn := Option.some.inj (prior.symm.trans earlier)
      subst_vars
      rw [tie] at strict
      contradiction
    | stereo p =>
      exact ⟨Option.isSome_iff_exists.mpr ⟨_,p.leftRead⟩,Option.isSome_iff_exists.mpr ⟨_,p.rightRead⟩⟩
  · rintro ⟨l,r⟩
    obtain ⟨xs,hx⟩ := Option.isSome_iff_exists.mp l
    obtain ⟨ys,hy⟩ := Option.isSome_iff_exists.mp r
    exact edge_covered prior tie hx hy

/-- Every admitted directed occurrence yields its endpoint atomic number, including
a ring closure reached on a rerooted walk. -/
theorem number_total (i : Input) (q : Arm i) : ∃ z, RingActivePairs.z? i q = some z := by
  obtain ⟨o,obs⟩ := RingRetainedChemicalCoverage.observed i (RingRetainedChemicalCoverage.admitted_atoms i) q
  unfold observation? at obs
  obtain ⟨a,ha,more⟩ := Option.bind_eq_some_iff.mp obs
  obtain ⟨r,hr,more⟩ := Option.bind_eq_some_iff.mp more
  obtain ⟨_,positive,branch⟩ := Option.bind_eq_some_iff.mp more
  have endpoint : RingActivePairs.endpointZ? i q = some r.element.atomicNumber := by
    simp [RingActivePairs.endpointZ?,ha,hr,positive]
  refine ⟨r.element.atomicNumber,?_⟩
  unfold RingActivePairs.z?
  cases hp : q.occurrence.val.node.provenance <;> simp only [hp] at branch ⊢
  all_goals first | contradiction | skip
  · exact endpoint
  · have dup := i.certified.isDuplicateLeaf_eq_true_of_ring_provenance q.occurrence.val.node hp
    simp [executableLocalizedRerootChildren,intendedLocalizedRerootChildFrames,dup,endpoint]

/-- The exact local requirements at one directed molecular occurrence. Absent
publications are permitted. A terminal occurrence must certify their absence. -/
def Ready (i : Input) (read : RingNestedActivePair.Reader i) (q : Arm i) : Prop :=
  ∃ (row : {xs : List (Arm i) // RingRetainedSiblingOrder.Order i q xs}) (labels : Option RingNestedActivePair.Labels),
    RingRetainedSiblingOrder.chemicalChildren? i q = some row ∧
    RingNestedActivePair.ShallowOrder i read row.val ∧
    read q.occurrence = some labels ∧ labels.all RingNestedActivePair.consistent = true ∧
    (row.val.length ≠ 0 ∨ labels.isNone = true)

private theorem step_ready {i : Input} {read : RingNestedActivePair.Reader i} {q : Arm i} :
    (∃ d, step? i read q = some d) ↔ Ready i read q := by
  constructor
  · rintro ⟨d,hit⟩
    unfold step? at hit
    obtain ⟨cs,row,more⟩ := Option.bind_eq_some_iff.mp hit
    obtain ⟨v,hv,rank⟩ := Option.bind_eq_some_iff.mp row
    split at rank <;> try contradiction
    rename_i shallow
    obtain rfl := Option.some.inj rank
    obtain ⟨_,_,more⟩ := Option.bind_eq_some_iff.mp more
    obtain ⟨w,hw,_⟩ := Option.bind_eq_some_iff.mp more
    unfold RingNestedActivePair.visit at hw
    obtain ⟨labels,readHit,ok⟩ := Option.bind_eq_some_iff.mp hw
    split at ok <;> try contradiction
    rename_i facts
    exact ⟨v,labels,hv,shallow,readHit,facts⟩
  · rintro ⟨row,labels,order,shallow,publication,flags⟩
    obtain ⟨z,number⟩ := number_total i q
    have terminal : row.val ≠ [] ∨ labels = none := by simpa using flags.2
    simp [step?,order,shallow,number,RingNestedActivePair.visit,publication,flags,terminal]

private theorem step_perm {i : Input} {read : RingNestedActivePair.Reader i} {q : Arm i} {d}
    (h : step? i read q = some d) : d.2.Perm (i.certified.executableLocalizedRerootChildren q) := by
  unfold step? at h
  obtain ⟨cs,_,more⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨_,_,more'⟩ := Option.bind_eq_some_iff.mp more
  obtain ⟨_,_,out⟩ := Option.bind_eq_some_iff.mp more'
  obtain rfl := Option.some.inj out
  exact cs.property.1.complete

private theorem map_ready {α β : Type} (f : α → Option β) (qs : List α) :
    (∃ ds, qs.mapM f = some ds) ↔ ∀ x ∈ qs, ∃ d, f x = some d := by
  induction qs with
  | nil => simp
  | cons q qs ih =>
    rw [List.forall_mem_cons,← ih]
    cases head : f q <;> cases tail : qs.mapM f <;> simp [List.mapM_cons,head,tail]

private theorem covered_children {i : Input} {read : RingNestedActivePair.Reader i}
    {qs : List (Arm i)} {ds} (hit : qs.mapM (step? i read) = some ds) (c : Arm i) :
    c ∈ ds.flatMap Prod.snd ↔ ∃ a ∈ qs, c ∈ i.certified.executableLocalizedRerootChildren a := by
  induction qs generalizing ds with
  | nil => obtain rfl : [] = ds := Option.some.inj hit; simp
  | cons q qs ih =>
    rw [List.mapM_cons] at hit
    obtain ⟨d,hd,more⟩ := Option.bind_eq_some_iff.mp hit
    obtain ⟨tail,ht,out⟩ := Option.bind_eq_some_iff.mp more
    obtain rfl := Option.some.inj out
    simp only [List.flatMap_cons,List.mem_append,(step_perm hd).mem_iff,ih ht,List.mem_cons]
    grind

private theorem complete_at {i : Input} (read : RingNestedActivePair.Reader i) :
    ∀ (n : Nat) (qs : List (Arm i)),
      (∀ a ∈ qs, i.certified.LocalizedRerootCursorValid a ∧ i.certified.localizedRerootCursorBudget a < n) →
      ((∃ vs, retainedLevels? i read n qs = some vs) ↔ ∀ a ∈ qs, ∀ t, Reaches i a t → Ready i read t)
  | 0,[],_ | _+1,[],_ => by simp [retainedLevels?]
  | 0,q::_,bound => by have := (bound q List.mem_cons_self).2; omega
  | n+1,q::qs,bound => by
    let cs := q::qs
    have next {ds} (hit : cs.mapM (step? i read) = some ds) :
        (∃ vs, retainedLevels? i read n (ds.flatMap Prod.snd) = some vs) ↔
          ∀ c ∈ ds.flatMap Prod.snd, ∀ t, Reaches i c t → Ready i read t := by
      apply complete_at read n
      intro c hc
      obtain ⟨a,ha,mem⟩ := (covered_children hit c).mp hc
      have frame := i.certified.executableLocalizedRerootChildren_declarative a
      have good := bound a ha
      have decrease := i.certified.localizedRerootChild_budget_lt a c _ good.1 frame mem
      exact ⟨i.certified.localizedRerootChild_valid a c _ frame mem,by omega⟩
    change (∃ vs, (cs.mapM (step? i read) >>= fun data => retainedLevels? i read n (data.flatMap Prod.snd) >>=
      fun rest => some (data.map Prod.fst :: rest)) = some vs) ↔ _
    constructor
    · rintro ⟨vs,hit⟩ a ha t reach
      obtain ⟨ds,hd,more⟩ := Option.bind_eq_some_iff.mp hit
      obtain ⟨tail,ht,_⟩ := Option.bind_eq_some_iff.mp more
      cases reach with
      | here => exact step_ready.mp ((map_ready _ cs).mp ⟨ds,hd⟩ a ha)
      | @descend _ child _ mem further =>
        exact (next hd).mp ⟨tail,ht⟩ child ((covered_children hd child).mpr ⟨a,ha,mem⟩) t further
    · intro ready
      obtain ⟨ds,hd⟩ := (map_ready (step? i read) cs).mpr (fun a ha => step_ready.mpr (ready a ha a .here))
      obtain ⟨tail,ht⟩ := (next hd).mpr (fun c hc t further => by
        obtain ⟨a,ha,mem⟩ := (covered_children hd c).mp hc
        exact ready a ha t (.descend mem further))
      exact ⟨ds.map Prod.fst :: tail,by simp [hd,ht]⟩

/-- At the evaluator's actual initial fuel, every failure has a reachable
source occurrence that violates its local sibling or observation requirements.
Conversely each such occurrence prevents a successful molecular profile. -/
theorem missing_iff {i : Input} (read : RingNestedActivePair.Reader i) (q : Arm i)
    (valid : i.certified.LocalizedRerootCursorValid q) :
    retainedLevels? i read (2*(i.certified.certified.input.molecule.atomCount+2)+2) [q] = none ↔
      ∃ t, Reaches i q t ∧ ¬ Ready i read t := by
  have budget := i.certified.localizedRerootCursorBudget_le_twice q
  have ready := complete_at read (2*(i.certified.certified.input.molecule.atomCount+2)+2) [q]
    (by simpa only [List.mem_singleton,forall_eq] using
          (show i.certified.LocalizedRerootCursorValid q ∧
            i.certified.localizedRerootCursorBudget q < 2*(i.certified.certified.input.molecule.atomCount+2)+2
            from ⟨valid,by omega⟩))
  simp only [List.mem_singleton,forall_eq] at ready
  rw [← not_iff_not]
  simpa only [Option.ne_none_iff_exists',not_exists,not_and,not_not] using ready

end TetraStereo.Engine.RingAtomicProfileShape

assert_kernel_only TetraStereo.Engine.RingAtomicProfileShape.expansion_unique
assert_kernel_only TetraStereo.Engine.RingAtomicProfileShape.shape_from_key
assert_kernel_only TetraStereo.Engine.RingAtomicProfileShape.tie_shape
assert_kernel_only TetraStereo.Engine.RingAtomicProfileShape.edge_covered
assert_kernel_only TetraStereo.Engine.RingAtomicProfileShape.edge_iff_materialized
assert_kernel_only TetraStereo.Engine.RingAtomicProfileShape.atomic_word_shape
assert_kernel_only TetraStereo.Engine.RingAtomicProfileShape.missing_iff
assert_kernel_only TetraStereo.Engine.RingAtomicProfileShape.number_total
