import TetraStereo.Engine.RingParentGroupWidth

set_option autoImplicit false

namespace TetraStereo.Engine.RingChildKeyRecovery
open OneCenter RingRetainedChemicalTrace

private abbrev Layers := List (List (List Nat))
private abbrev width (r : List (List Nat)) := (r.map List.length).sum

def interleave {α : Type} : List (List α) → List (List α) → List (List α)
  | [],ys => ys
  | xs,[] => xs
  | x::xs,y::ys => (x++y)::interleave xs ys

theorem combined {x y : Layers} {n m : Nat} (a : Framed n x) (b : Framed m y) :
    Framed (n+m) (interleave x y) := by
  induction x generalizing n m y with
  | nil => obtain rfl := a; simpa [interleave] using b
  | cons x xs ih =>
    cases y with
    | nil => obtain rfl := b; simpa [interleave] using a
    | cons y ys =>
      obtain ⟨n,hx,tx⟩ := a
      obtain ⟨m,hy,ty⟩ := b
      exact ⟨by omega,by simp [hx,hy],by
        change Framed (width (x++y)) _
        simpa [width] using ih tx ty⟩

private theorem same_empty {x y : Layers} {n : Nat} (a : Framed n x) (b : Framed n y) :
    x = [] ↔ y = [] := by
  cases x <;> cases y <;> simp_all [Framed]

/-- Recover the first framed forest and the remainder from a sphere-by-sphere concatenation.
At each distance the current width cuts the row and the two decoded rows determine
the widths for the next distance. -/
theorem separate {x u y v : Layers} {n m : Nat}
    (a : Framed n x) (b : Framed n u) (c : Framed m y) (d : Framed m v)
    (eqn : interleave x y = interleave u v) : x = u ∧ y = v := by
  induction x generalizing n m u y v with
  | nil =>
    obtain rfl := (same_empty a b).mp rfl
    exact ⟨rfl,eqn⟩
  | cons h t ih =>
    cases u with
    | nil => exact False.elim (List.cons_ne_nil _ _ ((same_empty a b).mpr rfl))
    | cons k us =>
      cases y with
      | nil =>
        obtain rfl := (same_empty c d).mp rfl
        simpa only [interleave, and_true] using eqn
      | cons g ys =>
        cases v with
        | nil => exact False.elim (List.cons_ne_nil _ _ ((same_empty c d).mpr rfl))
        | cons f vs =>
          obtain ⟨top,more⟩ := List.cons.inj eqn
          obtain ⟨rfl,rfl⟩ := List.append_inj top (a.2.1.trans b.2.1.symm)
          obtain ⟨rfl,rfl⟩ := ih a.2.2 b.2.2 c.2.2 d.2.2 more
          exact ⟨rfl,rfl⟩

private def forest (s : Stage) (cs : List Key) : Layers :=
  cs.foldr (fun k acc => interleave (k.column s).levels acc) []

private theorem forest_form (s : Stage) (cs : List Key) (valid : ∀ c ∈ cs, WellFormed c) :
    Framed (2*cs.length) (forest s cs) := by
  induction cs with
  | nil => rfl
  | cons k ks ih =>
    have now := (valid k List.mem_cons_self s).1
    have below := ih (fun _ h => valid _ (List.mem_cons_of_mem _ h))
    simpa [forest,Nat.mul_add,Nat.add_comm] using combined now below

private theorem children_levels (s : Stage) {xs ys : List Key}
    (a : ∀ c ∈ xs, WellFormed c) (b : ∀ c ∈ ys, WellFormed c)
    (size : xs.length = ys.length) (eqn : forest s xs = forest s ys) :
    xs.map (fun k => (k.column s).levels) = ys.map (fun k => (k.column s).levels) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at size
    | cons y ys =>
      have n := Nat.succ.inj size
      have va := fun c (hc : c ∈ xs) => a c (List.mem_cons_of_mem _ hc)
      have vb := fun c (hc : c ∈ ys) => b c (List.mem_cons_of_mem _ hc)
      have aa := (a x List.mem_cons_self s).1
      have bb := (b y List.mem_cons_self s).1
      have ⟨head,tail⟩ := separate aa bb (forest_form s xs va)
        (n ▸ forest_form s ys vb) eqn
      exact congrArg₂ List.cons head (ih va vb n tail)

private def prefixWords (s : Stage) (k : Key) : List Word :=
  match s with
  | .atomic => [k.atomic.word]
  | .duplicate => [k.atomic.word,k.duplicate.word]
  | .mass => RingRetainedChemicalPreorder.orderWord k

private def ranked (s : Stage) (ks : List Key) :=
  ks.mergeSort fun a b => decide (prefixWords s b ≤ prefixWords s a)

private abbrev heads (s : Stage) (ks : List Key) := ks.map fun k => k.root.atStage s

private theorem layout (s : Stage) (o : Observation) (cs : List Key) :
    ∃ row, ((assemble o cs).column s).levels =
      [row,heads s (ranked s cs)] :: forest s (ranked s cs) := by
  cases s <;> refine ⟨_,congrArg (List.cons _) ?_⟩
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

theorem take_le {α : Type} [LinearOrder α] {x y : List α} (h : x ≤ y) (n : Nat) :
    x.take n ≤ y.take n := by
  rcases lt_or_eq_of_le h with lt | rfl
  · clear h
    induction lt generalizing n with
    | nil => cases n with
      | zero => exact le_rfl
      | succ => exact le_of_lt List.Lex.nil
    | rel ab => cases n with
      | zero => exact le_rfl
      | succ => exact le_of_lt (List.Lex.rel ab)
    | cons _ ih => cases n with
      | zero => exact le_rfl
      | succ n => exact List.cons_le_cons _ (ih n)
  · exact le_rfl

private theorem prefix_order (s : Stage) {a b : Key}
    (h : prefixWords .mass a ≤ prefixWords .mass b) : prefixWords s a ≤ prefixWords s b := by
  cases s with
  | mass => exact h
  | atomic => exact take_le h 1
  | duplicate => exact take_le h 2

private abbrev Ordered (xs : List Key) := xs.Pairwise fun a b => prefixWords .mass b ≤ prefixWords .mass a

private theorem stable {xs : List Key} (ord : Ordered xs) (s : Stage) : ranked s xs = xs :=
  List.mergeSort_of_pairwise (ord.imp (fun h => decide_eq_true (prefix_order s h)))

private theorem ordered (xs : List Key) : Ordered (ranked .mass xs) := by
  have h := List.pairwise_mergeSort (le := fun a b : Key => decide (prefixWords .mass b ≤ prefixWords .mass a))
    (fun _ _ _ x y => decide_eq_true (le_trans (of_decide_eq_true y) (of_decide_eq_true x)))
    (fun a b => by simpa using le_total (prefixWords .mass b) (prefixWords .mass a)) xs
  exact h.imp (fun ab => of_decide_eq_true ab)

/-- In complete constitutional order, every earlier stage uses precisely the
same ordering of branches. Each child's single-stage word can then be
recovered from its immediate head and individual forest decoded below it. -/
private theorem stage_words (s : Stage) {x y : Observation} {xs ys : List Key}
    (ax : ∀ c ∈ xs, WellFormed c) (ay : ∀ c ∈ ys, WellFormed c)
    (ox : Ordered xs) (oy : Ordered ys) (same : assemble x xs = assemble y ys) :
    xs.map (fun k => (k.column s).word) = ys.map (fun k => (k.column s).word) := by
  obtain ⟨lr,hl⟩ := layout s x xs
  obtain ⟨rr,hr⟩ := layout s y ys
  rw [stable ox, same] at hl
  rw [stable oy] at hr
  obtain ⟨roots,rest⟩ := List.cons.inj (hl.symm.trans hr)
  have head := (List.cons.inj (List.cons.inj roots).2).1
  have size : xs.length = ys.length := by simpa [heads] using congrArg List.length head
  have tail := children_levels s ax ay size rest
  apply List.ext_getElem
  · simpa only [List.length_map] using size
  · intro j a b
    simp only [List.length_map] at a b
    simp only [List.getElem_map]
    rw [(ax xs[j] (List.getElem_mem a) s).2,(ay ys[j] (List.getElem_mem b) s).2]
    have he := List.getElem_of_eq head (i := j) (by simpa [heads] using a)
    have te := List.getElem_of_eq tail (i := j) (by simpa using a)
    simpa using congrArg₂ (fun h t => [h] :: List.flatten t) he te

/-- Complete parent equality determines the entire multiset of complete child keys.
This includes constitutional collisions between two or more nonterminal children. -/
theorem recover {x y : Observation} {xs ys : List Key}
    (ax : ∀ c ∈ xs, WellFormed c) (ay : ∀ c ∈ ys, WellFormed c)
    (same : assemble x xs = assemble y ys) : xs.Perm ys := by
  let l := ranked .mass xs
  let r := ranked .mass ys
  have pl : l.Perm xs := List.mergeSort_perm ..
  have pr : r.Perm ys := List.mergeSort_perm ..
  have vl := fun k (h : k ∈ l) => ax k (pl.mem_iff.mp h)
  have vr := fun k (h : k ∈ r) => ay k (pr.mem_iff.mp h)
  have parents := (assemble_perm x pl vl).trans (same.trans (assemble_perm y pr vr).symm)
  have each (s : Stage) := stage_words s vl vr (ordered xs) (ordered ys) parents
  have size : l.length = r.length := by simpa only [List.length_map] using congrArg List.length (each .atomic)
  suffices l = r by exact pl.symm.trans (this ▸ pr)
  apply List.ext_getElem size
  intro j a b
  apply RingPairGateCount.key_eq (vl l[j] (List.getElem_mem a)) (vr r[j] (List.getElem_mem b))
  have entry (s : Stage) : (l[j].column s).word = (r[j].column s).word := by
    exact List.getElem_of_eq (each s) (i := j) (by simpa using a) |> fun h => by simpa using h
  simp only [RingRetainedChemicalPreorder.orderWord,List.cons.injEq, and_true]
  exact ⟨entry .atomic,entry .duplicate,entry .mass⟩

open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)

private abbrev children (i : Input) (q : Arm i) := i.certified.executableLocalizedRerootChildren q

/-- Read the actual children into key space. Admission ensures each lookup is present. -/
def childKeys (i : Input) (q : Arm i) :=
  (children i q).filterMap (key? i)

def eligibleKeys (i : Input) (q : Arm i) :=
  (RingParentGroupWidth.eligible i q).filterMap (key? i)

private theorem source_children {i : Input} {q : Arm i} {k : Key} (read : key? i q = some k) :
    ∃ o, k = assemble o (childKeys i q) ∧
      (∀ c ∈ childKeys i q, WellFormed c) ∧ (childKeys i q).length = (children i q).length := by
  cases key_source read with
  | @node _ cs o ks frame obs lookup hit branches =>
    have actual := Option.some.inj (((i.certified.localizedRerootChildren?_eq_some_iff q cs).mpr frame).symm.trans
      (i.certified.localizedRerootChildren?_eq_some_executable q))
    have found (c : Arm i) (hc : c ∈ cs) {v} (hv : lookup c = some v) : key? i c = some v := by
      have valid := i.certified.localizedRerootChild_valid q c cs frame hc
      obtain ⟨l,hl⟩ := RingRetainedChemicalCoverage.key_total i (RingRetainedChemicalCoverage.admitted_atoms i) c valid
      exact (RingAtomicProfileShape.expansion_unique (key_source hl) (branches c hc hv)) ▸ hl
    have result : ∀ xs : List (Arm i), (∀ c ∈ xs, c ∈ cs) → ∀ {ys : List Key},
        xs.mapM lookup = some ys → ys = xs.filterMap (key? i) ∧ ys.length = xs.length := by
      intro xs
      induction xs with
      | nil => intro _ ys h; obtain rfl := Option.some.inj h; exact ⟨rfl,rfl⟩
      | cons x xs ih =>
        intro sub ys h
        rw [List.mapM_cons] at h
        obtain ⟨v,hv,more⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨vs,hs,out⟩ := Option.bind_eq_some_iff.mp more
        obtain rfl := Option.some.inj out
        obtain ⟨eqn,size⟩ := ih (fun c hc => sub c (List.mem_cons_of_mem _ hc)) hs
        simp [found x (sub x List.mem_cons_self) hv,eqn,← size]
    obtain ⟨eqn,size⟩ := result cs (fun _ h => h) hit
    have keys : ks = childKeys i q := by simpa only [actual,childKeys] using eqn
    refine ⟨o,congrArg _ keys,?_,?_⟩
    · intro c hc
      obtain ⟨a,_,ha⟩ := List.mem_filterMap.mp hc
      exact (key_source ha).formed
    · simpa only [← keys,← actual] using size

private def live (k : Key) := !(k.atomic.word[2]?.getD []).isEmpty

private theorem live_source {i : Input} {q : Arm i} {k : Key} (read : key? i q = some k) :
    live k = !(children i q).isEmpty := by
  obtain ⟨o,h,_,size⟩ := source_children read
  obtain ⟨row,hr⟩ := layout .atomic o (childKeys i q)
  have words := ((key_source read).formed .atomic).2
  change k.atomic.word = [k.root.atomic] :: k.atomic.levels.flatten at words
  rw [h] at words
  change (assemble o (childKeys i q)).atomic.levels = _ at hr
  rw [hr] at words
  unfold live
  rw [h,words]
  simp [heads,ranked]
  apply Bool.eq_iff_iff.mpr
  simp only [List.isEmpty_iff_length_eq_zero,List.length_mergeSort,size]

theorem eligible_filter (i : Input) (q : Arm i) :
    eligibleKeys i q = (childKeys i q).filter live := by
  change ((children i q).filter (fun c => !(children i c).isEmpty)).filterMap (key? i) =
    ((children i q).filterMap (key? i)).filter live
  generalize children i q = row
  induction row with
  | nil => rfl
  | cons c cs ih =>
    cases r : key? i c with
    | none => cases e : (children i c).isEmpty <;> simp [e,r,ih]
    | some v =>
      have label := live_source r
      cases e : (children i c).isEmpty <;> simp [e] at label <;> simp [e,r,ih,label]

/-- The parent cursors can belong to different molecular inputs, roots or paths. -/
theorem children_tie {i j : Input} {a : Arm i} {b : Arm j} {k : Key}
    (ka : key? i a = some k) (kb : key? j b = some k) :
    (childKeys i a).Perm (childKeys j b) ∧ (eligibleKeys i a).Perm (eligibleKeys j b) := by
  obtain ⟨o,ho,vl,_⟩ := source_children ka
  obtain ⟨p,hp,vr,_⟩ := source_children kb
  have perm := recover vl vr (ho.symm.trans hp)
  exact ⟨perm,by rw [eligible_filter,eligible_filter]; exact perm.filter _⟩

/-- Every molecular constitutional tie preserves complete child-key populations,
before and after projecting out terminals. The outputs enumerate the children
in the actual original-root retained carriers and preserve all multiplicities. -/
theorem molecular_tie {i : Input} {f a b : Site i} {t} (prior : compareAt? i f a b = some t)
    (tie : cipTraceOutcome t = .eq) :
    (childKeys i ⟨a,some f⟩).Perm (childKeys i ⟨b,some f⟩) ∧
      (eligibleKeys i ⟨a,some f⟩).Perm (eligibleKeys i ⟨b,some f⟩) := by
  unfold compareAt? at prior
  split at prior <;> try contradiction
  unfold trace? at prior
  obtain ⟨x,hx,more⟩ := Option.bind_eq_some_iff.mp prior
  obtain ⟨y,hy,out⟩ := Option.bind_eq_some_iff.mp more
  obtain rfl := Option.some.inj out
  change compareKeys x y = .eq at tie
  rw [RingRetainedChemicalPreorder.compare_word] at tie
  obtain rfl := RingPairGateCount.key_eq (key_source hx).formed (key_source hy).formed (Std.compare_eq_eq_iff_eq.mp tie)
  exact children_tie hx hy

/-- Canonical prior groups in descending order, using the first unequal
constitutional priority and preserving the multiplicity of every tie. -/
def constitutionalWidths (i : Input) (q : Arm i) :=
  let words := (eligibleKeys i q).map RingRetainedChemicalPreorder.orderWord
  let row := words.mergeSort (fun a b => decide (b ≤ a))
  RingParentGroupWidth.widths (· == ·) row

theorem same_widths {i : Input} {f a b : Site i} {t} (prior : compareAt? i f a b = some t)
    (tie : cipTraceOutcome t = .eq) :
    constitutionalWidths i ⟨a,some f⟩ = constitutionalWidths i ⟨b,some f⟩ := by
  let words (q : Arm i) := (eligibleKeys i q).map RingRetainedChemicalPreorder.orderWord
  let rank (xs : List (List Word)) := xs.mergeSort (fun a b => decide (b ≤ a))
  have sorted (xs : List (List Word)) : (rank xs).Pairwise (· ≥ ·) :=
    (List.pairwise_mergeSort (le := fun a b : List Word => decide (b ≤ a))
      (fun _ _ _ h k => decide_eq_true (le_trans (of_decide_eq_true k) (of_decide_eq_true h)))
      (fun a b => by simpa using le_total b a) xs).imp (fun h => of_decide_eq_true h)
  let l := words ⟨a,some f⟩
  let r := words ⟨b,some f⟩
  have p : l.Perm r := (molecular_tie prior tie).2.map _
  have h := (List.mergeSort_perm l (fun a b => decide (b ≤ a))).trans
    (p.trans (List.mergeSort_perm r (fun a b => decide (b ≤ a))).symm)
  exact congrArg (RingParentGroupWidth.widths (· == ·))
    (List.Perm.eq_of_pairwise (fun _ _ _ _ ab ba => le_antisymm ba ab) (sorted l) (sorted r) h)

end TetraStereo.Engine.RingChildKeyRecovery

assert_kernel_only TetraStereo.Engine.RingChildKeyRecovery.recover
assert_kernel_only TetraStereo.Engine.RingChildKeyRecovery.eligible_filter
assert_kernel_only TetraStereo.Engine.RingChildKeyRecovery.molecular_tie
assert_kernel_only TetraStereo.Engine.RingChildKeyRecovery.same_widths
assert_kernel_only TetraStereo.Engine.RingChildKeyRecovery.children_tie
