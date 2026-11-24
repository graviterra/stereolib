import TetraStereo.Engine.RingFullPathPairs

/-! # Absolute full-path keys against local sibling ordinals

`RingFullPathPairs` sorts every sphere by the whole path of each visit: per
edge the complete through-4a priority of the child (`Branch.deep`) followed
by its like/unlike code (`stepKey`).

This module replaces the absolute priority on each edge by a local ordinal:
the number of actual sibling incidences whose through-4a priority is strictly
higher (the loss count). For any two descents that start at molecular
readings tied through Rule 4a, on possibly different inputs, readers,
geometries and seeds, comparing absolute paths and comparing
(loss count, like code) paths give the same strict order and the same ties.

The induction recovers the child distribution at every equal prefix: an equal
edge key gives `k.deep = l.deep` at the two children, hence the same
constitutional key (`RingPairGateCount.key_eq`), the same unit word, and by
`RingRetainedUnitPass.child_priorities` the same sorted row of child
priorities one sphere further out. -/
set_option autoImplicit false

namespace TetraStereo.Engine.RingPathRankTransport
open OneCenter CertifiedLocalizedCIPInput RingStereoSiblingPass
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader)
open RingRetainedChemicalTrace (Word)
open RingRetainedReferenceGroup (Path)
open RingRetainedUnitPass (Reading)
open RingFullPathPairs (stepKey likeCode likeAt FullVisit FullReach rootVisit)

private abbrev kids (i : Input) (q : Arm i) := i.certified.executableLocalizedRerootChildren q

/-! ## Loss counts -/

/-- Number of entries strictly above `x`. -/
def losses {κ : Type} [LinearOrder κ] (xs : List κ) (x : κ) : Nat :=
  xs.countP fun y => decide (x < y)

theorem losses_le {κ : Type} [LinearOrder κ] (xs : List κ) {x y : κ} (le : x ≤ y) :
    losses xs y ≤ losses xs x := by
  unfold losses
  exact List.countP_mono_left fun _ _ above =>
    decide_eq_true (lt_of_le_of_lt le (of_decide_eq_true above))

/-- Strict anti-monotonicity on occupied values: the higher value is itself
one of the entries counted against the lower one. -/
theorem losses_strict {κ : Type} [LinearOrder κ] {xs : List κ} {x y : κ} (occupied : y ∈ xs)
    (lt : x < y) : losses xs y < losses xs x := by
  induction xs with
  | nil => contradiction
  | cons z zs ih =>
    have unfolded (w : κ) : losses (z :: zs) w = losses zs w + if w < z then 1 else 0 := by
      simp [losses,List.countP_cons]
    have weak : losses zs y ≤ losses zs x := losses_le zs (le_of_lt lt)
    rw [unfolded y,unfolded x]
    rcases List.mem_cons.mp occupied with eq | rest
    · have self : ¬ y < z := by rw [← eq]; exact lt_irrefl y
      have low : x < z := by rw [← eq]; exact lt
      rw [if_neg self,if_pos low]
      omega
    · have strict := ih rest
      by_cases above : y < z
      · rw [if_pos above,if_pos (lt_trans lt above)]
        omega
      · rw [if_neg above]
        split <;> omega

theorem losses_perm {κ : Type} [LinearOrder κ] {xs ys : List κ} (p : xs.Perm ys) (z : κ) :
    losses xs z = losses ys z := p.countP_eq _

theorem losses_lt_iff {κ : Type} [LinearOrder κ] {xs ys : List κ}
    (same : ∀ z, losses xs z = losses ys z) {x y : κ} (hy : y ∈ ys) :
    x < y ↔ losses ys y < losses xs x := by
  constructor
  · intro lt
    rw [same x]
    exact losses_strict hy lt
  · intro fewer
    refine not_le.mp fun ge => ?_
    have weak := losses_le ys ge
    rw [same x] at fewer
    omega

theorem losses_eq_iff {κ : Type} [LinearOrder κ] {xs ys : List κ}
    (same : ∀ z, losses xs z = losses ys z) {x y : κ} (hx : x ∈ xs) (hy : y ∈ ys) :
    x = y ↔ losses xs x = losses ys y := by
  constructor
  · rintro rfl
    exact same x
  · intro equal
    rcases lt_trichotomy x y with lt | eq | gt
    · have strict := losses_strict hy lt
      rw [same x] at equal
      omega
    · exact eq
    · have strict := losses_strict hx gt
      rw [← same y] at equal
      omega

/-! ## List order facts -/

private theorem no_lt_nil {α : Type} [LinearOrder α] {xs : List α} : ¬ xs < [] :=
  fun h => by cases h

private theorem nil_lt {α : Type} [LinearOrder α] (x : α) (xs : List α) :
    ([] : List α) < x :: xs := List.Lex.nil

/-- With equal-length fronts, one appended entry is compared only after the
fronts tie. -/
theorem snoc_lt {α : Type} [LinearOrder α] {a b : List α} (len : a.length = b.length)
    (x y : α) : a ++ [x] < b ++ [y] ↔ a < b ∨ (a = b ∧ x < y) := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil =>
      show [x] < [y] ↔ _
      constructor
      · intro h
        rcases List.cons_lt_cons_iff.mp h with lt | ⟨_,bad⟩
        · exact .inr ⟨rfl,lt⟩
        · exact (no_lt_nil bad).elim
      · rintro (bad | ⟨_,lt⟩)
        · exact (no_lt_nil bad).elim
        · exact List.cons_lt_cons_iff.mpr (.inl lt)
    | cons _ _ => simp at len
  | cons h t ih =>
    cases b with
    | nil => simp at len
    | cons k s =>
      have len' : t.length = s.length := by simpa using len
      show h :: (t ++ [x]) < k :: (s ++ [y]) ↔ _
      constructor
      · intro lt
        rcases List.cons_lt_cons_iff.mp lt with less | ⟨rfl,tail⟩
        · exact .inl (List.cons_lt_cons_iff.mpr (.inl less))
        · rcases (ih len').mp tail with less | ⟨rfl,last⟩
          · exact .inl (List.cons_lt_cons_iff.mpr (.inr ⟨rfl,less⟩))
          · exact .inr ⟨rfl,last⟩
      · rintro (lt | ⟨eq,last⟩)
        · rcases List.cons_lt_cons_iff.mp lt with less | ⟨rfl,tail⟩
          · exact List.cons_lt_cons_iff.mpr (.inl less)
          · exact List.cons_lt_cons_iff.mpr (.inr ⟨rfl,(ih len').mpr (.inl tail)⟩)
        · obtain ⟨rfl,rfl⟩ := List.cons.inj eq
          exact List.cons_lt_cons_iff.mpr (.inr ⟨rfl,(ih len').mpr (.inr ⟨rfl,last⟩)⟩)

private theorem code_lt (a b : Nat) : ([[a]] : Word) < [[b]] ↔ a < b := by
  constructor
  · intro h
    rcases List.cons_lt_cons_iff.mp h with inner | ⟨_,bad⟩
    · rcases List.cons_lt_cons_iff.mp inner with lt | ⟨_,bad⟩
      · exact lt
      · exact (no_lt_nil bad).elim
    · exact (no_lt_nil bad).elim
  · intro h
    exact List.cons_lt_cons_iff.mpr (.inl (List.cons_lt_cons_iff.mpr (.inl h)))

theorem likeCode_injective {m n : Option Bool} (h : likeCode m = likeCode n) : m = n := by
  rcases m with _ | (_ | _) <;> rcases n with _ | (_ | _) <;>
    first | rfl | exact absurd h (by decide)

/-- Strict order of two `stepKey`s whose priorities have the same width. -/
theorem stepKey_lt {d e : List Word} (len : d.length = e.length) (m n : Option Bool) :
    stepKey d m < stepKey e n ↔ d < e ∨ (d = e ∧ likeCode m < likeCode n) :=
  (snoc_lt len [[likeCode m]] [[likeCode n]]).trans
    (or_congr Iff.rfl (and_congr Iff.rfl (code_lt _ _)))

theorem stepKey_eq {d e : List Word} (len : d.length = e.length) (m n : Option Bool) :
    stepKey d m = stepKey e n ↔ d = e ∧ m = n := by
  constructor
  · intro same
    have shown : d ++ [[[likeCode m]]] = e ++ [[[likeCode n]]] := same
    obtain ⟨deep,last⟩ := List.append_inj shown len
    exact ⟨deep,likeCode_injective
      (List.cons.inj (List.cons.inj (List.cons.inj last).1).1).1⟩
  · rintro ⟨rfl,rfl⟩
    rfl

/-! ## Local ordinal paths -/

/-- Order on paths of (loss count, like code). Fewer losses is higher; with
equal losses the higher like code is higher; a proper prefix is lower, as in
the list order of the absolute paths. -/
inductive Below : List (Nat × Nat) → List (Nat × Nat) → Prop where
  | short {x xs} : Below [] (x :: xs)
  | rank {l m a b xs ys} (fewer : m < l) : Below ((l,a) :: xs) ((m,b) :: ys)
  | like {l a b xs ys} (higher : a < b) : Below ((l,a) :: xs) ((l,b) :: ys)
  | tail {x xs ys} (rest : Below xs ys) : Below (x :: xs) (x :: ys)

theorem Below.not_nil {xs : List (Nat × Nat)} : ¬ Below xs [] := fun h => by cases h

theorem below_cons {l m a b : Nat} {xs ys : List (Nat × Nat)} :
    Below ((l,a) :: xs) ((m,b) :: ys) ↔
      m < l ∨ (l = m ∧ a < b) ∨ (l = m ∧ a = b ∧ Below xs ys) := by
  constructor
  · intro h
    cases h with
    | rank fewer => exact .inl fewer
    | like higher => exact .inr (.inl ⟨rfl,higher⟩)
    | tail rest => exact .inr (.inr ⟨rfl,rfl,rest⟩)
  · rintro (fewer | ⟨rfl,higher⟩ | ⟨rfl,rfl,rest⟩)
    · exact .rank fewer
    · exact .like higher
    · exact .tail rest

/-- One recorded edge of a descent. -/
structure Edge where
  /-- Complete through-4a priority of the child. -/
  deep : List Word
  /-- Number of sibling incidences with a strictly higher priority. -/
  loss : Nat
  /-- Like/unlike status of the child against the seed. -/
  like : Option Bool

/-- The step used by `RingFullPathPairs`. -/
def Edge.absolute (e : Edge) : List Word := stepKey e.deep e.like
def Edge.ordinal (e : Edge) : Nat × Nat := (e.loss,likeCode e.like)

def absolute (es : List Edge) : Path := es.map Edge.absolute
def ordinals (es : List Edge) : List (Nat × Nat) := es.map Edge.ordinal

/-- One edge of the comparison, given that the two local ordinals reflect the
two absolute priorities. -/
private theorem cons_transport {d e : List Word} {m n : Option Bool} {la lb : Nat}
    {ta tb : List Edge} (len : d.length = e.length) (hlt : d < e ↔ lb < la)
    (heq : d = e ↔ la = lb)
    (below : d = e → (absolute ta < absolute tb ↔ Below (ordinals ta) (ordinals tb)) ∧
      (absolute ta = absolute tb ↔ ordinals ta = ordinals tb)) :
    (absolute (Edge.mk d la m :: ta) < absolute (Edge.mk e lb n :: tb) ↔
      Below (ordinals (Edge.mk d la m :: ta)) (ordinals (Edge.mk e lb n :: tb))) ∧
    (absolute (Edge.mk d la m :: ta) = absolute (Edge.mk e lb n :: tb) ↔
      ordinals (Edge.mk d la m :: ta) = ordinals (Edge.mk e lb n :: tb)) := by
  have klt := stepKey_lt len m n
  have keq := stepKey_eq len m n
  constructor
  · show stepKey d m :: absolute ta < stepKey e n :: absolute tb ↔
      Below ((la,likeCode m) :: ordinals ta) ((lb,likeCode n) :: ordinals tb)
    rw [below_cons]
    constructor
    · intro lt
      rcases List.cons_lt_cons_iff.mp lt with head | ⟨head,rest⟩
      · rcases klt.mp head with less | ⟨eq,code⟩
        · exact .inl (hlt.mp less)
        · exact .inr (.inl ⟨heq.mp eq,code⟩)
      · obtain ⟨eq,bit⟩ := keq.mp head
        exact .inr (.inr ⟨heq.mp eq,congrArg likeCode bit,(below eq).1.mp rest⟩)
    · rintro (fewer | ⟨rank,code⟩ | ⟨rank,code,rest⟩)
      · exact List.cons_lt_cons_iff.mpr (.inl (klt.mpr (.inl (hlt.mpr fewer))))
      · exact List.cons_lt_cons_iff.mpr (.inl (klt.mpr (.inr ⟨heq.mpr rank,code⟩)))
      · have eq := heq.mpr rank
        exact List.cons_lt_cons_iff.mpr
          (.inr ⟨keq.mpr ⟨eq,likeCode_injective code⟩,(below eq).1.mpr rest⟩)
  · show stepKey d m :: absolute ta = stepKey e n :: absolute tb ↔
      (la,likeCode m) :: ordinals ta = (lb,likeCode n) :: ordinals tb
    constructor
    · intro same
      obtain ⟨head,rest⟩ := List.cons.inj same
      obtain ⟨eq,bit⟩ := keq.mp head
      exact congrArg₂ List.cons (Prod.ext (heq.mp eq) (congrArg likeCode bit))
        ((below eq).2.mp rest)
    · intro same
      obtain ⟨head,rest⟩ := List.cons.inj same
      have rank : la = lb := congrArg Prod.fst head
      have code : likeCode m = likeCode n := congrArg Prod.snd head
      have eq := heq.mpr rank
      exact congrArg₂ List.cons (keq.mpr ⟨eq,likeCode_injective code⟩) ((below eq).2.mpr rest)

/-! ## Molecular descents -/

/-- A walk through actual child incidences from a cursor with a through-4a
reading to an endpoint with its reading. At every edge all incidences of the
parent are read (with multiplicity), and the edge records the child's
absolute priority, its loss count among those sibling readings, and its
like/unlike status. No sorted row and no executable order is mentioned. -/
inductive Descent (i : Input) (r : Reader i) (rev : Bool) (seed : RS) :
    Arm i → Branch → List Edge → Arm i → Branch → Prop where
  | stop {q b} (reading : Reading i r rev q b) : Descent i r rev seed q b [] q b
  | step {q b c k sibs rest e l} (reading : Reading i r rev q b) (edge : c ∈ kids i q)
      (siblings : List.Forall₂ (Reading i r rev) (kids i q) sibs)
      (tail : Descent i r rev seed c k rest e l) :
      Descent i r rev seed q b
        (Edge.mk k.deep (losses (sibs.map Branch.deep) k.deep) (likeAt i r rev seed c) :: rest) e l

theorem Descent.reading {i r rev seed q b es e l} (d : Descent i r rev seed q b es e l) :
    Reading i r rev q b := by
  cases d with
  | stop h => exact h
  | step h _ _ _ => exact h

theorem Descent.final {i r rev seed q b es e l} (d : Descent i r rev seed q b es e l) :
    Reading i r rev e l := by
  induction d with
  | stop h => exact h
  | step _ _ _ _ ih => exact ih

/-- Extend a descent by one actual incidence at its endpoint. -/
theorem Descent.snoc {i r rev seed q b es c k d l sibs}
    (walk : Descent i r rev seed q b es c k) (edge : d ∈ kids i c)
    (siblings : List.Forall₂ (Reading i r rev) (kids i c) sibs) (rank : Reading i r rev d l) :
    Descent i r rev seed q b
      (es ++ [Edge.mk l.deep (losses (sibs.map Branch.deep) l.deep) (likeAt i r rev seed d)])
      d l := by
  induction walk with
  | stop reading => exact .step reading edge siblings (.stop rank)
  | step reading first row _ ih => exact .step reading first row (ih edge siblings)

/-! ## Sibling distributions below tied parents -/

private theorem mapM_related {α β : Type} {f : α → Option β} {R : α → β → Prop} {xs : List α}
    {ys : List β} (h : xs.mapM f = some ys) (sound : ∀ a ∈ xs, ∀ b, f a = some b → R a b) :
    List.Forall₂ R xs ys := by
  induction xs generalizing ys with
  | nil =>
    have e : ([] : List α).mapM f = some [] := rfl
    obtain rfl := Option.some.inj (e.symm.trans h)
    exact .nil
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    obtain ⟨u,hu,more⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨us,hus,out⟩ := Option.bind_eq_some_iff.mp more
    obtain rfl := Option.some.inj out
    exact .cons (sound _ List.mem_cons_self _ hu)
      (ih hus (fun a ha => sound a (List.mem_cons_of_mem _ ha)))

private theorem forall2_functional {α β : Type} {R : α → β → Prop}
    (fn : ∀ a x y, R a x → R a y → x = y) {xs : List α} {us vs : List β}
    (l : List.Forall₂ R xs us) (r : List.Forall₂ R xs vs) : us = vs := by
  induction l generalizing vs with
  | nil => cases r; rfl
  | cons head _ ih =>
    cases r with
    | cons head' tail' => exact congrArg₂ List.cons (fn _ _ _ head head') (ih tail')

private theorem related_of_left {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {x : α} (hx : x ∈ xs) : ∃ y ∈ ys, R x y := by
  induction h with
  | nil => contradiction
  | cons head _ ih =>
    rcases List.mem_cons.mp hx with rfl | rest
    · exact ⟨_,List.mem_cons_self,head⟩
    · obtain ⟨b,mem,hb⟩ := ih rest
      exact ⟨b,List.mem_cons_of_mem _ mem,hb⟩

private theorem splitKeys {x y : Branch} (eqn : x.deep = y.deep) :
    x.priorDeep = y.priorDeep ∧ x.word = y.word :=
  ⟨by simpa [Branch.deep] using congrArg List.dropLast eqn,
    by simpa [Branch.deep] using congrArg List.getLast? eqn⟩

private theorem deep_length {i r rev q b} (h : Reading i r rev q b) : b.deep.length = 4 := by
  cases h with
  | node _ _ _ _ _ _ _ _ => rfl

/-- Parents tied through Rule 4a have the same multiset of complete child
priorities, whatever legal readings were chosen for the children and on
whichever inputs, readers and geometries the two parents live. -/
theorem sibling_keys {i j : Input} {r : Reader i} {v : Reader j} {g h : Bool} {q : Arm i}
    {p : Arm j} {a b : Branch} {us ws : List Branch} (ra : Reading i r g q a)
    (rb : Reading j v h p b) (tie : a.deep = b.deep)
    (sa : List.Forall₂ (Reading i r g) (kids i q) us)
    (sb : List.Forall₂ (Reading j v h) (kids j p) ws) :
    (us.map Branch.deep).Perm (ws.map Branch.deep) := by
  obtain ⟨k,ka,pa⟩ := ra.constitution
  obtain ⟨l,kb,pb⟩ := rb.constitution
  obtain rfl := RingPairGateCount.key_eq (RingRetainedChemicalTrace.key_source ka).formed
    (RingRetainedChemicalTrace.key_source kb).formed
    (pa.symm.trans ((splitKeys tie).1.trans pb))
  obtain ⟨x⟩ := ra.queue
  obtain ⟨y⟩ := rb.queue
  have same := RingRetainedUnitPass.child_priorities ka kb x y (splitKeys tie).2
  have left : us = x.childrenRead :=
    forall2_functional (R := Reading i r g) (fun _ _ _ u w => u.unique w) sa
      (mapM_related (R := Reading i r g) x.complete (fun c hc _ hb => x.source c hc hb))
  have right : ws = y.childrenRead :=
    forall2_functional (R := Reading j v h) (fun _ _ _ u w => u.unique w) sb
      (mapM_related (R := Reading j v h) y.complete (fun c hc _ hb => y.source c hc hb))
  rw [left,right]
  exact ((x.second.perm.map Branch.deep).symm.trans (List.Perm.of_eq same)).trans
    (y.second.perm.map Branch.deep)

private theorem occupied {i : Input} {r : Reader i} {rev : Bool} {q c : Arm i} {k : Branch}
    {sibs : List Branch} (siblings : List.Forall₂ (Reading i r rev) (kids i q) sibs)
    (edge : c ∈ kids i q) (rank : Reading i r rev c k) : k.deep ∈ sibs.map Branch.deep := by
  obtain ⟨m,mem,got⟩ := related_of_left siblings edge
  obtain rfl := got.unique rank
  exact List.mem_map_of_mem mem

/-! ## Transport -/

/-- For two descents from parents tied through Rule 4a, the absolute paths
(complete child priority, then like code, per edge) and the local paths
(loss count among the siblings, then like code, per edge) are in the same
strict order and tie together. The reverse strict order is the same
statement with the descents exchanged. -/
theorem transport {i : Input} {r : Reader i} {g : Bool} {s : RS} {q x : Arm i} {a ka : Branch}
    {ea : List Edge} (A : Descent i r g s q a ea x ka) :
    ∀ {j : Input} {v : Reader j} {h : Bool} {t : RS} {p y : Arm j} {b kb : Branch}
      {eb : List Edge}, Descent j v h t p b eb y kb → a.deep = b.deep →
      (absolute ea < absolute eb ↔ Below (ordinals ea) (ordinals eb)) ∧
      (absolute ea = absolute eb ↔ ordinals ea = ordinals eb) := by
  induction A with
  | stop _ =>
    intro j v h t p y b kb eb B _
    cases B with
    | stop _ =>
      exact ⟨⟨fun lt => (no_lt_nil lt).elim,fun lt => (Below.not_nil lt).elim⟩,
        ⟨fun _ => rfl,fun _ => rfl⟩⟩
    | step _ _ _ _ =>
      exact ⟨⟨fun _ => .short,fun _ => nil_lt _ _⟩,
        ⟨fun eq => (List.cons_ne_nil _ _ eq.symm).elim,
          fun eq => (List.cons_ne_nil _ _ eq.symm).elim⟩⟩
  | step reading edge siblings tail ih =>
    intro j v h t p y b kb eb B tie
    cases B with
    | stop _ =>
      exact ⟨⟨fun lt => (no_lt_nil lt).elim,fun lt => (Below.not_nil lt).elim⟩,
        ⟨fun eq => (List.cons_ne_nil _ _ eq).elim,fun eq => (List.cons_ne_nil _ _ eq).elim⟩⟩
    | step reading' edge' siblings' tail' =>
      exact cons_transport
        ((deep_length tail.reading).trans (deep_length tail'.reading).symm)
        (losses_lt_iff (losses_perm (sibling_keys reading reading' tie siblings siblings'))
          (occupied siblings' edge' tail'.reading))
        (losses_eq_iff (losses_perm (sibling_keys reading reading' tie siblings siblings'))
          (occupied siblings edge tail.reading) (occupied siblings' edge' tail'.reading))
        (fun eq => ih tail' eq)

/-! ## The sort keys of `RingFullPathPairs` -/

/-- The root step of a full path: empty priority, no sibling, own status. -/
def rootEdge (i : Input) (r : Reader i) (rev : Bool) (seed : RS) (q : Arm i) : Edge :=
  ⟨[],0,likeAt i r rev seed q⟩

/-- A descent below a reached visit ends at a reached visit whose sort key is
the visit's path extended by the absolute steps of the descent. -/
theorem Descent.reach {i r rev seed} {root : Arm i} {q b es e l}
    (d : Descent i r rev seed q b es e l) :
    ∀ pre : Path, FullReach i r rev seed root ⟨q,pre⟩ →
      FullReach i r rev seed root ⟨e,pre ++ absolute es⟩ := by
  induction d with
  | stop _ =>
    intro pre here
    rw [show pre ++ absolute [] = pre from List.append_nil pre]
    exact here
  | step _ edge _ tail ih =>
    intro pre here
    have next := ih _ (RingFullPathPairs.Oracle.Reach.child here edge tail.reading)
    rw [List.append_assoc] at next
    exact next

/-- Conversely every reached visit of the full-path order is the endpoint of
a descent from the ligand root, and its sort key is exactly the absolute
path of that descent behind the root step. -/
theorem descent_of_reach {i : Input} {r : Reader i} {rev : Bool} {seed : RS} {q : Arm i}
    {b : Branch} (start : Reading i r rev q b) {v : FullVisit i}
    (reached : FullReach i r rev seed q v) :
    ∃ es k, Descent i r rev seed q b es v.cursor k ∧
      v.path = absolute (rootEdge i r rev seed q :: es) := by
  induction reached with
  | root => exact ⟨[],b,.stop start,rfl⟩
  | @child p c k _ edge rank ih =>
    obtain ⟨es,m,walk,path⟩ := ih
    obtain ⟨x⟩ := walk.final.queue
    have siblings : List.Forall₂ (Reading i r rev) (kids i p.cursor) x.childrenRead :=
      mapM_related (R := Reading i r rev) x.complete (fun c hc _ hb => x.source c hc hb)
    refine ⟨es ++ [Edge.mk k.deep (losses (x.childrenRead.map Branch.deep) k.deep)
      (likeAt i r rev seed c)],k,walk.snoc edge siblings rank,?_⟩
    show p.path ++ [stepKey k.deep (likeAt i r rev seed c)] = _
    rw [path]
    simp [absolute,Edge.absolute]

/-- Root step included: the complete `FullVisit.path` keys of two descents
from tied ligand roots against their local ordinal paths. -/
theorem rooted {i j : Input} {r : Reader i} {v : Reader j} {g h : Bool} {s t : RS}
    {q x : Arm i} {p y : Arm j} {a ka b kb : Branch} {ea eb : List Edge}
    (A : Descent i r g s q a ea x ka) (B : Descent j v h t p b eb y kb)
    (tie : a.deep = b.deep) :
    (absolute (rootEdge i r g s q :: ea) < absolute (rootEdge j v h t p :: eb) ↔
      Below (ordinals (rootEdge i r g s q :: ea)) (ordinals (rootEdge j v h t p :: eb))) ∧
    (absolute (rootEdge i r g s q :: ea) = absolute (rootEdge j v h t p :: eb) ↔
      ordinals (rootEdge i r g s q :: ea) = ordinals (rootEdge j v h t p :: eb)) :=
  cons_transport (d := []) (e := []) (la := 0) (lb := 0) rfl
    ⟨fun lt => (no_lt_nil lt).elim,fun lt => (Nat.lt_irrefl 0 lt).elim⟩
    ⟨fun _ => rfl,fun _ => rfl⟩ (fun _ => transport A B tie)

/-- The endpoints of the two descents are reached visits carrying exactly the
compared keys. -/
theorem visit_order {i j : Input} {r : Reader i} {v : Reader j} {g h : Bool} {s t : RS}
    {q x : Arm i} {p y : Arm j} {a ka b kb : Branch} {ea eb : List Edge}
    (A : Descent i r g s q a ea x ka) (B : Descent j v h t p b eb y kb)
    (tie : a.deep = b.deep) :
    FullReach i r g s q ⟨x,absolute (rootEdge i r g s q :: ea)⟩ ∧
    FullReach j v h t p ⟨y,absolute (rootEdge j v h t p :: eb)⟩ ∧
    (absolute (rootEdge i r g s q :: ea) < absolute (rootEdge j v h t p :: eb) ↔
      Below (ordinals (rootEdge i r g s q :: ea)) (ordinals (rootEdge j v h t p :: eb))) ∧
    (absolute (rootEdge i r g s q :: ea) = absolute (rootEdge j v h t p :: eb) ↔
      ordinals (rootEdge i r g s q :: ea) = ordinals (rootEdge j v h t p :: eb)) :=
  ⟨A.reach (root := q) [stepKey [] (likeAt i r g s q)] .root,
    B.reach (root := p) [stepKey [] (likeAt j v h t p)] .root,rooted A B tie⟩

/-- Any two visits reached by the full-path order from ligand roots tied
through Rule 4a: their actual sort keys compare exactly as the local ordinal
paths of the descents that reach them. -/
theorem reached_order {i j : Input} {r : Reader i} {v : Reader j} {g h : Bool} {s t : RS}
    {q : Arm i} {p : Arm j} {a b : Branch} (ra : Reading i r g q a) (rb : Reading j v h p b)
    (tie : a.deep = b.deep) {x : FullVisit i} {y : FullVisit j}
    (hx : FullReach i r g s q x) (hy : FullReach j v h t p y) :
    ∃ ea eb ka kb, Descent i r g s q a ea x.cursor ka ∧ Descent j v h t p b eb y.cursor kb ∧
      (x.path < y.path ↔
        Below (ordinals (rootEdge i r g s q :: ea)) (ordinals (rootEdge j v h t p :: eb))) ∧
      (x.path = y.path ↔
        ordinals (rootEdge i r g s q :: ea) = ordinals (rootEdge j v h t p :: eb)) := by
  obtain ⟨ea,ka,A,pa⟩ := descent_of_reach ra hx
  obtain ⟨eb,kb,B,pb⟩ := descent_of_reach rb hy
  refine ⟨ea,eb,ka,kb,A,B,?_⟩
  rw [pa,pb]
  exact rooted A B tie

/-- Numerical character used in the author implementation, with neutral,
like and unlike offsets 0, 1 and 2 respectively. Lower characters rank first. -/
def Edge.charCode (e : Edge) := 64 + 4 * e.loss + (3 - likeCode e.like)

private theorem char_lt (a b : Edge) :
    b.charCode < a.charCode ↔ b.loss < a.loss ∨
      (a.loss = b.loss ∧ likeCode a.like < likeCode b.like) := by
  rcases a with ⟨da,la,_ | (_ | _)⟩ <;> rcases b with ⟨db,lb,_ | (_ | _)⟩ <;>
    simp only [Edge.charCode,likeCode] <;> omega

private theorem char_eq (a b : Edge) :
    a.charCode = b.charCode ↔ a.ordinal = b.ordinal := by
  have forward := char_lt a b
  have backward := char_lt b a
  change a.charCode = b.charCode ↔ (a.loss,likeCode a.like) = (b.loss,likeCode b.like)
  rw [Prod.mk.injEq]
  omega

private theorem chars_eq (a b : List Edge) :
    a.map Edge.charCode = b.map Edge.charCode ↔ ordinals a = ordinals b := by
  induction a generalizing b with
  | nil => cases b <;> simp [ordinals]
  | cons x xs ih => cases b with
    | nil => simp [ordinals]
    | cons y ys => simp only [List.map_cons,List.cons.injEq,char_eq,ih,ordinals]

/-- In a common sphere all paths have equal length. This also deals with
the fact that the character sorter uses the opposite order direction. -/
private theorem chars_lt {a b : List Edge} (same : a.length = b.length) :
    Below (ordinals a) (ordinals b) ↔ b.map Edge.charCode < a.map Edge.charCode := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => exact ⟨fun h => (Below.not_nil h).elim,fun h => (no_lt_nil h).elim⟩
    | cons _ _ => simp at same
  | cons x xs ih =>
    cases b with
    | nil => simp at same
    | cons y ys =>
      have len : xs.length = ys.length := by simpa using same
      change Below (x.ordinal :: ordinals xs) (y.ordinal :: ordinals ys) ↔
        y.charCode :: ys.map Edge.charCode < x.charCode :: xs.map Edge.charCode
      rw [List.cons_lt_cons_iff,char_lt,char_eq,← ih len]
      simp only [Edge.ordinal,below_cons,Prod.mk.injEq]
      grind

/-- Same-sphere molecular visits compare exactly as ascending packed
priority characters at every step, including ties. -/
theorem reached_characters {i j : Input} {r : Reader i} {v : Reader j} {g h : Bool} {s t : RS}
    {q : Arm i} {p : Arm j} {a b : Branch} (ra : Reading i r g q a) (rb : Reading j v h p b)
    (tie : a.deep = b.deep) {x : FullVisit i} {y : FullVisit j}
    (hx : FullReach i r g s q x) (hy : FullReach j v h t p y) (sphere : x.path.length = y.path.length) :
    ∃ ea eb ka kb, Descent i r g s q a ea x.cursor ka ∧ Descent j v h t p b eb y.cursor kb ∧
      let cx := (rootEdge i r g s q :: ea).map Edge.charCode
      let cy := (rootEdge j v h t p :: eb).map Edge.charCode
      (x.path < y.path ↔ cy < cx) ∧ (x.path = y.path ↔ cx = cy) := by
  obtain ⟨ea,ka,A,pa⟩ := descent_of_reach ra hx
  obtain ⟨eb,kb,B,pb⟩ := descent_of_reach rb hy
  refine ⟨ea,eb,ka,kb,A,B,?_⟩
  rw [pa,pb] at sphere ⊢
  have len : (rootEdge i r g s q :: ea).length = (rootEdge j v h t p :: eb).length := by
    simpa only [absolute,List.length_map] using sphere
  exact ⟨(rooted A B tie).1.trans (chars_lt len),(rooted A B tie).2.trans (chars_eq ..).symm⟩

end TetraStereo.Engine.RingPathRankTransport

assert_kernel_only TetraStereo.Engine.RingPathRankTransport.losses_strict
assert_kernel_only TetraStereo.Engine.RingPathRankTransport.sibling_keys
assert_kernel_only TetraStereo.Engine.RingPathRankTransport.transport
assert_kernel_only TetraStereo.Engine.RingPathRankTransport.descent_of_reach
assert_kernel_only TetraStereo.Engine.RingPathRankTransport.reached_order
assert_kernel_only TetraStereo.Engine.RingPathRankTransport.reached_characters
