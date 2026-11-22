import TetraStereo.Engine.RingChildKeyRecovery

set_option autoImplicit false

namespace TetraStereo.Engine.RingStereoSiblingPass
open RingRetainedChemicalTrace (Word Framed)

/-- One branch in a recursive sequence-rule pass. The two prefixes contain the
previous rules in seniority order, once for the endpoint and once for the full branch. -/
structure Branch where
  priorHead : List Nat
  priorDeep : List Word
  value : Nat
  levels : List (List (List Nat))
  deriving DecidableEq, Repr

def Branch.word (b : Branch) : Word := [b.value] :: b.levels.flatten
def Branch.shallow (b : Branch) := b.priorHead ++ [b.value]
def Branch.deep (b : Branch) := b.priorDeep ++ [b.word]

/-- Legal orders retain every occurrence and respect all strict comparisons.
An occurrence identifier never breaks a tie. -/
structure Legal {α κ : Type} [LinearOrder κ] (key : α → κ) (children row : List α) : Prop where
  perm : row.Perm children
  descending : (row.map key).Pairwise (· ≥ ·)

def order {α κ : Type} [LinearOrder κ] (key : α → κ) (xs : List α) :=
  xs.mergeSort fun a b => decide (key b ≤ key a)

theorem legal_order {α κ : Type} [LinearOrder κ] (key : α → κ) (xs : List α) : Legal key xs (order key xs) := by
  refine ⟨List.mergeSort_perm ..,List.pairwise_map.mpr ?_⟩
  exact (List.pairwise_mergeSort (le := fun a b : α => decide (key b ≤ key a))
    (fun _ _ _ h k => decide_eq_true (le_trans (of_decide_eq_true k) (of_decide_eq_true h)))
    (fun a b => by simpa using le_total (key b) (key a)) xs).imp fun h => of_decide_eq_true h

/-- Exact freedom within ties: a permutation is legal iff every position
retains the key of the sorted row. This also covers repeated nonterminal arms. -/
theorem legal_iff {α κ : Type} [LinearOrder κ] (key : α → κ) (xs ys : List α) :
    Legal key xs ys ↔ ys.Perm xs ∧ ys.map key = (order key xs).map key := by
  have canon := legal_order key xs
  constructor
  · intro h
    exact ⟨h.perm,List.Perm.eq_of_pairwise (fun _ _ _ _ ab ba => le_antisymm ba ab)
      h.descending canon.descending ((h.perm.trans canon.perm.symm).map _)⟩
  · rintro ⟨p,eqn⟩; exact ⟨p,eqn ▸ canon.descending⟩

private theorem project {α κ β : Type} [LinearOrder κ] {key : α → κ} {xs a b : List α}
    (left : Legal key xs a) (right : Legal key xs b) (f : α → β)
    (same : ∀ u ∈ xs, ∀ v ∈ xs, key u = key v → f u = f v) : a.map f = b.map f := by
  have aligned := ((legal_iff ..).mp left).2.trans ((legal_iff ..).mp right).2.symm
  apply List.ext_getElem
  · simp [left.perm.length_eq,right.perm.length_eq]
  · intro j hj hk
    simp only [List.length_map] at hj hk
    simp only [List.getElem_map]
    apply same _ (left.perm.mem_iff.mp (List.getElem_mem hj)) _ (right.perm.mem_iff.mp (List.getElem_mem hk))
    have h := List.getElem_of_eq aligned (i := j) (by simpa using hj)
    simpa only [List.getElem_map] using h

abbrev Layers := List (List (List Nat))

/-- At each parent, compare the shallow row first, compare the deep row next,
then enqueue only the deep row for expansion at the following distance. -/
def rows (sh de : List Branch) : Layers :=
  [sh.map Branch.value,de.map Branch.value] :: (de.map Branch.levels).foldr RingChildKeyRecovery.interleave []

private abbrev forest (bs : List Branch) := (bs.map Branch.levels).foldr RingChildKeyRecovery.interleave []

private theorem interleave_nil (x : Layers) : RingChildKeyRecovery.interleave x [] = x := by cases x <;> rfl

private theorem interleave_assoc : ∀ (x y z : Layers), RingChildKeyRecovery.interleave (RingChildKeyRecovery.interleave x y) z =
    RingChildKeyRecovery.interleave x (RingChildKeyRecovery.interleave y z)
  | [],_,_ => rfl
  | _::_,[],_ => rfl
  | _::_,_::_,[] => by simp [interleave_nil]
  | a::x,b::y,c::z => by simp only [RingChildKeyRecovery.interleave,List.append_assoc,interleave_assoc x y z]

private theorem forest_append (x y : List Branch) : forest (x++y) = RingChildKeyRecovery.interleave (forest x) (forest y) := by
  induction x with
  | nil => rfl
  | cons a x ih =>
    change RingChildKeyRecovery.interleave a.levels (forest (x++y)) = _
    rw [ih,← interleave_assoc]
    rfl

/-- Remaining parent rows, split between the current sphere and children
already queued for the next sphere. -/
def queueRows (current waiting : List Branch) : Word :=
  match forest current with
  | [] => (forest waiting).flatten
  | row::rest => row ++ (RingChildKeyRecovery.interleave (forest waiting) rest).flatten

theorem queue_start (b : Branch) : b.word = [b.value] :: queueRows [b] [] := by
  have one : forest [b] = b.levels := interleave_nil _
  unfold queueRows Branch.word
  rw [one]
  cases b.levels <;> rfl

theorem queue_rotate (waiting : List Branch) : queueRows [] waiting = queueRows waiting [] := by
  unfold queueRows
  change (forest waiting).flatten = _
  cases forest waiting <;> rfl

theorem queue_pop {parent : Branch} {sh de : List Branch} (built : parent.levels = rows sh de)
    (current waiting : List Branch) :
    queueRows (parent::current) waiting = [sh.map Branch.value,de.map Branch.value] ++
      queueRows current (waiting ++ de) := by
  have step : forest (parent::current) = RingChildKeyRecovery.interleave parent.levels (forest current) := rfl
  unfold queueRows
  rw [step,built,forest_append]
  change (match RingChildKeyRecovery.interleave (_ :: forest de) (forest current) with
    | [] => _ | row::rest => row ++ (RingChildKeyRecovery.interleave (forest waiting) rest).flatten) = _
  cases forest current <;> simp [RingChildKeyRecovery.interleave,interleave_assoc]

/-- FIFO visiting a vertex once uses its deep slot. The shallow row at
each parent was inspected by the recursive comparator before enqueuing. -/
def deepValues : Word → List Nat
  | _::de::rest => de ++ deepValues rest
  | _ => []

def Branch.stream (b : Branch) := b.value :: deepValues b.levels.flatten

private def pending (current waiting : List Branch) :=
  (current ++ waiting).map Branch.value ++ deepValues (queueRows current waiting)

theorem pending_step {b : Branch} {sh de : List Branch} (layout : b.levels = rows sh de)
    (xs ys : List Branch) : pending (b::xs) ys = b.value :: pending xs (ys++de) := by
  simp [pending,queue_pop layout,deepValues,List.append_assoc]

/-- A traversal may select fresh, independently legal rows at every pop.
It enqueues the complete deep row behind the current waiting queue. -/
inductive Visits {α : Type} (allowed : α → List α → List α → Prop) :
    List α → List α → List α → Prop where
  | stop : Visits allowed [] [] []
  | rotate {b bs out} (next : Visits allowed (b::bs) [] out) : Visits allowed [] (b::bs) out
  | pop {b xs ys sh de out} (ok : allowed b sh de)
      (next : Visits allowed xs (ys++de) out) : Visits allowed (b::xs) ys (b :: out)

theorem Visits.map {α β : Type} {legal : α → List α → List α → Prop} {after : β → List β → List β → Prop}
    (f : α → β) (step : ∀ p s d, legal p s d → after (f p) (s.map f) (d.map f))
    {xs ys out} (w : Visits legal xs ys out) : Visits after (xs.map f) (ys.map f) (out.map f) := by
  induction w with
  | stop => exact .stop
  | rotate _ ih => exact .rotate ih
  | pop ok _ ih => exact .pop (step _ _ _ ok) (List.map_append .. ▸ ih)

/-- Non-vacuity of the FIFO judgment for a molecular expansion whose children
have a strictly smaller cursor budget. A leaf drains its own queue entry. -/
theorem visits_exist {α : Type} {allowed : α → List α → List α → Prop}
    (good : Nat → α → Prop) (empty : ∀ b, ¬ good 0 b)
    (step : ∀ n b, good (n+1) b → ∃ sh de, allowed b sh de ∧ ∀ c ∈ de, good n c) :
    ∀ n qs, (∀ b ∈ qs, good n b) → ∃ out, Visits allowed qs [] out := by
  intro n
  induction n with
  | zero =>
    intro qs covered
    cases qs with
    | nil => exact ⟨[],.stop⟩
    | cons b bs => exact (empty b (covered b List.mem_cons_self)).elim
  | succ n ih =>
    have drain (qs ys : List α) (ok : ∀ b ∈ qs, good (n+1) b) :
        ∃ kids, (∀ c ∈ kids, good n c) ∧ ∀ tail, Visits allowed [] (ys++kids) tail →
          Visits allowed qs ys (qs++tail) := by
      induction qs generalizing ys with
      | nil => exact ⟨[],by simp,fun _ next => by simpa using next⟩
      | cons b bs rest =>
        obtain ⟨sh,de,legal,smaller⟩ := step n b (ok b List.mem_cons_self)
        obtain ⟨kids,small,finish⟩ := rest (ys++de) (fun c hc => ok c (List.mem_cons_of_mem _ hc))
        exact ⟨de++kids,by simpa only [List.forall_mem_append] using And.intro smaller small,
          fun tail next => .pop legal (finish tail (by simpa only [List.append_assoc] using next))⟩
    intro qs ok
    obtain ⟨kids,small,finish⟩ := drain qs [] ok
    obtain ⟨out,next⟩ := ih kids small
    apply Exists.intro (qs++out)
    apply finish
    simp only [List.nil_append]
    cases kids with
    | nil => exact next
    | cons _ _ => exact .rotate next

theorem fifo_stream {allowed : Branch → List Branch → List Branch → Prop}
    (sound : ∀ b sh de, allowed b sh de → b.levels = rows sh de)
    {b out} (walk : Visits allowed [b] [] out) : out.map Branch.value = b.stream := by
  have queue {xs ys word} (w : Visits allowed xs ys word) : word.map Branch.value = pending xs ys := by
    induction w with
    | stop => rfl
    | rotate _ ih => simpa only [pending,List.append_nil,List.nil_append,queue_rotate] using ih
    | pop ok _ ih => rw [pending_step (sound _ _ _ ok),List.map_cons,ih]
  have eqn := queue walk
  have root := (List.cons.inj (queue_start b)).2
  simpa only [pending,List.append_nil,List.map_singleton,List.singleton_append,Branch.stream,← root] using eqn

/-- Each shallow row records the arity of the vertex about to leave the
queue. The following deep row is the enqueue order for exactly that vertex. -/
def arities : Word → List Nat
  | sh::_::rest => sh.length :: arities rest
  | _ => []

def Branch.degree (b : Branch) := ((b.word[1]?).getD []).length

theorem fifo_degrees {allowed : Branch → List Branch → List Branch → Prop}
    (sound : ∀ b sh de, allowed b sh de → b.levels = rows sh de)
    {b out} (walk : Visits allowed [b] [] out) : out.map Branch.degree = arities b.levels.flatten := by
  have queue {xs ys word} (w : Visits allowed xs ys word) :
      word.map Branch.degree = arities (queueRows xs ys) := by
    induction w with
    | stop => rfl
    | rotate _ ih => simpa only [queue_rotate] using ih
    | @pop a xs ys sh de out ok _ ih =>
      have layout := sound _ _ _ ok
      have degree : a.degree = (sh.map Branch.value).length := by simp [Branch.degree,Branch.word,layout,rows]
      rw [List.map_cons,degree,ih,queue_pop layout]
      rfl
  simpa only [← (List.cons.inj (queue_start b)).2] using queue walk

/-- Keep the root and the nonterminal queued children, as required for a
reference-dependent pair traversal. Leaves remain present in the local sorts. -/
def projected (values degrees : List Nat) : List Nat :=
  values.head?.toList ++ (values.tail.zip degrees.tail).filterMap fun (v,d) => if d = 0 then none else some v

def Branch.nonterminalStream (b : Branch) := projected b.stream (arities b.levels.flatten)

theorem fifo_nonterminal {allowed : Branch → List Branch → List Branch → Prop}
    (sound : ∀ b sh de, allowed b sh de → b.levels = rows sh de)
    {b out} (walk : Visits allowed [b] [] out) :
    projected (out.map Branch.value) (out.map Branch.degree) = b.nonterminalStream := by
  rw [fifo_stream sound walk,fifo_degrees sound walk]
  rfl

theorem forest_framed (ds : List Branch) (h : ∀ c ∈ ds, Framed 2 c.levels) :
      Framed (2*ds.length) ((ds.map Branch.levels).foldr RingChildKeyRecovery.interleave []) := by
    induction ds with
    | nil => rfl
    | cons c cs ih =>
      simpa [Nat.mul_add,Nat.add_comm] using RingChildKeyRecovery.combined (h c List.mem_cons_self)
        (ih (fun _ hc => h _ (List.mem_cons_of_mem _ hc)))

theorem rows_framed {xs sh de : List Branch} (a : sh.Perm xs) (b : de.Perm xs)
    (formed : ∀ c ∈ xs, Framed 2 c.levels) : Framed 2 (rows sh de) := by
  refine ⟨by decide,rfl,?_⟩
  change Framed ((sh.map Branch.value).length + ((de.map Branch.value).length + 0)) _
  simp only [List.length_map,Nat.add_zero,a.length_eq,← b.length_eq]
  simpa only [two_mul] using
    forest_framed de (fun c hc => formed c (b.mem_iff.mp hc))

private theorem recover_levels {xs ys : List Branch} (size : xs.length = ys.length)
    (lx : ∀ x ∈ xs, Framed 2 x.levels) (ly : ∀ y ∈ ys, Framed 2 y.levels)
    (same : (xs.map Branch.levels).foldr RingChildKeyRecovery.interleave [] =
      (ys.map Branch.levels).foldr RingChildKeyRecovery.interleave []) :
    xs.map Branch.levels = ys.map Branch.levels := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at size
    | cons y ys =>
      have length := Nat.succ.inj size
      have left := fun c (h : c ∈ xs) => lx c (List.mem_cons_of_mem _ h)
      have right := fun c (h : c ∈ ys) => ly c (List.mem_cons_of_mem _ h)
      obtain ⟨top,tail⟩ := RingChildKeyRecovery.separate (lx x List.mem_cons_self)
        (ly y List.mem_cons_self) (forest_framed xs left) (length ▸ forest_framed ys right) same
      exact congrArg₂ List.cons top (ih length left right tail)

/-- Equal parent layers recover each child's complete current-rule word in
deep order, including its boundary with the next child in every sphere. -/
theorem recover_words {a b x y : List Branch}
    (lx : ∀ c ∈ x, Framed 2 c.levels) (ly : ∀ c ∈ y, Framed 2 c.levels)
    (same : rows a x = rows b y) : x.map Branch.word = y.map Branch.word := by
  obtain ⟨first,forest⟩ := List.cons.inj same
  have heads := (List.cons.inj (List.cons.inj first).2).1
  have size : x.length = y.length := by simpa using congrArg List.length heads
  have levels := recover_levels size lx ly forest
  apply List.ext_getElem
  · simpa only [List.length_map] using size
  · intro j hj hk
    simp only [List.length_map] at hj hk
    have v := List.getElem_of_eq heads (i := j) (by simpa using hj)
    have h := List.getElem_of_eq levels (i := j) (by simpa using hj)
    simp only [List.getElem_map] at v h ⊢
    simp only [Branch.word,v,h]

private theorem last_eq {α : Type} {xs ys : List α} {a b : α} (h : xs ++ [a] = ys ++ [b]) : a = b := by
  simpa using congrArg List.getLast? h

/-- All choices satisfying the molecular shallow and deep comparisons emit
identical parent rows and identical remaining FIFO layers. -/
theorem rows_unique {xs s t u v : List Branch} (a : Legal Branch.shallow xs s) (b : Legal Branch.deep xs t)
    (c : Legal Branch.shallow xs u) (d : Legal Branch.deep xs v)
    (formed : ∀ x ∈ xs, Framed 2 x.levels) : rows s t = rows u v := by
  have tied (x y : Branch) (h : x.deep = y.deep) := List.cons.inj (last_eq h : x.word = y.word)
  have sh := project a c Branch.value (fun _ _ _ _ h => last_eq h)
  have de := project b d Branch.value (fun x _ y _ h => (List.cons.inj (tied x y h).1).1)
  have lv := project b d Branch.levels (fun x hx y hy h => Framed.unique (formed x hx) (formed y hy) (tied x y h).2)
  simp only [rows,sh,de,lv]

end TetraStereo.Engine.RingStereoSiblingPass

assert_kernel_only TetraStereo.Engine.RingStereoSiblingPass.legal_iff
assert_kernel_only TetraStereo.Engine.RingStereoSiblingPass.rows_unique
assert_kernel_only TetraStereo.Engine.RingStereoSiblingPass.rows_framed

assert_kernel_only TetraStereo.Engine.RingStereoSiblingPass.recover_words

assert_kernel_only TetraStereo.Engine.RingStereoSiblingPass.queue_start
assert_kernel_only TetraStereo.Engine.RingStereoSiblingPass.queue_pop

assert_kernel_only TetraStereo.Engine.RingStereoSiblingPass.fifo_stream

assert_kernel_only TetraStereo.Engine.RingStereoSiblingPass.fifo_nonterminal

assert_kernel_only TetraStereo.Engine.RingStereoSiblingPass.visits_exist
