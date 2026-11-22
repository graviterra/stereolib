import TetraStereo.Engine.RingClosedPairGroup
import TetraStereo.Engine.RingRetainedChemicalPreorder

set_option autoImplicit false

namespace TetraStereo.Engine.RingSeededFIFOTransport
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm)
open RingNestedActivePair (Reader)
open RingClosedPairGroup (FIFO projected upperAt word)

/-- The PairList observation at one molecular cursor: an absent or lowercase
publication contributes no bit. The seed and geometry are independent on each side. -/
def observation {i : Input} (read : Reader i) (rev : Bool) (seed : RS) (q : Arm i) :=
  (upperAt read rev q).map fun h => (h == seed).toNat

/-- The key records the already justified priority of a child under the active
reference at its parent. Ties allow any permutation inside their priority block. -/
def Admissible {i : Input} {K : Type} [LinearOrder K] (key : Arm i → Arm i → K)
    (parent : Arm i) (row : List (Arm i)) : Prop :=
  (row.map (key parent)).Pairwise (· ≥ ·)

private def ordered {i : Input} {K : Type} [LinearOrder K] (key : Arm i → Arm i → K) (q : Arm i) :=
  (projected i q).mergeSort fun x y => decide (key q y ≤ key q x)

private theorem ordered_perm {i : Input} {K : Type} [LinearOrder K] (key : Arm i → Arm i → K) (q : Arm i) :
    (ordered key q).Perm (projected i q) := List.mergeSort_perm ..

private theorem ordered_allowed {i : Input} {K : Type} [LinearOrder K] (key : Arm i → Arm i → K) (q : Arm i) :
    Admissible key q (ordered key q) := by
  apply List.pairwise_map.mpr
  have sorted := List.pairwise_mergeSort (le := fun a b : Arm i => decide (key q b ≤ key q a))
    (fun _ _ _ x y => decide_eq_true (le_trans (of_decide_eq_true y) (of_decide_eq_true x)))
    (fun a b => by simpa using le_total (key q b) (key q a)) (projected i q)
  exact sorted.imp fun h => of_decide_eq_true h



private theorem prepend_layer {i : Input} {K : Type} [LinearOrder K] (key : Arm i → Arm i → K)
    (level pending out : List (Arm i))
    (tail : FIFO i (Admissible key) (pending ++ level.flatMap (ordered key)) out) :
    FIFO i (Admissible key) (level ++ pending) (level ++ out) := by
  induction level generalizing pending with
  | nil => simpa using tail
  | cons q rest ih =>
    apply FIFO.step (ordered_perm key q) (ordered_allowed key q)
    have below := ih (pending ++ ordered key q) (by simpa only [List.flatMap_cons,List.append_assoc] using tail)
    change FIFO i (Admissible key) ((rest ++ pending) ++ ordered key q) (rest ++ out)
    rw [List.append_assoc]
    exact below

/-- Every original carrier forest of valid reroot cursors has a complete
priority-sorted FIFO. Its existence uses the decreasing molecular cursor budget
and permits an initial queue with multiple parents or with an inward direction. -/
theorem walk_exists {i : Input} {K : Type} [LinearOrder K] (key : Arm i → Arm i → K)
    (qs : List (Arm i)) (valid : ∀ a ∈ qs, i.certified.LocalizedRerootCursorValid a) :
    ∃ out, FIFO i (Admissible key) qs out := by
  suffices recursor : ∀ n (row : List (Arm i)), (∀ a ∈ row, i.certified.LocalizedRerootCursorValid a ∧
      i.certified.localizedRerootCursorBudget a < n) → ∃ out, FIFO i (Admissible key) row out by
    exact recursor _ qs fun a ha => ⟨valid a ha,Nat.lt_succ_of_le (i.certified.localizedRerootCursorBudget_le_twice a)⟩
  intro n
  induction n with
  | zero =>
    intro row covered
    cases row with
    | nil => exact ⟨[],.stop⟩
    | cons a as => exact False.elim (Nat.not_lt_zero _ (covered a List.mem_cons_self).2)
  | succ n ih =>
    intro row covered
    obtain ⟨out,below⟩ := ih (row.flatMap (ordered key)) (by
      intro c member
      obtain ⟨a,ha,hc⟩ := List.mem_flatMap.mp member
      have child := List.mem_of_mem_filter ((ordered_perm key a).mem_iff.mp hc)
      have frame := i.certified.executableLocalizedRerootChildren_declarative a
      have smaller := i.certified.localizedRerootChild_budget_lt a c _ (covered a ha).1 frame child
      exact ⟨i.certified.localizedRerootChild_valid a c _ frame child,lt_of_lt_of_le smaller (Nat.le_of_lt_succ (covered a ha).2)⟩)
    exact ⟨row ++ out,by simpa only [List.append_nil] using prepend_layer key row [] out (by simpa using below)⟩

/-- Local molecular conditions for transporting a traversal. A related pair has
the same accepted observation, the same multiset of child priorities, and related
children at every common priority. The last clause checks *all* ways to pair a tie.
The relation can be restricted to the actual two arms and their descendants. -/
structure Correspondence {i j : Input} {K : Type} [LinearOrder K]
    (left : Reader i) (right : Reader j) (lr rr : Bool) (ls rs : RS)
    (lk : Arm i → Arm i → K) (rk : Arm j → Arm j → K)
    (related : Arm i → Arm j → Prop) : Prop where
  published : ∀ {a b}, related a b → (left a.occurrence).isSome = true ∧ (right b.occurrence).isSome = true
  observed : ∀ {a b}, related a b → observation left lr ls a = observation right rr rs b
  priorities : ∀ {a b}, related a b →
    ((projected i a).map (lk a)).Perm ((projected j b).map (rk b))
  children : ∀ {a b}, related a b → ∀ x ∈ projected i a, ∀ y ∈ projected j b,
    lk a x = rk b y → related x y

private theorem align {i j : Input} {K : Type} [LinearOrder K] {left right lr rr ls rs}
    {lk : Arm i → Arm i → K} {rk : Arm j → Arm j → K} {related : Arm i → Arm j → Prop}
    (h : Correspondence left right lr rr ls rs lk rk related) {a b} (matched : related a b)
    {xs ys} (px : xs.Perm (projected i a)) (py : ys.Perm (projected j b))
    (sx : Admissible lk a xs) (sy : Admissible rk b ys) : List.Forall₂ related xs ys := by
  have perm := (px.map (lk a)).trans ((h.priorities matched).trans (py.map (rk b)).symm)
  have keys := List.Perm.eq_of_pairwise (fun _ _ _ _ ab ba => le_antisymm ba ab) sx sy perm
  apply List.forall₂_iff_get.mpr
  refine ⟨by simpa using perm.length_eq,?_⟩
  intro n hn hm
  apply h.children matched _ (px.mem_iff.mp (List.get_mem ..)) _ (py.mem_iff.mp (List.get_mem ..))
  have eqn := List.getElem_of_eq keys (i := n) (by simpa using hn)
  simpa using eqn

/-- The two complete traversals can make independent choices at every tied
sibling block. The resulting output cursors remain related in FIFO order. -/
theorem aligned_visits {i j : Input} {K : Type} [LinearOrder K] {left right lr rr ls rs}
    {lk : Arm i → Arm i → K} {rk : Arm j → Arm j → K} {related : Arm i → Arm j → Prop}
    (h : Correspondence left right lr rr ls rs lk rk related) {qs ts xs ys}
    (start : List.Forall₂ related qs ts) (lw : FIFO i (Admissible lk) qs xs)
    (rw' : FIFO j (Admissible rk) ts ys) : List.Forall₂ related xs ys := by
  induction lw generalizing ts ys with
  | stop => cases start; cases rw'; exact .nil
  | step lp lo _ ih =>
    cases start with
    | cons parent pending =>
      cases rw' with
      | step rp ro next =>
        exact .cons parent (ih (List.rel_append pending (align h parent lp rp lo ro)) next)

private theorem filtered {α β : Type} {l : α → Option Nat} {r : β → Option Nat}
    {rel : α → β → Prop} (same : ∀ {a b}, rel a b → l a = r b)
    {xs ys} (seq : List.Forall₂ rel xs ys) : xs.filterMap l = ys.filterMap r := by
  induction seq with
  | nil => rfl
  | cons h _ ih => simp only [List.filterMap_cons,same h,ih]

/-- Equality of the complete PairList words attached to two actual molecular
FIFO traversals, for independently chosen seeds, geometries and tie orders. -/
theorem word_eq {i j : Input} {K : Type} [LinearOrder K] {left right lr rr ls rs}
    {lk : Arm i → Arm i → K} {rk : Arm j → Arm j → K} {related : Arm i → Arm j → Prop}
    (h : Correspondence left right lr rr ls rs lk rk related) {qs ts xs ys}
    (start : List.Forall₂ related qs ts) (lw : FIFO i (Admissible lk) qs xs)
    (rw' : FIFO j (Admissible rk) ts ys) : word left lr ls xs = word right rr rs ys := by
  have eqn := filtered (rel := related) (l := observation left lr ls) (r := observation right rr rs)
    (fun matched => h.observed matched) (aligned_visits h start lw rw')
  simpa only [word,List.map_filterMap,observation,List.cons.injEq,and_true] using congrArg (fun v => [v]) eqn




theorem tied_sibling_exchange {i : Input} {K : Type} [LinearOrder K] {read rev seed}
    {key : Arm i → Arm i → K} {rel : Arm i → Arm i → Prop}
    (h : Correspondence read read rev rev seed seed key key rel) {parent a b}
    (aChild : a ∈ projected i parent) (bChild : b ∈ projected i parent) (tie : key parent a = key parent b)
    (self : rel parent parent) (pre post xs ys : List (Arm i))
    (pending : ∀ x ∈ pre ++ post, rel x x)
    (left : FIFO i (Admissible key) (pre ++ a :: b :: post) xs)
    (right : FIFO i (Admissible key) (pre ++ b :: a :: post) ys) :
    word read rev seed xs = word read rev seed ys := by
  have before := List.forall₂_same.mpr (fun x hx => pending x (List.mem_append_left _ hx))
  have after := List.forall₂_same.mpr (fun x hx => pending x (List.mem_append_right _ hx))
  exact word_eq h (List.rel_append before (.cons (h.children self _ aChild _ bChild tie)
    (.cons (h.children self _ bChild _ aChild tie.symm) after))) left right

section Checker

variable {i j : Input} {K : Type} [LinearOrder K]
    (left : Reader i) (right : Reader j) (lr rr : Bool) (ls rs : RS)
    (lk : Arm i → Arm i → K) (rk : Arm j → Arm j → K)

/-- Inspect every pair of actual children in a matching priority bucket, including
all alternatives in a tied nonterminal block. The bound counts levels of the
left retained cursor. Each visit has a known publication or a known absence. -/
def check : Nat → Arm i → Arm j → Bool
  | 0,_,_ => false
  | n+1,a,b =>
    decide ((left a.occurrence).isSome = true ∧ (right b.occurrence).isSome = true ∧
      observation left lr ls a = observation right rr rs b ∧
      ((projected i a).map (lk a)).Perm ((projected j b).map (rk b))) &&
        (projected i a).all (fun x => (projected j b).all fun y =>
          if lk a x = rk b y then check n x y else true)

private theorem checked_relation :
    Correspondence left right lr rr ls rs lk rk (fun a b => ∃ n, check left right lr rr ls rs lk rk n a b = true) := by
  have step {a b} (h : ∃ n, check left right lr rr ls rs lk rk n a b = true) :
      ((left a.occurrence).isSome = true ∧ (right b.occurrence).isSome = true ∧
        observation left lr ls a = observation right rr rs b ∧
        ((projected i a).map (lk a)).Perm ((projected j b).map (rk b))) ∧
      (∀ x ∈ projected i a, ∀ y ∈ projected j b, lk a x = rk b y →
        ∃ n, check left right lr rr ls rs lk rk n x y = true) := by
    obtain ⟨_ | n,hit⟩ := h
    · contradiction
    · obtain ⟨root,below⟩ := Bool.and_eq_true_iff.mp hit
      refine ⟨of_decide_eq_true root,?_⟩
      intro x hx y hy same
      have pass := List.all_eq_true.mp (List.all_eq_true.mp below x hx) y hy
      exact ⟨n,by simpa only [if_pos same] using pass⟩
  exact ⟨fun h => ⟨(step h).1.1,(step h).1.2.1⟩,fun h => (step h).1.2.2.1,
    fun h => (step h).1.2.2.2,fun h => (step h).2⟩

/-- At the molecular cursor budget, the finite test recognizes exactly the rooted
correspondences above. Existence of a guessed relation, exploration depth or
completion of a chosen tie order need not be an external certificate. -/
theorem check_iff (a : Arm i) (b : Arm j) (valid : i.certified.LocalizedRerootCursorValid a) :
    check left right lr rr ls rs lk rk (i.certified.localizedRerootCursorBudget a + 1) a b = true ↔
    ∃ rel : Arm i → Arm j → Prop, Correspondence left right lr rr ls rs lk rk rel ∧ rel a b := by
  constructor
  · intro hit
    exact ⟨_,checked_relation left right lr rr ls rs lk rk,_,hit⟩
  · rintro ⟨rel,h,same⟩
    suffices done : ∀ n x y, i.certified.LocalizedRerootCursorValid x →
        i.certified.localizedRerootCursorBudget x < n → rel x y →
        check left right lr rr ls rs lk rk n x y = true from
      done _ a b valid (Nat.lt_succ_self _) same
    intro n
    induction n with
    | zero => intro x y _ bound; exact False.elim (Nat.not_lt_zero _ bound)
    | succ n ih =>
      intro x y good bound xy
      apply Bool.and_eq_true_iff.mpr
      refine ⟨decide_eq_true ⟨(h.published xy).1,(h.published xy).2,h.observed xy,h.priorities xy⟩,List.all_eq_true.mpr ?_⟩
      intro u hu
      apply List.all_eq_true.mpr
      intro v hv
      split
      next eqn =>
        have child := List.mem_of_mem_filter hu
        have frame := i.certified.executableLocalizedRerootChildren_declarative x
        have smaller := i.certified.localizedRerootChild_budget_lt x u _ good frame child
        exact ih u v (i.certified.localizedRerootChild_valid x u _ frame child)
          (lt_of_lt_of_le smaller (Nat.le_of_lt_succ bound)) (h.children xy u hu v hv eqn)
      next => rfl

/-- An executable positive test on two molecular roots certifies the same full
accepted PairList word for every independent choice of both traversals. -/
theorem checked_word {n a b xs ys} (hit : check left right lr rr ls rs lk rk n a b = true)
    (lw : FIFO i (Admissible lk) [a] xs) (rw' : FIFO j (Admissible rk) [b] ys) :
    word left lr ls xs = word right rr rs ys :=
  word_eq (checked_relation left right lr rr ls rs lk rk) (.cons ⟨n,hit⟩ .nil) lw rw'

end Checker

/-- Use the complete, rule-major constitutional key at the actual retained
child. A successful check here allows every refinement of constitutional ties,
including any later seed-dependent sibling ranking that preserves earlier priority. -/
def chemicalKey (i : Input) (_ : Arm i) (child : Arm i) :=
  ((RingRetainedChemicalTrace.key? i child).map RingRetainedChemicalPreorder.orderWord).getD []

/-- Both key comparisons are attached to their actual children. Their order is
the outcome of the complete retained molecular trace, including ties. -/
theorem chemical_priority {i : Input} (p a b : Arm i) (la : a ∈ projected i p) (lb : b ∈ projected i p) :
    ∃ t, RingRetainedChemicalTrace.trace? i a b = some t ∧
      cipTraceOutcome t = compare (chemicalKey i p a) (chemicalKey i p b) := by
  have valid {q : Arm i} (member : q ∈ projected i p) : i.certified.LocalizedRerootCursorValid q :=
    i.certified.localizedRerootChild_valid p q _ (i.certified.executableLocalizedRerootChildren_declarative p)
      (List.mem_of_mem_filter member)
  obtain ⟨x,hx⟩ := RingRetainedChemicalCoverage.key_total i (RingRetainedChemicalCoverage.admitted_atoms i) a (valid la)
  obtain ⟨y,hy⟩ := RingRetainedChemicalCoverage.key_total i (RingRetainedChemicalCoverage.admitted_atoms i) b (valid lb)
  refine ⟨RingRetainedChemicalTrace.keyTrace x y,by simp [RingRetainedChemicalTrace.trace?,hx,hy],?_⟩
  simpa only [chemicalKey,hx,hy,Option.map_some,Option.getD_some] using RingRetainedChemicalPreorder.compare_word x y

/-- Executable comparison using no supplied priority function or guessed
correspondence. It certifies every earlier-priority-preserving traversal on both arms. -/
def chemicalCheck {i j : Input} (l : Reader i) (r : Reader j) (lr rr : Bool) (ls rs : RS) (a : Arm i) (b : Arm j) :=
  check l r lr rr ls rs (chemicalKey i) (chemicalKey j) (i.certified.localizedRerootCursorBudget a + 1) a b

theorem chemical_checked_word {i j : Input} {l : Reader i} {r : Reader j} {lr rr ls rs a b xs ys}
    (hit : chemicalCheck l r lr rr ls rs a b = true) (lw : FIFO i (Admissible (chemicalKey i)) [a] xs)
    (rw' : FIFO j (Admissible (chemicalKey j)) [b] ys) : word l lr ls xs = word r rr rs ys :=
  checked_word l r lr rr ls rs _ _ hit lw rw'

/-- Cursors that can actually be enqueued from this branch in the molecular
PairList traversal. Terminal children outside the queue impose no publication premise. -/
inductive Enqueued {i : Input} (root : Arm i) : Arm i → Prop where
  | root : Enqueued root root
  | child {p q} : Enqueued root p → q ∈ projected i p → Enqueued root q

private theorem reflected_observation {i : Input} {read : Reader i} {q : Arm i}
    {labels} (hit : read q.occurrence = some labels)
    (physical : labels.all RingNestedActivePair.consistent = true) (seed : RS) :
    observation read false seed q = observation read true seed.swap q := by
  cases labels with
  | none => simp [observation,upperAt,hit,RingNestedActivePair.upper]
  | some v =>
    obtain ⟨a,b⟩ := v
    rcases a with ha | pa <;> rcases b with hb | pb
    · cases ha <;> cases hb <;> cases seed <;>
        simp_all [observation,upperAt,RingNestedActivePair.consistent,RingNestedActivePair.upper,RS.swap] <;> decide
    · contradiction
    · contradiction
    · simp [observation,upperAt,hit,RingNestedActivePair.upper]

/-- An arbitrary-depth success domain for the executable chemical checker.
If no two distinct nonterminal siblings share a constitutional priority word,
all observed descriptor streams survive reflection with the active seed swapped.
This includes chains of any length, and permits arbitrary branching and mixtures of
uppercase, lowercase and absent publications. -/
theorem separated_mirror_check {i : Input} (read : Reader i) (root : Arm i) (seed : RS)
    (valid : i.certified.LocalizedRerootCursorValid root)
    (known : ∀ p, Enqueued root p → ∃ labels, read p.occurrence = some labels ∧
      labels.all RingNestedActivePair.consistent = true)
    (separated : ∀ p, Enqueued root p → ∀ x ∈ projected i p, ∀ y ∈ projected i p,
      chemicalKey i p x = chemicalKey i p y → x = y) :
    chemicalCheck read read false true seed seed.swap root root = true := by
  let rel (a b : Arm i) := a = b ∧ Enqueued root a
  apply (check_iff read read false true seed seed.swap (chemicalKey i) (chemicalKey i) root root valid).mpr
  refine ⟨rel,?_,rfl,.root⟩
  constructor
  · rintro a b ⟨rfl,vis⟩
    obtain ⟨v,hit,_⟩ := known a vis
    simp [hit]
  · rintro a b ⟨rfl,vis⟩
    obtain ⟨v,hit,physical⟩ := known a vis
    exact reflected_observation hit physical seed
  · rintro a b ⟨rfl,_⟩
    exact List.Perm.refl _
  · rintro a b ⟨rfl,vis⟩ x hx y hy eqn
    exact ⟨separated a vis x hx y hy eqn,.child vis hx⟩

/-- For either fixed reference, equality of the accepted pairing words makes
the actual fixed-seed molecular comparator return a known zero. -/
theorem fixed_tie_of_words {i j : Input} {l : Reader i} {r : Reader j} {lr rr seed xs ys}
    (w : word l lr seed xs = word r rr seed ys) :
    RingSeededPairs.listSign? seed (xs.map (upperAt l lr)) (ys.map (upperAt r rr)) = some 0 := by
  let encode (h : RS) := (h == seed).toNat
  have injective : Function.Injective encode := by
    cases seed <;> intro a b <;> cases a <;> cases b <;> decide
  have same : xs.filterMap (upperAt l lr) = ys.filterMap (upperAt r rr) :=
    List.map_injective_iff.mpr injective (List.cons.inj w).1
  have self (bits : List Bool) : RingSeededPairs.compareBits bits bits = 0 := by
    induction bits with
    | nil => rfl
    | cons b bs ih => simpa [RingSeededPairs.compareBits] using ih
  simp [RingSeededPairs.listSign?,List.filterMap_map,same,self]

/-- At a constitutionally and Rule-4a tied mixed R/S group, the two active
references legitimately order the two siblings by their own like/unlike bits. -/
def likeKey {i : Input} (read : Reader i) (rev : Bool) (seed : RS) (_ : Arm i) :=
  RingClosedPairGroup.bit read rev seed

private theorem group_keys {i q read} (g : RingClosedPairGroup.Group i q read) (rev : Bool) (seed : RS) :
    ((projected i q).map (likeKey read rev seed q)).Perm [1,0] := by
  have pp := g.live.map (likeKey read rev seed q)
  cases rev <;> cases seed <;>
    simp [likeKey,RingClosedPairGroup.bit,g.posRead,g.negRead,RingClosedPairGroup.chiral,RingNestedActivePair.upper,RS.swap] at pp <;>
      first | exact pp | exact pp.trans (List.Perm.swap ..)

private theorem group_child {i q read} (g : RingClosedPairGroup.Group i q read) (rev : Bool) (seed : RS)
    {a} (member : a ∈ projected i q) :
    (read a.occurrence).isSome = true ∧
      observation read rev seed a = some (likeKey read rev seed q a) ∧ projected i a = [] := by
  have places := g.live.mem_iff.mp member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at places
  rcases places with rfl | rfl <;> cases rev <;> cases seed <;>
    simp [observation,upperAt,likeKey,RingClosedPairGroup.bit,RingNestedActivePair.upper,g.posRead,g.negRead,
      g.noLaterPos,g.noLaterNeg,RingClosedPairGroup.chiral,RS.swap]

/-- The finite correspondence checker succeeds on *every* earlier-certified
closed mixed pair even if its two geometries and reference seeds differ.
Both hands may participate in the same comparison. -/
theorem closed_groups_checked {i j : Input} {a : Arm i} {b : Arm j} {l : Reader i} {r : Reader j}
    (g : RingClosedPairGroup.Group i a l) (h : RingClosedPairGroup.Group j b r) (lr rr : Bool) (ls rs : RS) :
    check l r lr rr ls rs (likeKey l lr ls) (likeKey r rr rs) 2 a b = true := by
  apply Bool.and_eq_true_iff.mpr
  have head {m u read} (group : RingClosedPairGroup.Group m u read) (rev : Bool) (seed : RS) :
      observation read rev seed u = none := by
    cases rev <;> simp [observation,upperAt,group.rootRead,RingClosedPairGroup.lower,RingNestedActivePair.upper]
  refine ⟨decide_eq_true ⟨by rw [g.rootRead]; rfl,by rw [h.rootRead]; rfl,(head g lr ls).trans (head h rr rs).symm,
    (group_keys g lr ls).trans (group_keys h rr rs).symm⟩,List.all_eq_true.mpr ?_⟩
  intro x hx
  apply List.all_eq_true.mpr
  intro y hy
  split
  next eqn =>
    obtain ⟨kx,ox,emptyX⟩ := group_child g lr ls hx
    obtain ⟨ky,oy,emptyY⟩ := group_child h rr rs hy
    apply Bool.and_eq_true_iff.mpr
    refine ⟨decide_eq_true ⟨kx,ky,ox.trans ((congrArg some eqn).trans oy.symm),?_⟩,?_⟩
    · rw [emptyX,emptyY]; exact List.Perm.nil
    · rw [emptyX]; rfl
  next => rfl

end TetraStereo.Engine.RingSeededFIFOTransport

assert_kernel_only TetraStereo.Engine.RingSeededFIFOTransport.walk_exists
assert_kernel_only TetraStereo.Engine.RingSeededFIFOTransport.aligned_visits
assert_kernel_only TetraStereo.Engine.RingSeededFIFOTransport.word_eq
assert_kernel_only TetraStereo.Engine.RingSeededFIFOTransport.tied_sibling_exchange
assert_kernel_only TetraStereo.Engine.RingSeededFIFOTransport.check_iff
assert_kernel_only TetraStereo.Engine.RingSeededFIFOTransport.checked_word
assert_kernel_only TetraStereo.Engine.RingSeededFIFOTransport.chemical_priority
assert_kernel_only TetraStereo.Engine.RingSeededFIFOTransport.chemical_checked_word
assert_kernel_only TetraStereo.Engine.RingSeededFIFOTransport.closed_groups_checked
assert_kernel_only TetraStereo.Engine.RingSeededFIFOTransport.fixed_tie_of_words
assert_kernel_only TetraStereo.Engine.RingSeededFIFOTransport.separated_mirror_check
