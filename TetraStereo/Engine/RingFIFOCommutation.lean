import TetraStereo.Engine.RingSeededFIFOTransport

set_option autoImplicit false

namespace TetraStereo.Engine.RingFIFOCommutation
open OneCenter LocalizedChemicalRing RingActivePairs
open RingNestedActivePair (Reader)
open RingClosedPairGroup (FIFO projected)
open RingSeededFIFOTransport (Admissible)

/-- Swapping adjacent tied branches preserves the complete sphere word precisely
when their two contributions commute. Other branches at that distance cancel. -/
theorem swap_iff {β : Type} (pre x y post : List β) :
    (pre ++ (x ++ y)) ++ post = (pre ++ (y ++ x)) ++ post ↔ x ++ y = y ++ x := by rw [List.append_left_inj,List.append_right_inj]

private theorem slide {α β : Type} (word : α → List β) (x : α) (before : List α)
    (ok : ∀ y ∈ before, word y ++ word x = word x ++ word y) :
    before.flatMap word ++ word x = word x ++ before.flatMap word := by
  induction before with
  | nil => simp
  | cons y ys ih =>
    have tail := ih fun z hz => ok z (List.mem_cons_of_mem _ hz)
    simp only [List.flatMap_cons,List.append_assoc,tail]
    rw [← List.append_assoc,ok y List.mem_cons_self,List.append_assoc]

/-- At an arbitrary priority block, equal-priority siblings can carry different
words, including different lengths. Commutation is sufficient even when all
their permutations are allowed independently. -/
theorem ranked_word {α β K : Type} [LinearOrder K] (key : α → K) (word : α → List β)
    {xs ys : List α} (perm : xs.Perm ys) (sorted : xs.Pairwise fun x y => key y ≤ key x)
    (other : ys.Pairwise fun x y => key y ≤ key x)
    (ties : ∀ a ∈ xs, ∀ b ∈ xs, key a = key b → word a ++ word b = word b ++ word a) :
    xs.flatMap word = ys.flatMap word := by
  induction xs generalizing ys with
  | nil => rw [List.Perm.nil_eq perm]
  | cons x xs ih =>
    obtain ⟨pre,post,rfl,_⟩ := List.eq_append_cons_of_mem (perm.mem_iff.mp List.mem_cons_self)
    have rest := (perm.trans List.perm_middle).cons_inv
    obtain ⟨front,back,cross⟩ := List.pairwise_append.mp other
    have newOrder := List.pairwise_append.mpr
      ⟨front,(List.pairwise_cons.mp back).2,fun a ha b hb => cross a ha b (List.mem_cons_of_mem _ hb)⟩
    have rearrange := ih rest (List.pairwise_cons.mp sorted).2 newOrder
      (fun a ha b hb => ties a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
    have move := slide word x pre (fun y hy =>
      have mem := rest.mem_iff.mpr (List.mem_append_left post hy)
      ties y (List.mem_cons_of_mem x mem) x List.mem_cons_self
        (le_antisymm ((List.pairwise_cons.mp sorted).1 y mem) (cross y hy x List.mem_cons_self)))
    simp only [List.flatMap_cons,List.flatMap_append] at rearrange ⊢
    rw [rearrange,← List.append_assoc,← move,List.append_assoc]

/-- On a single already established priority class, commutation is also
necessary. Both adjacent orders can be realized after bringing two chosen
members to the front of this class. -/
theorem block_iff {α β : Type} (word : α → List β) (xs : List α) :
    (∀ ys : List α, ys.Perm xs → ys.flatMap word = xs.flatMap word) ↔
      ∀ a ∈ xs, ∀ b ∈ xs, word a ++ word b = word b ++ word a := by
  classical
  constructor
  · intro unique a ha b hb
    by_cases eqn : a = b
    · simp [eqn]
    have pa := List.perm_cons_erase ha
    have hb' : b ∈ xs.erase a := by
      rcases List.mem_cons.mp (pa.mem_iff.mp hb) with same | rest
      · exact False.elim (eqn same.symm)
      · exact rest
    have pb := List.perm_cons_erase hb'
    have first := ((pb.cons a).symm.trans pa.symm)
    have second := (List.Perm.swap _ _ _).trans first
    have both := (unique _ first).trans (unique _ second).symm
    simp only [List.flatMap_cons] at both
    exact (List.append_left_inj _).mp (by simpa only [List.append_assoc] using both :
      (word a ++ word b) ++ _ = (word b ++ word a) ++ _)
  · intro commute ys perm
    symm
    apply ranked_word (fun _ => (0 : Nat)) word perm.symm
    · exact List.pairwise_of_forall fun _ _ => le_rfl
    · exact List.pairwise_of_forall fun _ _ => le_rfl
    · intro a ha b hb _
      exact commute a ha b hb

private def sorted {α K : Type} [LinearOrder K] (key : α → K) (xs : List α) :=
  xs.mergeSort fun a b => decide (key b ≤ key a)

private theorem descending {α K : Type} [LinearOrder K] (key : α → K) (xs : List α) :
    (sorted key xs).Pairwise fun a b => key b ≤ key a := by
  have h := List.pairwise_mergeSort (le := fun a b : α => decide (key b ≤ key a))
    (fun _ _ _ x y => decide_eq_true (le_trans (of_decide_eq_true y) (of_decide_eq_true x)))
    (fun a b => by simpa using le_total (key b) (key a)) xs
  exact h.imp fun h => of_decide_eq_true h

def collect {α β : Type} (read : α → Option (List β)) (xs : List α) :=
  (xs.mapM read).map List.flatten

private theorem collect_present {α β : Type} (read : α → Option (List β)) (xs : List α)
    (ok : ∀ a ∈ xs, (read a).isSome = true) :
    collect read xs = some (xs.flatMap fun a => (read a).getD []) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    obtain ⟨v,found⟩ := Option.isSome_iff_exists.mp (ok a List.mem_cons_self)
    have tail := ih fun b hb => ok b (List.mem_cons_of_mem _ hb)
    unfold collect at tail ⊢
    cases h : xs.mapM read <;> simp [h] at tail
    simp only [List.mapM_cons,found,Option.bind_some,Option.bind_eq_bind,h,Option.getD_some,
      List.flatMap_cons,Option.map_some,List.flatten_cons,pure,← tail]

private def checkedRows {β K : Type} [DecidableEq β] [LinearOrder K]
    (rows : List (K × Option (List β))) : Option (List β) :=
  if rows.all (fun x => x.2.isSome) && rows.all (fun a => rows.all (fun b =>
      decide (a.1 = b.1 → a.2.getD [] ++ b.2.getD [] = b.2.getD [] ++ a.2.getD []))) then
    some (rows.flatMap fun a => a.2.getD [])
  else none

/-- Compute one parent's contribution to a single distance. The checker caches
each child observation before checking commutation within each priority block. -/
def merge? {α β K : Type} [DecidableEq β] [LinearOrder K] (key : α → K)
    (read : α → Option (List β)) (xs : List α) : Option (List β) :=
  checkedRows ((sorted key xs).map fun a => (key a,read a))

theorem merge_source {α β K : Type} [DecidableEq β] [LinearOrder K] {key : α → K}
    {read : α → Option (List β)} {xs ys v} (found : merge? key read xs = some v)
    (perm : ys.Perm xs) (order : ys.Pairwise fun a b => key b ≤ key a) :
    collect read ys = some v := by
  have canon : (sorted key xs).Perm xs := List.mergeSort_perm ..
  unfold merge? checkedRows at found
  split at found <;> try contradiction
  rename_i guard
  obtain ⟨known,ties⟩ := Bool.and_eq_true_iff.mp guard
  simp only [List.all_map,List.all_eq_true,Function.comp_apply,decide_eq_true_eq] at known ties
  have same := ranked_word key (fun a => (read a).getD []) (canon.trans perm.symm)
    (descending key xs) order ties
  rw [collect_present read ys (fun a ha => known a (canon.mem_iff.mpr (perm.mem_iff.mp ha))),← same]
  simpa only [List.flatMap_map,Function.comp_def] using found

/-- One depth, measured away from a retained directed arm. Nonterminal
children are exactly those visited by the molecular PairList queue. -/
def sphere? {i : Input} {β K : Type} [DecidableEq β] [LinearOrder K]
    (key : Arm i → Arm i → K) (read : Arm i → Option (List β)) :
    Nat → Arm i → Option (List β)
  | 0,a => read a
  | n+1,a => merge? (key a) (sphere? key read n) (projected i a)

private def Allowed {i : Input} {K : Type} [LinearOrder K] (key : Arm i → Arm i → K)
    (a : Arm i) (xs : List (Arm i)) :=
  xs.Perm (projected i a) ∧ Admissible key a xs

/-- One transition preserves parent order, appending the chosen complete
row of each parent after all rows that precede it. -/
inductive Layer {i : Input} {K : Type} [LinearOrder K] (key : Arm i → Arm i → K) :
    Nat → List (Arm i) → List (Arm i) → Prop where
  | here {qs} : Layer key 0 qs qs
  | next {n qs rows out} (step : List.Forall₂ (Allowed key) qs rows)
      (rest : Layer key n rows.flatten out) : Layer key (n+1) qs out

private theorem collect_append {α β : Type} (f : α → Option (List β)) (xs ys : List α) :
    collect f (xs ++ ys) = (do return (← collect f xs) ++ (← collect f ys)) := by
  unfold collect
  cases l : xs.mapM f <;> cases r : ys.mapM f <;> simp [List.mapM_append,l,r]

private theorem collect_cons {α β : Type} (f : α → Option (List β)) (a : α) (xs : List α) :
    collect f (a::xs) = (do return (← f a) ++ (← collect f xs)) := by
  unfold collect
  cases h : f a <;> cases t : xs.mapM f <;> simp [List.mapM_cons,h,t]

private theorem transition {i : Input} {β K : Type} [DecidableEq β] [LinearOrder K]
    {key : Arm i → Arm i → K} {read : Arm i → Option (List β)} {qs rows}
    (step : List.Forall₂ (Allowed key) qs rows) (n : Nat) {v}
    (found : collect (sphere? key read (n+1)) qs = some v) :
    collect (sphere? key read n) rows.flatten = some v := by
  induction step generalizing v with
  | nil => exact found
  | cons h _ ih =>
    rw [collect_cons] at found
    obtain ⟨u,hu,t⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨w,hw,out⟩ := Option.bind_eq_some_iff.mp t
    rw [List.flatten_cons,collect_append,merge_source hu h.1 (List.pairwise_map.mp h.2),ih hw]
    exact out

theorem layer_word {i : Input} {β K : Type} [DecidableEq β] [LinearOrder K]
    {key : Arm i → Arm i → K} {read : Arm i → Option (List β)} {n qs out}
    (seen : Layer key n qs out) {v} (found : collect (sphere? key read n) qs = some v) :
    collect read out = some v := by
  induction seen with
  | here => exact found
  | next step _ ih => exact ih (transition step _ found)

private theorem peel {i : Input} {K : Type} [LinearOrder K] {key : Arm i → Arm i → K}
    (qs pending : List (Arm i)) {out} (walk : FIFO i (Admissible key) (qs ++ pending) out) :
    ∃ rows tail, List.Forall₂ (Allowed key) qs rows ∧
      FIFO i (Admissible key) (pending ++ rows.flatten) tail ∧ out = qs ++ tail := by
  induction qs generalizing pending out with
  | nil => exact ⟨[],out,.nil,by simpa using walk,rfl⟩
  | cons a qs ih =>
    cases walk with
    | @step _ _ row _ perm order next =>
      obtain ⟨rows,tail,related,rest,eqn⟩ := ih (pending ++ row) (by simpa [List.append_assoc] using next)
      exact ⟨row::rows,tail,.cons ⟨perm,order⟩ related,by simpa [List.append_assoc] using rest,
        congrArg (List.cons a) eqn⟩

/-- Concatenate all distance layers. Unknown publications and noncommuting
tied blocks propagate to the outer option. A known empty word is successful. -/
def levels {β : Type} : Nat → (Nat → Option (List β)) → Option (List β)
  | 0, _ => some []
  | n+1, f => do return (← f 0) ++ (← levels n (fun d => f (d+1)))

private theorem levels_transport {β : Type} (n : Nat) {f g : Nat → Option (List β)}
    (preserve : ∀ d w, f d = some w → g d = some w) {v} (hit : levels n f = some v) :
    levels n g = some v := by
  induction n generalizing f g v with
  | zero => exact hit
  | succ n ih =>
    obtain ⟨u,hu,t⟩ := Option.bind_eq_some_iff.mp hit
    obtain ⟨w,hw,out⟩ := Option.bind_eq_some_iff.mp t
    simp only [levels,preserve _ _ hu,Option.bind_some,Option.bind_eq_bind,
      ih (fun d => preserve (d+1)) hw]
    exact out

private theorem parent_of_row {α β : Type} {R : α → β → Prop} {qs rows}
    (rel : List.Forall₂ R qs rows) {row} (hr : row ∈ rows) : ∃ p ∈ qs, R p row := by
  induction rel with
  | nil => contradiction
  | cons head _ ih =>
    rcases List.mem_cons.mp hr with rfl | mem
    · exact ⟨_,List.mem_cons_self,head⟩
    · obtain ⟨p,h,r⟩ := ih mem
      exact ⟨p,List.mem_cons_of_mem _ h,r⟩

/-- Every possible complete molecular FIFO traversal consumes the certified
sequence. The decreasing cursor budget accounts for returning through an
original parent and for every retained occurrence at arbitrary depth. -/
theorem fifo_word {i : Input} {β K : Type} [DecidableEq β] [LinearOrder K]
    {key : Arm i → Arm i → K} {read : Arm i → Option (List β)} (n : Nat) {qs out v}
    (covered : ∀ q ∈ qs, i.certified.LocalizedRerootCursorValid q ∧
      i.certified.localizedRerootCursorBudget q < n)
    (walk : FIFO i (Admissible key) qs out)
    (hit : levels n (fun d => collect (sphere? key read d) qs) = some v) :
    collect read out = some v := by
  induction n generalizing qs out v with
  | zero =>
    cases qs with
    | nil => cases walk; exact hit
    | cons a qs => exact False.elim (Nat.not_lt_zero _ (covered a List.mem_cons_self).2)
  | succ n ih =>
    obtain ⟨rows,tail,related,rest,rfl⟩ := peel qs [] (by simpa using walk)
    have small : ∀ q ∈ rows.flatten, i.certified.LocalizedRerootCursorValid q ∧
        i.certified.localizedRerootCursorBudget q < n := by
      intro q hq
      obtain ⟨row,hr,h⟩ := List.mem_flatten.mp hq
      obtain ⟨p,hp,allowed⟩ := parent_of_row related hr
      have child := List.mem_of_mem_filter (allowed.1.mem_iff.mp h)
      have frame := i.certified.executableLocalizedRerootChildren_declarative p
      exact ⟨i.certified.localizedRerootChild_valid p q _ frame child,
        lt_of_lt_of_le (i.certified.localizedRerootChild_budget_lt p q _ (covered p hp).1 frame child)
          (Nat.le_of_lt_succ (covered p hp).2)⟩
    obtain ⟨u,hu,t⟩ := Option.bind_eq_some_iff.mp hit
    obtain ⟨w,hw,result⟩ := Option.bind_eq_some_iff.mp t
    have next := levels_transport n (fun d _ => transition related d) hw
    rw [collect_append,show collect read qs = some u from hu,ih small (by simpa using rest) next]
    exact result

/-- Compact fixed-reference pairing only emits uppercase publications. The
outer read first authenticates presence of the frozen publication cell. -/
def accepted {i : Input} (read : Reader i) (rev : Bool) (seed : RS) (q : Arm i) :
    Option (List Nat) :=
  (read q.occurrence).map fun _ => (RingSeededFIFOTransport.observation read rev seed q).toList

private theorem accepted_word {i : Input} (read : Reader i) (rev : Bool) (seed : RS)
    (qs : List (Arm i)) {v} (known : collect (accepted read rev seed) qs = some v) :
    RingClosedPairGroup.word read rev seed qs = [v] := by
  induction qs generalizing v with
  | nil => have eqn : [] = v := Option.some.inj known; subst v; rfl
  | cons q qs ih =>
    rw [collect_cons] at known
    obtain ⟨u,hu,t⟩ := Option.bind_eq_some_iff.mp known
    obtain ⟨w,hw,out⟩ := Option.bind_eq_some_iff.mp t
    have tail := (List.cons.inj (ih hw)).1
    have result : u ++ w = v := Option.some.inj out
    subst v
    obtain ⟨cell,_,eqn⟩ := Option.map_eq_some_iff.mp hu
    subst u
    unfold RingClosedPairGroup.word
    cases obs : RingClosedPairGroup.upperAt read rev q <;>
      simp [RingSeededFIFOTransport.observation,obs,tail]

/-- Compute the accepted word at the molecular cursor's own bound, retaining
all orders compatible with the complete constitutional Rule 1a, 1b and 2 keys. -/
def chemicalWord? {i : Input} (read : Reader i) (rev : Bool) (seed : RS) (q : Arm i) :=
  levels (i.certified.localizedRerootCursorBudget q + 1) (fun d =>
    collect (sphere? (RingSeededFIFOTransport.chemicalKey i) (accepted read rev seed) d) [q])

theorem chemical_word {i : Input} {read : Reader i} {rev seed q xs v}
    (valid : i.certified.LocalizedRerootCursorValid q)
    (seen : FIFO i (Admissible (RingSeededFIFOTransport.chemicalKey i)) [q] xs)
    (known : chemicalWord? read rev seed q = some v) :
    RingClosedPairGroup.word read rev seed xs = [v] := by
  apply accepted_word
  apply fifo_word _ _ seen known
  intro p hp
  obtain rfl := List.mem_singleton.mp hp
  exact ⟨valid,Nat.lt_succ_self _⟩

theorem chemical_fixed_tie {i : Input} {read : Reader i} {rev seed a b xs ys v}
    (va : i.certified.LocalizedRerootCursorValid a) (vb : i.certified.LocalizedRerootCursorValid b)
    (la : FIFO i (Admissible (RingSeededFIFOTransport.chemicalKey i)) [a] xs)
    (lb : FIFO i (Admissible (RingSeededFIFOTransport.chemicalKey i)) [b] ys)
    (ha : chemicalWord? read rev seed a = some v) (hb : chemicalWord? read rev seed b = some v) :
    RingSeededPairs.listSign? seed (xs.map (RingClosedPairGroup.upperAt read rev))
      (ys.map (RingClosedPairGroup.upperAt read rev)) = some 0 :=
  RingSeededFIFOTransport.fixed_tie_of_words ((chemical_word va la ha).trans (chemical_word vb lb hb).symm)


/-- Read a certified compact word as the comparison of its accepted bits.
The length check is the one made by the fixed-reference PairList comparator. -/
def compactScore? (a b : List Nat) : Option Int :=
  if a.length = b.length then some (RingSeededPairs.compareBits (a.map (· == 1)) (b.map (· == 1))) else none

private theorem decode {seed : RS} (hs : List RS) :
    (hs.map (fun h => (h == seed).toNat)).map (· == 1) = hs.map (· == seed) := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro x _
  cases x <;> cases seed <;> rfl

theorem fixed_score {i : Input} {read : Reader i} {rev seed xs ys u v}
    (a : RingClosedPairGroup.word read rev seed xs = [u])
    (b : RingClosedPairGroup.word read rev seed ys = [v]) :
    RingSeededPairs.listSign? seed (xs.map (RingClosedPairGroup.upperAt read rev))
      (ys.map (RingClosedPairGroup.upperAt read rev)) = compactScore? u v := by
  rw [← (List.cons.inj a).1,← (List.cons.inj b).1]
  simp only [RingSeededPairs.listSign?,compactScore?,List.filterMap_map,Function.comp_def,id_eq,
    List.length_map,decode]

/-- If both arms have an order-independent accepted R-word, four independently
chosen walks suffice to determine the exact Rule 5 comparison. The S-seeded
walk may traverse different children first. Its score is the negative of the
R-seeded score, so a strict decision in this class always has magnitude two. -/
theorem chemical_two_seed {i : Input} {read : Reader i} {rev a b xs ys xs' ys' u v}
    (va : i.certified.LocalizedRerootCursorValid a) (vb : i.certified.LocalizedRerootCursorValid b)
    (la : chemicalWord? read rev .R a = some u) (lb : chemicalWord? read rev .R b = some v)
    (ar : FIFO i (Admissible (RingSeededFIFOTransport.chemicalKey i)) [a] xs)
    (br : FIFO i (Admissible (RingSeededFIFOTransport.chemicalKey i)) [b] ys)
    (as' : FIFO i (Admissible (RingSeededFIFOTransport.chemicalKey i)) [a] xs')
    (bs' : FIFO i (Admissible (RingSeededFIFOTransport.chemicalKey i)) [b] ys') :
    (do
      let r ← RingSeededPairs.listSign? .R (xs.map (RingClosedPairGroup.upperAt read rev))
        (ys.map (RingClosedPairGroup.upperAt read rev))
      let s ← RingSeededPairs.listSign? .S (xs'.map (RingClosedPairGroup.upperAt read rev))
        (ys'.map (RingClosedPairGroup.upperAt read rev))
      return CentresRing.PairList.combine r s) =
    (compactScore? u v).map (fun r => if r < 0 then (-2 : Int) else if 0 < r then 2 else 0) := by
  rw [fixed_score (chemical_word va ar la) (chemical_word vb br lb),RingSeededPairs.two_seed_sign,
    fixed_score (chemical_word va as' la) (chemical_word vb bs' lb)]
  cases h : compactScore? u v with
  | none => rfl
  | some r =>
    apply congrArg some
    change CentresRing.PairList.combine r (-r) = (if r < 0 then -2 else if 0 < r then 2 else 0)
    unfold CentresRing.PairList.combine
    split_ifs <;> omega

/-- A strict unit-magnitude Rule 5 result witnesses an actual change of
the accepted hand sequence on at least one ligand when the seed changes.
This converse needs neither the word checker nor unique sibling keys. -/
theorem unit_requires_reordering (a b a' b' : List (Option RS)) {r s : Int}
    (hr : RingSeededPairs.listSign? .R a b = some r)
    (hs : RingSeededPairs.listSign? .S a' b' = some s)
    (unit : (CentresRing.PairList.combine r s).natAbs = 1) :
    a.filterMap id ≠ a'.filterMap id ∨ b.filterMap id ≠ b'.filterMap id := by
  by_contra! same
  have eqn : RingSeededPairs.listSign? .R a' b' = some r := by
    simpa only [RingSeededPairs.listSign?,← same.1,← same.2] using hr
  rw [RingSeededPairs.two_seed_sign,eqn] at hs
  have sign : -r = s := Option.some.inj hs
  subst s
  unfold CentresRing.PairList.combine at unit
  split_ifs at unit <;> simp_all <;> omega

/-- One-reference Rule 4b visits even those positions without an accepted
uppercase hand. Keep a bit for every visit with the chosen reference. -/
def aligned {i : Input} (read : Reader i) (rev : Bool) (seed : RS) (q : Arm i) :
    Option (List Bool) :=
  (read q.occurrence).map fun _ => [RingSeededPairs.like seed (RingClosedPairGroup.upperAt read rev q)]

private theorem aligned_bits {i : Input} (read : Reader i) (rev : Bool) (seed : RS)
    (qs : List (Arm i)) {v} (known : collect (aligned read rev seed) qs = some v) :
    (qs.map (RingClosedPairGroup.upperAt read rev)).map (RingSeededPairs.like seed) = v := by
  induction qs generalizing v with
  | nil => exact Option.some.inj known
  | cons q qs ih =>
    rw [collect_cons] at known
    obtain ⟨u,hu,t⟩ := Option.bind_eq_some_iff.mp known
    obtain ⟨w,hw,out⟩ := Option.bind_eq_some_iff.mp t
    obtain ⟨_,_,eqn⟩ := Option.map_eq_some_iff.mp hu
    rw [← Option.some.inj out,← eqn,List.map_cons,List.map_cons,ih hw]
    rfl

def alignedWord? {i : Input} (read : Reader i) (rev : Bool) (seed : RS) (q : Arm i) :=
  levels (i.certified.localizedRerootCursorBudget q + 1) (fun d =>
    collect (sphere? (RingSeededFIFOTransport.chemicalKey i) (aligned read rev seed) d) [q])

theorem aligned_word {i : Input} {read : Reader i} {rev seed q xs v}
    (valid : i.certified.LocalizedRerootCursorValid q)
    (seen : FIFO i (Admissible (RingSeededFIFOTransport.chemicalKey i)) [q] xs)
    (known : alignedWord? read rev seed q = some v) :
    (xs.map (RingClosedPairGroup.upperAt read rev)).map (RingSeededPairs.like seed) = v := by
  apply aligned_bits
  apply fifo_word _ _ seen known
  intro p hp
  obtain rfl := List.mem_singleton.mp hp
  exact ⟨valid,Nat.lt_succ_self _⟩

/-- Different descriptor counts can still commute. Exchanging the two
single-bit contributions below changes their order and is rejected. -/
theorem merge_controls :
    merge? (fun _ : List Nat => (0 : Nat)) some [[1,0],[1,0,1,0]] = some [1,0,1,0,1,0] ∧
    merge? (fun _ : List Nat => (0 : Nat)) some [[1],[0]] = none := by
  have same (row : List (List Nat)) : sorted (fun _ : List Nat => (0 : Nat)) row = row :=
    List.mergeSort_of_pairwise (List.pairwise_of_forall fun _ _ => decide_eq_true (Nat.le_refl 0))
  simp only [merge?,same]
  decide +kernel

/-- The two source observation modes can produce different decisions on the
same pair of visit lists. Missing positions here are known neutral visits. -/
theorem aligned_control :
    let a : List (Option RS) := [none,some .R]
    let b : List (Option RS) := [some .R,none]
    RingSeededPairs.listSign? .R a b = some 0 ∧
    RingSeededPairs.compareBits (a.map (RingSeededPairs.like .R)) (b.map (RingSeededPairs.like .R)) = -1 := by
  decide +kernel

end TetraStereo.Engine.RingFIFOCommutation
assert_kernel_only TetraStereo.Engine.RingFIFOCommutation.swap_iff
assert_kernel_only TetraStereo.Engine.RingFIFOCommutation.ranked_word
assert_kernel_only TetraStereo.Engine.RingFIFOCommutation.merge_source
assert_kernel_only TetraStereo.Engine.RingFIFOCommutation.layer_word

assert_kernel_only TetraStereo.Engine.RingFIFOCommutation.fifo_word
assert_kernel_only TetraStereo.Engine.RingFIFOCommutation.chemical_word
assert_kernel_only TetraStereo.Engine.RingFIFOCommutation.chemical_fixed_tie
assert_kernel_only TetraStereo.Engine.RingFIFOCommutation.chemical_two_seed
assert_kernel_only TetraStereo.Engine.RingFIFOCommutation.aligned_word
assert_kernel_only TetraStereo.Engine.RingFIFOCommutation.block_iff
assert_kernel_only TetraStereo.Engine.RingFIFOCommutation.unit_requires_reordering
assert_kernel_only TetraStereo.Engine.RingFIFOCommutation.merge_controls
assert_kernel_only TetraStereo.Engine.RingFIFOCommutation.aligned_control
