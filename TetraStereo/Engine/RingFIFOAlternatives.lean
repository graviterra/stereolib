import TetraStereo.Engine.RingSeededFIFOTransport

set_option autoImplicit false

namespace TetraStereo.Engine.RingFIFOAlternatives
open OneCenter LocalizedChemicalRing RingActivePairs
open RingClosedPairGroup (FIFO projected)
open RingNestedActivePair (Reader)

abbrev Permit (i : Input) := Arm i → List (Arm i) → Bool

/-- A complete next distance layer retains each parent's relative position. -/
inductive Step {i : Input} (allow : Permit i) : List (Arm i) → List (Arm i) → Prop where
  | empty : Step allow [] []
  | cons {a as row below} (perm : row.Perm (projected i a)) (ok : allow a row = true)
      (rest : Step allow as below) : Step allow (a :: as) (row ++ below)

def successors {i : Input} (allow : Permit i) : List (Arm i) → List (List (Arm i))
  | [] => [[]]
  | q :: qs =>
    let tail := successors allow qs
    ((projected i q).permutations'.filter (allow q)).flatMap fun row => tail.map (row ++ ·)

theorem successor_iff {i : Input} (allow : Permit i) (qs cs : List (Arm i)) :
    cs ∈ successors allow qs ↔ Step allow qs cs := by
  induction qs generalizing cs with
  | nil =>
    constructor
    · intro h; obtain rfl := List.mem_singleton.mp h; exact .empty
    · intro h; cases h; exact List.mem_singleton_self _
  | cons q qs ih =>
    simp only [successors,List.mem_flatMap,List.mem_filter,List.mem_permutations',List.mem_map]
    constructor
    · rintro ⟨row,⟨perm,ok⟩,below,mem,rfl⟩
      exact .cons perm ok ((ih below).mp mem)
    · intro h
      cases h with
      | cons perm ok rest => exact ⟨_,⟨perm,ok⟩,_,(ih _).mpr rest,rfl⟩

private theorem split_layer {i : Input} {allow : Permit i} (qs pending : List (Arm i)) {out}
    (w : FIFO i (fun a row => allow a row = true) (qs ++ pending) out) :
    ∃ below tail, Step allow qs below ∧ FIFO i (fun a row => allow a row = true)
      (pending ++ below) tail ∧ out = qs ++ tail := by
  induction qs generalizing pending out with
  | nil => exact ⟨[],out,.empty,by simpa using w,rfl⟩
  | cons a qs ih =>
    cases w with
    | @step _ _ row _ perm ok next =>
      change FIFO i _ ((qs ++ pending) ++ row) _ at next
      obtain ⟨below,tail,s,r,rfl⟩ := ih (pending ++ row) (by simpa only [List.append_assoc] using next)
      exact ⟨_,_,.cons perm ok s,by simpa only [List.append_assoc] using r,rfl⟩

private theorem join_layer {i : Input} {allow : Permit i} {qs below}
    (s : Step allow qs below) (pending : List (Arm i)) {tail}
    (w : FIFO i (fun a row => allow a row = true) (pending ++ below) tail) :
    FIFO i (fun a row => allow a row = true) (qs ++ pending) (qs ++ tail) := by
  induction s generalizing pending with
  | empty => simpa using w
  | @cons q qs row below perm ok rest ih =>
    apply FIFO.step perm ok
    change FIFO i _ ((qs ++ pending) ++ row) (qs ++ tail)
    simpa only [List.append_assoc] using ih (pending ++ row) (by simpa only [List.append_assoc] using w)

private theorem Step.origin {i : Input} {allow : Permit i} {qs cs} (s : Step allow qs cs)
    {c : Arm i} (hc : c ∈ cs) : ∃ a ∈ qs, c ∈ projected i a := by
  induction s with
  | empty => contradiction
  | @cons a qs row below perm _ _ ih =>
    rcases List.mem_append.mp hc with hr | hb
    · exact ⟨a,List.mem_cons_self,perm.mem_iff.mp hr⟩
    · obtain ⟨b,mem,child⟩ := ih hb
      exact ⟨b,List.mem_cons_of_mem _ mem,child⟩

/-- Opt-in exhaustive diagnostics. An insufficient budget never manufactures a
truncated walk. Distinct row choices may enumerate the same observable. -/
def enumerate {i : Input} (allow : Permit i) : Nat → List (Arm i) → List (List (Arm i))
  | 0, qs => if qs.isEmpty then [[]] else []
  | n+1, qs => (successors allow qs).flatMap fun below => (enumerate allow n below).map (qs ++ ·)

theorem enumerate_iff {i : Input} (allow : Permit i) (n : Nat) (qs xs : List (Arm i))
    (covered : ∀ a ∈ qs, i.certified.LocalizedRerootCursorValid a ∧
      i.certified.localizedRerootCursorBudget a < n) :
    xs ∈ enumerate allow n qs ↔ FIFO i (fun a row => allow a row = true) qs xs := by
  induction n generalizing qs xs with
  | zero =>
    cases qs with
    | nil =>
      constructor
      · intro h; obtain rfl := List.mem_singleton.mp h; exact .stop
      · intro h; cases h; exact List.mem_singleton_self _
    | cons a qs => exact False.elim (Nat.not_lt_zero _ (covered a List.mem_cons_self).2)
  | succ n ih =>
    have small {below} (s : Step allow qs below) : ∀ c ∈ below,
        i.certified.LocalizedRerootCursorValid c ∧ i.certified.localizedRerootCursorBudget c < n := by
      intro c hc
      obtain ⟨a,ha,member⟩ := s.origin hc
      have child := List.mem_of_mem_filter member
      have frame := i.certified.executableLocalizedRerootChildren_declarative a
      exact ⟨i.certified.localizedRerootChild_valid a c _ frame child,
        lt_of_lt_of_le (i.certified.localizedRerootChild_budget_lt a c _ (covered a ha).1 frame child)
          (Nat.le_of_lt_succ (covered a ha).2)⟩
    simp only [enumerate,List.mem_flatMap,successor_iff,List.mem_map]
    constructor
    · rintro ⟨below,s,tail,hit,rfl⟩
      have w := (ih below tail (small s)).mp hit
      simpa only [List.append_nil] using join_layer s [] (by simpa using w)
    · intro w
      obtain ⟨below,tail,s,w',rfl⟩ := split_layer qs [] (by simpa using w : FIFO i _ (qs ++ []) xs)
      exact ⟨below,s,tail,(ih below tail (small s)).mpr (by simpa using w'),rfl⟩

/-- All observations of complete, allowed walks from this retained arm, evaluated
at the structural molecular cursor bound. The observation can retain paths,
compact PairList bits, or one comparison bit for every visited site. -/
def outcomes {i : Input} {β : Type} (allow : Permit i) (observe : List (Arm i) → β) (q : Arm i) :=
  (enumerate allow (i.certified.localizedRerootCursorBudget q + 1) [q]).map observe

theorem outcome_iff {i : Input} {β : Type} (allow : Permit i) (observe : List (Arm i) → β)
    {q : Arm i} (valid : i.certified.LocalizedRerootCursorValid q) (b : β) :
    b ∈ outcomes allow observe q ↔ ∃ xs, FIFO i (fun a row => allow a row = true) [q] xs ∧ observe xs = b := by
  simp only [outcomes,List.mem_map]
  have covered : ∀ a ∈ [q], i.certified.LocalizedRerootCursorValid a ∧
      i.certified.localizedRerootCursorBudget a < i.certified.localizedRerootCursorBudget q + 1 := by
    intro a ha; obtain rfl := List.mem_singleton.mp ha; exact ⟨valid,Nat.lt_succ_self _⟩
  simp only [enumerate_iff _ _ _ _ covered]

private def distinctValues {β : Type} [DecidableEq β] : List β → Bool
  | [] => false
  | a::as => as.any fun b => decide (a ≠ b)

private theorem distinct_iff {β : Type} [DecidableEq β] (bs : List β) :
    distinctValues bs = true ↔ ∃ x ∈ bs, ∃ y ∈ bs, x ≠ y := by
  cases bs with
  | nil => simp [distinctValues]
  | cons a as =>
    simp only [distinctValues,List.any_eq_true,decide_eq_true_eq]
    constructor
    · rintro ⟨b,hb,ne⟩
      exact ⟨a,List.mem_cons_self,b,List.mem_cons_of_mem _ hb,ne⟩
    · rintro ⟨x,hx,y,hy,ne⟩
      by_cases ax : a = x
      · subst x
        exact ⟨y,(List.mem_cons.mp hy).resolve_left (Ne.symm ne),ne⟩
      · exact ⟨x,(List.mem_cons.mp hx).resolve_left (Ne.symm ax),ax⟩

/-- A true result detects actual disagreement within the specified sibling order.
Once walks are enumerated, this test needs one pass through their observations. -/
def ambiguous {i : Input} {β : Type} [DecidableEq β] (allow : Permit i)
    (observe : List (Arm i) → β) (q : Arm i) : Bool :=
  distinctValues (outcomes allow observe q)

theorem ambiguous_iff {i : Input} {β : Type} [DecidableEq β] (allow : Permit i)
    (observe : List (Arm i) → β) {q : Arm i} (valid : i.certified.LocalizedRerootCursorValid q) :
    ambiguous allow observe q = true ↔ ∃ xs ys, FIFO i (fun a row => allow a row = true) [q] xs ∧
      FIFO i (fun a row => allow a row = true) [q] ys ∧ observe xs ≠ observe ys := by
  simp only [ambiguous,distinct_iff,outcome_iff allow observe valid]
  constructor
  · rintro ⟨x,⟨xs,hx,rfl⟩,y,⟨ys,hy,rfl⟩,ne⟩
    exact ⟨xs,ys,hx,hy,ne⟩
  · rintro ⟨xs,ys,hx,hy,ne⟩
    exact ⟨_,⟨xs,hx,rfl⟩,_,⟨ys,hy,rfl⟩,ne⟩

/-- Return two actual directed occurrence sequences exhibiting a disagreement.
The first complete traversal supplies the comparison value for the search. -/
def witness? {i : Input} {β : Type} [DecidableEq β] (allow : Permit i)
    (observe : List (Arm i) → β) (q : Arm i) : Option (List (Arm i) × List (Arm i)) :=
  match outcomes allow id q with
  | [] => none
  | xs :: rest => (rest.find? fun ys => decide (observe xs ≠ observe ys)).map (fun ys => (xs,ys))

theorem witness_issued {i : Input} {β : Type} [DecidableEq β] (allow : Permit i)
    (observe : List (Arm i) → β) {q : Arm i} (valid : i.certified.LocalizedRerootCursorValid q)
    {xs ys} (hit : witness? allow observe q = some (xs,ys)) :
    FIFO i (fun a row => allow a row = true) [q] xs ∧ FIFO i (fun a row => allow a row = true) [q] ys ∧
      observe xs ≠ observe ys := by
  have real {zs} (mem : zs ∈ outcomes allow id q) : FIFO i (fun a row => allow a row = true) [q] zs := by
    obtain ⟨ws,w,rfl⟩ := (outcome_iff allow id valid zs).mp mem
    exact w
  unfold witness? at hit
  cases pool : outcomes allow id q with
  | nil => simp [pool] at hit
  | cons a rest =>
    rw [pool] at hit
    obtain ⟨b,found,eqn⟩ := Option.map_eq_some_iff.mp hit
    cases eqn
    exact ⟨real (pool ▸ List.mem_cons_self),real (pool ▸ List.mem_cons_of_mem _ (List.mem_of_find?_eq_some found)),
      of_decide_eq_true (List.find?_some (p := fun ys => decide (observe xs ≠ observe ys)) found)⟩

theorem witness_complete {i : Input} {β : Type} [DecidableEq β] (allow : Permit i)
    (observe : List (Arm i) → β) (q : Arm i) :
    (witness? allow observe q).isSome = true ↔ ambiguous allow observe q = true := by
  have projection : outcomes allow observe q = (outcomes allow id q).map observe := by simp [outcomes]
  unfold ambiguous witness?
  rw [projection]
  cases outcomes allow id q with
  | nil => rfl
  | cons a rest =>
    simp only [List.map_cons,distinctValues,Option.isSome_map,List.any_map,List.find?_isSome,List.any_eq_true,
      Function.comp_apply,decide_eq_true_eq]

def chemicalPermit (i : Input) : Permit i := fun q row =>
  decide ((row.map (RingSeededFIFOTransport.chemicalKey i q)).Pairwise (· ≥ ·))

theorem chemical_permitted {i : Input} (q : Arm i) (row : List (Arm i)) :
    chemicalPermit i q row = true ↔ RingSeededFIFOTransport.Admissible (RingSeededFIFOTransport.chemicalKey i) q row :=
  decide_eq_true_iff

/-- All visited occurrence cells must have a result from the frozen schedule.
A scheduled absence contributes no bit; an unissued cell makes this walk's
observation unknown. -/
def checkedWord {i : Input} (read : Reader i) (rev : Bool) (seed : RS) (xs : List (Arm i)) :
    Option RingChemicalPriority.PairSpheres.Word :=
  if xs.all (fun x => (read x.occurrence).isSome) then some (RingClosedPairGroup.word read rev seed xs) else none

theorem checked_some {i : Input} (read : Reader i) (rev : Bool) (seed : RS) (xs : List (Arm i)) (b) :
    checkedWord read rev seed xs = some b ↔
      (∀ x ∈ xs, (read x.occurrence).isSome = true) ∧ RingClosedPairGroup.word read rev seed xs = b := by
  simp only [checkedWord,List.all_eq_true]
  split <;> simp_all

theorem checked_none {i : Input} (read : Reader i) (rev : Bool) (seed : RS) (xs : List (Arm i)) :
    checkedWord read rev seed xs = none ↔ ∃ x ∈ xs, read x.occurrence = none := by
  simp [checkedWord,List.all_eq_true]

def chemicalPairWords {i : Input} (read : Reader i) (rev : Bool) (seed : RS) (q : Arm i) :=
  outcomes (chemicalPermit i) (checkedWord read rev seed) q

private theorem chemical_outcomes {i : Input} (read : Reader i) (rev : Bool) (seed : RS)
    {q : Arm i} (valid : i.certified.LocalizedRerootCursorValid q) (b) :
    b ∈ chemicalPairWords read rev seed q ↔ ∃ xs, FIFO i
      (RingSeededFIFOTransport.Admissible (RingSeededFIFOTransport.chemicalKey i)) [q] xs ∧
      checkedWord read rev seed xs = b := by
  have eqn : (fun q row => chemicalPermit i q row = true) =
      RingSeededFIFOTransport.Admissible (RingSeededFIFOTransport.chemicalKey i) :=
    funext fun q => funext fun row => propext (chemical_permitted q row)
  simpa only [chemicalPairWords,eqn] using outcome_iff (chemicalPermit i) (checkedWord read rev seed) valid b

theorem chemical_pair_words {i : Input} (read : Reader i) (rev : Bool) (seed : RS)
    {q : Arm i} (valid : i.certified.LocalizedRerootCursorValid q) (b : RingChemicalPriority.PairSpheres.Word) :
    some b ∈ chemicalPairWords read rev seed q ↔ ∃ xs, FIFO i
      (RingSeededFIFOTransport.Admissible (RingSeededFIFOTransport.chemicalKey i)) [q] xs ∧
      (∀ x ∈ xs, (read x.occurrence).isSome = true) ∧ RingClosedPairGroup.word read rev seed xs = b := by
  simp only [chemical_outcomes read rev seed valid,checked_some]

theorem chemical_missing {i : Input} (read : Reader i) (rev : Bool) (seed : RS)
    {q : Arm i} (valid : i.certified.LocalizedRerootCursorValid q) :
    none ∈ chemicalPairWords read rev seed q ↔ ∃ xs, FIFO i
      (RingSeededFIFOTransport.Admissible (RingSeededFIFOTransport.chemicalKey i)) [q] xs ∧
      ∃ x ∈ xs, read x.occurrence = none := by
  simp only [chemical_outcomes read rev seed valid,checked_none]

abbrev ChemicalWalk (i : Input) (q : Arm i) (xs : List (Arm i)) :=
  FIFO i (RingSeededFIFOTransport.Admissible (RingSeededFIFOTransport.chemicalKey i)) [q] xs

/-- A complete frozen reader permits a total classification at every valid
molecular arm. The unique alternative is realized by a complete walk and
covers every walk. The other alternative provides two complete walks with
different PairList words. -/
theorem chemical_dichotomy {i : Input} (read : Reader i) (rev : Bool) (seed : RS)
    {q : Arm i} (valid : i.certified.LocalizedRerootCursorValid q)
    (complete : ∀ xs, ChemicalWalk i q xs → ∀ x ∈ xs, (read x.occurrence).isSome = true) :
    (∃ b, some b ∈ chemicalPairWords read rev seed q ∧
      ∀ xs, ChemicalWalk i q xs → checkedWord read rev seed xs = some b) ∨
    (∃ xs ys, ChemicalWalk i q xs ∧ ChemicalWalk i q ys ∧
      RingClosedPairGroup.word read rev seed xs ≠ RingClosedPairGroup.word read rev seed ys) := by
  obtain ⟨xs,hx⟩ := RingSeededFIFOTransport.walk_exists (RingSeededFIFOTransport.chemicalKey i) [q]
    (fun a ha => by obtain rfl := List.mem_singleton.mp ha; exact valid)
  let b := RingClosedPairGroup.word read rev seed xs
  have first := (chemical_pair_words read rev seed valid b).mpr ⟨xs,hx,complete xs hx,rfl⟩
  by_cases agree : ∀ ys, ChemicalWalk i q ys → RingClosedPairGroup.word read rev seed ys = b
  · exact Or.inl ⟨b,first,fun ys hy => (checked_some ..).mpr ⟨complete ys hy,agree ys hy⟩⟩
  · push_neg at agree
    obtain ⟨ys,hy,ne⟩ := agree
    exact Or.inr ⟨ys,xs,hy,hx,ne⟩

end TetraStereo.Engine.RingFIFOAlternatives
assert_kernel_only TetraStereo.Engine.RingFIFOAlternatives.successor_iff
assert_kernel_only TetraStereo.Engine.RingFIFOAlternatives.enumerate_iff
assert_kernel_only TetraStereo.Engine.RingFIFOAlternatives.outcome_iff
assert_kernel_only TetraStereo.Engine.RingFIFOAlternatives.ambiguous_iff
assert_kernel_only TetraStereo.Engine.RingFIFOAlternatives.chemical_pair_words
assert_kernel_only TetraStereo.Engine.RingFIFOAlternatives.chemical_missing
assert_kernel_only TetraStereo.Engine.RingFIFOAlternatives.chemical_dichotomy
assert_kernel_only TetraStereo.Engine.RingFIFOAlternatives.witness_issued
assert_kernel_only TetraStereo.Engine.RingFIFOAlternatives.witness_complete
