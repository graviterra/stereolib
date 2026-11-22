import TetraStereo.Engine.RingSiblingKeyObstruction

set_option autoImplicit false

namespace TetraStereo.Engine.RingParentGroupWidth
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingRetainedChemicalTrace

private abbrev children (i : Input) (q : Arm i) := i.certified.executableLocalizedRerootChildren q

/-- The molecular nonterminal projection, including all equivalent children with multiplicity. -/
def eligible (i : Input) (q : Arm i) :=
  (children i q).filter fun c => !(children i c).isEmpty

private abbrev z (i : Input) (q : Arm i) := (RingActivePairs.z? i q).getD 0

/-- Decode the nonterminal atomic-number multiset from the first two FIFO spheres. -/
def readEligible : List Nat → Word → List Nat
  | a::as,_::cs::rest =>
    if cs.isEmpty then readEligible as rest else a :: readEligible as rest
  | _,_ => []

def eligibleWord (w : Word) : List Nat := readEligible (w[2]?.getD []) (w.drop 3)

private def ranked (cs : List Key) := cs.mergeSort (fun a b => decide ([b.atomic.word] ≤ [a.atomic.word]))
private abbrev numbers (ks : List Key) := ks.map fun k => k.root.atomic
private abbrev arity (k : Key) := (k.atomic.word[2]?.getD []).length
private def kept (k : Key) : Option Nat := if arity k = 0 then none else some k.root.atomic

private theorem queue (o : Observation) (cs now later : List Key) :
    ∃ row, queueRows .atomic (assemble o cs :: now) later =
      row :: numbers (ranked cs) :: queueRows .atomic now (later ++ ranked cs) := by
  exact ⟨_,queue_pop .atomic o cs now later⟩

private theorem start (o : Observation) (cs : List Key) (formed : WellFormed (assemble o cs)) :
    ∃ row, (assemble o cs).atomic.word =
      [o.atomic] :: row :: numbers (ranked cs) :: queueRows .atomic (ranked cs) [] := by
  obtain ⟨row,pop⟩ := queue o cs [] []
  change queueRows .atomic [assemble o cs] [] = row :: numbers (ranked cs) :: queueRows .atomic [] ([] ++ ranked cs) at pop
  rw [List.nil_append,queue_rotate] at pop
  exact ⟨row,(queue_start .atomic _ formed).trans (congrArg _ pop)⟩

private theorem arity_assemble (o : Observation) (cs : List Key) (formed : WellFormed (assemble o cs)) :
    arity (assemble o cs) = cs.length := by
  obtain ⟨row,h⟩ := start o cs formed
  simp [arity,h,ranked]

private abbrev Form (k : Key) := ∃ o cs, k = assemble o cs ∧ WellFormed k

private theorem rows (ks later : List Key) (valid : ∀ k ∈ ks, Form k) :
    readEligible (numbers ks) (queueRows .atomic ks later) = ks.filterMap kept := by
  induction ks generalizing later with
  | nil => rfl
  | cons k ks ih =>
    obtain ⟨o,cs,rfl,formed⟩ := valid k List.mem_cons_self
    obtain ⟨r,out⟩ := queue o cs ks later
    have tail := ih (later ++ ranked cs) (fun k hk => valid k (List.mem_cons_of_mem _ hk))
    simp only [List.map_cons,out,readEligible,List.filterMap_cons,kept,arity_assemble o cs formed]
    have empty : (numbers (ranked cs)).isEmpty = cs.isEmpty := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.isEmpty_iff_length_eq_zero,List.length_map,ranked,List.length_mergeSort]
    rw [empty]
    cases cs <;> simp_all

private theorem decoder (o : Observation) (cs : List Key) (valid : ∀ k ∈ cs, Form k)
    (formed : WellFormed (assemble o cs)) :
    (eligibleWord (assemble o cs).atomic.word).Perm (cs.filterMap kept) := by
  obtain ⟨row,h⟩ := start o cs formed
  have perm : (ranked cs).Perm cs := List.mergeSort_perm ..
  simpa [eligibleWord,h,rows _ _ (fun k hk => valid k (perm.mem_iff.mp hk))] using perm.filterMap kept

private theorem paired {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) : List.Forall₂ (fun x y => f x = some y) xs ys := by
  induction xs generalizing ys with
  | nil => obtain rfl := Option.some.inj h; exact .nil
  | cons x xs ih =>
    rw [List.mapM_cons] at h
    obtain ⟨a,ha,tail⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨as,hs,out⟩ := Option.bind_eq_some_iff.mp tail
    obtain rfl := Option.some.inj out
    exact .cons ha (ih hs)

private theorem withMembers {α β : Type} {P Q : α → β → Prop} {xs : List α} {ys : List β}
    (r : List.Forall₂ P xs ys) (h : ∀ a ∈ xs, ∀ b ∈ ys, P a b → Q a b) : List.Forall₂ Q xs ys := by
  apply List.forall₂_of_length_eq_of_get r.length_eq
  intro idx hx hy
  exact h _ (List.get_mem ..) _ (List.get_mem ..) (r.get hx hy)

private theorem member {α β : Type} {P : α → β → Prop} {xs : List α} {ys : List β}
    (r : List.Forall₂ P xs ys) {b : β} (hb : b ∈ ys) : ∃ a, P a b := by
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp hb
  rw [← hj]
  have bound : j.val < xs.length := by simpa only [r.length_eq] using j.isLt
  exact ⟨_,r.get bound j.isLt⟩

private theorem child_kept {i : Input} {c : Arm i} {k : Key} (src : Expansion i c k)
    (valid : i.certified.LocalizedRerootCursorValid c) :
    kept k = (if (children i c).isEmpty then none else some (z i c)) := by
  obtain ⟨l,found⟩ := RingRetainedChemicalCoverage.key_total i (RingRetainedChemicalCoverage.admitted_atoms i) c valid
  obtain rfl := RingAtomicProfileShape.expansion_unique (key_source found) src
  have label := RingSiblingKeyObstruction.key_number found
  cases src with
  | @node _ cs o ks frame obs lookup hit branches =>
    have same := (i.certified.localizedRerootChildren?_eq_some_iff c cs).mpr frame
    have actual := Option.some.inj (same.symm.trans (i.certified.localizedRerootChildren?_eq_some_executable c))
    have size := (paired hit).length_eq
    unfold children
    rw [← actual]
    simp only [kept,arity_assemble o ks (key_source found).formed,z,label,Option.getD_some,← size]
    cases cs <;> rfl

/-- This holds even at parents where tied nonterminal siblings prevent a unique stereo walk. -/
theorem molecular_projection {i : Input} {q : Arm i} {k : Key} (read : key? i q = some k) :
    (eligibleWord k.atomic.word).Perm ((eligible i q).map (z i)) := by
  cases key_source read with
  | @node _ cs o ks frame obs lookup hit branches =>
    have act := Option.some.inj (((i.certified.localizedRerootChildren?_eq_some_iff q cs).mpr frame).symm.trans
      (i.certified.localizedRerootChildren?_eq_some_executable q))
    have src := withMembers (paired hit) fun c hc _ _ hr => branches c hc hr
    have valid (c) (hc : c ∈ cs) := i.certified.localizedRerootChild_valid q c cs frame hc
    have good (k : Key) (hk : k ∈ ks) : Form k := by
      obtain ⟨c,exp⟩ := member src hk
      cases exp with
      | node frame obs lookup hit branches =>
        exact ⟨_,_,rfl,(Expansion.node frame obs lookup hit branches).formed⟩
    refine (decoder o ks good (key_source read).formed).trans ?_
    unfold eligible children
    rw [← act]
    suffices ks.filterMap kept = (cs.filter fun c => !(children i c).isEmpty).map (z i) by rw [this]
    have witnesses := withMembers src fun c hc _ _ exp => child_kept exp (valid c hc)
    clear * - witnesses
    induction witnesses with
    | nil => rfl
    | @cons c k cs ks head _ ih =>
      cases e : (children i c).isEmpty <;> simp_all

/-- A returned constitutional tie forces equal nonterminal molecular atom populations by element. -/
theorem tie_projection {i : Input} {f a b : Site i} {t}
    (prior : compareAt? i f a b = some t) (tie : cipTraceOutcome t = .eq) :
    ((eligible i ⟨a,some f⟩).map (z i)).Perm ((eligible i ⟨b,some f⟩).map (z i)) := by
  unfold compareAt? at prior
  split at prior <;> try contradiction
  unfold trace? at prior
  obtain ⟨x,hx,more⟩ := Option.bind_eq_some_iff.mp prior
  obtain ⟨y,hy,out⟩ := Option.bind_eq_some_iff.mp more
  obtain rfl := Option.some.inj out
  change compareKeys x y = .eq at tie
  rw [RingRetainedChemicalPreorder.compare_word] at tie
  obtain rfl := RingPairGateCount.key_eq (key_source hx).formed (key_source hy).formed (Std.compare_eq_eq_iff_eq.mp tie)
  exact (molecular_projection hx).symm.trans (molecular_projection hy)

/-- Count the consecutive groups of the sorted row, comparing neighboring entries
as in Sort.getGroups. A zero comparison joins the current group. -/
def countFrom {α : Type} (same : α → α → Bool) : Nat → α → List α → List Nat
  | n,_,[] => [n]
  | n,p,c::cs => if same p c then countFrom same (n+1) c cs else n :: countFrom same 1 c cs

def widths {α : Type} (same : α → α → Bool) : List α → List Nat
  | [] => []
  | p::cs => countFrom same 1 p cs

private theorem counts_map {α : Type} (label : α → Nat) (same : α → α → Bool)
    (xs : List α) (p : α) (n : Nat)
    (agreement : ∀ a ∈ p::xs, ∀ b ∈ p::xs, same a b = (label a == label b)) :
    countFrom same n p xs = countFrom (· == ·) n (label p) (xs.map label) := by
  induction xs generalizing n p with
  | nil => rfl
  | cons x xs ih =>
    have h := agreement p (by simp) x (by simp)
    have rest := fun a (ha : a ∈ x::xs) b (hb : b ∈ x::xs) =>
      agreement a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)
    simp only [countFrom,List.map_cons,h]
    split <;> simp only [ih _ _ rest]

private theorem widths_map {α : Type} (label : α → Nat) (same : α → α → Bool)
    (xs : List α) (agreement : ∀ a ∈ xs, ∀ b ∈ xs, same a b = (label a == label b)) :
    widths same xs = widths (· == ·) (xs.map label) := by
  cases xs with
  | nil => rfl
  | cons p xs => exact counts_map label same xs p 1 agreement

/-- A row is a permutation of the eligible molecular children, respects Rule 1a
at the head, and its earlier comparisons leave equal-element siblings together.
The comparison at each parent may use a different publication context. -/
structure ElementGroups (i : Input) (q : Arm i) (same : Arm i → Arm i → Bool)
    (row : List (Arm i)) : Prop where
  complete : row.Perm (eligible i q)
  byElement : (row.map (z i)).Pairwise (· ≥ ·)
  localTie : ∀ a ∈ row, ∀ b ∈ row, same a b = (z i a == z i b)

/-- At equivalent parents this local criterion suffices for identical numbers
of priority groups and identical widths at each ordinal. It permits repeated
nonterminal elements and uses no correspondence between child occurrence IDs. -/
theorem same_widths {i : Input} {f a b : Site i} {t} {left right}
    {leq req : Arm i → Arm i → Bool} (prior : compareAt? i f a b = some t)
    (tie : cipTraceOutcome t = .eq) (l : ElementGroups i ⟨a,some f⟩ leq left)
    (r : ElementGroups i ⟨b,some f⟩ req right) :
    widths leq left = widths req right := by
  have perm := (l.complete.map (z i)).trans ((tie_projection prior tie).trans (r.complete.map (z i)).symm)
  have aligned := List.Perm.eq_of_pairwise (fun _ _ _ _ ab ba => le_antisymm ba ab) l.byElement r.byElement perm
  rw [widths_map _ _ _ l.localTie,widths_map _ _ _ r.localTie,aligned]

/-- A later stereo comparison can split a constitutional class only inside
that class. Its result outside that class is immaterial to adjacent groups. -/
def tieAfter (i : Input) (later : Arm i → Arm i → Bool) (a b : Arm i) : Bool :=
  key? i a == key? i b && later a b

private theorem separated {α : Type} (same : α → α → Bool) (xs : List α) (p : α)
    (n : Nat) (none : (p::xs).Pairwise (fun a b => same a b = false)) :
    countFrom same n p xs = n :: List.replicate xs.length 1 := by
  induction xs generalizing n p with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨first,rest⟩ := List.pairwise_cons.mp none
    simp [countFrom,first x List.mem_cons_self,ih x 1 rest,List.replicate_succ]

/-- The existing molecular sibling recognizer precludes any earlier-rule tie
between two distinct nonterminal children. This holds in every row ordering
and for every later auxiliary comparison. -/
theorem singleton_widths {i : Input} {q : Arm i} {row : List (Arm i)}
    (covered : (RingRetainedSiblingOrder.chemicalChildren? i q).isSome = true)
    (complete : row.Perm (eligible i q)) (later : Arm i → Arm i → Bool) :
    widths (tieAfter i later) row = List.replicate row.length 1 := by
  have clear := (RingSiblingKeyObstruction.covered_iff i q).mp covered
  have distinct : row.Nodup := complete.nodup_iff.mpr ((i.certified.executableLocalizedRerootChildren_nodup q).filter _)
  have strict := distinct.imp_of_mem (S := fun a b => tieAfter i later a b = false) (by
    intro a b ha hb ne
    obtain ⟨atA,live⟩ := List.mem_filter.mp (complete.mem_iff.mp ha)
    obtain ⟨atB,_⟩ := List.mem_filter.mp (complete.mem_iff.mp hb)
    obtain ⟨k,ka⟩ := RingRetainedChemicalCoverage.key_total i (RingRetainedChemicalCoverage.admitted_atoms i) a
      (i.certified.localizedRerootChild_valid q a _ (i.certified.executableLocalizedRerootChildren_declarative q) atA)
    have diff : key? i b ≠ some k := fun kb => clear ⟨a,atA,b,atB,ne,k,ka,kb,Or.inl (by
      intro empty; simp [empty] at live)⟩
    simp [tieAfter,ka,Ne.symm diff])
  cases row with
  | nil => rfl
  | cons p xs => exact (separated _ xs p 1 strict).trans (List.replicate_succ ..).symm

/-- A tied parent comparison and two successful chemical sibling checks give
the whole group-width vector independently of storage order, Rule 4a, and the
eventual reference. This includes equal-element children distinguished at depth. -/
theorem covered_widths {i : Input} {f a b : Site i} {t} {left right : List (Arm i)}
    (prior : compareAt? i f a b = some t) (tie : cipTraceOutcome t = .eq)
    (cl : (RingRetainedSiblingOrder.chemicalChildren? i ⟨a,some f⟩).isSome = true)
    (cr : (RingRetainedSiblingOrder.chemicalChildren? i ⟨b,some f⟩).isSome = true)
    (pl : left.Perm (eligible i ⟨a,some f⟩)) (pr : right.Perm (eligible i ⟨b,some f⟩))
    (laterL laterR : Arm i → Arm i → Bool) :
    widths (tieAfter i laterL) left = widths (tieAfter i laterR) right := by
  have eqn := (tie_projection prior tie).length_eq
  simp only [List.length_map] at eqn
  rw [singleton_widths cl pl,singleton_widths cr pr,pl.length_eq,pr.length_eq,eqn]

end TetraStereo.Engine.RingParentGroupWidth

assert_kernel_only TetraStereo.Engine.RingParentGroupWidth.molecular_projection
assert_kernel_only TetraStereo.Engine.RingParentGroupWidth.tie_projection
assert_kernel_only TetraStereo.Engine.RingParentGroupWidth.same_widths
assert_kernel_only TetraStereo.Engine.RingParentGroupWidth.singleton_widths
assert_kernel_only TetraStereo.Engine.RingParentGroupWidth.covered_widths
