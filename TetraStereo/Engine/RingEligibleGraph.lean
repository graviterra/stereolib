import TetraStereo.Engine.RingGraphCache

/-! Eligibility-parametric bonded-path auxiliary scheduling. -/
set_option autoImplicit false

namespace TetraStereo.Engine.RingEligibleGraph
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingGraphPaths (Path Represents site represents_site)
open RingActiveDistanceSchedule (Cell View Rule distance height frozen sites evaluate)

variable {i : Input} (eligible : i.certified.Atom → Bool)

/-- Real occurrences whose atom is admitted by the supplied chemical policy. -/
def Eligible (q : Site i) : Prop :=
  q.val.node.provenance = .realAtom ∧ ∃ a, q.val.node.current? = some a ∧ eligible a = true

instance (q : Site i) : Decidable (Eligible eligible q) := by
  unfold Eligible
  infer_instance

def candidate (root : i.certified.Atom) (q : Site i) : Prop :=
  q.val.root = root ∧ q.val.node.current? ≠ some root ∧ Eligible eligible q

instance (root : i.certified.Atom) (q : Site i) : Decidable (candidate eligible root q) := by
  unfold candidate
  infer_instance

/-- Ineligible occurrences publish known absence for every input reading. -/
def SkipsIneligible (rule : Rule i) : Prop :=
  ∀ q read, ¬ Eligible eligible q → rule q read = some none

variable {eligible}

private theorem lookup {i : Input} (rule : Rule i) (root : i.certified.Atom) (before : View i)
    (queue : List (Site i)) (q : Site i) :
    RingSphereQueue.commit rule root before queue q = if q ∈ queue then rule q (RingSphereQueue.reader root before) else before q := by
  induction queue with
  | nil => rfl
  | cons x xs ih =>
    by_cases same : x = q
    · subst x; simp [RingSphereQueue.commit]
    · simpa only [RingSphereQueue.commit,List.map_cons,List.find?_cons,same,decide_false,cond_false,
        List.mem_cons,Ne.symm same,false_or] using ih

/-- A batch enumeration may use any order. Its membership law is the sole
inventory requirement; even repeated visits within a batch are harmless. -/
def Inventory {i : Input} (eligible : i.certified.Atom → Bool) (root : i.certified.Atom) (queue : Nat → List (Site i)) : Prop :=
  ∀ d q, q ∈ queue d ↔ candidate eligible root q ∧ distance q = d

def molecularQueue (i : Input) (eligible : i.certified.Atom → Bool) (root : i.certified.Atom) (d : Nat) : List (Site i) :=
  (sites i).filter fun q => decide (candidate eligible root q ∧ distance q = d)

theorem molecular_inventory (i : Input) (eligible : i.certified.Atom → Bool) (root : i.certified.Atom) : Inventory eligible root (molecularQueue i eligible root) := by
  intro d q
  have mem : q ∈ sites i := List.mem_attach ..
  simp [molecularQueue,mem]

private theorem reads_at {rule : Rule i} (skip : SkipsIneligible eligible rule)
    {root : i.certified.Atom} {store : View i} {d : Nat}
    (before : ∀ q, store q = if candidate eligible root q ∧ d < distance q then evaluate rule q else some none)
    {focus : Site i} (on : focus.val.root = root) (atDepth : distance focus = d) :
    RingSphereQueue.reader root store = frozen (evaluate rule) focus := by
  funext q
  by_cases here : q.val.root = root
  · by_cases original : q.val.node.current? = some root
    · simp [RingSphereQueue.reader,here,before,candidate,original,frozen,on]
    · by_cases found : Eligible eligible q
      · simp [RingSphereQueue.reader,here,before,candidate,original,found,frozen,on,atDepth]
      · have empty : evaluate rule q = some none :=
          (RingActiveDistanceSchedule.evaluate_eq rule q).trans (skip q _ found)
        simp [RingSphereQueue.reader,here,before,candidate,original,found,frozen,on,empty]
  · simp [RingSphereQueue.reader,here,frozen,on]

/-- Exact snapshot after *every* batch for any local rule. The operational
reader never consults distance, eligibility, or a publication-table oracle. -/
theorem run_exact {rule : Rule i} (skip : SkipsIneligible eligible rule)
    {root : i.certified.Atom} {queue : Nat → List (Site i)} (listed : Inventory eligible root queue)
    (k : Nat) (bound : k ≤ height i + 1) (q : Site i) :
    RingSphereQueue.run rule root queue k q =
      if candidate eligible root q ∧ height i < distance q + k then evaluate rule q else some none := by
  induction k generalizing q with
  | zero =>
    have upper := RingActiveDistanceSchedule.distance_bound q
    simp [RingSphereQueue.run,Nat.not_lt.mpr upper]
  | succ k ih =>
    have le : k ≤ height i := by omega
    have old (t : Site i) := ih (by omega) t
    simp only [RingSphereQueue.run,lookup,listed (height i - k) q]
    by_cases hit : candidate eligible root q ∧ distance q = height i - k
    · rw [if_pos hit,if_pos ⟨hit.1,by omega⟩]
      rw [reads_at skip (focus := q) (root := root) (store := RingSphereQueue.run rule root queue k) (fun t => by
        rw [old]; have eqn : (height i < distance t + k) ↔ height i - k < distance t := by omega
        simp only [eqn]) hit.1.1 hit.2]
      exact (RingActiveDistanceSchedule.evaluate_eq rule q).symm
    · rw [if_neg hit,old]
      by_cases keep : candidate eligible root q
      · have ne : distance q ≠ height i - k := fun h => hit ⟨keep,h⟩
        have eqn : (height i < distance q + k) ↔ height i < distance q + (k+1) := by omega
        simp only [eqn]
      · simp [keep]

theorem final_exact {rule : Rule i} (skip : SkipsIneligible eligible rule)
    {root : i.certified.Atom} {queue : Nat → List (Site i)} (listed : Inventory eligible root queue) :
    RingSphereQueue.finalCell rule root queue = evaluate rule (RingGroupedReport.origin i root) := by
  have positive {q : Site i} (h : candidate eligible root q) : 0 < distance q := by
    by_contra! zero
    have empty : q.val.address = [] := List.length_eq_zero_iff.mp (by change distance q = 0; omega)
    have same := RingGroupedReport.origin_unique q empty
    exact h.2.1 (by rw [← h.1]; exact (congrArg (fun t : Site i => t.val.node.current?) same).trans rfl)
  unfold RingSphereQueue.finalCell
  change rule (RingGroupedReport.origin i root) (RingSphereQueue.reader root (RingSphereQueue.run rule root queue (height i + 1))) = _
  rw [reads_at skip (focus := RingGroupedReport.origin i root) (root := root)
    (store := RingSphereQueue.run rule root queue (height i + 1)) (d := 0) (fun t => by
    rw [run_exact skip listed _ (by omega)]
    by_cases cand : candidate eligible root t
    · simp [cand,positive cand,show height i < distance t + (height i+1) by omega]
    · simp [cand]) rfl rfl]
  exact (RingActiveDistanceSchedule.evaluate_eq rule _).symm

private def select {i : Input} (eligible : i.certified.Atom → Bool) {r}
    (v : RingGraphCache.Visit i r) : Option (Site i) :=
  if v.atom ≠ r ∧ eligible v.atom = true then some (site v.path) else none

/-- Enumerate eligible simple bonded paths at their original distance. -/
def queue (i : Input) (eligible : i.certified.Atom → Bool) (r : i.certified.Atom) (n : Nat) :=
  (RingGraphCache.sphere i r n).filterMap (select eligible)

theorem inventory (i : Input) (eligible : i.certified.Atom → Bool) (r : i.certified.Atom) :
    Inventory eligible r (queue i eligible r) := by
  intro n q
  constructor
  · intro found
    obtain ⟨v,mem,hit⟩ := List.mem_filterMap.mp found
    unfold select at hit
    split at hit
    · rename_i ok
      obtain rfl := Option.some.inj hit
      have rep := represents_site v.path
      have depth := RingGraphPaths.path_length rep
      have size := (RingGraphCache.sphere_iff v n).mp mem
      exact ⟨⟨rep.1,fun h => ok.1 (Option.some.inj (rep.2.2.2.symm.trans h)),
        rep.2.2.1,v.atom,rep.2.2.2,ok.2⟩,by omega⟩
    · contradiction
  · rintro ⟨⟨on,other,real,a,atom,allowed⟩,depth⟩
    obtain ⟨b,hb,path⟩ := RingGraphPaths.site_path q real
    have atomEq : b = a := Option.some.inj (hb.symm.trans atom)
    subst b
    have p : Path i r q.val.node.history a := on ▸ path
    let v : RingGraphCache.Visit i r := ⟨_,a,p⟩
    have rep : Represents q r q.val.node.history a := ⟨on,rfl,real,atom⟩
    have shape := RingGraphPaths.path_length rep
    have mem : v ∈ RingGraphCache.sphere i r n := (RingGraphCache.sphere_iff v n).mpr (by
      change q.val.node.history.length = n+1
      omega)
    refine List.mem_filterMap.mpr ⟨v,mem,?_⟩
    have different : a ≠ r := fun h => other (atom.trans (congrArg some h))
    exact (if_pos ⟨different,allowed⟩).trans
      (congrArg some (RingGraphPaths.unique_site (represents_site p) rep))

def root (i : Input) (eligible : i.certified.Atom → Bool) (rule : Rule i)
    (r : i.certified.Atom) : Cell :=
  RingSphereQueue.finalCell rule r (queue i eligible r)

theorem root_exact (rule : Rule i) (skip : SkipsIneligible eligible rule)
    (r : i.certified.Atom) :
    root i eligible rule r = evaluate rule (RingGroupedReport.origin i r) :=
  final_exact skip (inventory i eligible r)

private theorem path_of_read {i : Input} {r a} (q : Site i) (on : q.val.root = r)
    (real : q.val.node.provenance = .realAtom) (current : q.val.node.current? = some a) :
    Path i r q.val.node.history a := by
  obtain ⟨b,found,path⟩ := RingGraphPaths.site_path q real
  obtain rfl := Option.some.inj (found.symm.trans current)
  exact on ▸ path

abbrev Continuation (i : Input) (r : i.certified.Atom) :=
  ∀ {h a}, Path i r h a → Cell

/-- Only a deeper simple path ending at a different eligible atom can make a
recursive demand. Atoms in other digraphs are inaccessible. -/
def reader (eligible : i.certified.Atom → Bool) (r : i.certified.Atom) (length : Nat) (next : Continuation i r) : View i :=
  fun q =>
    if on : q.val.root = r then
      match current : q.val.node.current? with
      | none => some none
      | some a =>
        if ok : q.val.node.provenance = .realAtom ∧ length < q.val.node.history.length ∧
            a ≠ r ∧ eligible a = true then
          next (path_of_read q on ok.1 current)
        else some none
    else none

/-- Bonded-path lookup agrees with a frozen store whenever it supplies
every deeper eligible site and the store gives absence at ineligible occurrences. -/
theorem reader_eq_frozen {r h a} (store : View i)
    (empty : ∀ q, ¬ Eligible eligible q → store q = some none)
    (p : Path i r h a) (next : Continuation i r)
    (deeper : ∀ {k b} (child : Path i r k b), h.length < k.length → b ≠ r →
      eligible b = true →
      next child = store (site child)) :
    reader eligible r h.length next = frozen (store) (site p) := by
  funext q
  have rep := represents_site p
  have size := RingGraphPaths.path_length rep
  have len := i.certified.carrierOccurrence_history_length_eq_address_succ q
  change q.val.node.history.length = distance q + 1 at len
  have farther : (distance (site p) < distance q) ↔ h.length < q.val.node.history.length := by omega
  unfold reader frozen
  simp only [rep.1,farther]
  by_cases on : q.val.root = r
  · simp only [dif_pos on,if_neg (not_not_intro on)]
    split
    · rename_i current
      simp only [current,ne_eq,reduceCtorEq,not_false_eq_true,and_true]
      split
      · symm
        apply empty
        rintro ⟨_,b,found,_⟩
        simp [current] at found
      · rfl
    · rename_i b current
      simp only [current,ne_eq,Option.some.injEq]
      by_cases ok : q.val.node.provenance = .realAtom ∧ h.length < q.val.node.history.length ∧
          b ≠ r ∧ eligible b = true
      · simp only [dif_pos ok,if_pos (And.intro ok.2.1 ok.2.2.1)]
        let child := path_of_read q on ok.1 current
        have same : site child = q := RingGraphPaths.unique_site (represents_site child) ⟨on,rfl,ok.1,current⟩
        exact (deeper child ok.2.1 ok.2.2.1 ok.2.2.2).trans (congrArg _ same)
      · simp only [dif_neg ok]
        split
        · rename_i visible
          symm
          apply empty
          rintro ⟨real,b',found,allowed⟩
          obtain rfl := Option.some.inj (found.symm.trans current)
          exact (ok ⟨real,visible.1,visible.2,allowed⟩).elim
        · rfl
  · simp only [dif_neg on,if_pos on]

open RingNestedActivePair (Labels)
abbrev LocalLaw (i : Input) := Site i → View i → Option Labels → Prop

/-- A tree of molecular decisions. Every child value used by the local derivation must
itself have a derivation at its full atom path. A completed refusal is a possible value.
A missing reading cannot witness coverage of a required child. -/
inductive Derives (eligible : i.certified.Atom → Bool) (law : LocalLaw i) (r : i.certified.Atom) :
    {h : List i.certified.Atom} → {a : i.certified.Atom} → Path i r h a → Option Labels → Prop where
  | step {h a v} (p : Path i r h a)
      (next : ∀ {k b}, Path i r k b → Option Labels)
      (observed : law (site p) (reader eligible r h.length (fun c => some (next c))) v)
      (children : ∀ {k b} (c : Path i r k b), h.length < k.length → b ≠ r →
        eligible b = true →
        Derives eligible law r c (next c)) : Derives eligible law r p v

/-- Agreement on deeper eligible paths suffices for the whole local reader,
including the inward direction when a retained site is rerooted. -/
theorem reader_congr {r} (len : Nat) (l m : Continuation i r)
    (same : ∀ {k b} (c : Path i r k b), len < k.length → b ≠ r →
      eligible b = true → l c = m c) :
    reader eligible r len l = reader eligible r len m := by
  funext q
  unfold reader
  split
  · split
    · rfl
    · split
      · rename_i ok
        exact same _ ok.2.1 ok.2.2.1 ok.2.2.2
      · rfl
  · rfl

theorem Derives.unique {r h a law} {p : Path i r h a} {v w}
    (one : ∀ f read x y, law f read x → law f read y → x = y)
    (x : Derives eligible law r p v) (y : Derives eligible law r p w) : v = w := by
  induction x generalizing w with
  | step p next observed _ ih =>
    cases y with
    | step _ next' observed' children' =>
      have eqn := reader_congr _ (fun c => some (next c)) (fun c => some (next' c)) (by
        intro k b child longer other four
        exact congrArg some (ih child longer other four (children' child longer other four)))
      rw [← eqn] at observed'
      exact one _ _ _ _ observed observed'

/-- A molecular derivation recurses on bonded paths. Its only store
requirements are coverage, absence at ineligible occurrences and local agreement. -/
theorem derives_iff_store (store : View i)
    (empty : ∀ q, ¬ Eligible eligible q → store q = some none)
    (coveredAt : ∀ q, (store q).isSome = true)
    {law : LocalLaw i} (localLaw : ∀ q v, law q (frozen store q) v ↔ store q = some v)
    {r h a} (p : Path i r h a) (v : Option Labels) :
    Derives eligible law r p v ↔ store (site p) = some v := by
  constructor
  · intro tree
    induction tree with
    | step p next observed children ih =>
      have same := reader_eq_frozen store empty p (fun c => some (next c)) (by
        intro k b c deeper other four
        exact (ih c deeper other four).symm)
      rw [same] at observed
      exact (localLaw _ _).mp observed
  · suffices ∀ n {k b} (c : Path i r k b), i.certified.certified.input.molecule.atomCount < k.length + n →
        ∀ w, store (site c) = some w → Derives eligible law r c w from
      this (i.certified.certified.input.molecule.atomCount + 1) p (by omega) v
    intro n
    induction n with
    | zero =>
      intro k b c enough
      have upper := RingGraphAuxiliaries.length_bound c
      omega
    | succ n ih =>
      intro k b c enough w issued
      let next {l d} (child : Path i r l d) := (store (site child)).getD none
      have covered {l d} (child : Path i r l d) : store (site child) = some (next child) := by
        obtain ⟨z,hz⟩ := Option.isSome_iff_exists.mp
          (coveredAt (site child))
        simp [next,hz]
      apply Derives.step c next
      · rw [reader_eq_frozen store empty c (fun child => some (next child)) (fun child _ _ _ => (covered child).symm)]
        exact (localLaw _ _).mpr issued
      · intro l d child longer _ _
        exact ih child (by omega) _ (covered child)

end TetraStereo.Engine.RingEligibleGraph

assert_kernel_only TetraStereo.Engine.RingEligibleGraph.inventory
assert_kernel_only TetraStereo.Engine.RingEligibleGraph.run_exact
assert_kernel_only TetraStereo.Engine.RingEligibleGraph.root_exact
assert_kernel_only TetraStereo.Engine.RingEligibleGraph.reader_eq_frozen
assert_kernel_only TetraStereo.Engine.RingEligibleGraph.derives_iff_store
