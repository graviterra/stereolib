import TetraStereo.Engine.RingAtomicProfileShape

set_option autoImplicit false

namespace TetraStereo.Engine.RingSpherePopulation

open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm)
open RingNestedActivePair (Reader Visit Walk NodeSource)

/-- Every child in the full rerooted carrier participates, including leaves with
no published descriptor and duplicate occurrences reached by a different path. -/
def children (i : Input) (q : Arm i) := i.certified.executableLocalizedRerootChildren q

def next (i : Input) (qs : List (Arm i)) := qs.flatMap (children i)

/-- A different sibling permutation may be chosen for every parent in every
sphere. An empty child list stops only its own branch. -/
inductive Hierarchy (i : Input) : List (Arm i) → List (List (Arm i)) → Prop where
  | stop : Hierarchy i [] []
  | layer {q qs rows rest}
      (parents : List.Forall₂ (fun a cs => cs.Perm (children i a)) (q::qs) rows)
      (below : Hierarchy i rows.flatten rest) : Hierarchy i (q::qs) ((q::qs)::rest)

private theorem next_perm {i : Input} {qs : List (Arm i)} {rows}
    (parents : List.Forall₂ (fun a cs => cs.Perm (children i a)) qs rows) :
    rows.flatten.Perm (next i qs) := by
  induction parents with
  | nil => exact .refl _
  | cons head _ ih => exact head.append ih

/-- Any two full legal hierarchies from the same starting multiset agree on
each distance sphere with multiplicity. The order choices can be unrelated. -/
theorem same_spheres {i : Input} {qs ts : List (Arm i)} {xs ys}
    (same : qs.Perm ts) (left : Hierarchy i qs xs) (right : Hierarchy i ts ys) :
    List.Forall₂ List.Perm xs ys := by
  induction left generalizing ts ys with
  | stop =>
    obtain rfl := same.symm.eq_nil
    cases right
    exact .nil
  | @layer q qs rows rest parents below ih =>
    cases right with
    | stop => have eqn := same.eq_nil; contradiction
    | @layer t ts rows' rest' parents' below' =>
      exact .cons same (ih ((next_perm parents).trans ((same.flatMap_right _).trans (next_perm parents').symm)) below')

/-- Deterministic unsorted enumeration in the molecular carrier's native child
order. The valid-cursor theorem below gives the complete bound used by `full`. -/
def layers (i : Input) : Nat → List (Arm i) → List (List (Arm i))
  | 0,_ | _+1,[] => []
  | n+1,q::qs => (q::qs) :: layers i n (next i (q::qs))

def full (i : Input) (qs : List (Arm i)) :=
  layers i (2*(i.certified.certified.input.molecule.atomCount+2)+2) qs

private theorem native_rows (i : Input) (qs : List (Arm i)) :
    List.Forall₂ (fun a cs => cs.Perm (children i a)) qs (qs.map (children i)) := by
  induction qs with
  | nil => exact .nil
  | cons _ _ ih => exact .cons (.refl _) ih

theorem layers_complete (i : Input) : ∀ (n : Nat) (qs : List (Arm i)),
    (∀ a ∈ qs, i.certified.LocalizedRerootCursorValid a ∧ i.certified.localizedRerootCursorBudget a < n) →
    Hierarchy i qs (layers i n qs)
  | 0,[],_ | _+1,[],_ => .stop
  | 0,q::_,bound => by have := (bound q List.mem_cons_self).2; omega
  | n+1,q::qs,bound => by
    have rest := layers_complete i n (next i (q::qs)) (by
      intro c hc
      obtain ⟨a,ha,hc⟩ := List.mem_flatMap.mp hc
      have frame := i.certified.executableLocalizedRerootChildren_declarative a
      have parent := bound a ha
      have smaller := i.certified.localizedRerootChild_budget_lt a c _ parent.1 frame hc
      exact ⟨i.certified.localizedRerootChild_valid a c _ frame hc,by omega⟩)
    exact Hierarchy.layer (native_rows i (q::qs)) rest

theorem full_complete {i : Input} {qs : List (Arm i)}
    (valid : ∀ q ∈ qs, i.certified.LocalizedRerootCursorValid q) : Hierarchy i qs (full i qs) := by
  apply layers_complete
  intro q h
  have limit := i.certified.localizedRerootCursorBudget_le_twice q
  exact ⟨valid q h,by omega⟩

/-- Directed molecular reachability in exactly the given number of reroot
steps. The original cursor can point inward, outward or be an uncut root. -/
inductive AtDistance (i : Input) : Nat → Arm i → Arm i → Prop where
  | here {q} : AtDistance i 0 q q
  | descend {n q c t} (child : c ∈ children i q) (rest : AtDistance i n c t) :
      AtDistance i (n+1) q t

def atDistance (i : Input) : Nat → List (Arm i) → List (Arm i)
  | 0,qs => qs
  | d+1,qs => atDistance i d (next i qs)

theorem mem_distance {i : Input} (d : Nat) (qs : List (Arm i)) (t : Arm i) :
    t ∈ atDistance i d qs ↔ ∃ q ∈ qs, AtDistance i d q t := by
  induction d generalizing qs with
  | zero =>
    constructor
    · exact fun h => ⟨t,h,.here⟩
    · rintro ⟨q,h,step⟩; cases step; exact h
  | succ d ih =>
    rw [atDistance,ih]
    constructor
    · rintro ⟨c,hc,further⟩
      obtain ⟨q,hq,child⟩ := List.mem_flatMap.mp hc
      exact ⟨q,hq,.descend child further⟩
    · rintro ⟨q,hq,step⟩
      cases step with
      | descend child further => exact ⟨_,List.mem_flatMap.mpr ⟨q,hq,child⟩,further⟩

theorem AtDistance.root_and_budget {i : Input} {d q t} (path : AtDistance i d q t)
    (valid : i.certified.LocalizedRerootCursorValid q) :
    t.occurrence.val.root = q.occurrence.val.root ∧
      i.certified.LocalizedRerootCursorValid t ∧
      i.certified.localizedRerootCursorBudget t + d ≤ i.certified.localizedRerootCursorBudget q := by
  induction path with
  | here => exact ⟨rfl,valid,by omega⟩
  | @descend n q c t child _ ih =>
    have frame := i.certified.executableLocalizedRerootChildren_declarative q
    have parent := i.certified.localizedRerootChildren_root_eq q c _ frame child
    have smaller := i.certified.localizedRerootChild_budget_lt q c _ valid frame child
    have below := ih (i.certified.localizedRerootChild_valid q c _ frame child)
    exact ⟨below.1.trans parent,below.2.1,by have := below.2.2; omega⟩

private theorem distance_perm {i : Input} (d : Nat) {qs ts : List (Arm i)} (same : qs.Perm ts) :
    (atDistance i d qs).Perm (atDistance i d ts) := by
  induction d generalizing qs ts with
  | zero => exact same
  | succ d ih => exact ih (same.flatMap_right _)

private theorem distance_empty {i : Input} (d : Nat) : atDistance i d [] = [] := by
  induction d with
  | zero => rfl
  | succ d ih => exact ih

/-- Every realized sphere consists exactly of the addressed molecular visits at
that distance. Beyond the final sphere its population is empty. -/
theorem layer_at {i : Input} {qs : List (Arm i)} {xs} (h : Hierarchy i qs xs) (d : Nat) :
    (xs[d]?.getD []).Perm (atDistance i d qs) := by
  induction h generalizing d with
  | stop => rw [distance_empty]; exact .refl _
  | @layer q qs rows rest ps below ih =>
    cases d with
    | zero => exact .refl _
    | succ d => exact (ih d).trans (distance_perm d (next_perm ps))

/-- The address, atomic number, full child count and both publications from the
actual reader are observed at the very same cursor. A missing cell remains missing. -/
def observe (i : Input) (read : Reader i) (q : Arm i) : Option Visit := do
  let z ← RingActivePairs.z? i q
  RingNestedActivePair.visit read q z (children i q).length

private theorem node_observed {i : Input} {read : Reader i} {q : Arm i} {data}
    (s : NodeSource i read q data) : observe i read q = some data.1 := by
  have degree := s.degree.trans s.order.complete.length_eq
  have ok : (children i q).length ≠ 0 ∨ data.1.publication.isNone = true := by
    by_cases zero : data.1.children = 0
    · rw [s.leaf zero]; exact Or.inr rfl
    · exact Or.inl (fun h => zero (degree.trans h))
  cases data with
  | mk v cs =>
    cases v with
    | mk addr num arity pub =>
      have consistent := s.physical
      simp only [observe,s.number,RingNestedActivePair.visit,s.state,Option.bind_eq_bind,Option.bind_some,
        if_pos (And.intro consistent ok),Option.pure_def,Option.some.injEq]
      exact congrArg₂ (fun a d => Visit.mk a num d pub) s.address.symm degree.symm

private theorem walk_row {i : Input} {read : Reader i} {qs : List (Arm i)} {data}
    (src : List.Forall₂ (NodeSource i read) qs data) :
    List.Forall₂ (fun a cs => cs.Perm (children i a)) qs (data.map Prod.snd) ∧
    qs.map (observe i read) = (data.map Prod.fst).map some := by
  induction src with
  | nil => exact ⟨.nil,rfl⟩
  | cons first _ ih => exact ⟨.cons first.order.complete ih.1,congrArg₂ List.cons (node_observed first) ih.2⟩

/-- The independent hierarchy of actual directed cursors realizes every
reported row of a molecular stereochemical walk, including its publications. -/
theorem realize_walk {i : Input} {read : Reader i} {qs : List (Arm i)} {vs}
    (w : Walk i read qs vs) :
    ∃ hs, Hierarchy i qs hs ∧ hs.map (List.map (observe i read)) = vs.map (List.map some) := by
  induction w with
  | empty => exact ⟨[],.stop,rfl⟩
  | @layer q qs data tail visits below ih =>
    obtain ⟨hs,hier,labels⟩ := ih
    have row := walk_row visits
    refine ⟨(q::qs)::hs,.layer row.1 hier,?_⟩
    exact congrArg₂ List.cons row.2 labels

theorem project {α β : Type} (f : α → β) {xs ys : List (List α)}
    (p : List.Forall₂ List.Perm xs ys) : List.Forall₂ List.Perm (xs.map (List.map f)) (ys.map (List.map f)) := by
  induction p with
  | nil => exact .nil
  | cons head _ ih => exact .cons (head.map f) ih

/-- Full independent molecular sphere populations agree with every actual
retained profile, for every frozen reader and every successful evaluation fuel. -/
theorem retained_population {i : Input} {read : Reader i} {n : Nat} {qs : List (Arm i)} {vs}
    (valid : ∀ q ∈ qs, i.certified.LocalizedRerootCursorValid q)
    (hit : RingNestedActivePair.retainedLevels? i read n qs = some vs) :
    List.Forall₂ List.Perm ((full i qs).map (List.map (observe i read))) (vs.map (List.map some)) := by
  obtain ⟨hs,w,seen⟩ := realize_walk (RingNestedActivePair.retained_source i read n qs vs hit)
  rw [← seen]
  exact project _ (same_spheres (.refl _) (full_complete valid) w)

/-- Materialize the checked frozen visits of a given full hierarchy. A missing
or inconsistent publication prevents construction of a whole profile. -/
def read? (i : Input) (read : Reader i) (hs : List (List (Arm i))) : Option (List (List Visit)) :=
  hs.mapM (List.mapM (observe i read))

def profile? (i : Input) (read : Reader i) (q : Arm i) := read? i read (full i [q])

private theorem observations {α β : Type} {f : α → Option β} {xs : List α} {ys}
    (hit : xs.mapM f = some ys) : xs.map f = ys.map some := by
  induction xs generalizing ys with
  | nil => obtain rfl : [] = ys := Option.some.inj hit; rfl
  | cons x xs ih =>
    rw [List.mapM_cons] at hit
    obtain ⟨y,hy,more⟩ := Option.bind_eq_some_iff.mp hit
    obtain ⟨tail,ht,out⟩ := Option.bind_eq_some_iff.mp more
    obtain rfl := Option.some.inj out
    exact congrArg₂ List.cons hy (ih ht)

private theorem materialized {i : Input} {read : Reader i} {hs vs}
    (hit : read? i read hs = some vs) :
    hs.map (List.map (observe i read)) = vs.map (List.map some) := by
  induction hs generalizing vs with
  | nil => obtain rfl : [] = vs := Option.some.inj hit; rfl
  | cons h hs ih =>
    rw [read?,List.mapM_cons] at hit
    obtain ⟨row,hr,more⟩ := Option.bind_eq_some_iff.mp hit
    obtain ⟨tail,ht,out⟩ := Option.bind_eq_some_iff.mp more
    obtain rfl := Option.some.inj out
    exact congrArg₂ List.cons (observations hr) (ih ht)

private theorem drop_some {α : Type} {xs ys : List (List α)}
    (p : List.Forall₂ List.Perm (xs.map (List.map some)) (ys.map (List.map some))) :
    List.Forall₂ List.Perm xs ys := by
  rw [List.forall₂_map_left_iff,List.forall₂_map_right_iff] at p
  exact p.imp (fun _ _ h => by simpa using h.filterMap id)

/-- Any independently chosen legal ordering gives the same checked visits
at each distance, retaining addresses and complete original/reflected cells. -/
theorem hierarchy_perm {i : Input} {read : Reader i} {q : Arm i} {hs xs ys}
    (valid : i.certified.LocalizedRerootCursorValid q) (alternative : Hierarchy i [q] hs)
    (canonical : profile? i read q = some xs) (issued : read? i read hs = some ys) :
    List.Forall₂ List.Perm xs ys := by
  apply drop_some
  rw [← materialized canonical,← materialized issued]
  exact project _ (same_spheres (.refl _) (full_complete (by simpa using valid)) alternative)

/-- Actual retained visits, including terminal occurrences, agree
with the sorted-independent molecular inventory at every sphere. -/
theorem retained_perm {i : Input} {read : Reader i} {q : Arm i} {n xs ys}
    (valid : i.certified.LocalizedRerootCursorValid q) (canonical : profile? i read q = some xs)
    (returned : RingNestedActivePair.retainedLevels? i read n [q] = some ys) :
    List.Forall₂ List.Perm xs ys := by
  apply drop_some
  rw [← materialized canonical]
  exact retained_population (by simpa using valid) returned

theorem AtDistance.reaches {i : Input} {d q t} (h : AtDistance i d q t) : RingRetainedChemicalTrace.Reaches i q t := by
  induction h with
  | here => exact .here
  | descend child _ ih => exact .descend child ih

private theorem map_complete {α β : Type} (f : α → Option β) (xs : List α)
    (all : ∀ a ∈ xs, ∃ v, f a = some v) : ∃ vs, xs.mapM f = some vs := by
  induction xs with
  | nil => exact ⟨[],rfl⟩
  | cons x xs ih =>
    obtain ⟨v,hv⟩ := all x List.mem_cons_self
    obtain ⟨vs,rest⟩ := ih (fun a ha => all a (List.mem_cons_of_mem x ha))
    exact ⟨v::vs,by simp [List.mapM_cons,hv,rest]⟩

private theorem full_map {α β : Type} {f : α → Option β} {xs : List α} {ys}
    (found : xs.mapM f = some ys) {a : α} (ha : a ∈ xs) : ∃ b, f a = some b := by
  have mem : f a ∈ xs.map f := List.mem_map_of_mem ha
  rw [observations found] at mem
  obtain ⟨b,_,eqn⟩ := List.mem_map.mp mem
  exact ⟨b,eqn.symm⟩

/-- One canonical success materializes every legal hierarchy. Alternative
hierarchies reorder the same molecular cells and may make arbitrary,
different choices within every sibling block. -/
theorem every_hierarchy {i : Input} {read : Reader i} {q : Arm i} {hs xs}
    (valid : i.certified.LocalizedRerootCursorValid q) (alternative : Hierarchy i [q] hs)
    (canonical : profile? i read q = some xs) :
    ∃ ys, read? i read hs = some ys ∧ List.Forall₂ List.Perm xs ys := by
  have spheres := same_spheres (.refl _) (full_complete (by simpa using valid)) alternative
  have transfer {cs ts : List (List (Arm i))} (perm : List.Forall₂ List.Perm cs ts) :
      ∀ {vs}, read? i read cs = some vs → ∃ ys, read? i read ts = some ys := by
    induction perm with
    | nil => exact fun _ => ⟨[],rfl⟩
    | @cons a b as bs p _ ih =>
      intro vs found
      rw [read?,List.mapM_cons] at found
      obtain ⟨row,hr,more⟩ := Option.bind_eq_some_iff.mp found
      obtain ⟨tail,ht,_⟩ := Option.bind_eq_some_iff.mp more
      obtain ⟨newRow,nr⟩ := map_complete (observe i read) b (fun t mem => full_map hr (p.mem_iff.mpr mem))
      obtain ⟨newTail,nt⟩ := ih ht
      exact ⟨newRow::newTail,by unfold read? at nt ⊢; simp [List.mapM_cons,nr,nt]⟩
  obtain ⟨ys,issued⟩ := transfer spheres canonical
  exact ⟨ys,issued,hierarchy_perm valid alternative canonical issued⟩

/-- Fully known, consistent frozen publications on the reachable component
materialize all the canonical spheres. A terminal cursor requires known absence. -/
theorem profile?_of_ready {i : Input} {read : Reader i} {q : Arm i}
    (valid : i.certified.LocalizedRerootCursorValid q)
    (ready : ∀ t, RingRetainedChemicalTrace.Reaches i q t → ∃ v, read t.occurrence = some v ∧
      v.all RingNestedActivePair.consistent = true ∧ (children i t = [] → v = none)) :
    ∃ xs, profile? i read q = some xs := by
  apply map_complete
  intro sphere hs
  apply map_complete
  intro t ht
  obtain ⟨d,hd,idx⟩ := List.getElem_of_mem hs
  have derived := layer_at (full_complete (qs := [q]) (by simpa using valid)) d
  have member := derived.mem_iff.mp (by simpa only [List.getElem?_eq_getElem hd,Option.getD_some,idx] using ht)
  obtain ⟨a,ha,reach⟩ := (mem_distance d [q] t).mp member
  obtain rfl := List.mem_singleton.mp ha
  obtain ⟨v,seen,consistent,leaf⟩ := ready t reach.reaches
  obtain ⟨z,number⟩ := RingAtomicProfileShape.number_total i t
  have accept : (children i t).length ≠ 0 ∨ v.isNone = true := by
    by_cases empty : children i t = []
    · rw [leaf empty]; exact Or.inr rfl
    · exact Or.inl (fun eqn => empty (List.length_eq_zero_iff.mp eqn))
  exact ⟨⟨t.occurrence.val.address,z,(children i t).length,v⟩,by
    simp only [observe,number,RingNestedActivePair.visit,seen,Option.bind_eq_bind,Option.bind_some,
      if_pos (And.intro consistent accept),Option.pure_def]⟩

end TetraStereo.Engine.RingSpherePopulation

assert_kernel_only TetraStereo.Engine.RingSpherePopulation.same_spheres
assert_kernel_only TetraStereo.Engine.RingSpherePopulation.full_complete
assert_kernel_only TetraStereo.Engine.RingSpherePopulation.mem_distance
assert_kernel_only TetraStereo.Engine.RingSpherePopulation.AtDistance.root_and_budget
assert_kernel_only TetraStereo.Engine.RingSpherePopulation.layer_at
assert_kernel_only TetraStereo.Engine.RingSpherePopulation.realize_walk
assert_kernel_only TetraStereo.Engine.RingSpherePopulation.project
assert_kernel_only TetraStereo.Engine.RingSpherePopulation.retained_population
assert_kernel_only TetraStereo.Engine.RingSpherePopulation.hierarchy_perm
assert_kernel_only TetraStereo.Engine.RingSpherePopulation.retained_perm
assert_kernel_only TetraStereo.Engine.RingSpherePopulation.profile?_of_ready
assert_kernel_only TetraStereo.Engine.RingSpherePopulation.every_hierarchy
