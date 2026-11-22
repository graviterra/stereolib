import TetraStereo.Engine.RingAuxiliaryInventory

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority.DiscoveredSchedule
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation Recursive

private theorem successful_children {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (done : xs.mapM f = some ys) : xs.filterMap f = ys := by
  induction xs generalizing ys with
  | nil => simpa using done
  | cons x xs ih =>
    cases fx : f x <;> cases fs : xs.mapM f <;> simp_all [List.mapM_cons]

/-- Each entry in the computed candidate inventory retains the entire address of the
starting occurrence. Even when a ring revisits an atom, its occurrence address grows. -/
theorem carbonSites_address {m : RawMolecule} {fuel : Nat} {n : RawMolecule.CanonicalBranchNode}
    {paths : List (List Nat)} (complete : carbonSites m fuel n = some paths)
    {q : List Nat} (member : q ∈ paths) : ∃ tail, q = n.history.reverse ++ tail := by
  induction fuel generalizing n paths with
  | zero => simp [carbonSites] at complete
  | succ fuel ih =>
    cases leaf : n.forcedLeaf with
    | true =>
      simp [carbonSites,leaf] at complete
      subst paths
      simp at member
    | false =>
      cases atom : m.atoms[n.atom]? with
      | none => simp [carbonSites,leaf,atom] at complete
      | some a =>
        cases children : (m.canonicalChildren n).mapM (carbonSites m fuel) with
        | none => simp [carbonSites,leaf,atom,children] at complete
        | some rows =>
          have collect (here : Bool) (eqn : (if here then [n.history.reverse] else []) ++
              rows.flatten = paths) : ∃ tail, q = n.history.reverse ++ tail := by
            rw [← eqn] at member
            rcases List.mem_append.mp member with atNode | below
            · cases here with
              | false => simp at atNode
              | true =>
                have same : q = n.history.reverse := by simpa using atNode
                exact ⟨[],by simpa using same⟩
            · obtain ⟨row,inRows,inRow⟩ := List.mem_flatten.mp below
              rw [← successful_children children] at inRows
              obtain ⟨child,edge,found⟩ := List.mem_filterMap.mp inRows
              obtain ⟨tail,ht⟩ := ih found inRow
              refine ⟨child.atom :: tail,?_⟩
              simpa [m.canonicalChildren_history n child edge,List.append_assoc] using ht
          simp [carbonSites,leaf,atom,children] at complete
          split at complete
          · exact collect true (by simpa using complete)
          · exact collect false (by simpa using complete)

/-- An addressed dependency belongs to one of the two particular tied arms;
the part after that arm may be empty. -/
theorem required_address {m p d} (f : SignedPair.Frame m p d)
    {q : List Nat} (required : q ∈ f.requiredPaths) :
    ∃ i tail, (i = f.left.ligand ∨ i = f.right.ligand) ∧ q = p ++ (i :: tail) := by
  rcases List.mem_append.mp required with left | right
  · obtain ⟨tail,h⟩ := carbonSites_address f.leftComplete left
    exact ⟨_,tail,Or.inl rfl,by simpa [f.leftAt.2,List.append_assoc] using h⟩
  · obtain ⟨tail,h⟩ := carbonSites_address f.rightComplete right
    exact ⟨_,tail,Or.inr rfl,by simpa [f.rightAt.2,List.append_assoc] using h⟩

theorem required_deeper {m p d} (f : SignedPair.Frame m p d) {q : List Nat}
    (required : q ∈ f.requiredPaths) : p.length < q.length := by
  obtain ⟨i,tail,_,rfl⟩ := required_address f required
  simp

/-- A store can contain a justified reading, a justified absence, or an unresolved
occurrence. The value type remembers the full molecular address and geometry. -/
abbrev Store (m : RawMolecule) (g : Geometry) :=
  (q : List Nat) → Option (RingAuxiliaryInventory.Result m g q)

private theorem traverse_congr {α β : Type} {a b : α → Option β} (xs : List α)
    (same : ∀ x ∈ xs, a x = b x) : xs.mapM a = xs.mapM b := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.mapM_cons,List.mapM_cons,same x List.mem_cons_self,
      ih (fun y h => same y (List.mem_cons_of_mem x h))]

theorem collect_congr {m g} (s t : Store m g) (paths : List (List Nat))
    (same : ∀ q ∈ paths, s q = t q) :
    RingAuxiliaryInventory.collectRows s paths = RingAuxiliaryInventory.collectRows t paths := by
  unfold RingAuxiliaryInventory.collectRows
  apply traverse_congr
  intro q h
  rw [same q h]

/-- Equality at the actual source-derived addresses suffices for equality of the
complete discovered result, including failures, both ligand orders, and every
positive or negative child certificate. -/
theorem discoverAt?_congr {m g p d} (s t : Store m g)
    (same : ∀ f : SignedPair.Frame m p d, SignedPair.frame? m p d = some f →
      ∀ q ∈ f.requiredPaths, s q = t q) :
    RingAuxiliaryInventory.discoverAt? p d s = RingAuxiliaryInventory.discoverAt? p d t := by
  cases found : SignedPair.frame? m p d with
  | none => simp [RingAuxiliaryInventory.discoverAt?,found]
  | some f =>
    have left := collect_congr s t f.leftPaths
      (fun q h => same f found q (List.mem_append_left _ h))
    have right := collect_congr s t f.rightPaths
      (fun q h => same f found q (List.mem_append_right _ h))
    simp only [RingAuxiliaryInventory.discoverAt?,found,Option.bind_eq_bind,Option.bind_some]
    rw [left,right]

theorem discoverAt?_of_deeper {m g p d} (s t : Store m g)
    (same : ∀ q : List Nat, p.length < q.length → s q = t q) :
    RingAuxiliaryInventory.discoverAt? p d s = RingAuxiliaryInventory.discoverAt? p d t :=
  discoverAt?_congr s t (fun f _ q h => same q (required_deeper f h))

/-- Publish a single fresh result from the discovered-pair step on the current store. -/
def refresh {m g} (radius : List Nat → Nat) (s : Store m g) (q : List Nat) : Store m g :=
  fun p => if p = q then RingAuxiliaryInventory.discoverAt? p (radius p) s else s p

/-- Events execute in list order and each event sees all earlier publications. -/
def run {m g} (radius : List Nat → Nat) (s : Store m g) (events : List (List Nat)) : Store m g :=
  events.foldl (refresh radius) s

/-- Refreshing a finite set of occurrences at one distance gives the same value
as reading the incoming snapshot at each refreshed occurrence. The execution
may contain duplicates and stores a failed result at the site that failed. -/
theorem run_layer {m g} (radius : List Nat → Nat) (distance : Nat)
    (events : List (List Nat)) (level : ∀ q ∈ events, q.length = distance)
    (s : Store m g) (p : List Nat) :
    run radius s events p =
      if p ∈ events then RingAuxiliaryInventory.discoverAt? p (radius p) s else s p := by
  induction events generalizing s with
  | nil => simp [run]
  | cons q qs ih =>
    have qLevel := level q List.mem_cons_self
    have rest : ∀ x ∈ qs, x.length = distance := fun x h => level x (List.mem_cons_of_mem q h)
    change run radius (refresh radius s q) qs p = _
    rw [ih rest]
    by_cases later : p ∈ qs
    · have done := discoverAt?_of_deeper (p := p) (d := radius p) (refresh radius s q) s (by
        intro x deeper
        have diff : x ≠ q := by
          intro h
          subst x
          rw [rest p later,qLevel] at deeper
          exact (Nat.lt_irrefl _ deeper)
        simp [refresh,diff])
      simp [later,done]
    · by_cases current : p = q
      · subst p
        simp [later,refresh]
      · simp [later,current,refresh]

/-- Any permutation of equal-distance publications is observationally identical
as a dependent store. This applies to the raw outcomes and their certificates. -/
theorem permute_layer {m g} (radius : List Nat → Nat) (s : Store m g) (distance : Nat)
    {a b : List (List Nat)} (perm : a.Perm b)
    (level : ∀ q ∈ a, q.length = distance) : run radius s a = run radius s b := by
  funext p
  rw [run_layer radius distance a level s p,
    run_layer radius distance b (fun q h => level q (perm.mem_iff.mpr h)) s p]
  simp only [perm.mem_iff]

end TetraStereo.Engine.RingChemicalPriority.DiscoveredSchedule

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.DiscoveredSchedule.carbonSites_address
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.DiscoveredSchedule.required_address
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.DiscoveredSchedule.discoverAt?_congr
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.DiscoveredSchedule.run_layer
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.DiscoveredSchedule.permute_layer
