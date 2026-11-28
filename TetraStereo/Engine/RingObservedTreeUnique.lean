import TetraStereo.Engine.RingObservedTreeMatch

/-! A retained rerooted arm cannot reach one occurrence address by two routes.
Each edge cuts the original address tree into a prefix subtree and its complement.
Successive nonbacktracking edges select successively smaller sides of these cuts. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingObservedTreeUnique
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm)

private abbrev Addr := List Nat
private abbrev addr {i : Input} (q : Arm i) := q.occurrence.val.address
private abbrev kids {i : Input} (q : Arm i) := i.certified.executableLocalizedRerootChildren q

private def Edge (p q : Addr) := (∃ a, q = p ++ [a]) ∨ (∃ a, p = q ++ [a])
private def Side (p q x : Addr) : Prop :=
  if p.length < q.length then q <+: x else ¬ p <+: x

private theorem sides_reverse {p q x : Addr} (edge : Edge p q) :
    Side p q x ↔ ¬ Side q p x := by
  rcases edge with ⟨a,rfl⟩ | ⟨a,rfl⟩ <;> simp [Side]

private theorem side_self {p q : Addr} (edge : Edge p q) : Side p q q := by
  rcases edge with ⟨a,rfl⟩ | ⟨a,rfl⟩
  · simp [Side]
  · simp only [Side,List.length_append,List.length_singleton,Nat.not_succ_lt_self,if_false]
    intro h
    have := h.length_le
    simp at this

private theorem nested {p q t x : Addr} (pq : Edge p q) (qt : Edge q t) (different : p ≠ t)
    (inside : Side q t x) : Side p q x := by
  rcases pq with ⟨a,rfl⟩ | ⟨a,rfl⟩
  · rcases qt with ⟨b,rfl⟩ | ⟨b,h⟩
    · simp only [Side,List.length_append,List.length_singleton,Nat.lt_add_one,if_true] at *
      exact (List.prefix_append _ _).trans inside
    · exact (different ((List.append_inj_left' h (by simp)))).elim
  · rcases qt with ⟨b,rfl⟩ | ⟨b,rfl⟩
    · simp [Side] at inside ⊢
      intro pre
      exact different ((List.prefix_of_prefix_length_le pre inside (by simp)).eq_of_length (by simp))
    · simp [Side] at inside ⊢
      intro pre
      exact inside ((List.prefix_append (t ++ [b]) [a]).trans (by simpa [List.append_assoc] using pre))

private theorem extension {p q : Addr} (len : p.length+1 = q.length) (drop : p = q.dropLast) :
    ∃ a, q = p ++ [a] := by
  have ne : q ≠ [] := fun h => by simp [h] at len
  exact ⟨q.getLast ne,by rw [drop,List.dropLast_append_getLast]⟩

private theorem child_edge {i : Input} {p q : Arm i} (hq : q ∈ kids p) : Edge (addr p) (addr q) := by
  have d := i.certified.executableLocalizedRerootChildren_declarative p
  have kept : q.occurrence.val ∈ i.certified.intendedLocalizedRerootChildFrames p := by
    rw [← d.1]
    exact List.mem_map.mpr ⟨q,hq,rfl⟩
  have n := i.certified.mem_localizedRerootNeighborFrames_of_mem_intended p _ kept
  rcases ((i.certified.mem_localizedRerootNeighborFrames_iff _ _).mp n).2.2 with h | h
  · exact .inr (extension h.1 h.2)
  · exact .inl (extension h.1 h.2)

private theorem edge_symm {p q : Addr} (h : Edge p q) : Edge q p := h.symm

private theorem uncut {i : Input} {p q t : Arm i} (hq : q ∈ kids p) (ht : t ∈ kids q) :
    addr p ≠ addr t := by
  have d := i.certified.executableLocalizedRerootChildren_declarative q
  have kept : t.occurrence.val ∈ i.certified.intendedLocalizedRerootChildFrames q := by
    rw [← d.1]
    exact List.mem_map.mpr ⟨t,ht,rfl⟩
  exact (i.certified.address_ne_previous_of_mem_intended q p.occurrence
    ((i.certified.executableLocalizedRerootChildren_declarative p).2 q hq) _ kept).symm

/-- The list records the successive cursor visits after the starting cursor. -/
inductive Route {i : Input} : Arm i → List (Arm i) → Arm i → Prop where
  | here {p : Arm i} : Route p [] p
  | step {p q t : Arm i} {xs : List (Arm i)} (child : q ∈ kids p)
      (tail : Route q xs t) : Route p (q :: xs) t

private theorem side_route {i : Input} {p q t : Arm i} {xs : List (Arm i)}
    (child : q ∈ kids p) (tail : Route q xs t) : Side (addr p) (addr q) (addr t) := by
  induction tail generalizing p with
  | here => exact side_self (child_edge child)
  | step edge _ ih => exact nested (child_edge child) (child_edge edge) (uncut child edge) (ih edge)

private theorem same_child {i : Input} {p q t : Arm i} (hq : q ∈ kids p) (ht : t ∈ kids p)
    (same : addr q = addr t) : q = t := by
  have d := i.certified.executableLocalizedRerootChildren_declarative p
  apply LocalizedRerootCursor.ext
  · apply Subtype.ext
    exact i.certified.declarativeLocalizedOccurrence_functional_at_root_address
      ((i.certified.mem_localizedOccurrences_iff _ _).mp q.occurrence.property)
      ((i.certified.mem_localizedOccurrences_iff _ _).mp t.occurrence.property)
      ((i.certified.localizedRerootChildren_root_eq p q _ d hq).trans
        (i.certified.localizedRerootChildren_root_eq p t _ d ht).symm) same
  · exact (d.2 q hq).trans (d.2 t ht).symm

/-- Starting at any retained arm, the final original occurrence address uniquely
determines the complete reroot route. This includes an initially inward
direction, subsequent outward directions, and visits to duplicate atoms. -/
theorem route_unique {i : Input} {p q t : Arm i} {xs ys : List (Arm i)}
    (l : Route p xs q) (r : Route p ys t) (ends : addr q = addr t) : xs = ys := by
  induction l generalizing ys t with
  | here =>
    cases r with
    | here => rfl
    | step edge tail =>
      have wrong := side_route edge tail
      rw [← ends] at wrong
      exact ((sides_reverse (child_edge edge)).mp wrong (side_self (edge_symm (child_edge edge)))).elim
  | @step now a target rest left lt ih =>
    cases r with
    | here =>
      have wrong := side_route left lt
      rw [ends] at wrong
      exact ((sides_reverse (child_edge left)).mp wrong (side_self (edge_symm (child_edge left)))).elim
    | @step _ b _ _ right rt =>
      have lside := side_route left lt
      rw [ends] at lside
      have rside := side_route right rt
      have eq : a = b := by
        apply same_child left right
        by_contra diff
        have outside := nested (edge_symm (child_edge left)) (child_edge right) diff rside
        exact (sides_reverse (child_edge left)).mp lside outside
      subst b
      rw [ih rt ends]

open RingObservedTreeMatch (propose)
open private Tree Tree.preorder Tree.key tree observed cachedChildren children_exact candidate from TetraStereo.Engine.RingObservedTreeMatch

private def Reach {i : Input} (q t : Arm i) := ∃ xs, Route q xs t

private theorem forest {i : Input} (p : Arm i) {cs : List (Arm i)} {ts : List (List (Arm i))}
    (rows : List.Forall₂ (fun q visits => visits.Nodup ∧ ∀ x ∈ visits, Reach q x) cs ts)
    (unique : cs.Nodup) (children : ∀ q ∈ cs, q ∈ kids p) :
    ts.flatten.Nodup ∧ ∀ x ∈ ts.flatten, ∃ q ∈ cs, Reach q x := by
  induction rows with
  | nil => simp
  | @cons q visits cs ts hp _ ih =>
    obtain ⟨ne,unique⟩ := List.nodup_cons.mp unique
    obtain ⟨nd,cover⟩ := ih unique (fun a ha => children a (List.mem_cons_of_mem q ha))
    have child := children q List.mem_cons_self
    refine ⟨List.nodup_append'.mpr ⟨hp.1,nd,?_⟩,?_⟩
    · intro x h1 h2
      obtain ⟨as,h⟩ := hp.2 x h1
      obtain ⟨t,ht,bs,k⟩ := cover x h2
      have eq := route_unique (.step child h) (.step (children t (List.mem_cons_of_mem q ht)) k) rfl
      exact ne ((List.cons.inj eq).1 ▸ ht)
    · intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact ⟨q,List.mem_cons_self,hp.2 x h⟩
      · obtain ⟨a,ha,path⟩ := cover x h
        exact ⟨a,List.mem_cons_of_mem _ ha,path⟩

private theorem preorder {i : Input} (read : RingNestedActivePair.Reader i) (m : Option Nat)
    (n : Nat) (q : Arm i) {x : Tree i} (got : tree read m kids n q = some x) :
    (Tree.preorder x).Nodup ∧ ∀ t ∈ Tree.preorder x, Reach q t := by
  induction n generalizing q x with
  | zero => contradiction
  | succ n ih =>
    obtain ⟨ts,rows,got⟩ := Option.bind_eq_some_iff.mp got
    obtain rfl := Option.some.inj got
    have paired := TerminalTie.mapM_forall₂ _ _ _ rows
    have hp : List.Forall₂ (fun a visits => visits.Nodup ∧ ∀ v ∈ visits, Reach a v)
        (kids q) (ts.map Tree.preorder) := List.forall₂_map_right_iff.mpr (paired.imp (fun a _ h => ih a h))
    obtain ⟨nd,cover⟩ := forest q hp (i.certified.executableLocalizedRerootChildren_nodup q) (fun _ h => h)
    have perm := (RingStereoSiblingPass.legal_order (fun t : Tree i => Tree.key t) ts).perm.flatMap_right
      Tree.preorder
    rw [← List.flatMap_def] at nd cover
    refine ⟨List.nodup_cons.mpr ⟨?_,perm.nodup_iff.mpr nd⟩,?_⟩
    · intro member
      obtain ⟨a,ha,as,path⟩ := cover q (perm.mem_iff.mp member)
      have impossible := route_unique (Route.step ha path) (Route.here (p := q)) rfl
      contradiction
    · intro t ht
      rcases List.mem_cons.mp ht with rfl | member
      · exact ⟨[],.here⟩
      · obtain ⟨a,ha,as,path⟩ := cover t (perm.mem_iff.mp member)
        exact ⟨a::as,.step ha path⟩

private theorem zip_left {α β : Type} (as : List α) (bs : List β) :
    ((as.zip bs).map Prod.fst).Sublist as := by
  induction as generalizing bs with
  | nil => simp
  | cons a as ih =>
    cases bs with
    | nil => simp
    | cons b bs => exact List.Sublist.cons₂ a (ih bs)




theorem proposed_sources_nodup {i : Input} {f : RingActivePairs.Site i}
    (fr : RingNestedActivePair.Frame i f) (r : RingNestedActivePair.Reader i)
    (m : Option Nat) (u v : RingActivePairReport.Slot) {rows : RingBranchMatching.Rows i}
    (hit : propose fr r m u v = some rows) : (rows.map Prod.fst).Nodup := by
  unfold propose candidate observed at hit
  have cache : cachedChildren f = kids := funext (children_exact f)
  rw [cache] at hit
  obtain ⟨x,hx,hit⟩ := Option.bind_eq_some_iff.mp hit
  obtain ⟨y,_,hit⟩ := Option.bind_eq_some_iff.mp hit
  obtain ⟨_,_,hit⟩ := Option.bind_eq_some_iff.mp hit
  obtain rfl := Option.some.inj hit
  exact (preorder r m _ _ hx).1.sublist (zip_left _ _)

end TetraStereo.Engine.RingObservedTreeUnique
assert_kernel_only TetraStereo.Engine.RingObservedTreeUnique.route_unique
assert_kernel_only TetraStereo.Engine.RingObservedTreeUnique.proposed_sources_nodup
