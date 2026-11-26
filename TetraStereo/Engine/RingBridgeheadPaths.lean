import TetraStereo.Engine.RingBridgeheadNitrogen

set_option autoImplicit false
namespace TetraStereo.Engine.RingBridgeheadNitrogen

/-- Consecutive directed bonds in a path, with the bridgeheads supplied separately. -/
def OrderedBonds {V : Type} (edge : V → V → Bool) : V → List V → V → Prop
  | a, [], b => edge a b = true
  | a, v :: vs, b => edge a v = true ∧ OrderedBonds edge v vs b

/-- A simple path with at least one interior vertex. -/
structure SimpleInterior {V : Type} (edge : V → V → Bool) (a b : V) (xs : List V) : Prop where
  nonempty : xs ≠ []
  nodup : xs.Nodup
  endpoints : ∀ v ∈ xs, v ≠ a ∧ v ≠ b
  bonds : OrderedBonds edge a xs b

/-- Three simple paths with pairwise disjoint interiors. The common path and
each remaining path form a cycle of at most seven vertices. -/
structure ThreePathWitness {V : Type} (edge : V → V → Bool) (a : V) where
  other : V
  distinct : a ≠ other
  nonadjacent : edge a other = false
  common : List V
  left : List V
  right : List V
  common_path : SimpleInterior edge a other common
  left_path : SimpleInterior edge a other left
  right_path : SimpleInterior edge a other right
  common_left : ∀ v ∈ common, v ∉ left
  common_right : ∀ v ∈ common, v ∉ right
  left_right : ∀ v ∈ left, v ∉ right
  common_bound : common.length ≤ 4
  left_bound : left.length ≤ 4
  right_bound : right.length ≤ 4
  left_cycle : common.length + left.length + 2 ≤ 7
  right_cycle : common.length + right.length + 2 ≤ 7

private theorem route_iff {V : Type} [Fintype V] [DecidableEq V]
    (edge : V → V → Bool) (b : V) (blocked used : List V)
    (accept : List V → Bool) (fuel : Nat) (a : V) :
    route edge b blocked accept fuel a used = true ↔
      ∃ xs : List V, xs ≠ [] ∧ xs.length ≤ fuel ∧ xs.Nodup ∧
        (∀ v ∈ xs, v ∉ blocked ∧ v ∉ used) ∧ OrderedBonds edge a xs b ∧
        accept (xs.reverse ++ used) = true := by
  induction fuel generalizing a used with
  | zero => simp [route]
  | succ fuel ih =>
    simp only [route, anyVertex, decide_eq_true_eq, Bool.and_eq_true,
      Bool.or_eq_true, ih]
    constructor
    · rintro ⟨v, ⟨⟨av, vb⟩, vu⟩, close | more⟩
      · exact ⟨[v], by simp, by simp, by simp,
          by simpa using And.intro vb vu, ⟨av, close.1⟩, by simpa using close.2⟩
      · obtain ⟨xs, ne, len, nd, fresh, bonds, accepted⟩ := more
        refine ⟨v :: xs, by simp, by simp only [List.length_cons]; omega,
          List.nodup_cons.mpr ⟨?_, nd⟩, ?_, ⟨av,bonds⟩, ?_⟩
        · intro mem
          exact (fresh v mem).2 (by simp)
        · intro w mem
          rcases List.mem_cons.mp mem with rfl | mem
          · exact ⟨vb,vu⟩
          · exact ⟨(fresh w mem).1, fun h => (fresh w mem).2 (by simp [h])⟩
        · simpa [List.reverse_cons, List.append_assoc] using accepted
    · rintro ⟨xs, ne, len, nd, fresh, bonds, accepted⟩
      cases xs with
      | nil => contradiction
      | cons v xs =>
        have fv := fresh v (by simp)
        refine ⟨v, ⟨⟨bonds.1, fv.1⟩,fv.2⟩, ?_⟩
        cases xs with
        | nil => exact Or.inl ⟨bonds.2, by simpa using accepted⟩
        | cons w ws =>
          apply Or.inr
          refine ⟨w :: ws, by simp, by simp only [List.length_cons] at len ⊢; omega,
            (List.nodup_cons.mp nd).2, ?_, bonds.2, ?_⟩
          · intro x hx
            have f := fresh x (by simp [hx])
            refine ⟨f.1, ?_⟩
            intro mem
            rcases List.mem_cons.mp mem with eq | hu
            · exact (List.nodup_cons.mp nd).1 (eq ▸ hx)
            · exact f.2 hu
          · simpa [List.reverse_cons, List.append_assoc] using accepted

private theorem simple_of_fresh {V : Type} {edge : V → V → Bool} {a b : V} {xs : List V}
    (ne : xs ≠ []) (nd : xs.Nodup)
    (fresh : ∀ v ∈ xs, v ∉ [a,b]) (bonds : OrderedBonds edge a xs b) :
    SimpleInterior edge a b xs :=
  ⟨ne, nd, by simpa using fresh, bonds⟩

/-- Every accepted finite search supplies independent simple path witnesses. -/
theorem paths_of_test {V : Type} [Fintype V] [DecidableEq V]
    (edge : V → V → Bool) (a : V) (ok : test edge a = true) :
    Nonempty (ThreePathWitness edge a) := by
  unfold test anyVertex at ok
  simp only [decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true'] at ok
  obtain ⟨b, ⟨distinct, nonadjacent⟩, path⟩ := ok
  obtain ⟨p, pn, pl, pd, pf, pb, rest⟩ := (route_iff _ _ _ _ _ _ _).mp path
  simp only [List.append_nil] at rest
  obtain ⟨q, qn, ql, qd, qf, qb, rest⟩ := (route_iff _ _ _ _ _ _ _).mp rest
  simp only [List.append_nil, Bool.and_eq_true, decide_eq_true_eq, List.length_reverse] at rest
  obtain ⟨leftCycle, rest⟩ := rest
  obtain ⟨r, rn, rl, rd, rf, rb, rightCycle⟩ := (route_iff _ _ _ _ _ _ _).mp rest
  simp only [List.append_nil, decide_eq_true_eq, List.length_reverse] at rightCycle
  refine ⟨⟨b,distinct,nonadjacent,p,q,r,
    simple_of_fresh pn pd (fun v hv => (pf v hv).1) pb,
    simple_of_fresh qn qd ?_ qb,
    simple_of_fresh rn rd ?_ rb, ?_, ?_, ?_, pl, ql, rl, leftCycle, rightCycle⟩⟩
  · intro v hv h
    exact (qf v hv).1 (List.mem_append.mpr (Or.inr h))
  · intro v hv h
    exact (rf v hv).1 (List.mem_append.mpr (Or.inr h))
  · intro v hp hq
    exact (qf v hq).1 (by simp [hp])
  · intro v hp hr
    exact (rf v hr).1 (by simp [hp])
  · intro v hq hr
    exact (rf v hr).1 (by simp [hq])

/-- Any independent three-path witness is found by the finite search. -/
theorem test_of_paths {V : Type} [Fintype V] [DecidableEq V]
    (edge : V → V → Bool) (a : V) (witness : Nonempty (ThreePathWitness edge a)) :
    test edge a = true := by
  obtain ⟨w⟩ := witness
  unfold test anyVertex
  simp only [decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true']
  refine ⟨w.other, ⟨w.distinct,w.nonadjacent⟩, ?_⟩
  apply (route_iff _ _ _ _ _ _ _).mpr
  refine ⟨w.common, w.common_path.nonempty, w.common_bound, w.common_path.nodup,
    ?_, w.common_path.bonds, ?_⟩
  · intro v hv
    exact ⟨by simpa using w.common_path.endpoints v hv, by simp⟩
  · simp only [List.append_nil]
    apply (route_iff _ _ _ _ _ _ _).mpr
    refine ⟨w.left,w.left_path.nonempty,w.left_bound,w.left_path.nodup,
      ?_,w.left_path.bonds,?_⟩
    · intro v hv
      refine ⟨?_, by simp⟩
      simp only [List.mem_append, List.mem_reverse, List.mem_cons, not_or, List.not_mem_nil, not_false_eq_true, and_true]
      exact ⟨fun hp => w.common_left v hp hv, w.left_path.endpoints v hv⟩
    · simp only [List.append_nil, Bool.and_eq_true, decide_eq_true_eq, List.length_reverse]
      refine ⟨w.left_cycle, ?_⟩
      apply (route_iff _ _ _ _ _ _ _).mpr
      refine ⟨w.right,w.right_path.nonempty,w.right_bound,w.right_path.nodup,
        ?_,w.right_path.bonds,?_⟩
      · intro v hv
        refine ⟨?_, by simp⟩
        simp only [List.mem_append,List.mem_reverse,List.mem_cons,not_or, List.not_mem_nil, not_false_eq_true, and_true]
        exact ⟨⟨fun hp => w.common_right v hp hv, fun hq => w.left_right v hq hv⟩,
          w.right_path.endpoints v hv⟩
      · simpa using w.right_cycle

/-- The Boolean procedure recognizes exactly three short simple paths with
pairwise-disjoint interiors; this statement contains no search implementation. -/
theorem test_iff_paths {V : Type} [Fintype V] [DecidableEq V]
    (edge : V → V → Bool) (a : V) :
    test edge a = true ↔ Nonempty (ThreePathWitness edge a) :=
  ⟨paths_of_test edge a, test_of_paths edge a⟩

end TetraStereo.Engine.RingBridgeheadNitrogen
assert_kernel_only TetraStereo.Engine.RingBridgeheadNitrogen.test_iff_paths
