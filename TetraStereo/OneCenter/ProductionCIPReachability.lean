import TetraStereo.OneCenter.BranchSphereKey

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace RawMolecule

/-!
Kernel-checked semantics for the bounded list BFS used by `reachableWithoutEdge`.

The relation below deliberately describes the raw edge list rather than a molecule graph: an edge
may be traversed in either direction, except for either orientation of `blocked`.  This keeps the
proof reusable by the raw-to-relational mancude realization layer.
-/

/-- The option-valued one-edge operation implemented inside `reachableWithoutEdge`. -/
def neighborWithout? (blocked : ℕ × ℕ) (atom : ℕ) (edge : ℕ × ℕ) : Option ℕ :=
  let isBlocked :=
    (edge.1 == blocked.1 && edge.2 == blocked.2) ||
      (edge.1 == blocked.2 && edge.2 == blocked.1)
  if isBlocked then none
  else if edge.1 == atom then some edge.2
  else if edge.2 == atom then some edge.1
  else none

/-- Undirected adjacency in a raw edge list, omitting both orientations of one blocked edge. -/
def UnblockedListEdge (blocked : ℕ × ℕ) (edges : List (ℕ × ℕ))
    (left right : ℕ) : Prop :=
  ∃ edge ∈ edges, neighborWithout? blocked left edge = some right

theorem unblockedListEdge_iff (blocked : ℕ × ℕ) (edges : List (ℕ × ℕ))
    (left right : ℕ) :
    UnblockedListEdge blocked edges left right ↔
      ∃ edge ∈ edges,
        ¬ ((edge.1 = blocked.1 ∧ edge.2 = blocked.2) ∨
          (edge.1 = blocked.2 ∧ edge.2 = blocked.1)) ∧
        ((edge.1 = left ∧ edge.2 = right) ∨
          (edge.2 = left ∧ edge.1 = right)) := by
  constructor
  · rintro ⟨⟨edgeLeft, edgeRight⟩, hedge, hneighbor⟩
    refine ⟨(edgeLeft, edgeRight), hedge, ?_⟩
    simp only [neighborWithout?] at hneighbor
    split at hneighbor
    · contradiction
    · rename_i hnotBlocked
      constructor
      · intro hblocked
        apply hnotBlocked
        simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
        exact hblocked
      · by_cases hleft : edgeLeft = left
        · simp only [hleft, beq_self_eq_true, if_true, Option.some.injEq] at hneighbor
          exact Or.inl ⟨hleft, hneighbor⟩
        · simp only [beq_iff_eq, hleft, if_false] at hneighbor
          by_cases hright : edgeRight = left
          · simp only [hright, if_true, Option.some.injEq] at hneighbor
            exact Or.inr ⟨hright, hneighbor⟩
          · simp only [hright, if_false] at hneighbor
            contradiction
  · rintro ⟨⟨edgeLeft, edgeRight⟩, hedge, hblocked, horientation⟩
    refine ⟨(edgeLeft, edgeRight), hedge, ?_⟩
    simp only [neighborWithout?, beq_iff_eq, Bool.and_eq_true, Bool.or_eq_true]
    split
    · rename_i hisBlocked
      exact (hblocked hisBlocked).elim
    · rcases horientation with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simp
      · by_cases heq : edgeLeft = edgeRight <;> simp [heq]

theorem unblockedListEdge_symm {blocked : ℕ × ℕ} {edges : List (ℕ × ℕ)}
    {left right : ℕ} (hstep : UnblockedListEdge blocked edges left right) :
    UnblockedListEdge blocked edges right left := by
  rw [unblockedListEdge_iff] at hstep ⊢
  rcases hstep with ⟨edge, hedge, hblocked, horientation⟩
  refine ⟨edge, hedge, hblocked, ?_⟩
  rcases horientation with horientation | horientation
  · exact Or.inr ⟨horientation.2, horientation.1⟩
  · exact Or.inl ⟨horientation.2, horientation.1⟩

/-- One BFS expansion, before duplicate removal. -/
def reachableWithoutEdgeNext (blocked : ℕ × ℕ) (edges : List (ℕ × ℕ))
    (frontier seen : List ℕ) : List ℕ :=
  (frontier.flatMap fun atom => edges.filterMap (neighborWithout? blocked atom)).filter fun atom =>
    !(seen.contains atom)

private theorem mem_of_mem_eraseDups {atom : ℕ} {values : List ℕ}
    (hatom : atom ∈ values.eraseDups) : atom ∈ values := by
  match values with
  | [] => simp at hatom
  | value :: rest =>
      rw [List.eraseDups_cons] at hatom
      rcases List.mem_cons.mp hatom with hvalue | hrest
      · exact List.mem_cons.mpr (Or.inl hvalue)
      · apply List.mem_cons.mpr
        apply Or.inr
        exact (List.mem_filter.mp (mem_of_mem_eraseDups hrest)).1
termination_by values.length
decreasing_by
  simpa only [List.length_cons] using
    Nat.lt_succ_of_le (List.length_filter_le (fun b : ℕ => !b == value) rest)

private theorem mem_eraseDups_of_mem {atom : ℕ} {values : List ℕ}
    (hatom : atom ∈ values) : atom ∈ values.eraseDups := by
  match values with
  | [] => simp at hatom
  | value :: rest =>
      rw [List.eraseDups_cons]
      rcases List.mem_cons.mp hatom with hvalue | hrest
      · exact List.mem_cons.mpr (Or.inl hvalue)
      · by_cases hvalue : atom = value
        · exact List.mem_cons.mpr (Or.inl hvalue)
        · apply List.mem_cons.mpr
          apply Or.inr
          apply mem_eraseDups_of_mem
          exact List.mem_filter.mpr ⟨hrest, by simp [hvalue]⟩
termination_by values.length
decreasing_by
  simpa only [List.length_cons] using
    Nat.lt_succ_of_le (List.length_filter_le (fun b : ℕ => !b == value) rest)

private theorem reachableWithoutEdge_empty_frontier (blocked : ℕ × ℕ) (fuel : ℕ)
    (edges : List (ℕ × ℕ)) (seen : List ℕ) :
    reachableWithoutEdge blocked fuel edges [] seen = seen := by
  cases fuel <;> rfl

theorem unblockedListEdge_of_mem_next {blocked : ℕ × ℕ} {edges : List (ℕ × ℕ)}
    {frontier seen : List ℕ} {right : ℕ}
    (hright : right ∈ reachableWithoutEdgeNext blocked edges frontier seen) :
    ∃ left ∈ frontier, UnblockedListEdge blocked edges left right := by
  simp only [reachableWithoutEdgeNext, List.mem_filter] at hright
  rcases (List.mem_flatMap.mp hright.1) with ⟨left, hleft, hright⟩
  rw [List.mem_filterMap] at hright
  rcases hright with ⟨edge, hedge, hedgeResult⟩
  exact ⟨left, hleft, edge, hedge, hedgeResult⟩

theorem mem_next_of_unblockedListEdge {blocked : ℕ × ℕ}
    {edges : List (ℕ × ℕ)} {frontier seen : List ℕ} {left right : ℕ}
    (hleft : left ∈ frontier) (hstep : UnblockedListEdge blocked edges left right)
    (hnotSeen : right ∉ seen) :
    right ∈ reachableWithoutEdgeNext blocked edges frontier seen := by
  rw [reachableWithoutEdgeNext, List.mem_filter]
  constructor
  · apply List.mem_flatMap.mpr
    refine ⟨left, hleft, ?_⟩
    rcases hstep with ⟨edge, hedge, hedgeResult⟩
    rw [List.mem_filterMap]
    exact ⟨edge, hedge, hedgeResult⟩
  · simpa using hnotSeen

/-- The accumulator is monotone: no amount of remaining fuel removes an already seen atom. -/
theorem seen_subset_reachableWithoutEdge (blocked : ℕ × ℕ)
    (edges : List (ℕ × ℕ)) : ∀ fuel frontier seen,
    ∀ atom ∈ seen, atom ∈ reachableWithoutEdge blocked fuel edges frontier seen := by
  intro fuel
  induction fuel with
  | zero =>
      intro frontier seen atom hatom
      exact hatom
  | succ fuel inductionHypothesis =>
      intro frontier seen atom hatom
      cases frontier with
      | nil => exact hatom
      | cons first rest =>
          simp only [reachableWithoutEdge]
          apply inductionHypothesis
          exact List.mem_append.mpr (Or.inl hatom)

/-- A positive-fuel expansion discovers every unblocked neighbour of the current nonempty
frontier.  This is the one-layer completeness lemma used in the bounded-path induction. -/
theorem unblockedNeighbor_mem_reachableWithoutEdge (blocked : ℕ × ℕ)
    (edges : List (ℕ × ℕ)) (fuel : ℕ) {frontier seen : List ℕ}
    {left right : ℕ} (hleft : left ∈ frontier)
    (hstep : UnblockedListEdge blocked edges left right) :
    right ∈ reachableWithoutEdge blocked (fuel + 1) edges frontier seen := by
  by_cases hseen : right ∈ seen
  · exact seen_subset_reachableWithoutEdge blocked edges (fuel + 1) frontier seen right hseen
  · rcases frontier with _ | ⟨first, rest⟩
    · simp at hleft
    · let next := reachableWithoutEdgeNext blocked edges (first :: rest) seen
      let fresh := next.eraseDups
      have hnext : right ∈ next :=
        mem_next_of_unblockedListEdge hleft hstep hseen
      have hfresh : right ∈ fresh := mem_eraseDups_of_mem hnext
      simp only [reachableWithoutEdge]
      apply seen_subset_reachableWithoutEdge blocked edges fuel fresh (seen ++ fresh)
      exact List.mem_append.mpr (Or.inr hfresh)

/-- A walk with exactly the displayed number of edges.  Its head-recursive presentation matches
one BFS expansion followed by the recursive call. -/
inductive UnblockedWalkLength (blocked : ℕ × ℕ) (edges : List (ℕ × ℕ)) :
    ℕ → ℕ → ℕ → Prop where
  | refl (atom : ℕ) : UnblockedWalkLength blocked edges 0 atom atom
  | step {length left middle right : ℕ} :
      UnblockedListEdge blocked edges left middle →
      UnblockedWalkLength blocked edges length middle right →
      UnblockedWalkLength blocked edges (length + 1) left right

/-- All already seen vertices outside the current frontier have had their neighbours processed. -/
def ProcessedOutsideFrontier (blocked : ℕ × ℕ) (edges : List (ℕ × ℕ))
    (frontier seen : List ℕ) : Prop :=
  ∀ left, left ∈ seen → left ∉ frontier →
    ∀ right, UnblockedListEdge blocked edges left right → right ∈ seen

private theorem walk_mem_of_closed {blocked : ℕ × ℕ} {edges : List (ℕ × ℕ)}
    {seen : List ℕ} (hclosed : ∀ left ∈ seen, ∀ right,
      UnblockedListEdge blocked edges left right → right ∈ seen) :
    ∀ {length left right}, left ∈ seen →
      UnblockedWalkLength blocked edges length left right → right ∈ seen := by
  intro length left right hleft hwalk
  induction hwalk with
  | refl => exact hleft
  | step hstep _ inductionHypothesis =>
      exact inductionHypothesis (hclosed _ hleft _ hstep)

private theorem processedOutsideFrontier_next {blocked : ℕ × ℕ}
    {edges : List (ℕ × ℕ)} {frontier seen : List ℕ}
    (hprocessed : ProcessedOutsideFrontier blocked edges frontier seen) :
    let next := reachableWithoutEdgeNext blocked edges frontier seen
    let fresh := next.eraseDups
    ProcessedOutsideFrontier blocked edges fresh (seen ++ fresh) := by
  dsimp only
  intro left hleft hleftFresh right hstep
  rcases List.mem_append.mp hleft with hleftSeen | hleftFresh'
  · by_cases hleftFrontier : left ∈ frontier
    · by_cases hrightSeen : right ∈ seen
      · exact List.mem_append.mpr (Or.inl hrightSeen)
      · apply List.mem_append.mpr
        apply Or.inr
        apply mem_eraseDups_of_mem
        exact mem_next_of_unblockedListEdge hleftFrontier hstep hrightSeen
    · exact List.mem_append.mpr (Or.inl (hprocessed left hleftSeen hleftFrontier right hstep))
  · exact (hleftFresh hleftFresh').elim

/-- General bounded completeness invariant.  Besides `frontier ⊆ seen`, it requires exactly the
history fact maintained by BFS: a seen vertex absent from the frontier has already been expanded. -/
theorem reachableWithoutEdge_complete_of_walk (blocked : ℕ × ℕ)
    (edges : List (ℕ × ℕ)) : ∀ fuel frontier seen,
    (∀ atom ∈ frontier, atom ∈ seen) →
    ProcessedOutsideFrontier blocked edges frontier seen →
    ∀ {length left right}, length ≤ fuel → left ∈ seen →
      UnblockedWalkLength blocked edges length left right →
      right ∈ reachableWithoutEdge blocked fuel edges frontier seen := by
  intro fuel
  induction fuel with
  | zero =>
      intro frontier seen _ _ length left right hlength hleft hwalk
      have : length = 0 := Nat.eq_zero_of_le_zero hlength
      subst length
      cases hwalk
      exact hleft
  | succ fuel inductionHypothesis =>
      intro frontier seen hfrontierSeen hprocessed length left right hlength hleft hwalk
      cases length with
      | zero =>
          cases hwalk
          exact seen_subset_reachableWithoutEdge blocked edges (fuel + 1)
            frontier seen left hleft
      | succ length =>
          cases hwalk with
          | step hstep htail =>
              rename_i middle
              cases frontier with
              | nil =>
                  have hclosed : ∀ current ∈ seen, ∀ next,
                      UnblockedListEdge blocked edges current next → next ∈ seen := by
                    intro current hcurrent next hnext
                    exact hprocessed current hcurrent (by simp) next hnext
                  exact walk_mem_of_closed hclosed hleft
                    (UnblockedWalkLength.step hstep htail)
              | cons first rest =>
                  let next := reachableWithoutEdgeNext blocked edges (first :: rest) seen
                  let fresh := next.eraseDups
                  have hmiddle : middle ∈ seen ++ fresh := by
                    by_cases hleftFrontier : left ∈ first :: rest
                    · by_cases hmiddleSeen : middle ∈ seen
                      · exact List.mem_append.mpr (Or.inl hmiddleSeen)
                      · apply List.mem_append.mpr
                        apply Or.inr
                        apply mem_eraseDups_of_mem
                        exact mem_next_of_unblockedListEdge hleftFrontier hstep hmiddleSeen
                    · exact List.mem_append.mpr
                        (Or.inl (hprocessed left hleft hleftFrontier _ hstep))
                  have hfreshSeen : ∀ atom ∈ fresh, atom ∈ seen ++ fresh := by
                    intro atom hatom
                    exact List.mem_append.mpr (Or.inr hatom)
                  have hprocessedNext :
                      ProcessedOutsideFrontier blocked edges fresh (seen ++ fresh) :=
                    processedOutsideFrontier_next hprocessed
                  simp only [reachableWithoutEdge]
                  apply inductionHypothesis fresh (seen ++ fresh) hfreshSeen hprocessedNext
                  · exact Nat.le_of_succ_le_succ hlength
                  · exact hmiddle
                  · exact htail

/-- Exact bounded completeness from an arbitrary singleton start: every unblocked walk of length
at most `fuel` from that start is present in the returned list. -/
theorem reachableWithoutEdge_from_start_complete (blocked : ℕ × ℕ)
    (edges : List (ℕ × ℕ)) (start : ℕ) {fuel length atom : ℕ}
    (hlength : length ≤ fuel)
    (hwalk : UnblockedWalkLength blocked edges length start atom) :
    atom ∈ reachableWithoutEdge blocked fuel edges [start] [start] := by
  exact reachableWithoutEdge_complete_of_walk blocked edges fuel [start] [start]
    (by intro current hcurrent; exact hcurrent)
    (by intro left hleft hleftFrontier; exact (hleftFrontier hleft).elim)
    (length := length) (left := start) (right := atom) hlength (by simp) hwalk

/-- Production bridge-detection specialization, whose start is the blocked edge's first endpoint. -/
theorem reachableWithoutEdge_from_singleton_complete (blocked : ℕ × ℕ)
    (edges : List (ℕ × ℕ)) {fuel length atom : ℕ} (hlength : length ≤ fuel)
    (hwalk : UnblockedWalkLength blocked edges length blocked.1 atom) :
    atom ∈ reachableWithoutEdge blocked fuel edges [blocked.1] [blocked.1] :=
  reachableWithoutEdge_from_start_complete blocked edges blocked.1 hlength hwalk

/-- Every atom returned by the bounded BFS is connected to `start`, provided both input lists
already satisfy that invariant. -/
theorem reachableWithoutEdge_sound (blocked : ℕ × ℕ) (edges : List (ℕ × ℕ))
    (start : ℕ) : ∀ fuel frontier seen,
    (∀ atom ∈ frontier,
      Relation.ReflTransGen (UnblockedListEdge blocked edges) start atom) →
    (∀ atom ∈ seen,
      Relation.ReflTransGen (UnblockedListEdge blocked edges) start atom) →
    ∀ atom ∈ reachableWithoutEdge blocked fuel edges frontier seen,
      Relation.ReflTransGen (UnblockedListEdge blocked edges) start atom := by
  intro fuel
  induction fuel with
  | zero =>
      intro frontier seen _ hseen atom hatom
      exact hseen atom hatom
  | succ fuel inductionHypothesis =>
      intro frontier seen hfrontier hseen
      cases frontier with
      | nil =>
          intro atom hatom
          exact hseen atom hatom
      | cons first rest =>
          cases edges with
          | nil =>
              intro atom hatom
              apply hseen atom
              simpa [reachableWithoutEdge, List.flatMap,
                reachableWithoutEdge_empty_frontier] using hatom
          | cons edge remaining =>
              let next := reachableWithoutEdgeNext blocked (edge :: remaining)
                (first :: rest) seen
              let fresh := next.eraseDups
              have hfresh : ∀ atom ∈ fresh,
                  Relation.ReflTransGen
                    (UnblockedListEdge blocked (edge :: remaining)) start atom := by
                intro atom hatom
                have hnext : atom ∈ next := by
                  exact mem_of_mem_eraseDups hatom
                rcases unblockedListEdge_of_mem_next hnext with ⟨left, hleft, hstep⟩
                exact (hfrontier left hleft).tail hstep
              have hseenFresh : ∀ atom ∈ seen ++ fresh,
                  Relation.ReflTransGen
                    (UnblockedListEdge blocked (edge :: remaining)) start atom := by
                intro atom hatom
                rcases List.mem_append.mp hatom with hatom | hatom
                · exact hseen atom hatom
                · exact hfresh atom hatom
              change ∀ atom ∈
                reachableWithoutEdge blocked fuel (edge :: remaining) fresh (seen ++ fresh), _
              exact inductionHypothesis fresh (seen ++ fresh) hfresh hseenFresh

/-- A bounded call from an arbitrary singleton start never reports an atom outside its unblocked
connected component. -/
theorem reachableWithoutEdge_from_start_sound (blocked : ℕ × ℕ)
    (fuel : ℕ) (edges : List (ℕ × ℕ)) (start : ℕ) {atom : ℕ}
    (hatom : atom ∈ reachableWithoutEdge blocked fuel edges [start] [start]) :
    Relation.ReflTransGen (UnblockedListEdge blocked edges) start atom := by
  apply reachableWithoutEdge_sound blocked edges start fuel [start] [start]
  · intro current hcurrent
    simp only [List.mem_singleton] at hcurrent
    subst current
    exact Relation.ReflTransGen.refl
  · intro current hcurrent
    simp only [List.mem_singleton] at hcurrent
    subst current
    exact Relation.ReflTransGen.refl
  · exact hatom

/-- The production bridge-detection specialization starts at the blocked edge's first endpoint. -/
theorem reachableWithoutEdge_from_singleton_sound (blocked : ℕ × ℕ)
    (fuel : ℕ) (edges : List (ℕ × ℕ)) {atom : ℕ}
    (hatom : atom ∈ reachableWithoutEdge blocked fuel edges [blocked.1] [blocked.1]) :
    Relation.ReflTransGen (UnblockedListEdge blocked edges) blocked.1 atom :=
  reachableWithoutEdge_from_start_sound blocked fuel edges blocked.1 hatom

end RawMolecule
end OneCenter
end TetraStereo
