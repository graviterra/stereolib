import TetraStereo.OneCenter.BranchSphereKey

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeRingReachability

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule

/-- Exact adjacency enumerated by the production breadth-first cycle guard. -/
def avoidingNeighbors (mol : RawMolecule) (blocked atom : Nat) : List Nat :=
  mol.bonds.filterMap fun bond =>
    if bond.source == atom && bond.target != blocked then some bond.target
    else if bond.target == atom && bond.source != blocked then some bond.source else none

def freshNeighbors (mol : RawMolecule) (blocked : Nat) (frontier seen : List Nat) : List Nat :=
  ((frontier.flatMap (avoidingNeighbors mol blocked)).filter
    (fun atom => !(seen.contains atom))).eraseDups

theorem mem_eraseDups_iff (atom : Nat) (values : List Nat) :
    atom ∈ values.eraseDups ↔ atom ∈ values := by
  cases values with
  | nil => simp
  | cons head tail =>
      rw [List.eraseDups_cons]
      by_cases same : atom = head
      · subst head
        simp
      · have filtered := mem_eraseDups_iff atom (tail.filter fun next => !next == head)
        simpa [same] using filtered
termination_by values.length
decreasing_by
  have filtered := List.length_filter_le (fun next => !next == head) tail
  simpa using Nat.lt_succ_of_le filtered

theorem mem_freshNeighbors (mol : RawMolecule) (blocked atom : Nat) (frontier seen : List Nat) :
    atom ∈ freshNeighbors mol blocked frontier seen ↔
      (∃ previous ∈ frontier, atom ∈ avoidingNeighbors mol blocked previous) ∧ atom ∉ seen := by
  simp [freshNeighbors, mem_eraseDups_iff, List.mem_flatMap]

/-- Visited nodes outside the current frontier have already had every unblocked edge expanded. -/
def FrontierInvariant (mol : RawMolecule) (blocked : Nat) (frontier seen : List Nat) : Prop :=
  ∀ atom ∈ seen, atom ∉ frontier → ∀ next ∈ avoidingNeighbors mol blocked atom, next ∈ seen

inductive AvoidingWalk (mol : RawMolecule) (blocked : Nat) : Nat → Nat → Nat → Prop
  | nil (atom : Nat) : AvoidingWalk mol blocked 0 atom atom
  | cons {length start next finish : Nat}
      (edge : next ∈ avoidingNeighbors mol blocked start)
      (tail : AvoidingWalk mol blocked length next finish) :
      AvoidingWalk mol blocked (length + 1) start finish

theorem reachable_seen (mol : RawMolecule) (blocked fuel atom : Nat) (frontier seen : List Nat)
    (member : atom ∈ seen) : atom ∈ mol.reachableAvoiding fuel blocked frontier seen := by
  induction fuel generalizing frontier seen with
  | zero => exact member
  | succ fuel ih =>
      cases frontier with
      | nil => exact member
      | cons head tail =>
          change atom ∈ mol.reachableAvoiding fuel blocked
            (freshNeighbors mol blocked (head :: tail) seen)
            (seen ++ freshNeighbors mol blocked (head :: tail) seen)
          exact ih _ _ (List.mem_append_left _ member)

theorem advance_neighbor (mol : RawMolecule) (blocked : Nat) (frontier seen : List Nat)
    (invariant : FrontierInvariant mol blocked frontier seen) (atom next : Nat)
    (member : atom ∈ seen) (edge : next ∈ avoidingNeighbors mol blocked atom) :
    next ∈ seen ++ freshNeighbors mol blocked frontier seen := by
  by_cases already : next ∈ seen
  · exact List.mem_append_left _ already
  · have active : atom ∈ frontier := by
      by_contra inactive
      exact already (invariant atom member inactive next edge)
    exact List.mem_append_right _ ((mem_freshNeighbors mol blocked next frontier seen).mpr
      ⟨⟨atom, active, edge⟩, already⟩)

theorem advance_invariant (mol : RawMolecule) (blocked : Nat) (frontier seen : List Nat)
    (invariant : FrontierInvariant mol blocked frontier seen) :
    FrontierInvariant mol blocked (freshNeighbors mol blocked frontier seen)
      (seen ++ freshNeighbors mol blocked frontier seen) := by
  intro atom member inactive next edge
  rcases List.mem_append.mp member with old | fresh
  · exact advance_neighbor mol blocked frontier seen invariant atom next old edge
  · exact (inactive fresh).elim

private theorem closed_walk (mol : RawMolecule) (blocked length start finish : Nat)
    (seen : List Nat) (closed : ∀ atom ∈ seen, ∀ next ∈ avoidingNeighbors mol blocked atom,
      next ∈ seen) (walk : AvoidingWalk mol blocked length start finish) (member : start ∈ seen) :
    finish ∈ seen := by
  induction walk with
  | nil => exact member
  | cons edge tail ih => exact ih (closed _ member _ edge)

/-- Completeness of the actual breadth-first reachability function at the length of an explicit
unblocked graph walk. The frontier invariant is structural; no returned reachability value is a
hypothesis. This lemma is reusable independently of the ring-family coordinates. -/
theorem reachable_of_walk (mol : RawMolecule) (blocked fuel length start finish : Nat)
    (frontier seen : List Nat) (invariant : FrontierInvariant mol blocked frontier seen)
    (walk : AvoidingWalk mol blocked length start finish) (member : start ∈ seen)
    (enough : length ≤ fuel) :
    finish ∈ mol.reachableAvoiding fuel blocked frontier seen := by
  induction fuel generalizing length start finish frontier seen with
  | zero =>
      have zero : length = 0 := by omega
      subst length
      cases walk
      exact member
  | succ fuel ih =>
      cases frontier with
      | nil =>
          exact closed_walk mol blocked length start finish seen
            (fun atom present next edge => invariant atom present (by simp) next edge) walk member
      | cons head tail =>
          cases walk with
          | nil => exact reachable_seen mol blocked (fuel + 1) _ (head :: tail) seen member
          | cons edge remaining =>
              change _ ∈ mol.reachableAvoiding fuel blocked
                (freshNeighbors mol blocked (head :: tail) seen)
                (seen ++ freshNeighbors mol blocked (head :: tail) seen)
              exact ih _ _ _ _ _ (advance_invariant mol blocked (head :: tail) seen invariant)
                remaining (advance_neighbor mol blocked (head :: tail) seen invariant _ _ member edge)
                (by omega)

/-- Public initial frontier: every finite unblocked path is found with at least its edge count. -/
theorem reachable_singleton_of_walk (mol : RawMolecule) (blocked fuel length start finish : Nat)
    (walk : AvoidingWalk mol blocked length start finish) (enough : length ≤ fuel) :
    (mol.reachableAvoiding fuel blocked [start] [start]).contains finish = true := by
  have found := reachable_of_walk mol blocked fuel length start finish [start] [start]
    (by intro atom member inactive; exact (inactive member).elim) walk (by simp) enough
  simpa only [List.contains_eq_mem, decide_eq_true_eq] using found

end TetraStereo.UniversalProof.NativeRingReachability
