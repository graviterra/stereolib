import TetraStereo.UniversalProof.NextFrontier.FramedDescriptorRuntime

set_option autoImplicit false





namespace TetraStereo.OneCenter.FramedCompleteRuntime

open RawMolecule

/-! Primitive structural equations; hypotheses identify actual primitive observations or recursive
subcalls, never an assumed full fact output. -/

theorem trackedInsertComplete?_nil (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (authoritative : Bool) (state : OccurrenceAuxState) (fuel : Nat)
    (candidate : CanonicalRerootCursor) :
    trackedInsertComplete? mol profile authoritative state fuel candidate [] =
      (FrameRuntime.cursor? mol profile (.actual candidate)).map (fun _ => ([candidate], 0)) := by
  cases observed : FrameRuntime.cursor? mol profile (.actual candidate) <;>
    simp [trackedInsertComplete?, observed]

theorem trackedInsertComplete?_nil_refuses (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (authoritative : Bool) (state : OccurrenceAuxState) (fuel : Nat)
    (candidate : CanonicalRerootCursor)
    (refused : FrameRuntime.cursor? mol profile (.actual candidate) = none) :
    trackedInsertComplete? mol profile authoritative state fuel candidate [] = none := by
  simp [trackedInsertComplete?, refused]

theorem trackedInsertComplete?_before (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (authoritative : Bool) (state : OccurrenceAuxState) (fuel : Nat)
    (candidate head : CanonicalRerootCursor) (tail : List CanonicalRerootCursor)
    (decision : OccurrenceComparison)
    (computed : FrameRuntime.decisionComplete? mol profile authoritative state fuel candidate head =
      some decision) (before : (decision.ordering == Ordering.lt) = false) :
    trackedInsertComplete? mol profile authoritative state fuel candidate (head :: tail) =
      some (candidate :: head :: tail, if decision.pseudo then 1 else 0) := by
  have ordering_ne : decision.ordering ≠ Ordering.lt := by
    intro ordering_eq
    simp [ordering_eq] at before
  simp [trackedInsertComplete?, computed, ordering_ne]

theorem trackedInsertComplete?_after (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (authoritative : Bool) (state : OccurrenceAuxState) (fuel : Nat)
    (candidate head : CanonicalRerootCursor) (tail : List CanonicalRerootCursor)
    (decision : OccurrenceComparison) (inserted : List CanonicalRerootCursor × Nat)
    (computed : FrameRuntime.decisionComplete? mol profile authoritative state fuel candidate head =
      some decision) (after : (decision.ordering == Ordering.lt) = true)
    (deeper : trackedInsertComplete? mol profile authoritative state fuel candidate tail =
      some inserted) :
    trackedInsertComplete? mol profile authoritative state fuel candidate (head :: tail) =
      some (head :: inserted.1, (if decision.pseudo then 1 else 0) + inserted.2) := by
  have ordering_eq : decision.ordering = Ordering.lt := by
    exact beq_iff_eq.mp after
  simp [trackedInsertComplete?, computed, ordering_eq, deeper]

theorem trackedSortComplete?_nil (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (authoritative : Bool) (state : OccurrenceAuxState) (fuel : Nat) :
    trackedSortComplete? mol profile authoritative state fuel [] = some ([], 0) := rfl

theorem trackedSortComplete?_cons (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (authoritative : Bool) (state : OccurrenceAuxState) (fuel : Nat)
    (head : CanonicalRerootCursor) (tail : List CanonicalRerootCursor)
    (sorted inserted : List CanonicalRerootCursor × Nat)
    (tailComputed : trackedSortComplete? mol profile authoritative state fuel tail = some sorted)
    (insertComputed : trackedInsertComplete? mol profile authoritative state fuel head sorted.1 =
      some inserted) :
    trackedSortComplete? mol profile authoritative state fuel (head :: tail) =
      some (inserted.1, sorted.2 + inserted.2) := by
  simp [trackedSortComplete?, tailComputed, insertComputed]

theorem adjacentComplete?_nil (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (authoritative : Bool) (state : OccurrenceAuxState) (fuel : Nat) :
    adjacentComplete? mol profile authoritative state fuel [] = some [] := rfl

theorem adjacentComplete?_singleton (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (authoritative : Bool) (state : OccurrenceAuxState) (fuel : Nat)
    (cursor : CanonicalRerootCursor) :
    adjacentComplete? mol profile authoritative state fuel [cursor] = some [] := rfl

theorem adjacentComplete?_cons (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (authoritative : Bool) (state : OccurrenceAuxState) (fuel : Nat)
    (left right : CanonicalRerootCursor) (tail : List CanonicalRerootCursor)
    (decision : OccurrenceComparison) (rest : List (OccurrenceComparedPair mol state fuel))
    (computed : FrameRuntime.decisionComplete? mol profile authoritative state fuel left right =
      some decision)
    (deeper : adjacentComplete? mol profile authoritative state fuel (right :: tail) = some rest) :
    adjacentComplete? mol profile authoritative state fuel (left :: right :: tail) =
      some ({ left := left, right := right, decision := decision } :: rest) := by
  simp [adjacentComplete?, computed, deeper]

/-- Every final retained decision is the actual complete decision at that exact pair/profile. -/
theorem adjacentComplete?_sound (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (authoritative : Bool) (state : OccurrenceAuxState) (fuel : Nat)
    (sorted : List CanonicalRerootCursor)
    (compared : List (OccurrenceComparedPair mol state fuel))
    (computed : adjacentComplete? mol profile authoritative state fuel sorted = some compared) :
    ∀ comparison, comparison ∈ compared →
      FrameRuntime.decisionComplete? mol profile authoritative state fuel
        comparison.left comparison.right = some comparison.decision := by
  induction sorted generalizing compared with
  | nil =>
      simp [adjacentComplete?] at computed
      subst compared
      simp
  | cons left tail inductionHypothesis =>
      cases tail with
      | nil =>
          simp [adjacentComplete?] at computed
          subst compared
          simp
      | cons right remaining =>
          simp only [adjacentComplete?] at computed
          cases comparisonEq : FrameRuntime.decisionComplete? mol profile authoritative state fuel
              left right with
          | none => simp [comparisonEq] at computed
          | some decision =>
              cases deeperEq : adjacentComplete? mol profile authoritative state fuel
                  (right :: remaining) with
              | none => simp [deeperEq] at computed
              | some deeper =>
                  simp [comparisonEq, deeperEq] at computed
                  subst compared
                  intro comparison member
                  rcases List.mem_cons.mp member with head | tailMember
                  · subst comparison
                    exact comparisonEq
                  · exact inductionHypothesis deeper deeperEq comparison tailMember

/-! The restricted runtime bridge is deliberately scoped to EMPTY auxiliary state. No universal
legacy/framed equality or nonempty descriptor-tie equivalence is asserted. -/

theorem decisionComplete?_empty_eq (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (authoritative : Bool) (fuel : Nat) (left right : CanonicalRerootCursor) :
    FrameRuntime.decisionComplete? mol profile authoritative [] fuel left right =
      FrameRuntime.decision? mol profile authoritative [] fuel left right := by
  rfl

theorem trackedInsertComplete?_empty_eq (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (authoritative : Bool) (fuel : Nat) (candidate : CanonicalRerootCursor)
    (entries : List CanonicalRerootCursor) :
    trackedInsertComplete? mol profile authoritative [] fuel candidate entries =
      FrameRuntime.trackedInsert? mol profile authoritative [] fuel candidate entries := by
  rfl

/-- Empty-state complete insertion cannot observe a Rule5 pseudo flag. -/
theorem trackedInsertComplete?_empty_counter_zero (mol : RawMolecule)
    (profile : FrameRuntime.Profile) (authoritative : Bool) (fuel : Nat)
    (candidate : CanonicalRerootCursor) (entries : List CanonicalRerootCursor)
    (result : List CanonicalRerootCursor × Nat)
    (computed : trackedInsertComplete? mol profile authoritative [] fuel candidate entries =
      some result) : result.2 = 0 := by
  induction entries generalizing result with
  | nil =>
      cases observed : FrameRuntime.cursor? mol profile (.actual candidate) with
      | none => simp [trackedInsertComplete?, observed] at computed
      | some distance =>
          simp [trackedInsertComplete?, observed] at computed
          subst result
          rfl
  | cons head tail inductionHypothesis =>
      cases constitutional : FrameRuntime.compareBranch? mol profile authoritative fuel .rule2
          (.actual candidate) (.actual head) with
      | none =>
          simp [trackedInsertComplete?, FrameRuntime.decisionComplete?, constitutional] at computed
      | some ordering =>
          cases ordering with
          | lt =>
              cases deeper : trackedInsertComplete? mol profile authoritative [] fuel
                  candidate tail with
              | none =>
                  simp [trackedInsertComplete?, FrameRuntime.decisionComplete?, constitutional,
                    deeper] at computed
              | some inserted =>
                  simp [trackedInsertComplete?, FrameRuntime.decisionComplete?, constitutional,
                    deeper] at computed
                  subst result
                  exact inductionHypothesis inserted deeper
          | eq =>
              simp [trackedInsertComplete?, FrameRuntime.decisionComplete?, constitutional] at computed
              subst result
              rfl
          | gt =>
              simp [trackedInsertComplete?, FrameRuntime.decisionComplete?, constitutional] at computed
              subst result
              rfl

theorem trackedSortComplete?_empty_counter_zero (mol : RawMolecule)
    (profile : FrameRuntime.Profile) (authoritative : Bool) (fuel : Nat)
    (entries : List CanonicalRerootCursor) (result : List CanonicalRerootCursor × Nat)
    (computed : trackedSortComplete? mol profile authoritative [] fuel entries = some result) :
    result.2 = 0 := by
  induction entries generalizing result with
  | nil =>
      simp [trackedSortComplete?] at computed
      subst result
      rfl
  | cons head tail inductionHypothesis =>
      cases tailComputed : trackedSortComplete? mol profile authoritative [] fuel tail with
      | none => simp [trackedSortComplete?, tailComputed] at computed
      | some sorted =>
          cases insertComputed : trackedInsertComplete? mol profile authoritative [] fuel
              head sorted.1 with
          | none => simp [trackedSortComplete?, tailComputed, insertComputed] at computed
          | some inserted =>
              simp [trackedSortComplete?, tailComputed, insertComputed] at computed
              subst result
              have tailZero := inductionHypothesis sorted tailComputed
              have insertZero := trackedInsertComplete?_empty_counter_zero mol profile
                authoritative fuel head sorted.1 inserted insertComputed
              simp [tailZero, insertZero]

/-- Exact restricted-sort bridge in the empty-state domain, including its zero counter. -/
theorem trackedSortComplete?_empty_eq (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (authoritative : Bool) (fuel : Nat) (entries : List CanonicalRerootCursor) :
    trackedSortComplete? mol profile authoritative [] fuel entries =
      FrameRuntime.trackedSort? mol profile authoritative [] fuel entries := by
  rfl

theorem adjacentComplete?_empty_eq (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (authoritative : Bool) (fuel : Nat) (entries : List CanonicalRerootCursor) :
    adjacentComplete? mol profile authoritative [] fuel entries =
      FrameRuntime.adjacent? mol profile authoritative [] fuel entries := by
  rfl

/-- Actual profile producer refusal propagates to the complete ordinary caller. -/
theorem occurrenceFactComplete?_refuses_profile (mol : RawMolecule) (authoritative : Bool)
    (fuel : Nat) (state : OccurrenceAuxState) (node : CanonicalBranchNode)
    (unsupported : FrameRuntime.profile? mol node = none) :
    occurrenceFactComplete? mol authoritative fuel state node = none := by
  simp [occurrenceFactComplete?, unsupported]

/-- The complete fast caller agrees unconditionally with the framed backend, including refusal. -/
theorem occurrenceFactComplete?_empty_framed_fast_eq (mol : RawMolecule) (fuel : Nat)
    (node : CanonicalBranchNode) :
    occurrenceFactComplete? mol false fuel [] node = framedOccurrenceFact? mol fuel [] node :=
  (framedOccurrenceFact?_eq_complete mol fuel [] node).symm

/-- Public dispatch selects the framed fast caller whenever its actual profile exists. -/
theorem occurrenceFactComplete?_empty_fast_eq (mol : RawMolecule) (fuel : Nat)
    (node : CanonicalBranchNode) (profile : FrameRuntime.Profile)
    (available : FrameRuntime.profile? mol node = some profile) :
    occurrenceFactComplete? mol false fuel [] node = occurrenceFact? mol fuel [] node := by
  rw [occurrenceFact?_eq_framed_of_profile_some mol fuel [] node profile available]
  exact occurrenceFactComplete?_empty_framed_fast_eq mol fuel node

end TetraStereo.OneCenter.FramedCompleteRuntime
