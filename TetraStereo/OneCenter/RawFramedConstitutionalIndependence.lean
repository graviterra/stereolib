import TetraStereo.OneCenter.SmilesTetrahedral
import TetraStereo.KernelOnly
































set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace RawFramedConstitutionalIndependence

open RawMolecule

/-! ## The constitutional-separation condition on the actual frame -/

/-- The actual framed root frame is constitutionally separated when

* the frame has no repeated cursors, and
* every distinct ordered pair of cursors is strictly decided by the actual framed constitutional
  comparison `FrameRuntime.compareBranch?` at `CanonicalRuleStage.rule2` with the resolved shared
  profile.

This predicate mentions the molecule, the profile, the fuel bound and the actual
`occurrenceLigandFrame?` output.  It does not mention or quantify over the auxiliary state. -/
def RootsConstitutionallySeparated (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (fuel : Nat) (roots : List CanonicalRerootCursor) : Prop :=
  roots.Nodup ∧
    ∀ left ∈ roots, ∀ right ∈ roots, left ≠ right →
      ∃ order : Ordering, order ≠ Ordering.eq ∧
        FrameRuntime.compareBranch? mol profile true fuel CanonicalRuleStage.rule2
          (FrameRuntime.Cursor.actual left) (FrameRuntime.Cursor.actual right) = some order

/-! ## Decisions are read from the constitution when the constitutional result is strict -/




theorem decisionComplete?_eq_of_compareBranch?_strict
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (authoritative : Bool)
    (fuel : Nat) (state : OccurrenceAuxState)
    (left right : CanonicalRerootCursor) (order : Ordering)
    (constitutional : FrameRuntime.compareBranch? mol profile authoritative fuel
      CanonicalRuleStage.rule2 (FrameRuntime.Cursor.actual left)
      (FrameRuntime.Cursor.actual right) = some order)
    (strict : order ≠ Ordering.eq) :
    FrameRuntime.decisionComplete? mol profile authoritative state fuel left right =
      some { ordering := order } := by
  unfold FrameRuntime.decisionComplete?
  rw [constitutional]
  cases order with
  | lt => rfl
  | gt => rfl
  | eq => exact absurd rfl strict

/-- The actual complete decision on a distinct pair of separated root cursors is independent of
the auxiliary state. -/
theorem decisionComplete?_state_independent_of_separated
    (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (fuel : Nat) (roots : List CanonicalRerootCursor)
    (state₁ state₂ : OccurrenceAuxState)
    (separated : ∀ left ∈ roots, ∀ right ∈ roots, left ≠ right →
      ∃ order : Ordering, order ≠ Ordering.eq ∧
        FrameRuntime.compareBranch? mol profile true fuel CanonicalRuleStage.rule2
          (FrameRuntime.Cursor.actual left) (FrameRuntime.Cursor.actual right) = some order)
    {left right : CanonicalRerootCursor}
    (leftMem : left ∈ roots) (rightMem : right ∈ roots) (distinct : left ≠ right) :
    FrameRuntime.decisionComplete? mol profile true state₁ fuel left right =
      FrameRuntime.decisionComplete? mol profile true state₂ fuel left right := by
  obtain ⟨order, strict, constitutional⟩ := separated left leftMem right rightMem distinct
  rw [decisionComplete?_eq_of_compareBranch?_strict mol profile true fuel state₁ left right order
        constitutional strict,
    decisionComplete?_eq_of_compareBranch?_strict mol profile true fuel state₂ left right order
        constitutional strict]

/-! ## The actual tracked insertion sort preserves permutations -/

/-- The actual complete tracked insertion returns a permutation of the candidate consed onto the
input list. -/
theorem trackedInsertComplete?_perm
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : Nat)
    (candidate : CanonicalRerootCursor) (input : List CanonicalRerootCursor)
    (output : List CanonicalRerootCursor × Nat)
    (computed : FramedCompleteRuntime.trackedInsertComplete? mol profile authoritative state fuel
      candidate input = some output) :
    output.1.Perm (candidate :: input) := by
  induction input generalizing output with
  | nil =>
      cases observed : FrameRuntime.cursor? mol profile (FrameRuntime.Cursor.actual candidate) with
      | none => simp [FramedCompleteRuntime.trackedInsertComplete?, observed] at computed
      | some distance =>
          simp [FramedCompleteRuntime.trackedInsertComplete?, observed] at computed
          subst output
          exact List.Perm.refl _
  | cons head tail inductionHypothesis =>
      simp only [FramedCompleteRuntime.trackedInsertComplete?] at computed
      cases decisionEq : FrameRuntime.decisionComplete? mol profile authoritative state fuel
          candidate head with
      | none => simp [decisionEq] at computed
      | some decision =>
          cases isLt : decision.ordering == Ordering.lt with
          | false =>
              have notLt : decision.ordering ≠ Ordering.lt := by
                intro eqLt
                have isLtTrue : (decision.ordering == Ordering.lt) = true := beq_iff_eq.mpr eqLt
                rw [isLtTrue] at isLt
                exact Bool.false_ne_true isLt.symm
              simp [decisionEq, notLt] at computed
              subst output
              exact List.Perm.refl _
          | true =>
              have isLt' : decision.ordering = Ordering.lt := beq_iff_eq.mp isLt
              cases deeperEq : FramedCompleteRuntime.trackedInsertComplete? mol profile
                  authoritative state fuel candidate tail with
              | none => simp [decisionEq, isLt', deeperEq] at computed
              | some deeper =>
                  simp [decisionEq, isLt', deeperEq] at computed
                  subst output
                  exact (List.Perm.cons head
                      (inductionHypothesis deeper deeperEq)).trans
                    (List.Perm.swap candidate head tail)

/-- The actual complete tracked sort returns a permutation of its input. -/
theorem trackedSortComplete?_perm
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : Nat)
    (input : List CanonicalRerootCursor) (output : List CanonicalRerootCursor × Nat)
    (computed : FramedCompleteRuntime.trackedSortComplete? mol profile authoritative state fuel
      input = some output) :
    output.1.Perm input := by
  induction input generalizing output with
  | nil =>
      simp [FramedCompleteRuntime.trackedSortComplete?] at computed
      subst output
      exact List.Perm.refl []
  | cons head tail inductionHypothesis =>
      simp only [FramedCompleteRuntime.trackedSortComplete?] at computed
      cases sortedEq : FramedCompleteRuntime.trackedSortComplete? mol profile authoritative state
          fuel tail with
      | none => simp [sortedEq] at computed
      | some sorted =>
          cases insertedEq : FramedCompleteRuntime.trackedInsertComplete? mol profile authoritative
              state fuel head sorted.1 with
          | none => simp [sortedEq, insertedEq] at computed
          | some inserted =>
              simp [sortedEq, insertedEq] at computed
              subst output
              exact (trackedInsertComplete?_perm mol profile authoritative state fuel head
                  sorted.1 inserted insertedEq).trans
                (List.Perm.cons head (inductionHypothesis sorted sortedEq))

/-! ## State independence of the actual tracked sort -/

/-- If the actual complete decision is independent of the auxiliary state on every distinct pair of
frame elements, then the actual complete tracked insertion at a fresh candidate is independent of
the auxiliary state. -/
theorem trackedInsertComplete?_state_independent
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (authoritative : Bool)
    (fuel : Nat) (state₁ state₂ : OccurrenceAuxState)
    (frame : List CanonicalRerootCursor)
    (pairwise : ∀ left ∈ frame, ∀ right ∈ frame, left ≠ right →
      FrameRuntime.decisionComplete? mol profile authoritative state₁ fuel left right =
        FrameRuntime.decisionComplete? mol profile authoritative state₂ fuel left right)
    (candidate : CanonicalRerootCursor) (candidateMem : candidate ∈ frame)
    (tail : List CanonicalRerootCursor)
    (tailMem : ∀ cursor ∈ tail, cursor ∈ frame)
    (fresh : candidate ∉ tail) :
    FramedCompleteRuntime.trackedInsertComplete? mol profile authoritative state₁ fuel candidate
        tail =
      FramedCompleteRuntime.trackedInsertComplete? mol profile authoritative state₂ fuel candidate
        tail := by
  induction tail with
  | nil => simp [FramedCompleteRuntime.trackedInsertComplete?]
  | cons head rest inductionHypothesis =>
      have headMem : head ∈ frame := tailMem head (List.mem_cons_self ..)
      have restMem : ∀ cursor ∈ rest, cursor ∈ frame :=
        fun cursor hcursor => tailMem cursor (List.mem_cons_of_mem head hcursor)
      have restFresh : candidate ∉ rest := fun h => fresh (List.mem_cons_of_mem head h)
      have distinct : candidate ≠ head :=
        fun h => fresh (List.mem_cons.mpr (Or.inl h))
      simp only [FramedCompleteRuntime.trackedInsertComplete?]
      rw [pairwise candidate candidateMem head headMem distinct]
      cases decisionEq : FrameRuntime.decisionComplete? mol profile authoritative state₂ fuel
          candidate head with
      | none => simp
      | some decision =>
          cases isLt : decision.ordering == Ordering.lt with
          | false =>
              have notLt : decision.ordering ≠ Ordering.lt := by
                intro eqLt
                have isLtTrue : (decision.ordering == Ordering.lt) = true := beq_iff_eq.mpr eqLt
                rw [isLtTrue] at isLt
                exact Bool.false_ne_true isLt.symm
              simp [notLt]
          | true =>
              have isLt' : decision.ordering = Ordering.lt := beq_iff_eq.mp isLt
              simp [isLt']
              rw [inductionHypothesis restMem restFresh]

/-- If the actual complete decision is independent of the auxiliary state on every distinct pair of
root cursors, then the actual complete tracked sort of the root frame is independent of the
auxiliary state. -/
theorem trackedSortComplete?_state_independent
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (authoritative : Bool)
    (fuel : Nat) (state₁ state₂ : OccurrenceAuxState)
    (roots : List CanonicalRerootCursor)
    (pairwise : ∀ left ∈ roots, ∀ right ∈ roots, left ≠ right →
      FrameRuntime.decisionComplete? mol profile authoritative state₁ fuel left right =
        FrameRuntime.decisionComplete? mol profile authoritative state₂ fuel left right)
    (distinctRoots : roots.Nodup) :
    FramedCompleteRuntime.trackedSortComplete? mol profile authoritative state₁ fuel roots =
      FramedCompleteRuntime.trackedSortComplete? mol profile authoritative state₂ fuel roots := by
  induction roots with
  | nil => simp [FramedCompleteRuntime.trackedSortComplete?]
  | cons head tail inductionHypothesis =>
      have tailPairwise : ∀ left ∈ tail, ∀ right ∈ tail, left ≠ right →
          FrameRuntime.decisionComplete? mol profile authoritative state₁ fuel left right =
            FrameRuntime.decisionComplete? mol profile authoritative state₂ fuel left right :=
        fun left leftMem right rightMem distinct =>
          pairwise left (List.mem_cons_of_mem head leftMem)
            right (List.mem_cons_of_mem head rightMem) distinct
      have tailNodup : tail.Nodup := distinctRoots.of_cons
      have headNotMem : head ∉ tail := (List.nodup_cons.mp distinctRoots).1
      simp only [FramedCompleteRuntime.trackedSortComplete?]
      rw [inductionHypothesis tailPairwise tailNodup]
      cases sortedEq : FramedCompleteRuntime.trackedSortComplete? mol profile authoritative
          state₂ fuel tail with
      | none => simp
      | some sorted =>
          obtain ⟨sortedList, sortedCount⟩ := sorted
          have sortedPerm : sortedList.Perm tail :=
            trackedSortComplete?_perm mol profile authoritative state₂ fuel tail
              (sortedList, sortedCount) sortedEq
          have headNotMemSorted : head ∉ sortedList :=
            fun hmem => headNotMem (sortedPerm.mem_iff.mp hmem)
          have insertEq :
              FramedCompleteRuntime.trackedInsertComplete? mol profile authoritative state₁ fuel
                  head sortedList =
                FramedCompleteRuntime.trackedInsertComplete? mol profile authoritative state₂ fuel
                  head sortedList :=
            trackedInsertComplete?_state_independent mol profile authoritative fuel state₁ state₂
              (head :: tail) pairwise head (List.mem_cons_self ..) sortedList
              (fun cursor hcursor =>
                List.mem_cons_of_mem head (sortedPerm.mem_iff.mp hcursor))
              headNotMemSorted
          simp [insertEq]

/-! ## State independence of the actual adjacent comparison pass -/

/-- The decision stream consumed by the actual framed evaluator: the actual complete adjacent pass
projected onto its `OccurrenceComparison` decisions.  `OccurrenceComparedPair mol state fuel` is
indexed by the auxiliary state, so this state-erased projection is the strongest well-typed
statement of adjacent-pass independence. -/
def adjacentDecisionsComplete? (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (authoritative : Bool) (state : OccurrenceAuxState) (fuel : Nat) :
    List CanonicalRerootCursor → Option (List OccurrenceComparison)
  | [] | [_] => some []
  | left :: right :: tail => do
      let decision ← FrameRuntime.decisionComplete? mol profile authoritative state fuel left right
      let rest ← adjacentDecisionsComplete? mol profile authoritative state fuel (right :: tail)
      some (decision :: rest)

/-- The state-erased adjacent decision stream is exactly the map of the actual complete adjacent
pair list onto its decisions, i.e. exactly what the evaluator consumes. -/
theorem adjacentDecisionsComplete?_eq_map
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (authoritative : Bool)
    (state : OccurrenceAuxState) (fuel : Nat) (frame : List CanonicalRerootCursor) :
    adjacentDecisionsComplete? mol profile authoritative state fuel frame =
      (FramedCompleteRuntime.adjacentComplete? mol profile authoritative state fuel frame).map
        (fun pairs => pairs.map OccurrenceComparedPair.decision) := by
  induction frame with
  | nil => simp [adjacentDecisionsComplete?, FramedCompleteRuntime.adjacentComplete?]
  | cons left rest inductionHypothesis =>
      cases rest with
      | nil => simp [adjacentDecisionsComplete?, FramedCompleteRuntime.adjacentComplete?]
      | cons right remaining =>
          unfold adjacentDecisionsComplete? FramedCompleteRuntime.adjacentComplete?
          rw [inductionHypothesis]
          dsimp only [Bind.bind]
          simp only [Option.map_bind, Option.bind_map]
          refine Option.bind_congr ?_
          intro decision _
          simp only [Function.comp_apply]
          rw [Option.map_bind]
          simp [Option.map_some]

/-- If the actual complete decision is independent of the auxiliary state on every distinct pair of
frame elements, then the decision stream of the actual complete adjacent pass over a
duplicate-free frame is independent of the auxiliary state. -/
theorem adjacentDecisionsComplete?_state_independent
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (authoritative : Bool)
    (fuel : Nat) (state₁ state₂ : OccurrenceAuxState)
    (frame : List CanonicalRerootCursor)
    (pairwise : ∀ left ∈ frame, ∀ right ∈ frame, left ≠ right →
      FrameRuntime.decisionComplete? mol profile authoritative state₁ fuel left right =
        FrameRuntime.decisionComplete? mol profile authoritative state₂ fuel left right)
    (distinctFrame : frame.Nodup) :
    adjacentDecisionsComplete? mol profile authoritative state₁ fuel frame =
      adjacentDecisionsComplete? mol profile authoritative state₂ fuel frame := by
  induction frame with
  | nil => simp [adjacentDecisionsComplete?]
  | cons left rest inductionHypothesis =>
      cases rest with
      | nil => simp [adjacentDecisionsComplete?]
      | cons right remaining =>
          have leftNotMem : left ∉ right :: remaining :=
            (List.nodup_cons.mp distinctFrame).1
          have tailNodup : (right :: remaining).Nodup := distinctFrame.of_cons
          have distinct : left ≠ right :=
            fun h => leftNotMem (List.mem_cons.mpr (Or.inl h))
          have tailPairwise :
              ∀ a ∈ right :: remaining, ∀ b ∈ right :: remaining, a ≠ b →
                FrameRuntime.decisionComplete? mol profile authoritative state₁ fuel a b =
                  FrameRuntime.decisionComplete? mol profile authoritative state₂ fuel a b :=
            fun a aMem b bMem distinctPairs =>
              pairwise a (List.mem_cons_of_mem left aMem)
                b (List.mem_cons_of_mem left bMem) distinctPairs
          simp only [adjacentDecisionsComplete?]
          rw [pairwise left (List.mem_cons_self ..)
            right (List.mem_cons_of_mem left (List.mem_cons_self ..)) distinct]
          rw [inductionHypothesis tailPairwise tailNodup]

/-! ## The pseudo-pair count on the actual adjacent output is zero -/

/-- Under constitutional separation, every comparison actually produced by the complete adjacent
pass has the default `pseudo = false` flag: no Rule-5 enantiomorphic pair survives the strict
constitutional short-circuit. -/
theorem adjacentComplete?_decisions_pseudo_false
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (fuel : Nat)
    (state : OccurrenceAuxState) (frame : List CanonicalRerootCursor)
    (separated : ∀ left ∈ frame, ∀ right ∈ frame, left ≠ right →
      ∃ order : Ordering, order ≠ Ordering.eq ∧
        FrameRuntime.compareBranch? mol profile true fuel CanonicalRuleStage.rule2
          (FrameRuntime.Cursor.actual left) (FrameRuntime.Cursor.actual right) = some order)
    (distinctFrame : frame.Nodup)
    (pairs : List (OccurrenceComparedPair mol state fuel))
    (computed : FramedCompleteRuntime.adjacentComplete? mol profile true state fuel frame =
      some pairs) :
    ∀ pair ∈ pairs, pair.decision.pseudo = false := by
  induction frame generalizing pairs with
  | nil =>
      simp [FramedCompleteRuntime.adjacentComplete?] at computed
      subst pairs
      simp
  | cons left rest inductionHypothesis =>
      cases rest with
      | nil =>
          simp [FramedCompleteRuntime.adjacentComplete?] at computed
          subst pairs
          simp
      | cons right remaining =>
          have leftNotMem : left ∉ right :: remaining :=
            (List.nodup_cons.mp distinctFrame).1
          have tailNodup : (right :: remaining).Nodup := distinctFrame.of_cons
          have distinct : left ≠ right :=
            fun h => leftNotMem (List.mem_cons.mpr (Or.inl h))
          have tailSeparated :
              ∀ a ∈ right :: remaining, ∀ b ∈ right :: remaining, a ≠ b →
                ∃ order : Ordering, order ≠ Ordering.eq ∧
                  FrameRuntime.compareBranch? mol profile true fuel CanonicalRuleStage.rule2
                    (FrameRuntime.Cursor.actual a) (FrameRuntime.Cursor.actual b) = some order :=
            fun a aMem b bMem distinctPairs =>
              separated a (List.mem_cons_of_mem left aMem)
                b (List.mem_cons_of_mem left bMem) distinctPairs
          simp only [FramedCompleteRuntime.adjacentComplete?] at computed
          cases decisionEq : FrameRuntime.decisionComplete? mol profile true state fuel
              left right with
          | none => simp [decisionEq] at computed
          | some decision =>
              cases deeperEq : FramedCompleteRuntime.adjacentComplete? mol profile true state fuel
                  (right :: remaining) with
              | none => simp [decisionEq, deeperEq] at computed
              | some deeper =>
                  simp [decisionEq, deeperEq] at computed
                  subst pairs
                  intro pair hpair
                  rcases List.mem_cons.mp hpair with head | tailMember
                  · subst pair
                    obtain ⟨order, strict, constitutional⟩ :=
                      separated left (List.mem_cons_self ..)
                        right (List.mem_cons_of_mem left (List.mem_cons_self ..)) distinct
                    have classified :=
                      decisionComplete?_eq_of_compareBranch?_strict mol profile true fuel state
                        left right order constitutional strict
                    rw [decisionEq] at classified
                    injection classified with decisionShape
                    subst decision
                    rfl
                  · exact inductionHypothesis tailSeparated tailNodup deeper deeperEq pair
                      tailMember

/-- The actual complete adjacent pass therefore contributes zero pseudo pairs on a
constitutionally separated frame. -/
theorem adjacentComplete?_pseudoCount_zero
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (fuel : Nat)
    (state : OccurrenceAuxState) (frame : List CanonicalRerootCursor)
    (separated : ∀ left ∈ frame, ∀ right ∈ frame, left ≠ right →
      ∃ order : Ordering, order ≠ Ordering.eq ∧
        FrameRuntime.compareBranch? mol profile true fuel CanonicalRuleStage.rule2
          (FrameRuntime.Cursor.actual left) (FrameRuntime.Cursor.actual right) = some order)
    (distinctFrame : frame.Nodup)
    (pairs : List (OccurrenceComparedPair mol state fuel))
    (computed : FramedCompleteRuntime.adjacentComplete? mol profile true state fuel frame =
      some pairs) :
    ((pairs.map OccurrenceComparedPair.decision).filter
        (fun decision => decision.pseudo)).length = 0 := by
  have pseudoFalse :=
    adjacentComplete?_decisions_pseudo_false mol profile fuel state frame separated
      distinctFrame pairs computed
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro decision decisionMem
  obtain ⟨pair, pairMem, pairDecision⟩ := List.mem_map.mp decisionMem
  rw [← pairDecision]
  rw [pseudoFalse pair pairMem]
  exact Bool.false_ne_true

/-! ## State independence of the actual framed occurrence evaluator -/

/-- The actual framed occurrence evaluator `framedOccurrenceFactAuthoritative?` returns the same
option for any two auxiliary states, provided that the actual resolved frame at the evaluated node
is constitutionally separated by the actual framed comparator.

No sorting or result equality is assumed: the tracked sort and the adjacent pass are proved equal by
induction on the actual runtime functions, using only `roots.Nodup` and strictness of the actual
constitutional comparisons. -/
theorem framedOccurrenceFactAuthoritative?_state_independent
    (mol : RawMolecule) (fuel : Nat) (node : RawMolecule.CanonicalBranchNode)
    (profile : FrameRuntime.Profile) (roots : List CanonicalRerootCursor)
    (state₁ state₂ : OccurrenceAuxState)
    (profileEq : FrameRuntime.profile? mol node = some profile)
    (rootsEq : occurrenceLigandFrame? mol node = some roots)
    (separated : RootsConstitutionallySeparated mol profile fuel roots) :
    framedOccurrenceFactAuthoritative? mol fuel state₁ node =
      framedOccurrenceFactAuthoritative? mol fuel state₂ node := by
  rcases separated with ⟨distinctRoots, strictPairs⟩
  have pairwise : ∀ left ∈ roots, ∀ right ∈ roots, left ≠ right →
      FrameRuntime.decisionComplete? mol profile true state₁ fuel left right =
        FrameRuntime.decisionComplete? mol profile true state₂ fuel left right :=
    fun left leftMem right rightMem distinct =>
      decisionComplete?_state_independent_of_separated mol profile fuel roots state₁ state₂
        strictPairs leftMem rightMem distinct
  have sortEq :
      FramedCompleteRuntime.trackedSortComplete? mol profile true state₁ fuel roots =
        FramedCompleteRuntime.trackedSortComplete? mol profile true state₂ fuel roots :=
    trackedSortComplete?_state_independent mol profile true fuel state₁ state₂ roots pairwise
      distinctRoots
  unfold framedOccurrenceFactAuthoritative?
  dsimp only [FrameRuntime.trackedSort?, FrameRuntime.adjacent?, Bind.bind]
  rw [profileEq, rootsEq]
  simp only [Option.bind_some]
  rw [sortEq]
  cases sortedEq : FramedCompleteRuntime.trackedSortComplete? mol profile true state₂ fuel roots with
  | none => simp only [Option.bind_none]
  | some sorted =>
      obtain ⟨sortedList, sortedCount⟩ := sorted
      have sortedPerm : sortedList.Perm roots :=
        trackedSortComplete?_perm mol profile true state₂ fuel roots
          (sortedList, sortedCount) sortedEq
      have sortedNodup : sortedList.Nodup := sortedPerm.nodup_iff.mpr distinctRoots
      have sortedPairwise : ∀ left ∈ sortedList, ∀ right ∈ sortedList, left ≠ right →
          FrameRuntime.decisionComplete? mol profile true state₁ fuel left right =
            FrameRuntime.decisionComplete? mol profile true state₂ fuel left right :=
        fun left leftMem right rightMem distinct =>
          pairwise left (sortedPerm.mem_iff.mp leftMem)
            right (sortedPerm.mem_iff.mp rightMem) distinct
      have adjacentEq :
          adjacentDecisionsComplete? mol profile true state₁ fuel sortedList =
            adjacentDecisionsComplete? mol profile true state₂ fuel sortedList :=
        adjacentDecisionsComplete?_state_independent mol profile true fuel state₁ state₂
          sortedList sortedPairwise sortedNodup
      simp only [Option.bind_some]
      rw [← adjacentDecisionsComplete?_eq_map mol profile true state₁ fuel sortedList,
        ← adjacentDecisionsComplete?_eq_map mol profile true state₂ fuel sortedList,
        adjacentEq]

/-- The actual framed occurrence evaluator succeeds for one auxiliary state exactly when it
succeeds for the other. -/
theorem framedOccurrenceFactAuthoritative?_isSome_state_independent
    (mol : RawMolecule) (fuel : Nat) (node : RawMolecule.CanonicalBranchNode)
    (profile : FrameRuntime.Profile) (roots : List CanonicalRerootCursor)
    (state₁ state₂ : OccurrenceAuxState)
    (profileEq : FrameRuntime.profile? mol node = some profile)
    (rootsEq : occurrenceLigandFrame? mol node = some roots)
    (separated : RootsConstitutionallySeparated mol profile fuel roots) :
    (framedOccurrenceFactAuthoritative? mol fuel state₁ node).isSome =
      (framedOccurrenceFactAuthoritative? mol fuel state₂ node).isSome := by
  rw [framedOccurrenceFactAuthoritative?_state_independent mol fuel node profile roots state₁
    state₂ profileEq rootsEq separated]

/-- A fact is produced in one auxiliary state exactly when the same fact is produced in the
other. -/
theorem framedOccurrenceFactAuthoritative?_some_iff
    (mol : RawMolecule) (fuel : Nat) (node : RawMolecule.CanonicalBranchNode)
    (profile : FrameRuntime.Profile) (roots : List CanonicalRerootCursor)
    (state₁ state₂ : OccurrenceAuxState) (fact : OccurrenceAuxFact)
    (profileEq : FrameRuntime.profile? mol node = some profile)
    (rootsEq : occurrenceLigandFrame? mol node = some roots)
    (separated : RootsConstitutionallySeparated mol profile fuel roots) :
    framedOccurrenceFactAuthoritative? mol fuel state₁ node = some fact ↔
      framedOccurrenceFactAuthoritative? mol fuel state₂ node = some fact := by
  rw [framedOccurrenceFactAuthoritative?_state_independent mol fuel node profile roots state₁
    state₂ profileEq rootsEq separated]

/-- Every field of the produced occurrence fact -- including the `uppercase` field derived from the
pseudo-pair count and the `priorityPositions` field derived from the tracked ranking -- agrees
across auxiliary states. -/
theorem framedOccurrenceFactAuthoritative?_fields_state_independent
    (mol : RawMolecule) (fuel : Nat) (node : RawMolecule.CanonicalBranchNode)
    (profile : FrameRuntime.Profile) (roots : List CanonicalRerootCursor)
    (state₁ state₂ : OccurrenceAuxState) (fact₁ fact₂ : OccurrenceAuxFact)
    (profileEq : FrameRuntime.profile? mol node = some profile)
    (rootsEq : occurrenceLigandFrame? mol node = some roots)
    (separated : RootsConstitutionallySeparated mol profile fuel roots)
    (first : framedOccurrenceFactAuthoritative? mol fuel state₁ node = some fact₁)
    (second : framedOccurrenceFactAuthoritative? mol fuel state₂ node = some fact₂) :
    fact₁.key = fact₂.key ∧ fact₁.atom = fact₂.atom ∧
      fact₁.descriptor = fact₂.descriptor ∧ fact₁.uppercase = fact₂.uppercase ∧
      fact₁.priorityPositions = fact₂.priorityPositions := by
  have same := framedOccurrenceFactAuthoritative?_state_independent mol fuel node profile roots
    state₁ state₂ profileEq rootsEq separated
  rw [first, second] at same
  have factsEqual : fact₁ = fact₂ := Option.some.inj same
  subst fact₂
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end RawFramedConstitutionalIndependence
end OneCenter
end TetraStereo

/-! ## Kernel-authority guards -/

assert_kernel_only
  TetraStereo.OneCenter.RawFramedConstitutionalIndependence.decisionComplete?_eq_of_compareBranch?_strict
assert_kernel_only
  TetraStereo.OneCenter.RawFramedConstitutionalIndependence.decisionComplete?_state_independent_of_separated
assert_kernel_only
  TetraStereo.OneCenter.RawFramedConstitutionalIndependence.trackedInsertComplete?_perm
assert_kernel_only
  TetraStereo.OneCenter.RawFramedConstitutionalIndependence.trackedSortComplete?_perm
assert_kernel_only
  TetraStereo.OneCenter.RawFramedConstitutionalIndependence.trackedInsertComplete?_state_independent
assert_kernel_only
  TetraStereo.OneCenter.RawFramedConstitutionalIndependence.trackedSortComplete?_state_independent
assert_kernel_only
  TetraStereo.OneCenter.RawFramedConstitutionalIndependence.adjacentDecisionsComplete?_eq_map
assert_kernel_only
  TetraStereo.OneCenter.RawFramedConstitutionalIndependence.adjacentDecisionsComplete?_state_independent
assert_kernel_only
  TetraStereo.OneCenter.RawFramedConstitutionalIndependence.adjacentComplete?_decisions_pseudo_false
assert_kernel_only
  TetraStereo.OneCenter.RawFramedConstitutionalIndependence.adjacentComplete?_pseudoCount_zero
assert_kernel_only
  TetraStereo.OneCenter.RawFramedConstitutionalIndependence.framedOccurrenceFactAuthoritative?_state_independent
assert_kernel_only
  TetraStereo.OneCenter.RawFramedConstitutionalIndependence.framedOccurrenceFactAuthoritative?_isSome_state_independent
assert_kernel_only
  TetraStereo.OneCenter.RawFramedConstitutionalIndependence.framedOccurrenceFactAuthoritative?_some_iff
assert_kernel_only
  TetraStereo.OneCenter.RawFramedConstitutionalIndependence.framedOccurrenceFactAuthoritative?_fields_state_independent
