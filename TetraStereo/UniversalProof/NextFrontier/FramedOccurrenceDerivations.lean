import TetraStereo.UniversalProof.NextFrontier.FramedDescriptorSorting

set_option autoImplicit false

/-! Independent primitive evidence for the actual complete framed caller. Legacy Rule6 and
legacy Rules456 interfaces are not imported or redefined. -/
namespace TetraStereo.OneCenter.FramedOrdinaryConformance

open RawMolecule

/-- The exact lowercase-guarded stage between actual framed Rule4b and Rule5. -/
def ordinaryRule4cStageComplete? (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (authoritative : Bool) (aux : OccurrenceAuxState) (fuel : Nat)
    (left right : CanonicalRerootCursor) : Option OccurrenceRule4cDecision :=
  if aux.any (fun fact => !fact.uppercase) then
    FrameRuntime.compareRule4cWithWitness? mol profile authoritative aux
      (FrameRuntime.compareDescriptorBranchAt? mol profile authoritative aux fuel .rule4c)
      (FrameRuntime.compareDescriptorBranchAt? mol profile authoritative aux fuel .rule4c)
      fuel [(.actual left, .actual right)]
  else some { ordering := Ordering.eq }

/-- Pure precedence with the actual empty-environment tie shortcut. It performs no molecular walk. -/
def assembleCompleteComparison? (empty : Bool)
    (constitutional rule4a rule4b : Option Ordering)
    (rule4c : Option OccurrenceRule4cDecision)
    (rule5 : Option RawRule5Comparison) : Option OccurrenceComparison := do
  let constitutional ← constitutional
  if constitutional != Ordering.eq then return { ordering := constitutional }
  if empty then return { ordering := Ordering.eq }
  let rule4a ← rule4a
  if rule4a != Ordering.eq then return { ordering := rule4a }
  let rule4b ← rule4b
  if rule4b != Ordering.eq then return { ordering := rule4b }
  let rule4c ← rule4c
  if rule4c.ordering != Ordering.eq then
    return { ordering := rule4c.ordering, rule4cCarrier? := rule4c.carrier? }
  let rule5 ← rule5
  some { ordering := rule5.ordering, pseudo := rule5.pseudo }

theorem decisionComplete?_factorization (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (authoritative : Bool) (aux : OccurrenceAuxState) (fuel : Nat)
    (left right : CanonicalRerootCursor) :
    FrameRuntime.decisionComplete? mol profile authoritative aux fuel left right =
      assembleCompleteComparison? aux.isEmpty
        (FrameRuntime.compareBranch? mol profile authoritative fuel .rule2 (.actual left) (.actual right))
        (FrameRuntime.compareDescriptorAtTiedRoot? mol profile authoritative aux fuel .rule4a
          (.actual left) (.actual right))
        (FrameRuntime.compareRule4b? mol profile authoritative aux fuel (.actual left) (.actual right))
        (ordinaryRule4cStageComplete? mol profile authoritative aux fuel left right)
        (FrameRuntime.compareRule5? mol profile authoritative aux fuel (.actual left) (.actual right)) := by
  unfold FrameRuntime.decisionComplete? assembleCompleteComparison? ordinaryRule4cStageComplete?
  cases constitutional : FrameRuntime.compareBranch? mol profile authoritative fuel .rule2
      (.actual left) (.actual right) <;>
    cases rule4a : FrameRuntime.compareDescriptorAtTiedRoot? mol profile authoritative aux fuel .rule4a
      (.actual left) (.actual right) <;>
    cases rule4b : FrameRuntime.compareRule4b? mol profile authoritative aux fuel
      (.actual left) (.actual right) <;>
    cases empty : aux.isEmpty <;>
    cases lower : aux.any (fun fact => !fact.uppercase) <;>
    cases rule4c : FrameRuntime.compareRule4cWithWitness? mol profile authoritative aux
      (FrameRuntime.compareDescriptorBranchAt? mol profile authoritative aux fuel .rule4c)
      (FrameRuntime.compareDescriptorBranchAt? mol profile authoritative aux fuel .rule4c)
      fuel [(.actual left, .actual right)] <;>
    cases rule5 : FrameRuntime.compareRule5? mol profile authoritative aux fuel
      (.actual left) (.actual right) <;>
    rfl

variable {mol : RawMolecule} {profile : FrameRuntime.Profile} {authoritative : Bool}

/-- No whole decision equation is a field: reconstruct it from five actual primitive equations
and the independent pure precedence equation. All stages share the same profile/mode. -/
structure FrameRule45Evaluation (profile : FrameRuntime.Profile) (authoritative : Bool)
    (aux : OccurrenceAuxState) (fuel : Nat) (comparison : OccurrenceComparedPair mol aux fuel) where
  constitutionalResult : Option Ordering
  constitutionalEquation : FrameRuntime.compareBranch? mol profile authoritative fuel .rule2
    (.actual comparison.left) (.actual comparison.right) = constitutionalResult
  rule4aResult : Option Ordering
  rule4aEquation : FrameRuntime.compareDescriptorAtTiedRoot? mol profile authoritative aux fuel .rule4a
    (.actual comparison.left) (.actual comparison.right) = rule4aResult
  rule4bResult : Option Ordering
  rule4bEquation : FrameRuntime.compareRule4b? mol profile authoritative aux fuel
    (.actual comparison.left) (.actual comparison.right) = rule4bResult
  rule4cResult : Option OccurrenceRule4cDecision
  rule4cEquation : ordinaryRule4cStageComplete? mol profile authoritative aux fuel
    comparison.left comparison.right = rule4cResult
  rule5Result : Option RawRule5Comparison
  rule5Equation : FrameRuntime.compareRule5? mol profile authoritative aux fuel
    (.actual comparison.left) (.actual comparison.right) = rule5Result
  precedenceEquation : assembleCompleteComparison? aux.isEmpty constitutionalResult rule4aResult
    rule4bResult rule4cResult rule5Result = some comparison.decision

theorem FrameRule45Evaluation.production_eq {aux : OccurrenceAuxState} {fuel : Nat}
    {comparison : OccurrenceComparedPair mol aux fuel}
    (evaluation : FrameRule45Evaluation profile authoritative aux fuel comparison) :
    FrameRuntime.decisionComplete? mol profile authoritative aux fuel comparison.left comparison.right =
      some comparison.decision := by
  rw [decisionComplete?_factorization]
  rw [evaluation.constitutionalEquation, evaluation.rule4aEquation, evaluation.rule4bEquation,
    evaluation.rule4cEquation, evaluation.rule5Equation]
  exact evaluation.precedenceEquation

/-- Completeness extracts actual stage calls and precedence from a computed primitive decision.
The computed whole decision is an input to this extraction theorem, never a stored certificate field. -/
def frameRule45Evaluation (profile : FrameRuntime.Profile) (authoritative : Bool)
    (aux : OccurrenceAuxState) (fuel : Nat) (comparison : OccurrenceComparedPair mol aux fuel)
    (computed : FrameRuntime.decisionComplete? mol profile authoritative aux fuel
      comparison.left comparison.right = some comparison.decision) :
    FrameRule45Evaluation profile authoritative aux fuel comparison :=
  { constitutionalResult := FrameRuntime.compareBranch? mol profile authoritative fuel .rule2
      (.actual comparison.left) (.actual comparison.right)
    constitutionalEquation := rfl
    rule4aResult := FrameRuntime.compareDescriptorAtTiedRoot? mol profile authoritative aux fuel .rule4a
      (.actual comparison.left) (.actual comparison.right)
    rule4aEquation := rfl
    rule4bResult := FrameRuntime.compareRule4b? mol profile authoritative aux fuel
      (.actual comparison.left) (.actual comparison.right)
    rule4bEquation := rfl
    rule4cResult := ordinaryRule4cStageComplete? mol profile authoritative aux fuel
      comparison.left comparison.right
    rule4cEquation := rfl
    rule5Result := FrameRuntime.compareRule5? mol profile authoritative aux fuel
      (.actual comparison.left) (.actual comparison.right)
    rule5Equation := rfl
    precedenceEquation := by
      rw [← decisionComplete?_factorization]
      exact computed }


theorem frameRule45Evaluation_iff_production (profile : FrameRuntime.Profile)
    (authoritative : Bool) (aux : OccurrenceAuxState) (fuel : Nat)
    (comparison : OccurrenceComparedPair mol aux fuel) :
    Nonempty (FrameRule45Evaluation profile authoritative aux fuel comparison) ↔
      FrameRuntime.decisionComplete? mol profile authoritative aux fuel comparison.left comparison.right =
        some comparison.decision := by
  constructor
  · rintro ⟨evaluation⟩
    exact evaluation.production_eq
  · intro computed
    exact ⟨frameRule45Evaluation profile authoritative aux fuel comparison computed⟩

inductive FrameInsertOccurrenceDerivation (profile : FrameRuntime.Profile) (authoritative : Bool) (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (candidate : CanonicalRerootCursor) :
    List CanonicalRerootCursor → (List CanonicalRerootCursor × Nat) → Prop
  | nil (distance : Nat)
      (observed : FrameRuntime.cursor? mol profile (.actual candidate) = some distance) :
      FrameInsertOccurrenceDerivation profile authoritative aux fuel candidate [] ([candidate], 0)
  | before (head : CanonicalRerootCursor) (tail : List CanonicalRerootCursor)
      (decision : OccurrenceComparison)
      (stage : FrameRule45Evaluation (mol := mol) profile authoritative aux fuel
        { left := candidate, right := head, decision := decision })
      (not_lt : (decision.ordering == Ordering.lt) = false) :
      FrameInsertOccurrenceDerivation profile authoritative aux fuel candidate (head :: tail)
        (candidate :: head :: tail, if decision.pseudo then 1 else 0)
  | after (head : CanonicalRerootCursor) (tail inserted : List CanonicalRerootCursor)
      (count : Nat) (decision : OccurrenceComparison)
      (stage : FrameRule45Evaluation (mol := mol) profile authoritative aux fuel
        { left := candidate, right := head, decision := decision })
      (is_lt : (decision.ordering == Ordering.lt) = true)
      (deeper : FrameInsertOccurrenceDerivation profile authoritative aux fuel candidate tail (inserted, count)) :
      FrameInsertOccurrenceDerivation profile authoritative aux fuel candidate (head :: tail)
        (head :: inserted, (if decision.pseudo then 1 else 0) + count)

theorem FrameInsertOccurrenceDerivation.production_eq
    {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {candidate : CanonicalRerootCursor} {input : List CanonicalRerootCursor}
    {output : List CanonicalRerootCursor × Nat}
    (derivation : FrameInsertOccurrenceDerivation (mol := mol) profile authoritative aux fuel candidate input output) :
    FramedCompleteRuntime.trackedInsertComplete? mol profile authoritative aux fuel candidate input = some output := by
  induction derivation with
  | nil distance observed => simp [FramedCompleteRuntime.trackedInsertComplete?, observed]
  | before head tail decision stage not_lt =>
      have not_lt' : decision.ordering ≠ Ordering.lt := by
        intro ordering_eq
        simp [ordering_eq] at not_lt
      simp [FramedCompleteRuntime.trackedInsertComplete?, stage.production_eq, not_lt']
  | after head tail inserted count decision stage is_lt deeper inductionHypothesis =>
      have is_lt' : decision.ordering = Ordering.lt := beq_iff_eq.mp is_lt
      simp [FramedCompleteRuntime.trackedInsertComplete?, stage.production_eq, is_lt', inductionHypothesis]

theorem frameInsertOccurrenceDerivation_of_production
    (profile : FrameRuntime.Profile) (authoritative : Bool) (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (candidate : CanonicalRerootCursor) (input : List CanonicalRerootCursor)
    (output : List CanonicalRerootCursor × Nat)
    (computed : FramedCompleteRuntime.trackedInsertComplete? mol profile authoritative aux fuel candidate input = some output) :
    FrameInsertOccurrenceDerivation (mol := mol) profile authoritative aux fuel candidate input output := by
  induction input generalizing output with
  | nil =>
      cases observed : FrameRuntime.cursor? mol profile (.actual candidate) with
      | none => simp [FramedCompleteRuntime.trackedInsertComplete?, observed] at computed
      | some distance =>
          simp [FramedCompleteRuntime.trackedInsertComplete?, observed] at computed
          subst output
          exact .nil distance observed
  | cons head tail inductionHypothesis =>
      simp only [FramedCompleteRuntime.trackedInsertComplete?] at computed
      cases comparisonEq : FrameRuntime.decisionComplete? mol profile authoritative aux fuel candidate head with
      | none => simp [comparisonEq] at computed
      | some decision =>
          cases isLt : decision.ordering == Ordering.lt with
          | false =>
              have notLt : decision.ordering ≠ Ordering.lt := by
                intro ordering_eq
                simp [ordering_eq] at isLt
              have direct : FramedCompleteRuntime.trackedInsertComplete? mol profile authoritative aux fuel candidate (head :: tail) =
                  some (candidate :: head :: tail, if decision.pseudo then 1 else 0) := by
                simp [FramedCompleteRuntime.trackedInsertComplete?, comparisonEq, notLt]
              have outputEq : output =
                  (candidate :: head :: tail, if decision.pseudo then 1 else 0) :=
                Option.some.inj (computed.symm.trans direct)
              subst output
              exact .before head tail decision
                (frameRule45Evaluation (mol := mol) profile authoritative aux fuel _ comparisonEq) isLt
          | true =>
              have isLt' : decision.ordering = Ordering.lt := beq_iff_eq.mp isLt
              cases deeperEq : FramedCompleteRuntime.trackedInsertComplete? mol profile authoritative aux fuel candidate tail with
              | none =>
                  simp [comparisonEq, isLt', deeperEq] at computed
              | some deeper =>
                  have direct : FramedCompleteRuntime.trackedInsertComplete? mol profile authoritative aux fuel candidate (head :: tail) =
                      some (head :: deeper.1,
                        (if decision.pseudo then 1 else 0) + deeper.2) := by
                    simp [FramedCompleteRuntime.trackedInsertComplete?, comparisonEq, isLt', deeperEq]
                  have outputEq : output =
                      (head :: deeper.1, (if decision.pseudo then 1 else 0) + deeper.2) :=
                    Option.some.inj (computed.symm.trans direct)
                  subst output
                  exact .after head tail deeper.1 deeper.2 decision
                    (frameRule45Evaluation (mol := mol) profile authoritative aux fuel _ comparisonEq) isLt
                    (inductionHypothesis deeper deeperEq)

inductive FrameSortOccurrencesDerivation (profile : FrameRuntime.Profile) (authoritative : Bool) (aux : OneCenter.OccurrenceAuxState) (fuel : Nat) :
    List CanonicalRerootCursor → (List CanonicalRerootCursor × Nat) → Prop
  | nil : FrameSortOccurrencesDerivation profile authoritative aux fuel [] ([], 0)
  | cons (cursor : CanonicalRerootCursor) (cursors : List CanonicalRerootCursor)
      (sorted inserted : List CanonicalRerootCursor × Nat)
      (tail : FrameSortOccurrencesDerivation profile authoritative aux fuel cursors sorted)
      (insertion : FrameInsertOccurrenceDerivation (mol := mol) profile authoritative aux fuel cursor sorted.1 inserted) :
      FrameSortOccurrencesDerivation profile authoritative aux fuel (cursor :: cursors)
        (inserted.1, sorted.2 + inserted.2)

theorem FrameSortOccurrencesDerivation.production_eq
    {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {input : List CanonicalRerootCursor} {output : List CanonicalRerootCursor × Nat}
    (derivation : FrameSortOccurrencesDerivation (mol := mol) profile authoritative aux fuel input output) :
    FramedCompleteRuntime.trackedSortComplete? mol profile authoritative aux fuel input = some output := by
  induction derivation with
  | nil => rfl
  | cons cursor cursors sorted inserted tail insertion tailHypothesis =>
      simp [FramedCompleteRuntime.trackedSortComplete?, tailHypothesis, insertion.production_eq]

theorem frameSortOccurrencesDerivation_of_production
    (profile : FrameRuntime.Profile) (authoritative : Bool) (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (input : List CanonicalRerootCursor) (output : List CanonicalRerootCursor × Nat)
    (computed : FramedCompleteRuntime.trackedSortComplete? mol profile authoritative aux fuel input = some output) :
    FrameSortOccurrencesDerivation (mol := mol) profile authoritative aux fuel input output := by
  induction input generalizing output with
  | nil =>
      simp [FramedCompleteRuntime.trackedSortComplete?] at computed
      subst output
      exact .nil
  | cons cursor cursors inductionHypothesis =>
      simp only [FramedCompleteRuntime.trackedSortComplete?] at computed
      cases sortedEq : FramedCompleteRuntime.trackedSortComplete? mol profile authoritative aux fuel cursors with
      | none => simp [sortedEq] at computed
      | some sorted =>
          cases insertedEq : FramedCompleteRuntime.trackedInsertComplete? mol profile authoritative aux fuel cursor sorted.1 with
          | none => simp [sortedEq, insertedEq] at computed
          | some inserted =>
              simp [sortedEq, insertedEq] at computed
              subst output
              exact .cons cursor cursors sorted inserted
                (inductionHypothesis sorted sortedEq)
                (frameInsertOccurrenceDerivation_of_production profile authoritative aux fuel cursor sorted.1 inserted
                  insertedEq)

inductive FrameAdjacentComparisonsDerivation (profile : FrameRuntime.Profile) (authoritative : Bool) (aux : OneCenter.OccurrenceAuxState) (fuel : Nat) :
    List CanonicalRerootCursor → List (OccurrenceComparedPair mol aux fuel) → Prop
  | nil : FrameAdjacentComparisonsDerivation profile authoritative aux fuel [] []
  | singleton (cursor : CanonicalRerootCursor) :
      FrameAdjacentComparisonsDerivation profile authoritative aux fuel [cursor] []
  | cons (left right : CanonicalRerootCursor) (remaining : List CanonicalRerootCursor)
      (decision : OccurrenceComparison) (deeper : List (OccurrenceComparedPair mol aux fuel))
      (stage : FrameRule45Evaluation (mol := mol) profile authoritative aux fuel
        { left := left, right := right, decision := decision })
      (tail : FrameAdjacentComparisonsDerivation profile authoritative aux fuel (right :: remaining) deeper) :
      FrameAdjacentComparisonsDerivation profile authoritative aux fuel (left :: right :: remaining)
        ({ left := left, right := right, decision := decision } :: deeper)

theorem FrameAdjacentComparisonsDerivation.production_eq
    {aux : OneCenter.OccurrenceAuxState} {fuel : Nat}
    {input : List CanonicalRerootCursor}
    {output : List (OccurrenceComparedPair mol aux fuel)}
    (derivation : FrameAdjacentComparisonsDerivation (mol := mol) profile authoritative aux fuel input output) :
    FramedCompleteRuntime.adjacentComplete? mol profile authoritative aux fuel input = some output := by
  induction derivation with
  | nil => rfl
  | singleton cursor => rfl
  | cons left right remaining decision deeper stage tail inductionHypothesis =>
      simp [FramedCompleteRuntime.adjacentComplete?, stage.production_eq, inductionHypothesis]

theorem frameAdjacentComparisonsDerivation_of_production
    (profile : FrameRuntime.Profile) (authoritative : Bool) (aux : OneCenter.OccurrenceAuxState) (fuel : Nat)
    (input : List CanonicalRerootCursor)
    (output : List (OccurrenceComparedPair mol aux fuel))
    (computed : FramedCompleteRuntime.adjacentComplete? mol profile authoritative aux fuel input = some output) :
    FrameAdjacentComparisonsDerivation (mol := mol) profile authoritative aux fuel input output := by
  induction input generalizing output with
  | nil =>
      simp [FramedCompleteRuntime.adjacentComplete?] at computed
      subst output
      exact .nil
  | cons left tail inductionHypothesis =>
      cases tail with
      | nil =>
          simp [FramedCompleteRuntime.adjacentComplete?] at computed
          subst output
          exact .singleton left
      | cons right remaining =>
          simp only [FramedCompleteRuntime.adjacentComplete?] at computed
          cases comparisonEq : FrameRuntime.decisionComplete? mol profile authoritative aux fuel left right with
          | none => simp [comparisonEq] at computed
          | some decision =>
              cases deeperEq : FramedCompleteRuntime.adjacentComplete? mol profile authoritative aux fuel
                  (right :: remaining) with
              | none => simp [comparisonEq, deeperEq] at computed
              | some deeper =>
                  simp [comparisonEq, deeperEq] at computed
                  subst output
                  exact .cons left right remaining decision deeper
                    (frameRule45Evaluation (mol := mol) profile authoritative aux fuel _ comparisonEq)
                    (inductionHypothesis deeper deeperEq)


theorem frameInsertOccurrenceDerivation_iff_production (profile : FrameRuntime.Profile)
    (authoritative : Bool) (aux : OccurrenceAuxState) (fuel : Nat)
    (candidate : CanonicalRerootCursor) (input : List CanonicalRerootCursor)
    (output : List CanonicalRerootCursor × Nat) :
    FrameInsertOccurrenceDerivation (mol := mol) profile authoritative aux fuel candidate input output ↔
      FramedCompleteRuntime.trackedInsertComplete? mol profile authoritative aux fuel candidate input =
        some output :=
  ⟨FrameInsertOccurrenceDerivation.production_eq,
    frameInsertOccurrenceDerivation_of_production profile authoritative aux fuel candidate input output⟩

theorem frameSortOccurrencesDerivation_iff_production (profile : FrameRuntime.Profile)
    (authoritative : Bool) (aux : OccurrenceAuxState) (fuel : Nat)
    (input : List CanonicalRerootCursor) (output : List CanonicalRerootCursor × Nat) :
    FrameSortOccurrencesDerivation (mol := mol) profile authoritative aux fuel input output ↔
      FramedCompleteRuntime.trackedSortComplete? mol profile authoritative aux fuel input = some output :=
  ⟨FrameSortOccurrencesDerivation.production_eq,
    frameSortOccurrencesDerivation_of_production profile authoritative aux fuel input output⟩

theorem frameAdjacentComparisonsDerivation_iff_production (profile : FrameRuntime.Profile)
    (authoritative : Bool) (aux : OccurrenceAuxState) (fuel : Nat)
    (input : List CanonicalRerootCursor) (output : List (OccurrenceComparedPair mol aux fuel)) :
    FrameAdjacentComparisonsDerivation (mol := mol) profile authoritative aux fuel input output ↔
      FramedCompleteRuntime.adjacentComplete? mol profile authoritative aux fuel input = some output :=
  ⟨FrameAdjacentComparisonsDerivation.production_eq,
    frameAdjacentComparisonsDerivation_of_production profile authoritative aux fuel input output⟩

end TetraStereo.OneCenter.FramedOrdinaryConformance
